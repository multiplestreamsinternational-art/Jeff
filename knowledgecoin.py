#!/usr/bin/env python3
"""
KnowledgeCoin (KNC) - reference implementation, stdlib only, MIT-style open source.

Design (Bitcoin-like, scaled to a 21-coin hard cap):
  * Proof-of-work, ~10 min blocks, difficulty retarget every 2016 blocks.
  * Subsidy halves every 210,000 blocks (~4 years). Total issuance < 21 KNC, forever.
  * Miners/ledger maintainers get subsidy + fees. After the subsidy fades out,
    fees alone pay for security (same long-term model as Bitcoin).
  * 20% of every subsidy (and 10% of fees) goes to an on-chain KNOWLEDGE TREASURY.
    The treasury is spent only through coin-weighted votes on grant proposals
    for open knowledge-sharing projects. No admin keys.
  * AI assistance is ADVISORY and off-chain: a pluggable reviewer scores proposals;
    its report hash is committed on-chain so voters can audit it. AI never
    decides consensus (consensus must be deterministic).

NOT audited. Pure-Python ECDSA is not constant-time. Do not hold real value
with this code before independent review.

Usage:
  python knowledgecoin.py demo
  python knowledgecoin.py wallet new --file alice.json
  python knowledgecoin.py node --port 8333 --miner <address> [--peers http://host:8333]
  python knowledgecoin.py send --wallet alice.json --to <addr> --amount 0.01
  python knowledgecoin.py propose --wallet alice.json --title ... --uri https://... --amount 0.5 --recipient <addr>
  python knowledgecoin.py vote --wallet alice.json --proposal <id> --yes
  python knowledgecoin.py balance <address>
"""
import argparse, copy, hashlib, hmac, json, os, secrets, threading, time
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ----------------------------------------------------------------- consensus
COIN = 10**12                              # 1 KNC = 10^12 base units
MAX_SUPPLY = 21 * COIN                     # hard cap: 21 coins
HALVING_INTERVAL = 210_000                 # blocks (~4 years at 10 min)
TARGET_BLOCK_TIME = 600
RETARGET_INTERVAL = 2016
INITIAL_REWARD = COIN // 20_000            # 2 * 210000 * INITIAL_REWARD == 21 COIN
TREASURY_SUBSIDY_PCT = 20
TREASURY_FEE_PCT = 10
GENESIS_BITS = 16                          # easiest allowed difficulty
MAX_TARGET = 2 ** (256 - GENESIS_BITS)
MAX_TXS_PER_BLOCK = 500
MIN_FEE = 1_000
PROPOSAL_DEPOSIT = INITIAL_REWARD // 5     # anti-spam, goes to treasury
GENESIS_TIME = 1_767_225_600
PARAMS = {"voting_blocks": 2016, "quorum_pct": 10}   # governance knobs


def subsidy(height):
    era = height // HALVING_INTERVAL
    return 0 if era >= 64 else INITIAL_REWARD >> era


def _check_supply_cap():
    total = sum((INITIAL_REWARD >> e) * HALVING_INTERVAL for e in range(64))
    assert total <= MAX_SUPPLY, "supply schedule exceeds cap"
    return total


# -------------------------------------------------------------------- crypto
def jdump(o):
    return json.dumps(o, sort_keys=True, separators=(",", ":")).encode()

def sha256(b): return hashlib.sha256(b).digest()
def sha256d(b): return sha256(sha256(b))

# secp256k1 (same curve as Bitcoin), minimal pure-Python ECDSA
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

def _add(p, q):
    if p is None: return q
    if q is None: return p
    if p[0] == q[0] and (p[1] + q[1]) % P == 0: return None
    if p == q: l = 3 * p[0] * p[0] * pow(2 * p[1], -1, P) % P
    else:      l = (q[1] - p[1]) * pow(q[0] - p[0], -1, P) % P
    x = (l * l - p[0] - q[0]) % P
    return (x, (l * (p[0] - x) - p[1]) % P)

def _mul(k, p=G):
    r = None
    while k:
        if k & 1: r = _add(r, p)
        p = _add(p, p); k >>= 1
    return r

def new_key(): return secrets.randbelow(N - 1) + 1
def pub_hex(priv):
    x, y = _mul(priv); return f"{x:064x}{y:064x}"
def addr_of(pub): return sha256(bytes.fromhex(pub)).hex()[:40]

def sign(priv, msg):
    z = int.from_bytes(sha256(msg), "big")
    k = int.from_bytes(hmac.new(priv.to_bytes(32, "big"), sha256(msg), hashlib.sha256).digest(), "big") % N or 1
    r = _mul(k)[0] % N
    s = pow(k, -1, N) * (z + r * priv) % N
    if s > N // 2: s = N - s
    return f"{r:064x}{s:064x}"

def verify(pub, msg, sig):
    try:
        x, y = int(pub[:64], 16), int(pub[64:], 16)
        if (y * y - x * x * x - 7) % P != 0: return False
        r, s = int(sig[:64], 16), int(sig[64:], 16)
        if not (0 < r < N and 0 < s < N): return False
        z = int.from_bytes(sha256(msg), "big")
        w = pow(s, -1, N)
        pt = _add(_mul(z * w % N), _mul(r * w % N, (x, y)))
        return pt is not None and pt[0] % N == r
    except Exception:
        return False


# -------------------------------------------------------------- transactions
def _body(tx): return {k: v for k, v in tx.items() if k != "sig"}
def tx_id(tx): return sha256d(jdump(_body(tx))).hex()

def make_tx(priv, kind, data, nonce, fee=MIN_FEE):
    body = {"type": kind, "sender": pub_hex(priv), "nonce": nonce, "fee": fee, "data": data}
    body["sig"] = sign(priv, jdump(body))
    return body

def tx_static_ok(tx):
    try:
        return (tx["type"] in ("TRANSFER", "PROPOSE", "VOTE") and isinstance(tx["fee"], int)
                and tx["fee"] >= MIN_FEE and isinstance(tx["nonce"], int) and tx["nonce"] >= 0
                and verify(tx["sender"], jdump(_body(tx)), tx["sig"]))
    except Exception:
        return False


# --------------------------------------------------------------------- state
class State:
    """Deterministic ledger state, rebuilt by replaying the chain."""
    def __init__(s):
        s.bal, s.nonce, s.props = {}, {}, {}
        s.treasury = 0
        s.issued = 0

    def credit(s, a, v): s.bal[a] = s.bal.get(a, 0) + v

    def apply_tx(s, tx, height):
        """Validates fully BEFORE mutating, so a failure leaves state unchanged."""
        if not tx_static_ok(tx): raise ValueError("malformed or badly signed tx")
        a = addr_of(tx["sender"])
        if tx["nonce"] != s.nonce.get(a, 0): raise ValueError("bad nonce")
        d, t, fee = tx["data"], tx["type"], tx["fee"]
        cost = fee
        if t == "TRANSFER":
            amt, to = d["amount"], d["to"]
            if not (isinstance(amt, int) and amt > 0 and isinstance(to, str) and len(to) == 40):
                raise ValueError("bad transfer")
            cost += amt
        elif t == "PROPOSE":
            if not (isinstance(d["title"], str) and 0 < len(d["title"]) <= 120
                    and isinstance(d["uri"], str) and 0 < len(d["uri"]) <= 300
                    and isinstance(d["amount"], int) and d["amount"] > 0
                    and isinstance(d["recipient"], str) and len(d["recipient"]) == 40
                    and isinstance(d.get("review_hash", ""), str) and len(d.get("review_hash", "")) <= 64):
                raise ValueError("bad proposal")
            cost += PROPOSAL_DEPOSIT
        elif t == "VOTE":
            p = s.props.get(d["proposal"])
            if not p or p["status"] != "open" or height >= p["end"]: raise ValueError("proposal not open")
            if a in p["voted"]: raise ValueError("already voted")
            if p["snapshot"].get(a, 0) <= 0: raise ValueError("no voting weight")
        if s.bal.get(a, 0) < cost: raise ValueError("insufficient funds")

        s.bal[a] -= cost
        s.nonce[a] = tx["nonce"] + 1
        if t == "TRANSFER":
            s.credit(d["to"], d["amount"])
        elif t == "PROPOSE":
            s.treasury += PROPOSAL_DEPOSIT
            s.props[tx_id(tx)] = {
                "proposer": a, "title": d["title"], "uri": d["uri"], "amount": d["amount"],
                "recipient": d["recipient"], "review_hash": d.get("review_hash", ""),
                "start": height, "end": height + PARAMS["voting_blocks"],
                "snapshot": dict(s.bal), "voted": [], "yes": 0, "no": 0, "status": "open"}
        elif t == "VOTE":
            p = s.props[d["proposal"]]
            p["voted"].append(a)
            p["yes" if d["yes"] else "no"] += p["snapshot"][a]
        return fee

    def apply_block(s, b):
        h = b["header"]["height"]
        fees = sum(s.apply_tx(tx, h) for tx in b["txs"])
        sub = subsidy(h)
        cut = sub * TREASURY_SUBSIDY_PCT // 100 + fees * TREASURY_FEE_PCT // 100
        s.treasury += cut
        s.credit(b["header"]["miner"], sub + fees - cut)
        s.issued += sub
        assert s.issued <= MAX_SUPPLY
        for p in s.props.values():                    # finalize ended votes
            if p["status"] == "open" and h >= p["end"]:
                quorum = s.issued * PARAMS["quorum_pct"] // 100
                if p["yes"] + p["no"] >= quorum and p["yes"] > p["no"]:
                    pay = min(p["amount"], s.treasury)
                    s.treasury -= pay
                    s.credit(p["recipient"], pay)
                    p["status"] = "funded"
                else:
                    p["status"] = "rejected"


# --------------------------------------------------------------------- chain
def block_hash(header): return sha256d(jdump(header)).hex()

def merkle(ids):
    if not ids: return "0" * 64
    l = [bytes.fromhex(i) for i in ids]
    while len(l) > 1:
        if len(l) % 2: l.append(l[-1])
        l = [sha256d(l[i] + l[i + 1]) for i in range(0, len(l), 2)]
    return l[0].hex()

def genesis():
    return {"header": {"height": 0, "prev": "0" * 64, "time": GENESIS_TIME, "merkle": "0" * 64,
                       "target": format(MAX_TARGET, "x"), "nonce": 0, "miner": "0" * 40}, "txs": []}

def work(b): return 2**256 // (int(b["header"]["target"], 16) + 1)


class Chain:
    def __init__(s, path=None):
        s.blocks, s.state, s.mempool = [genesis()], State(), {}
        s.lock, s.path = threading.RLock(), path
        if path and os.path.exists(path):
            for b in json.load(open(path))[1:]:
                s.add_block(b, save=False)

    def height(s): return len(s.blocks) - 1

    def expected_target(s, h):
        prev = s.blocks[h - 1]
        pt = int(prev["header"]["target"], 16)
        if h % RETARGET_INTERVAL: return pt
        first = s.blocks[h - RETARGET_INTERVAL]
        exp = TARGET_BLOCK_TIME * (RETARGET_INTERVAL - 1)
        actual = prev["header"]["time"] - first["header"]["time"]
        actual = max(exp // 4, min(exp * 4, actual))
        return min(MAX_TARGET, pt * actual // exp)

    def add_block(s, b, save=True):
        with s.lock:
            hd, h = b["header"], len(s.blocks)
            prev = s.blocks[-1]["header"]
            if hd["height"] != h or hd["prev"] != block_hash(prev): raise ValueError("does not extend tip")
            if int(hd["target"], 16) != s.expected_target(h): raise ValueError("wrong difficulty")
            if int(block_hash(hd), 16) > int(hd["target"], 16): raise ValueError("insufficient work")
            if not (prev["time"] < hd["time"] <= time.time() + 7200): raise ValueError("bad timestamp")
            if len(b["txs"]) > MAX_TXS_PER_BLOCK: raise ValueError("too many txs")
            if hd["merkle"] != merkle([tx_id(t) for t in b["txs"]]): raise ValueError("bad merkle root")
            if not (isinstance(hd["miner"], str) and len(hd["miner"]) == 40): raise ValueError("bad miner")
            st = copy.deepcopy(s.state)
            st.apply_block(b)                       # raises if any tx invalid
            s.blocks.append(b); s.state = st
            for t in b["txs"]: s.mempool.pop(tx_id(t), None)
            if save and s.path: json.dump(s.blocks, open(s.path, "w"))

    def add_tx(s, tx):
        with s.lock:
            if not tx_static_ok(tx): raise ValueError("invalid tx")
            if tx["nonce"] < s.state.nonce.get(addr_of(tx["sender"]), 0): raise ValueError("stale nonce")
            s.mempool[tx_id(tx)] = tx

    def pending_nonce(s, addr):
        with s.lock:
            n = s.state.nonce.get(addr, 0)
            return n + sum(1 for t in s.mempool.values() if addr_of(t["sender"]) == addr)

    def try_replace(s, blocks):
        """Adopt a competing chain if it is valid and has more cumulative work."""
        if blocks[0] != genesis(): return False
        cand = Chain()
        try:
            for b in blocks[1:]: cand.add_block(b, save=False)
        except Exception:
            return False
        with s.lock:
            if sum(map(work, cand.blocks)) <= sum(map(work, s.blocks)): return False
            s.blocks, s.state = cand.blocks, cand.state
            s.mempool = {k: t for k, t in s.mempool.items()
                         if t["nonce"] >= s.state.nonce.get(addr_of(t["sender"]), 0)}
            if s.path: json.dump(s.blocks, open(s.path, "w"))
            return True

    def mine(s, miner, stop=None):
        with s.lock:
            h, prev = len(s.blocks), s.blocks[-1]["header"]
            st, chosen = copy.deepcopy(s.state), []
            cands = sorted(s.mempool.values(), key=lambda t: (-t["fee"], t["nonce"]))
            for _ in range(3):                      # multiple passes resolve nonce ordering
                for tx in cands:
                    if tx in chosen or len(chosen) >= MAX_TXS_PER_BLOCK: continue
                    try: st.apply_tx(tx, h); chosen.append(tx)
                    except ValueError: pass
            hd = {"height": h, "prev": block_hash(prev), "time": max(int(time.time()), prev["time"] + 1),
                  "merkle": merkle([tx_id(t) for t in chosen]),
                  "target": format(s.expected_target(h), "x"), "nonce": 0, "miner": miner}
        target = int(hd["target"], 16)
        while int(block_hash(hd), 16) > target:
            hd["nonce"] += 1
            if stop and hd["nonce"] % 2000 == 0 and (stop.is_set() or s.height() >= h): return None
        b = {"header": hd, "txs": chosen}
        s.add_block(b)
        return b


# ---------------------------------------------------- AI-assisted grant review
class HeuristicReviewer:
    """Offline, deterministic baseline. Replace/extend with an LLM reviewer.

    Contract: review(proposal) -> {"score": 0-100, "notes": [...]}.
    The proposer (or anyone) publishes the JSON report anywhere (IPFS, git, web)
    and puts sha256(report) in the proposal's `review_hash`, so voters can verify
    they are reading the same report. Advisory only - never part of consensus.
    """
    def review(self, p):
        score, notes = 50, []
        uri = p["uri"].lower()
        if uri.startswith("https://"): score += 10; notes.append("HTTPS project link")
        else: score -= 15; notes.append("Project link is not HTTPS")
        text = (p["title"] + " " + uri).lower()
        if any(w in text for w in ("open", "wiki", "edu", "learn", "library", "translate", "archive")):
            score += 15; notes.append("Mentions open/educational themes")
        if p["amount"] > 5 * COIN: score -= 20; notes.append("Very large request relative to supply")
        if len(p["title"]) < 12: score -= 10; notes.append("Title too vague")
        return {"score": max(0, min(100, score)), "notes": notes}

def review_hash(report): return sha256(jdump(report)).hex()
# An LLM reviewer can implement the same review() method: send the proposal text,
# a rubric (openness, reach, cost, track record) and parse a JSON score back.


# ------------------------------------------------------------------ networking
def http(url, obj=None, timeout=10):
    req = urllib.request.Request(url, data=None if obj is None else json.dumps(obj).encode(),
                                 headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=timeout))

def serve(chain, port, peers, miner):
    def broadcast(path, obj):
        for p in peers:
            try: http(p + path, obj, 3)
            except Exception: pass

    class H(BaseHTTPRequestHandler):
        def log_message(self, *a): pass
        def reply(self, obj, code=200):
            data = json.dumps(obj).encode()
            self.send_response(code); self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data))); self.end_headers(); self.wfile.write(data)
        def do_GET(self):
            st = chain.state
            if self.path == "/info":
                self.reply({"height": chain.height(), "issued": st.issued / COIN, "treasury": st.treasury / COIN,
                            "max_supply": MAX_SUPPLY / COIN, "next_reward": subsidy(chain.height() + 1) / COIN})
            elif self.path == "/chain": self.reply(chain.blocks)
            elif self.path.startswith("/account/"):
                a = self.path.split("/")[-1]
                self.reply({"balance": st.bal.get(a, 0), "nonce": chain.pending_nonce(a)})
            elif self.path == "/proposals":
                self.reply({k: {x: y for x, y in v.items() if x not in ("snapshot", "voted")}
                            for k, v in st.props.items()})
            else: self.reply({"error": "not found"}, 404)
        def do_POST(self):
            try:
                obj = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                if self.path == "/tx":
                    chain.add_tx(obj); threading.Thread(target=broadcast, args=("/tx", obj)).start()
                elif self.path == "/block":
                    chain.add_block(obj)
                else: return self.reply({"error": "not found"}, 404)
                self.reply({"ok": True})
            except Exception as e:
                self.reply({"error": str(e)}, 400)

    def sync_loop():
        while True:
            for p in peers:
                try: chain.try_replace(http(p + "/chain", timeout=30))
                except Exception: pass
            time.sleep(30)

    def mine_loop():
        while True:
            stop = threading.Event()
            b = chain.mine(miner, stop)
            if b: print(f"mined block {b['header']['height']}"); broadcast("/block", b)

    threading.Thread(target=sync_loop, daemon=True).start()
    if miner: threading.Thread(target=mine_loop, daemon=True).start()
    print(f"node on :{port} | miner={miner or 'off'} | peers={peers}")
    ThreadingHTTPServer(("0.0.0.0", port), H).serve_forever()


# ------------------------------------------------------------------------ CLI
def load_wallet(path): return int(json.load(open(path))["priv"], 16)

def submit(args, kind, data):
    priv = load_wallet(args.wallet)
    a = addr_of(pub_hex(priv))
    nonce = http(f"{args.node}/account/{a}")["nonce"]
    tx = make_tx(priv, kind, data, nonce)
    http(args.node + "/tx", tx)
    print("submitted", tx_id(tx))

def demo():
    print(f"Schedule check: lifetime issuance = {_check_supply_cap() / COIN:.10f} KNC (cap 21)")
    PARAMS.update(voting_blocks=4, quorum_pct=1)
    ch = Chain()
    alice, bob = new_key(), new_key()
    A, B = addr_of(pub_hex(alice)), addr_of(pub_hex(bob))
    for _ in range(6): ch.mine(A)
    print("alice balance:", ch.state.bal[A] / COIN, "| treasury:", ch.state.treasury / COIN)

    ch.add_tx(make_tx(alice, "TRANSFER", {"to": B, "amount": 1_000_000}, ch.pending_nonce(A)))
    prop = {"title": "Open multilingual wiki translator", "uri": "https://example.org/open-wiki",
            "amount": 30_000_000, "recipient": B}
    report = HeuristicReviewer().review(prop)
    print("AI-advisory review:", report)
    prop["review_hash"] = review_hash(report)
    ptx = make_tx(alice, "PROPOSE", prop, ch.pending_nonce(A))
    ch.add_tx(ptx); ch.mine(A)
    pid = tx_id(ptx)
    ch.add_tx(make_tx(alice, "VOTE", {"proposal": pid, "yes": True}, ch.pending_nonce(A)))
    for _ in range(5): ch.mine(A)
    p = ch.state.props[pid]
    print("proposal status:", p["status"], "| bob balance:", ch.state.bal[B] / COIN)
    total = sum(ch.state.bal.values()) + ch.state.treasury
    assert total == ch.state.issued, "conservation violated"
    print(f"conservation OK: balances + treasury == issued == {ch.state.issued / COIN} KNC")
    assert ch.try_replace(copy.deepcopy(ch.blocks)) is False
    print("demo passed")

def main():
    ap = argparse.ArgumentParser(); sp = ap.add_subparsers(dest="cmd", required=True)
    w = sp.add_parser("wallet"); w.add_argument("action"); w.add_argument("--file", default="wallet.json")
    n = sp.add_parser("node"); n.add_argument("--port", type=int, default=8333)
    n.add_argument("--miner", default=""); n.add_argument("--peers", nargs="*", default=[])
    n.add_argument("--data", default="chain.json")
    for name in ("send", "propose", "vote"):
        c = sp.add_parser(name); c.add_argument("--wallet", required=True)
        c.add_argument("--node", default="http://127.0.0.1:8333")
        if name == "send": c.add_argument("--to", required=True); c.add_argument("--amount", type=float, required=True)
        if name == "propose":
            c.add_argument("--title", required=True); c.add_argument("--uri", required=True)
            c.add_argument("--amount", type=float, required=True); c.add_argument("--recipient", required=True)
        if name == "vote": c.add_argument("--proposal", required=True); c.add_argument("--yes", action="store_true")
    b = sp.add_parser("balance"); b.add_argument("address"); b.add_argument("--node", default="http://127.0.0.1:8333")
    sp.add_parser("demo")
    a = ap.parse_args()
    if a.cmd == "demo": demo()
    elif a.cmd == "wallet":
        k = new_key(); json.dump({"priv": f"{k:064x}"}, open(a.file, "w"))
        print("address:", addr_of(pub_hex(k)), "\nsaved to", a.file, "(keep it secret!)")
    elif a.cmd == "node": serve(Chain(a.data), a.port, a.peers, a.miner)
    elif a.cmd == "send": submit(a, "TRANSFER", {"to": a.to, "amount": int(a.amount * COIN)})
    elif a.cmd == "propose":
        prop = {"title": a.title, "uri": a.uri, "amount": int(a.amount * COIN), "recipient": a.recipient}
        rep = HeuristicReviewer().review(prop); print("AI-advisory review:", rep)
        prop["review_hash"] = review_hash(rep); submit(a, "PROPOSE", prop)
    elif a.cmd == "vote": submit(a, "VOTE", {"proposal": a.proposal, "yes": a.yes})
    elif a.cmd == "balance": print(http(f"{a.node}/account/{a.address}")["balance"] / COIN, "KNC")

if __name__ == "__main__":
    main()
