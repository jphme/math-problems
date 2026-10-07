"""Compute weak (Maker-Breaker) and strong (maker-maker) board/move numbers for the
polyominoes of A380597/A380598 with index n (sizes <= 5), and compare with OEIS.

For the weak game every claim is backed by a certificate checked by check_cert.py:
  * Breaker win in the full game on (b-1) x (b-1)       -> board number >= b
  * Maker win within m moves on b x b                    -> board number <= b, moves <= m
  * Breaker win against m-1 Maker moves on b x b         -> moves >= m
For the strong game only the solver's verdict is recorded (see README).

usage: uv run python validate_small.py --game weak|strong [--n 1,2,...] [--bmax 8] [--time-limit 600]
Appends one JSON record per solver run to results/validate_<game>.jsonl.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SOLVER = os.path.join(HERE, "solver")
# flags for runs whose expected outcome is a Breaker win (null move off, pairing rules on)
BRK = ["--no-null", "--pair-budget", "300", "--pair-try", "20", "--pair-strat", "10"]


def num(x, y):
    d = x + y
    return d * (d + 1) // 2 + y


def decode(c):
    return [(d - y, y) for d in range(12) for y in range(d + 1) if c >> num(d - y, y) & 1]


def read_b(path):
    out = {}
    for line in open(path):
        if line.strip() and not line.startswith("#"):
            i, v = line.split()
            out[int(i)] = int(v)
    return out


def run(args, tl):
    cmd = [SOLVER] + args + ["--time-limit", str(tl), "--tt-mb", "1024", "--max-rss-mb", "3000"]
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.stdout


def check(cert):
    p = subprocess.run(["uv", "run", "python", os.path.join(HERE, "check_cert.py"), cert], capture_output=True, text=True)
    return p.stdout.strip()


def parse_done(out):
    for line in out.splitlines():
        if line.startswith("DONE maker_wins"):
            return ("win", int(line.split("=")[1]))
        if line.startswith("DONE maker_cannot_win"):
            return ("nowin", None)
        if line.startswith("ABORT"):
            return ("abort", line)
    return ("error", out[-500:])


def main():
    a = sys.argv[1:]
    game = a[a.index("--game") + 1]
    ns = [int(x) for x in a[a.index("--n") + 1].split(",")] if "--n" in a else list(range(1, 22))
    bmax = int(a[a.index("--bmax") + 1]) if "--bmax" in a else 8
    tl = int(a[a.index("--time-limit") + 1]) if "--time-limit" in a else 600
    od = os.path.join(HERE, "..", "oeis_fetch")
    b246 = read_b(os.path.join(od, "b246521.txt"))
    a97 = read_b(os.path.join(od, "b380597.txt"))
    a98 = read_b(os.path.join(od, "b380598.txt"))
    resf = open(os.path.join(HERE, "results", f"validate_{game}.jsonl"), "a")
    os.makedirs(os.path.join(HERE, "certs", "small"), exist_ok=True)
    for n in ns:
        code = b246[n + 1]
        cells = decode(code)
        shape = ";".join(f"{x},{y}" for x, y in cells)
        rec = {"n": n, "code": code, "shape": shape, "game": game, "oeis_board": a97[n], "oeis_moves": a98[n]}
        board = None
        status = "ok"
        for b in range(1, bmax + 1):
            if len(cells) > b * b:
                continue
            if game == "weak":
                cert = os.path.join(HERE, "certs", "small", f"n{n}_b{b}_full.txt")
                out = run(["--board", str(b), "--shape", shape, "--full", "--cert", cert] + BRK, tl)
            else:
                cert = None
                out = run(["--board", str(b), "--shape", shape, "--game", "strong"], tl)
            r = parse_done(out)
            entry = {"step": "full", "b": b, "result": r[0]}
            if cert and r[0] in ("win", "nowin"):
                entry["check"] = check(cert)
            if game == "strong" and r[0] == "win":
                entry["min_moves"] = r[1]
            rec.setdefault("runs", []).append(entry)
            print(n, b, entry, flush=True)
            if r[0] in ("abort", "error"):
                status = f"unresolved at b={b}"
                break
            if r[0] == "win":
                board = b
                break
        rec["board"] = board
        rec["status"] = status
        if board is not None:
            if game == "weak":
                cert = os.path.join(HERE, "certs", "small", f"n{n}_b{board}_moves.txt")
                out = run(["--board", str(board), "--shape", shape, "--cert", cert], tl)
                r = parse_done(out)
                rec["moves"] = r[1] if r[0] == "win" else None
                rec["moves_check"] = check(cert) if r[0] == "win" else None
                if r[0] == "win" and r[1] > 1:
                    m = r[1]
                    cert2 = os.path.join(HERE, "certs", "small", f"n{n}_b{board}_lt{m}.txt")
                    out = run(["--board", str(board), "--shape", shape, "--dmin", str(m - 1), "--dmax", str(m - 1), "--cert", cert2] + BRK, tl)
                    rec["moves_lower_check"] = check(cert2)
            else:
                rec["moves"] = rec["runs"][-1].get("min_moves")
        rec["matches_oeis"] = (rec["board"] or 0) == a97[n] and (rec.get("moves") or 0) == a98[n]
        print(json.dumps(rec), flush=True)
        resf.write(json.dumps(rec) + "\n")
        resf.flush()


if __name__ == "__main__":
    main()
