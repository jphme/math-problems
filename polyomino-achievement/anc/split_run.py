"""Resumable root-split driver for long Snaky runs.

Breaker mode (prove Breaker wins the full weak game on k x k):
  one solver job per symmetry class of Maker's first cell m, each solving the
  position {Maker: m}, Breaker to move, with a certificate that check_cert.py
  verifies. Breaker wins from the empty board iff he wins after every first Maker
  move; by the board's symmetry one representative per orbit suffices (the script
  recomputes the orbits and checks they cover every cell).
Maker mode (look for a Maker win within --budget moves on k x k):
  one job per orbit representative m with opening m; the first job that proves a
  Maker win (certificate checked) settles the question, and the driver then stops
  the jobs still running and starts no new ones.

Every finished job appends one JSON record to results/<tag>.jsonl (and the solver
appends progress records). On restart, jobs with a final record are skipped, so an
interrupted run loses only the jobs in flight. Prints a final DONE or ABORT line.

Resource caps per job: the solver's --max-rss-mb and --time-limit (job-hours) cover
the search and the certificate export; the solver exits before check_cert.py starts,
and the checker runs with the same --max-rss-mb and its own job-hours time limit. So a
job never holds more than --max-rss-mb, and takes at most 2 x job-hours (the checker
is about 15x faster than search plus export in the 8x8 runs). A job is final only if
the checker prints PASS with the expected board, shape, kind, budget and opening.

usage:
  uv run python split_run.py --mode breaker --board 9 --tag b9_breaker \\
      --max-rss-mb 6000 --tt-mb 4096 --job-hours 6 [--jobs 1..3]
  uv run python split_run.py --mode maker --board 16 --budget 15 --tag b16_m15 ...
"""
import json
import os
import subprocess
import sys
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
SNAKY = "0,0;1,0;2,0;3,0;3,1;4,1"
BRK = ["--no-null", "--pair-budget", "300", "--pair-try", "20", "--pair-strat", "10"]
MKR = ["--pair-budget", "300", "--pair-try", "20", "--pair-strat", "10"]


def orbits(k):
    def syms(x, y):
        out = set()
        for t in range(8):
            a, b = x, y
            if t & 1:
                a = k - 1 - a
            if t & 2:
                b = k - 1 - b
            if t & 4:
                a, b = b, a
            out.add(b * k + a)
        return out

    seen, reps = set(), []
    for c in range(k * k):
        if c in seen:
            continue
        orb = syms(c % k, c // k)
        seen |= orb
        reps.append((c, sorted(orb)))
    assert seen == set(range(k * k))
    return reps


def arg(a, name, default=None, cast=str):
    return cast(a[a.index(name) + 1]) if name in a else default


def main():
    a = sys.argv[1:]
    mode = arg(a, "--mode")
    k = arg(a, "--board", cast=int)
    tag = arg(a, "--tag")
    rss = arg(a, "--max-rss-mb", 4000, int)
    tt = arg(a, "--tt-mb", 2048, int)
    hours = arg(a, "--job-hours", 1.0, float)
    jobs = min(3, arg(a, "--jobs", 1, int))
    budget = arg(a, "--budget", None, int)
    shape = arg(a, "--shape", SNAKY)  # default Snaky; other shapes are for testing the driver
    if tt + 200 > rss:
        print(f"ABORT config: --tt-mb {tt} + 200 exceeds --max-rss-mb {rss}")
        sys.exit(3)
    if jobs * rss > 12000:
        print("ABORT config: jobs * max-rss-mb exceeds 12000 MB")
        sys.exit(3)
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "certs", tag), exist_ok=True)
    resf = os.path.join(HERE, "results", f"{tag}.jsonl")
    done = {}
    if os.path.exists(resf):
        for line in open(resf):
            r = json.loads(line)
            if r.get("final"):
                done[r["first_move"]] = r
    reps = orbits(k)
    stop = threading.Event()
    running = set()
    lock = threading.Lock()

    def run(cmd):
        """run a subprocess that the driver can terminate once a Maker win is certified"""
        with lock:
            if stop.is_set():
                return None
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
            running.add(p)
        out = p.communicate()[0]
        with lock:
            running.discard(p)
        return None if stop.is_set() else out

    def job(rep):
        c, orb = rep
        if c in done:
            return done[c]
        if stop.is_set():
            return None
        cert = os.path.join(HERE, "certs", tag, f"m{c}.txt")
        cmd = [os.path.join(HERE, "solver"), "--board", str(k), "--shape", shape, "--opening", str(c),
               "--tt-mb", str(tt), "--max-rss-mb", str(rss), "--time-limit", str(int(hours * 3600)),
               "--results", resf, "--tag", f"{tag}_m{c}", "--progress-sec", "600", "--cert", cert]
        if mode == "breaker":
            cmd += ["--full"] + BRK
        else:
            cmd += ["--dmin", str(budget - 1), "--dmax", str(budget - 1)] + MKR  # Maker used one move on m
        out = run(cmd)
        if out is None:  # stopped after a certified Maker win elsewhere; drop the partial certificate
            if os.path.exists(cert):
                os.remove(cert)
            return None
        res = "abort"
        for line in out.splitlines():
            if line.startswith("DONE maker_wins"):
                res = "maker_wins"
            elif line.startswith("DONE maker_cannot_win"):
                res = "maker_cannot_win"
        chk = ""
        if res != "abort" and os.path.exists(cert):
            want_kind = "makerwin" if res == "maker_wins" else "breakerwin"
            want_budget = -1 if mode == "breaker" else budget - 1
            chk = run(["uv", "run", "python", os.path.join(HERE, "check_cert.py"), cert,
                       "--expect-board", f"{k}x{k}", "--expect-shape", shape,
                       "--expect-kind", want_kind, "--expect-budget", str(want_budget),
                       "--expect-opening", str(c),
                       "--max-rss-mb", str(rss), "--time-limit", str(int(hours * 3600))])
            if chk is None:  # stopped while checking: the certificate is unverified, drop it
                os.remove(cert)
                return None
            chk = chk.strip()
        rec = {"tag": tag, "final": res != "abort", "first_move": c, "orbit": orb, "result": res,
               "check": chk, "solver_tail": out.strip().splitlines()[-3:]}
        if res != "abort" and not chk.startswith("PASS"):
            rec["final"] = False
            rec["result"] = "check_aborted" if chk.startswith("ABORT") else "check_failed"
        with open(resf, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(json.dumps({k2: rec[k2] for k2 in ("first_move", "result", "check")}), flush=True)
        return rec

    recs = [None] * len(reps)
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(job, rep): i for i, rep in enumerate(reps)}
        for f in as_completed(futs):
            if f.cancelled():
                continue
            r = f.result()
            recs[futs[f]] = r
            if mode == "maker" and r and r["result"] == "maker_wins" and r["check"].startswith("PASS"):
                with lock:
                    stop.set()
                    for p in running:
                        p.terminate()
                for g in futs:
                    g.cancel()
    recs = [r if r is not None else {"result": "stopped", "check": ""} for r in recs]
    covered = set()
    for rep, r in zip(reps, recs):
        if mode == "breaker" and r["result"] == "maker_cannot_win" and r["check"].startswith("PASS"):
            covered |= set(rep[1])
        if mode == "maker" and r["result"] == "maker_wins" and r["check"].startswith("PASS"):
            print(f"DONE maker_wins board={k} budget={budget} first_move={rep[0]} certificate=certs/{tag}/m{rep[0]}.txt")
            return
    if mode == "breaker":
        if covered == set(range(k * k)):
            print(f"DONE breaker_wins board={k}: all {len(reps)} first-move classes certified")
        else:
            print(f"ABORT unresolved first-move classes: {[r[0] for r, x in zip(reps, recs) if x['result'] != 'maker_cannot_win']}")
    else:
        if all(r["result"] == "maker_cannot_win" for r in recs):
            print(f"DONE maker_cannot_win board={k} budget={budget} (every first move refuted, certificates checked)")
        else:
            print("ABORT some first moves unresolved")


if __name__ == "__main__":
    main()
