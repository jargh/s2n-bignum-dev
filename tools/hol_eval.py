#!/usr/bin/env python3
"""
Thin driver for interactive HOL Light evaluation from Claude Code.

Usage:
  python3 tools/hol_eval.py 'expr1;;' 'expr2;;' ...
  python3 tools/hol_eval.py --init 'arm/proofs/base.ml' 'expr;;'
  echo 'some_tactic;;' | python3 tools/hol_eval.py -

Each expression is sent to the running HOL Light toplevel and its output
is captured and printed. Uses the same sentinel mechanism as the HOL MCP
server in ~/hol-light/mcp/server.py.
"""

import argparse
import os
import queue
import re
import subprocess
import sys
import threading
import time

# Strip ANSI colour/bold codes from HOL Light output
_ANSI_RE = re.compile(r'\x1b\[[0-9;]*m')

HOL_DIR = os.path.expanduser("~/hol-light")
SENTINEL = "HOL_EVAL_DONE_b1c2d3e4"


def opam_env():
    """Return environment dict with opam paths activated for the hol-light switch."""
    env = os.environ.copy()
    switch = HOL_DIR + "/"
    result = subprocess.run(
        ["opam", "env", "--switch", switch, "--set-switch"],
        capture_output=True, text=True)
    if result.returncode != 0:
        return env
    for line in result.stdout.splitlines():
        # lines look like: export VAR='value'; or VAR='value'; export VAR;
        line = line.strip()
        if line.startswith("export ") and "=" in line:
            line = line[7:]
        if "=" in line and not line.startswith("#"):
            k, _, v = line.partition("=")
            k = k.strip()
            v = v.strip().rstrip(";").strip("'\"")
            env[k] = v
    return env


def reader_thread(proc, q):
    lines = []
    for raw in proc.stdout:
        line = _ANSI_RE.sub("", raw.rstrip("\n"))
        if SENTINEL in line:
            q.put("\n".join(lines))
            lines = []
        else:
            lines.append(line)
    q.put(None)   # signals process ended


def start_hol(workdir):
    env = opam_env()
    env["HOLLIGHT_DIR"] = HOL_DIR
    env["HOLLIGHT_USE_MODULE"] = "0"
    proc = subprocess.Popen(
        [os.path.join(HOL_DIR, "ocaml-hol"),
         "-init", os.path.join(HOL_DIR, "hol.ml"),
         "-I", HOL_DIR],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        env=env,
        cwd=workdir)
    q = queue.Queue()
    t = threading.Thread(target=reader_thread, args=(proc, q), daemon=True)
    t.start()
    return proc, q


def send(proc, q, code, timeout=300):
    """Send OCaml code and return output, blocking until sentinel."""
    expr = code.strip()
    if not expr.endswith(";;"):
        expr += ";;"
    expr += f'\nPrintf.printf "{SENTINEL}\\n%!";;\n'
    proc.stdin.write(expr)
    proc.stdin.flush()
    try:
        result = q.get(timeout=timeout)
        if result is None:
            return "[HOL Light process ended unexpectedly]"
        return result
    except queue.Empty:
        return f"[timeout after {timeout}s]"


def wait_ready(proc, q, timeout=300):
    """Wait for HOL Light hol.ml to finish loading."""
    proc.stdin.write(f'Printf.printf "{SENTINEL}\\n%!";;\n')
    proc.stdin.flush()
    try:
        result = q.get(timeout=timeout)
        return result if result is not None else "[died during startup]"
    except queue.Empty:
        return "[startup timeout]"


def main():
    ap = argparse.ArgumentParser(description="Evaluate HOL Light expressions.")
    ap.add_argument("exprs", nargs="*",
                    help="Expressions to evaluate (each should end with ;;)")
    ap.add_argument("--timeout", type=int, default=300,
                    help="Timeout per expression in seconds (default: 300)")
    ap.add_argument("--startup-timeout", type=int, default=300,
                    help="Timeout for HOL Light to start (default: 300)")
    ap.add_argument("--init", metavar="FILE",
                    help="Load this .ml file first (via loadt)")
    ap.add_argument("--workdir", default="/Users/jargh/s2n-bignum-dev",
                    help="Working directory (default: s2n-bignum-dev root)")
    args = ap.parse_args()

    exprs = list(args.exprs)

    # Accept stdin if '-' passed or stdin is a pipe
    if exprs == ["-"] or (not exprs and not sys.stdin.isatty()):
        exprs = [sys.stdin.read()]

    print(f"[hol_eval] Starting HOL Light (workdir={args.workdir}) ...",
          file=sys.stderr, flush=True)
    proc, q = start_hol(args.workdir)

    print(f"[hol_eval] Waiting for hol.ml to load (up to {args.startup_timeout}s) ...",
          file=sys.stderr, flush=True)
    startup = wait_ready(proc, q, timeout=args.startup_timeout)
    print(f"[hol_eval] Ready. ({len(startup)} chars of startup output suppressed)",
          file=sys.stderr, flush=True)

    if args.init:
        print(f"[hol_eval] Loading {args.init} ...", file=sys.stderr, flush=True)
        t0 = time.time()
        out = send(proc, q, f'loadt "{args.init}"', timeout=args.timeout)
        print(f"[hol_eval] Loaded in {time.time()-t0:.0f}s", file=sys.stderr, flush=True)
        if out.strip():
            print(out)

    for expr in exprs:
        label = expr.strip()[:60].replace("\n", " ")
        print(f"\n--- {label} ---", file=sys.stderr, flush=True)
        t0 = time.time()
        out = send(proc, q, expr, timeout=args.timeout)
        elapsed = time.time() - t0
        print(out)
        print(f"[{elapsed:.1f}s]", file=sys.stderr, flush=True)

    proc.stdin.close()
    proc.wait()


if __name__ == "__main__":
    main()
