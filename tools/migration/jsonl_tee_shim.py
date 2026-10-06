#!/usr/bin/env python3
"""Logging pass-through for a JSON Lines service: SHIM_REAL is the real binary,
SHIM_LOG the file that records each request line and its response line."""
import os, subprocess, sys
real, log = os.environ["SHIM_REAL"], os.environ["SHIM_LOG"]
p = subprocess.Popen([real], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
with open(log, "a", buffering=1) as lg:
    for line in sys.stdin:
        p.stdin.write(line); p.stdin.flush()
        resp = p.stdout.readline()
        lg.write("REQ " + line.rstrip("\n") + "\nRES " + resp.rstrip("\n") + "\n")
        sys.stdout.write(resp); sys.stdout.flush()
p.stdin.close(); p.wait()
