#!/usr/bin/env python3
"""
Elaborates a term with subverso-helper and fails unless the helper accepts it.

Usage: ci/query-helper.py MODULE TERM

The script runs the helper with `lake env` in the current directory.
"""

import json
import signal
import subprocess
import sys

TIME_LIMIT_SECONDS = 300


def send(helper, message):
    """Writes a JSON message to the helper as a netstring."""
    payload = json.dumps(message).encode()
    helper.stdin.write(str(len(payload)).encode() + b":" + payload + b",")
    helper.stdin.flush()


def receive(helper):
    """Reads a netstring JSON message from the helper, or returns None at the end of its output."""
    length = b""
    while True:
        byte = helper.stdout.read(1)
        if not byte:
            return None
        if byte == b":":
            break
        length += byte
    payload = helper.stdout.read(int(length) + 1)
    return json.loads(payload[:-1])


def main():
    module, term = sys.argv[1:3]
    signal.alarm(TIME_LIMIT_SECONDS)
    helper = subprocess.Popen(
        ["lake", "env", "subverso-helper", module],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    send(helper, {"method": "term", "params": {"code": term}})
    response = receive(helper)
    if response is None:
        sys.exit(f"subverso-helper exited with code {helper.wait()} on {module}")
    if "result" not in response:
        sys.exit(f"subverso-helper rejected '{term}' in {module}: {response}")
    send(helper, {"method": "exit", "params": {}})
    helper.wait()
    print(f"subverso-helper elaborated '{term}' in {module}")


if __name__ == "__main__":
    main()
