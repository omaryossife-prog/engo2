import struct
import sys


def main() -> int:
    print("PROBE_STATUS=START", flush=True)
    print("Python executable:", sys.executable, flush=True)
    print("Python version:", sys.version.replace("\n", " "), flush=True)
    print("Architecture:", struct.calcsize("P") * 8, flush=True)

    valid = sys.version_info[:2] == (3, 13) and struct.calcsize("P") * 8 == 64
    print("PROBE_STATUS=OK" if valid else "PROBE_STATUS=REJECTED", flush=True)
    return 0 if valid else 2


if __name__ == "__main__":
    raise SystemExit(main())
