#!/usr/bin/env bash
set -euo pipefail

sos_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$sos_root"

python3 -c 'import sys; sys.exit("SOS setup requires Python 3.10 or newer") if sys.version_info < (3, 10) else None'
if ! python3 -m venv .venv-sos; then
  sos_python_version="$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
  echo "On Debian/Ubuntu, run: sudo apt install python${sos_python_version}-venv" >&2
  echo "Then rerun: bash 'Week 10/setup_sos.sh'" >&2
  exit 1
fi

.venv-sos/bin/python -m pip install -r 'Week 10/requirements-sos.txt'
.venv-sos/bin/python 'Week 10/find_sos.py' < 'Week 10/triangle-problem.json'
echo 'SOS setup complete. Re-elaborate the Lean example.'
