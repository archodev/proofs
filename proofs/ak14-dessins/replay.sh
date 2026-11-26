#!/bin/sh
set -eu
cd "$(dirname "$0")"
lean --version
lake --version
python3 prepare_dependency.py
lake build
lake env lean Audit.lean > replay-audit.txt
python3 check_audit.py replay-audit.txt
lake env lean AuditImports.lean > import-audit.txt
cat import-audit.txt
lake env leanchecker -v AK14.Dessins AK14.Uniformization > kernel-replay.txt
cat kernel-replay.txt
python3 check_dessins.py > finite-checks.txt
cat finite-checks.txt
