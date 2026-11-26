"""Check that a successful Audit.lean transcript covers every requested axiom report."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
requests = re.findall(r'^#print axioms (\S+)$', (root / 'Audit.lean').read_text(), re.M)
transcript = Path(sys.argv[1]).read_text()
reports = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", transcript, re.M)
if [name for name, _ in reports] != requests:
    raise SystemExit('The requested and reported axiom lists differ.')
if re.search(r'\berror:|\bsorryAx\b', transcript):
    raise SystemExit('Replay transcript contains a diagnostic or placeholder axiom.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
used = {item.strip() for _, deps in reports for item in deps.split(',') if item.strip()}
if unexpected := used - allowed:
    raise SystemExit('Unexpected axiom dependencies: ' + ', '.join(sorted(unexpected)))
print(f'{len(reports)} axiom reports verified. Union: {", ".join(sorted(used))}.')
