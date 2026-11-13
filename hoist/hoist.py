"""Hoist the rounding lattice out of `LeanLLVM/JSON/Strtod.lean` into
`LeanLLVM/Binary64.lean`.

The lattice is the set of declarations of `LeanLLVM.JSON` that a binary64
rounding needs: the magnitude predicate and its code types, the
binade/ulp/significand arithmetic, the two nearest-even choosers, `roundMag`, and
the theorems those are stated and proved with.  The decimal specification
(`Decimal`, `JSON.Binary64`, `strtodSpec`, the number-record arms) stays where it
is; every reference it makes to the lattice resolves through the enclosing
`LeanLLVM` namespace once the lattice is declared there.

The lattice occupies one contiguous region of `Strtod.lean`, from the
`### The binary64 lattice` doc block through `roundMag_mono`, with the
decimal-specification declarations interleaved in it.  This script walks that
region's declaration spans, removes the spans that are not in `KEEP`, and writes
them, in order, into `Binary64.lean` in place of the duplicate lattice it
currently carries between the `### The lattice` and `### The encoding` blocks.

The script writes `hoist/pins.sed`, then applies it: the pin renames are the
mechanical part of the move, and the file it applied is the record of them.  Each
rename is `#print axioms LeanLLVM.JSON.<moved>` to `LeanLLVM.<moved>`, computed
from the declarations the span walk actually moved rather than from a hand-kept
list, so a pin whose declaration stays in `JSON` is left alone and a pin whose
declaration moves cannot be missed.
"""
import io, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STRTOD = os.path.join(ROOT, 'LeanLLVM/JSON/Strtod.lean')
BIN64 = os.path.join(ROOT, 'LeanLLVM/Binary64.lean')
PINS = os.path.join(ROOT, 'hoist/pins.sed')

# The decimal specification's own declarations inside the lattice region.
KEEP = {
    'strtodSpec', 'strtodSpec_isCode', 'strtodSpec_zero',
    'bitsBytes', 'NumberRecordAt', 'EventStreamNumberArm',
    'numberArm_payload', 'strtodSpec_isNumberArm', 'numberArm_isCode',
    'NumberArmOwed',
}

DECL = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:private |protected |noncomputable |partial )?'
                  r'(theorem|lemma|def|structure|inductive|abbrev|namespace)\s+([\w.\']+)')

lines = io.open(STRTOD, encoding='utf-8').read().split('\n')

region_start = next(i for i, l in enumerate(lines) if l.startswith('/-! ### The binary64 lattice'))
region_end = next(i for i, l in enumerate(lines) if l.startswith('theorem strtodSpec_mono'))
# `region_end` is the declaration line; take its doc block with it.
while region_end > region_start and lines[region_end - 1].lstrip().startswith('--'):
    region_end -= 1
if region_end > region_start and lines[region_end - 1].rstrip().endswith('-/'):
    k = region_end - 1
    while k > region_start and '/-' not in lines[k]:
        k -= 1
    if lines[k].lstrip().startswith('/-'):
        region_end = k


def doc_start(i, lo):
    """Start of the comment block immediately above line `i`, or `i`."""
    j = i
    while j > lo and lines[j-1].lstrip().startswith('--'):
        j -= 1
    if j > lo and lines[j-1].rstrip().endswith('-/'):
        k = j - 1
        while k > lo and '/-' not in lines[k]:
            k -= 1
        if lines[k].lstrip().startswith('/-'):
            j = k
    return j


starts = []
for i in range(region_start, region_end):
    m = DECL.match(lines[i])
    if m and lines[i][0] not in ' ':
        starts.append((doc_start(i, region_start), i, m.group(1), m.group(2)))

spans = []
for idx, (j, i, kind, name) in enumerate(starts):
    if kind == 'namespace':
        e = next(k for k in range(i, region_end) if lines[k].startswith('end ' + name))
        spans.append(('namespace', name, j, e + 1))
        continue
    if any(a <= i < b for _, _, a, b in spans):
        continue
    nxt = starts[idx + 1][0] if idx + 1 < len(starts) else region_end
    spans.append((kind, name, j, nxt))

moved = [(n, a, b) for _, n, a, b in spans if n not in KEEP]
kept = [(n, a, b) for _, n, a, b in spans if n in KEEP]
missing = KEEP - {n for n, _, _ in kept}
if missing:
    print('NOT FOUND:', sorted(missing))
    sys.exit(1)

# The fully-qualified names whose pins move: each top-level declaration, and
# each declaration inside a moved namespace (the `Code` block).
moved_names = []
for n, a, b in moved:
    moved_names.append(n)
    if lines[a].startswith('namespace '):
        for k in range(a + 1, b):
            m = DECL.match(lines[k])
            if m:
                moved_names.append(n + '.' + m.group(2))

moved_names = list(dict.fromkeys(moved_names))

render = lambda ss: '\n\n'.join('\n'.join(lines[a:b]).rstrip() for _, a, b in ss)
moved_text = render(moved)
kept_text = render(kept)

# ---------------------------------------------------------------- Binary64
bin64 = io.open(BIN64, encoding='utf-8').read()
head = bin64[:bin64.index('/-! ### The lattice')]
enc = bin64.index('/-! ### The encoding')
tail = bin64[enc:]
lattice_doc = '''/-! ### The lattice, hoisted from `LeanLLVM.JSON.Strtod`

`IsB64Mag` is the set of tick counts a binary64 value can have, `Code` is an
encoding's exponent field and significand, and `findFrom`/`binade` locate the
binade.  `subCode`/`normalCode` choose the nearest code with the even significand
on a tie, and `roundMag` rounds an exact `P / d` in ticks to the nearest
magnitude.  The decimal specification of `LeanLLVM.JSON.Strtod` imports this
module and reads `roundMag` from here. -/

'''
io.open(BIN64, 'w', encoding='utf-8').write(head + lattice_doc + moved_text + '\n\n' + tail)

# ---------------------------------------------------------------- Strtod
header = '\n'.join(lines[:region_start]).replace(
    'import LeanLLVM.JSON.Spec', 'import LeanLLVM.Binary64\nimport LeanLLVM.JSON.Spec')
if 'import LeanLLVM.Binary64' not in header:
    print('the Spec import was not found; the header is not the expected one')
    sys.exit(1)
io.open(STRTOD, 'w', encoding='utf-8').write(
    header + '\n\n' +
    '\n\n'.join(('\n'.join(lines[a:b]).rstrip() for _, a, b in kept)) + '\n\n' +
    '\n'.join(lines[region_end:]).lstrip('\n'))

# ---------------------------------------------------------------- pins
pins = []
for name in sorted(moved_names):
    esc = re.escape(name)
    pins.append(f's/^#print axioms LeanLLVM\\.JSON\\.{esc}$/'
                f'#print axioms LeanLLVM.{name}/')
sed = ('# Pin renames for the lattice hoist: one `#print axioms` line per moved\n'
       '# declaration, from the JSON namespace to the model namespace.  Applied with\n'
       '#   sed -i -f hoist/pins.sed LeanLLVM/JSON/Strtod.lean\n'
       + '\n'.join(pins) + '\n')
io.open(PINS, 'w', encoding='utf-8').write(sed)
subprocess.run(['sed', '-i', '-f', PINS, STRTOD], check=True)
print(f'moved {len(moved)} blocks ({len(moved_names)} names); sed with {len(pins)} pin renames applied')
