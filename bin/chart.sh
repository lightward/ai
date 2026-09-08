#!/usr/bin/env bash
# chart: the map of relations, drawn from the proofs — every organ of a grown stream as a node,
# grouped by the storey it lives in, an arrow for each citation the elaborator reads.
# relations, not relata: the names are only where the arrows touch down.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
src="${1:?a grown stream: grown/Room.lean or grown/assays/eih.lean}"
laws="${2:-}"   # `--laws`: the citation lattice alone — theorem to theorem, no carriers
python3 - "$src" "$laws" <<'PY'
import re, subprocess, sys, os
src = sys.argv[1]
laws_only = sys.argv[2] == '--laws'
text = open(src).read()
imports = re.findall(r'^import (\S+)', text, re.M)
ns_m = re.search(r'^namespace ([\w.]+)', text, re.M)
ns = ns_m.group(1) if ns_m else os.path.splitext(os.path.basename(src))[0]
res = subprocess.run(['lake', 'env', 'lean', '--run', 'bin/judge.lean', 'cites', src, ns, ','.join(imports)], capture_output=True, text=True)
nodes, edges = {}, []
for l in res.stdout.splitlines():
    head, sep, deps = l.partition(' <- ')
    if not sep: continue
    kind, name = head.split()
    if laws_only and kind != 'theorem': continue
    nodes[name] = kind
    for d in deps.split():
        edges.append((name, d))
if laws_only:
    # the citation lattice alone: an edge's target must be a theorem — ours, or one read from the
    # grown house (every `theorem` of every grown stream, qualified by its namespace)
    import glob
    laws = set(n for n, k in nodes.items() if k == 'theorem')
    for gp in glob.glob('grown/*.lean') + glob.glob('grown/assays/*.lean'):
        gt = open(gp).read()
        gm = re.search(r'^namespace ([\w.]+)', gt, re.M)
        gns = gm.group(1) if gm else ''
        for n in re.findall(r'^theorem (\w+)', gt, re.M):
            laws.add(f'{gns}.{n}' if gns else n)
    edges = [(a, b) for a, b in edges if a in laws and b in laws]
def storey(n):
    return n.rsplit('.', 1)[0] if '.' in n else ns
def nid(n):
    return re.sub(r'[^A-Za-z0-9_]', '_', n)
def label(n):
    return n.rsplit('.', 1)[-1]
groups = {}
for a, b in edges:
    for n in (a, b):
        groups.setdefault(storey(n), set()).add(n)
for n in nodes:
    groups.setdefault(ns, set()).add(n)
out = ['graph LR']
for st, ns_ in groups.items():
    out.append(f'  subgraph {nid(st)}["{st}"]')
    for n in sorted(ns_):
        shape = '([' + label(n) + '])' if nodes.get(n) == 'carrier' or (n not in nodes and False) else '["' + label(n) + '"]'
        if n not in nodes and st != ns:
            shape = '["' + label(n) + '"]'
        out.append(f'    {nid(n)}{shape}')
    out.append('  end')
seen = set()
for a, b in edges:
    if (a, b) in seen or a == b: continue
    seen.add((a, b))
    out.append(f'  {nid(a)} --> {nid(b)}')
print('\n'.join(out))
PY
