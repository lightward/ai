#!/usr/bin/env bash
# draw: a grown assay as the grid its makers would draw on a whiteboard — seats down the side,
# probes across the top, a mark where a seat hears a probe, the walls beside each seat as the
# theorems that cite it, and the doors (the clerks) with the theorems that describe them. read
# from the kernel (bin/judge.lean schema), never from memory; markdown, so it pastes anywhere.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
src="${1:?a grown assay: grown/assays/eih.lean}"
python3 - "$src" <<'PY'
import re, subprocess, sys, os
src = sys.argv[1]
text = open(src).read()
imports = re.findall(r'^import (\S+)', text, re.M)
ns_m = re.search(r'^namespace ([\w.]+)', text, re.M)
ns = ns_m.group(1) if ns_m else os.path.splitext(os.path.basename(src))[0]
res = subprocess.run(['lake', 'env', 'lean', '--run', 'bin/judge.lean', 'schema', src, ns, ','.join(imports)], capture_output=True, text=True)
short = lambda n: n.split('.')[-1]
types, seats, readers, faces, cites, rules, clerks = {}, {}, {}, {}, {}, [], []
for l in res.stdout.splitlines():
    p = l.split()
    if not p: continue
    if p[0] == 'type': types[short(p[1])] = p[2:]
    elif p[0] == 'seat': seats[p[1]] = (short(p[2]), p[3:])
    elif p[0] == 'reader': readers[p[1]] = (short(p[2]), short(p[3]))
    elif p[0] == 'face':
        m = re.match(r'face (\S+) (\S+) (\S+) params=(\d+)', l)
        if m: faces[m.group(1)] = (short(m.group(2)), short(m.group(3)), int(m.group(4)))
    elif p[0] == 'cites':
        for s in set(p[2:]): cites.setdefault(s, []).append(p[1])
    elif p[0] == 'rule':
        m = re.match(r'rule (\S+) depth=(\d+) ret=(\S+) params=(\S*) :: (.*)$', l)
        if m: rules.append((m.group(1), m.group(3), m.group(4).split(','), m.group(5)))
    elif p[0] == 'derived':
        m = re.match(r'derived (\S+) clerk over=(\S+) .*? :: (.*?) \| ?(.*?)(?: @by \S+)?$', l)
        if m: clerks.append((m.group(1), short(m.group(2)), m.group(3), m.group(4).split()))
out = [f'# {ns}, drawn', '', f'read from the kernel of `{src}`. a mark is a probe the seat hears; beside each seat, the theorems that cite it — the walls, licensed. below, the doors: the clerks, with the theorems that describe them.', '']
# the grids: for each enum some seat lists, the seats over it against its constructors; the face
# that reads at that enum names the room
for enum, ctors in types.items():
    rows = [(n, ps) for n, (e, ps) in seats.items() if e == enum]
    if not rows: continue
    face = next((f for f, (st, pr, _) in faces.items() if pr == enum), None)
    reader = next((r for r, (st, pr) in readers.items() if pr == enum), None)
    room = faces[face][0] if face else (readers[reader][0] if reader else None)
    title = f'## {enum}' + (f' — asked of a {room}' if room else '') + (f' through `{face}`' if face else '')
    out.append(title); out.append('')
    out.append('| seat | ' + ' | '.join(ctors) + ' | walls |')
    out.append('|---|' + '---|' * len(ctors) + '---|')
    rows = [(n, ps) for n, ps in rows if not (set(ps) == set(ctors) and not (face or reader))]   # the list of every constructor is the enum itself, not a seat
    if not rows: out.pop(); out.pop(); out.pop(); out.pop(); continue
    for n, ps in rows:
        marks = ' | '.join('●' if c in ps else '' for c in ctors)
        walls = ', '.join(f'`{t}`' for t in sorted(set(cites.get(n, []))))
        out.append(f'| `{n}` | {marks} | {walls} |')
    out.append('')
# the rules over one enum: a rule that hands each constructor a list of another enum (a role's
# pages) is a grid; the rules that hand each constructor a truth are columns of one table
norm = lambda t: re.sub(r'[^a-z]', '', t.lower())
typeOf = lambda t: next((k for k in types if norm(k) == norm(t)), None)
for name, ret, params, expr in rules:
    if len(params) != 1 or not typeOf(params[0]): continue
    arms = re.findall(r"WHEN '(\w+)' THEN ARRAY\[([^\]]*)\]", expr)
    if not arms: continue
    enum = typeOf(params[0]); cols = types.get(typeOf(ret.rstrip('[]')) or '') or sorted({c.strip("' ") for _, a in arms for c in a.split(',') if c.strip()})
    out.append(f'## `{name}` — each {enum}, the {typeOf(ret.rstrip("[]")) or ret}s it is handed'); out.append('')
    out.append(f'| {enum} | ' + ' | '.join(cols) + ' |')
    out.append('|---|' + '---|' * len(cols))
    for who, a in arms:
        got = {c.strip("' ") for c in a.split(',') if c.strip()}
        out.append(f'| `{who}` | ' + ' | '.join('●' if c in got else '' for c in cols) + ' |')
    out.append('')
for enum in types:
    truths = [(name, dict(re.findall(r"WHEN '(\w+)' THEN (true|false)", expr))) for name, ret, params, expr in rules if ret == 'boolean' and len(params) == 1 and typeOf(params[0]) == enum]
    truths = [(n, a) for n, a in truths if a]
    if not truths: continue
    out.append(f'## {enum} — the rules that hand each one a truth'); out.append('')
    out.append(f'| {enum} | ' + ' | '.join(f'`{n}`' for n, _ in truths) + ' |'); out.append('|---|' + '---|' * len(truths))
    for c in types[enum]:
        out.append(f'| `{c}` | ' + ' | '.join('●' if a.get(c) == 'true' else '' for _, a in truths) + ' |')
    out.append('')
if clerks:
    out.append('## the doors'); out.append('')
    out.append('| door | over | what it does | described by |'); out.append('|---|---|---|---|')
    for name, over, expr, desc in clerks:
        what = expr.replace('$0', 'the argument').replace('row.', '')
        m = re.match(r'^SET (\w+) = ARRAY\(SELECT \(CASE WHEN (.+) THEN (\w+)\(x(?:, [^)]*)?\) ELSE x END\) FROM unnest\((\w+)\)', what)
        if m: what = f'run `{m.group(3)}` on each of {m.group(4)} where {re.sub(r"\(SELECT (\w+) FROM \w+ WHERE id = x\)", lambda k: "its " + k.group(1), m.group(2)).replace("$1", "the argument").strip("()")}'
        m = re.match(r'^FOLD\[(\w+)\]\(row; the argument\)$', what)
        if m: what = f'run `{m.group(1)}` for each of the argument, in order'
        m = re.match(r'^SET (\w+) = ARRAY\(SELECT (\w+)\(x\) FROM unnest\((\w+)\)', what)
        if m: what = f'run `{m.group(2)}` on each of {m.group(3)}'
        if '⟨unread' in what: what = 'beyond the drawer\'s fragment'
        out.append(f'| `{name}` | {over} | `{what}` | ' + ', '.join(f'`{t}`' for t in desc if t and not t.startswith('(')) + ' |')
    out.append('')
print('\n'.join(out))
PY
