#!/usr/bin/env bash
# treaty: the assay's rows, replayed as SQL against the shadow — the assay's defs seated as rows,
# each `#guard` translated where the fragment reaches it and run inside a rolled-back transaction
# (a clerk's effect never leaks into the next row). reports replayed / identical / unread.
# needs a Postgres: PGSOCK and PGPORT for a private one, else the machine's default.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
assay="${1:?an assay with rows: assays/eih.lean}"
stem="$(basename "${assay%.lean}")"
grown="grown/assays/${stem}.lean"
[ -f "$grown" ] || { echo "treaty: ${grown} is not grown (bin/counter grow ${assay})"; exit 1; }
export PATH="/opt/homebrew/opt/postgresql@17/bin:$PATH"
PGSOCK="${PGSOCK:-/tmp}"; PGPORT="${PGPORT:-5432}"; PGUSER="${PGUSER:-$USER}"
q() { psql -h "$PGSOCK" -p "$PGPORT" -U "$PGUSER" -d "$1" -q -X -tA "${@:2}"; }
db="treaty_${stem}"
q postgres -c "DROP DATABASE IF EXISTS ${db}" >/dev/null 2>&1
q postgres -c "CREATE DATABASE ${db}" >/dev/null || { echo "treaty: no database at ${PGSOCK}:${PGPORT}"; exit 1; }
bin/counter schema "$grown" > "/tmp/treaty-${stem}.sql"
load="$(q "$db" -f "/tmp/treaty-${stem}.sql" 2>&1)"
if echo "$load" | grep -q ERROR; then echo "treaty: the shadow does not load"; echo "$load" | grep ERROR | head -5; exit 1; fi
python3 - "$assay" "$db" "$PGSOCK" "$PGPORT" "$PGUSER" "$grown" "/tmp/treaty-${stem}.sql" <<'PY2'
import re, subprocess, sys
assay, db, sock, port, user, grown, sqlfile = sys.argv[1:8]
text = open(assay).read()
def q(sql):
    r = subprocess.run(['psql', '-h', sock, '-p', port, '-U', user, '-d', db, '-q', '-X', '-tA', '-c', sql], capture_output=True, text=True)
    return (r.stdout.strip(), r.stderr.strip())
RESERVED = set("user table order group from select where to end check default primary references in is on all and or not as by into join case when then else null limit offset union values with using cast column constraint create do for grant having only some window distinct desc asc any array between except fetch foreign intersect lateral returning unique".split())
def snake(n):
    s = re.sub(r'(?<!^)(?=[A-Z])', '_', n).lower()
    return s + '_' if s in RESERVED else s
short = lambda n: n.split('.')[-1]
shed = lambda t: re.sub(r'\.\{[^}]*\}', '', t)
def split_top(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '([⟨{': depth += 1
        elif ch in ')]⟩}': depth -= 1
        if ch == ',' and depth == 0: out.append(cur.strip()); cur = ''
        else: cur += ch
    if cur.strip(): out.append(cur.strip())
    return out
def lit_list(s):
    s = s.strip()
    if s.startswith('[') and s.endswith(']'):
        inner = s[1:-1].strip(); return split_top(inner) if inner else []
    return None
def sql_array(items, ty='integer'):
    return 'ARRAY[' + ','.join(str(x) for x in items) + f']::{ty}[]' if items else f'ARRAY[]::{ty}[]'
# the shadow, as the judge reads it: tables with their fields' types, enums, seats, readers, faces
ns = re.search(r'^namespace (\S+)', open(grown).read(), re.M).group(1)
imports = ','.join(re.findall(r'^import (\S+)', open(grown).read(), re.M))
rep = subprocess.run(['lake', 'env', 'lean', '--run', 'bin/judge.lean', 'schema', grown, ns, imports], capture_output=True, text=True).stdout
tables, enums, seats, readers, facefns, nameprobed = {}, {}, {}, {}, {}, set()
for l in rep.splitlines():
    p = l.split(' ')
    if p[0] == 'face':
        m = re.match(r'face (\S+) (\S+) (\S+) params=(\d+)', l)
        if m: facefns[m.group(1)] = (short(m.group(2)), int(m.group(4)))
        if m and m.group(3) == 'Nat': nameprobed.add(m.group(1))
    if p[0] == 'table':
        # a field's type may carry spaces (List X, Prod ...): split on the next `name:`
        rest = l[len('table ') + len(p[1]) + 1:]
        fields = [(m.group(1), shed(m.group(2)).strip()) for m in re.finditer(r'(\w+):(.+?)(?= \w+:|$)', rest)]
        tables[short(p[1])] = fields
    elif p[0] == 'type': enums[short(p[1])] = p[2:]
    elif p[0] == 'seat': seats[p[1]] = (short(p[2]), p[3:])
    elif p[0] == 'reader':
        arms = {}
        for a in p[4:]:
            probe, _, col = a.partition('='); arms[probe] = col
        readers[p[1]] = (short(p[2]), short(p[3]), arms)
def is_table(t): return short(t) in tables
def is_enum(t): return short(t) in enums
def elem(t):   # List X -> X
    m = re.match(r'^List (?:\((.+)\)|(\S+))$', t); return (m.group(1) or m.group(2)) if m else None
def is_tuple(t): return t.startswith('Prod ') or '×' in t
# the drawn functions: name -> (param types, return type)
funcs = {}
pnames = {}
for m in re.finditer(r'^CREATE FUNCTION (\w+)\(([^)]*)\) RETURNS (\S+)', open(sqlfile).read(), re.M):
    params = [x.strip().split(' ')[-1] for x in m.group(2).split(',') if x.strip()]
    pnames[m.group(1)] = [x.strip().split(' ')[0] for x in m.group(2).split(',') if x.strip()]
    funcs[m.group(1)] = (params, m.group(3))
# the assay's defs and faces
defs = {}
for m in re.finditer(r'^def (\w+) : (.+?) :=[ \t]*\n?[ \t]*(.+)$', text, re.M):
    defs[m.group(1)] = (m.group(2).strip(), m.group(3).strip())
# a name in a list of numbers is the number it names
def num(x):
    x = x.strip()
    if x in defs and defs[x][0] == 'Nat': return defs[x][1]
    if x in ids: return str(ids[x])
    return x
faces = {}   # face def -> reader
for name, (ty, val) in defs.items():
    if ty == 'Face' and val.startswith('⟨'):
        parts = split_top(val[1:-1])
        if len(parts) == 4 and parts[3] in readers: faces[name] = parts[3]
ids, lists, next_id = {}, {}, {}
def new_id(t): next_id[t] = next_id.get(t, 0) + 1; return next_id[t]
def has_many(field_ty): return elem(field_ty) is not None and (is_table(elem(field_ty)) or is_tuple(elem(field_ty)))
def scalar_sql(v, ty):
    v = v.strip()
    if ty == 'Nat': return str(defs[v][1]) if v in defs and defs[v][0] == 'Nat' else v
    if ty == 'Bool': return v
    if is_enum(ty): return f"'{v.lstrip('.')}'"
    if elem(ty) == 'Nat':
        l = lit_list(v) if lit_list(v) is not None else lit_list(defs[v][1]) if v in defs else None
        return sql_array(l or [])
    if elem(ty) and is_enum(elem(ty)):
        l = lit_list(v) or []; return sql_array([f"'{x.lstrip('.')}'" for x in l], snake(elem(ty)))
    if is_table(ty): return str(seat_value(v, ty))
    return None
def seat_value(v, ty):
    # a table-typed value: a def name (its id) or a literal (seated now)
    v = v.strip()
    if v in ids: return ids[v]
    if v.startswith('⟨'): return seat_literal(short(ty), v, None)
    return None
def seat_literal(t, val, name):
    fields = tables[t]; parts = split_top(val[1:-1]); i = new_id(snake(t))
    cols, vals, children = ['id'], [str(i)], []
    for (f, fty), v in zip(fields, parts):
        if has_many(fty):
            e = elem(fty)
            items = lists.get(v) if v in lists else lit_list(v) or []
            children.append((f, e, items))
        else:
            s = scalar_sql(v, fty)
            if s is None: return None
            cols.append(snake(f)); vals.append(s)
    q(f"INSERT INTO {snake(t)} ({', '.join(cols)}) VALUES ({', '.join(vals)})")
    for f, e, items in children:
        child = f"{snake(t)}_{snake(f)}"
        for pos, item in enumerate(items):
            if is_table(e):
                eid = item if isinstance(item, int) else seat_value(item, e)
                q(f"INSERT INTO {child} ({snake(t)}_id, position, {snake(short(e))}_id) VALUES ({i}, {pos}, {eid})")
            else:
                c = split_top(item.strip('()')); cols_c = ', '.join(f'c{k}' for k in range(len(c)))
                q(f"INSERT INTO {child} ({snake(t)}_id, position, {cols_c}) VALUES ({i}, {pos}, {', '.join(c)})")
    if name: ids[name] = i
    return i
def clone(t, base):
    i = new_id(snake(t)); tn = snake(t)
    cols = ['id'] + [snake(f) for f, fty in tables[t] if not has_many(fty)]
    if len(cols) == 1: q(f"INSERT INTO {tn} (id) VALUES ({i})")   # a row that is only its children
    else: q(f"INSERT INTO {tn} ({', '.join(cols)}) SELECT {i}, {', '.join(cols[1:])} FROM {tn} WHERE id = {base}")
    for f, fty in tables[t]:
        if has_many(fty):
            child = f"{tn}_{snake(f)}"; e = elem(fty)
            if is_table(e):
                # the element rows are copied too — a value never aliases, so a clerk on the copy
                # must not reach the original's elements
                key = f"{snake(short(e))}_id"
                olds, _ = q(f"SELECT {key} FROM {child} WHERE {tn}_id = {base} ORDER BY position")
                for pos, old in enumerate([x for x in olds.split('\n') if x]):
                    new = clone(short(e), int(old))
                    q(f"INSERT INTO {child} ({tn}_id, position, {key}) VALUES ({i}, {pos}, {new})")
            else:
                cs = ', '.join(f'c{k}' for k in range(len(re.findall(r'Nat', e))))
                q(f"INSERT INTO {child} ({tn}_id, position, {cs}) SELECT {i}, position, {cs} FROM {child} WHERE {tn}_id = {base}")
    return i
def arg_sql(a, pty):
    a = a.strip()
    if pty == 'integer[]':
        l = lit_list(a)
        if l is not None: return sql_array([num(x) for x in l])
        if a in lists: return sql_array(lists[a])
        m = re.match(r'^\(?(\w+) :: (\w+)\)?$', a)   # a row prepended to a list
        if m and m.group(1) in ids and m.group(2) in lists: return sql_array([ids[m.group(1)]] + lists[m.group(2)])
        if m and (m.group(1) in defs and defs[m.group(1)][0] == 'Nat' or re.match(r'^\d+$', m.group(1))):   # a number prepended
            rest_ = arg_sql(m.group(2), 'integer[]')
            if rest_ is not None: return f"array_prepend({num(m.group(1))}, {rest_})"
        if a.startswith('(') and a.endswith(')') and ' ++ ' in a:   # two lists appended
            parts = [x.strip() for x in split_top(a[1:-1].replace(' ++ ', ','))]
            if len(parts) == 2:
                x, y = arg_sql(parts[0], 'integer[]'), arg_sql(parts[1], 'integer[]')
                if x is not None and y is not None: return f"({x} || {y})"
        if a.startswith('(') and ',' in a and not a.startswith('(('): return sql_array(split_top(a.strip('()')))   # a tuple
        if a in defs and elem(defs[a][0]) == 'Nat': return sql_array([num(x) for x in (lit_list(defs[a][1]) or [])])
        return None
    if pty == 'integer':
        if a in defs and defs[a][0] == 'Nat': return defs[a][1]
        return a if re.match(r'^\d+$', a) else None
    if pty in enums or pty in [snake(e) for e in enums]: return f"'{a.lstrip('.')}'"
    if pty.endswith('[]'):
        l = lit_list(a) or []; return sql_array([f"'{x.lstrip('.')}'" for x in l], pty[:-2])
    return None
def toks_of(rest):
    # arguments split on spaces at depth zero: a parenthesized application stays one token
    toks, depth, cur = [], 0, ''
    for ch in rest:
        if ch in '([⟨': depth += 1
        elif ch in ')]⟩': depth -= 1
        if ch == ' ' and depth == 0:
            if cur: toks.append(cur); cur = ''
        else: cur += ch
    if cur: toks.append(cur)
    return toks
row_table = {}
def row_of(e, t=None):
    # a table-typed expression: a def name, or a clerk applied inline (to a def, or to another clerk's result)
    e = e.strip()
    if e.startswith('(') and e.endswith(')'): e = e[1:-1].strip()
    if e in ids: return ids[e]
    toks = toks_of(e)
    if len(toks) >= 2 and snake(toks[0]) in funcs and funcs[snake(toks[0])][1] == 'void':
        base = toks[1]
        bid = ids[base] if base in ids else row_of(base)
        if bid is None: return None
        bt = defs[base][0] if base in defs else row_table.get(bid)
        if bt is None: return None
        i = clone(short(bt), bid); row_table[i] = bt; params = funcs[snake(toks[0])][0]
        extra = ''
        for a, pty in zip(toks[2:], params[1:]):
            v = arg_sql(a, pty)
            if v is None or a.startswith('('):
                inner = expr(a)
                if inner and inner[0] == 's': v = inner[1]
            if v is None: return None
            extra += ', ' + v
        q(f"SELECT {snake(toks[0])}({i}{extra})"); return i
    return None
def column(t, field):
    # a field read as SQL at a row of table t: a column, a has-many as its child rows in order, a component thereof
    f, _, comp = field.partition('#')
    fty = dict(tables[t]).get(f)
    tn = snake(t)
    if fty and has_many(fty):
        e = elem(fty); child = f"{tn}_{snake(f)}"
        key = f"{snake(short(e))}_id" if is_table(e) else (f"c{comp}" if comp else 'c0')
        return f"(SELECT array_agg({key} ORDER BY position) FROM {child} c WHERE c.{tn}_id = {tn}.id)"
    return snake(f)
def view_col(field): return snake(field.partition('#')[0])
def earshot_of(e):
    # a def `earshot face seats` -> the seats' names
    m = re.match(r'^earshot (\w+) (\w+)$', e)
    if m and m.group(2) in defs:
        l = lit_list(defs[m.group(2)][1]) or []
        return [s for s in l if s in seats]
    return None
def expr(e):
    e = e.strip()
    if e in defs and e not in ids and e not in lists and defs[e][0] in ('List Nat', 'List (List Nat)', 'Nat', 'Bool') or (e in defs and is_enum(defs[e][0])):
        return expr(defs[e][1])
    if e.startswith('(') and e.endswith(')') and not e.startswith('(('): 
        inner = expr(e[1:-1])
        if inner: return inner
    m = re.match(r'^(.+?) && (.+)$', e)
    if m:
        a, b = expr(m.group(1)), expr(m.group(2))
        if a and b and a[0] == 's' and b[0] == 's': return ('s', f"(({a[1]}) AND ({b[1]}))")
    if e.startswith('!(') and e.endswith(')'):
        a = expr(e[2:-1])
        if a and a[0] == 's': return ('s', f"(NOT ({a[1]}))")
    if e.startswith('.') and re.match(r'^\.\w+$', e): return ('s', f"'{e[1:]}'")
    # a drawn function applied: the first argument a row (or a list of rows), the rest by parameter type
    m = re.match(r'^(\w+)((?: .+)?)$', e)
    if m and snake(m.group(1)) in funcs and (m.group(1) not in defs or '→' in defs[m.group(1)][0]):
        fname = snake(m.group(1)); params, ret = funcs[fname]
        if ret == 'void': return None
        args = split_top(m.group(2).strip().replace(' ', ',')) if False else None
        rest = m.group(2).strip()
        # arguments: a parenthesized clerk application, a def, a literal, a constructor — split on spaces at depth zero
        toks, depth, cur = [], 0, ''
        for ch in rest:
            if ch in '([⟨': depth += 1
            elif ch in ')]⟩': depth -= 1
            if ch == ' ' and depth == 0:
                if cur: toks.append(cur); cur = ''
            else: cur += ch
        if cur: toks.append(cur)
        if len(toks) != len(params): return None
        sqls = []
        for a, pty in zip(toks, params):
            if pty == 'integer' and (a in ids or (a.startswith('(') and row_of(a) is not None)):
                sqls.append(str(row_of(a)))
            elif pty == 'integer[]' and a in lists: sqls.append(sql_array(lists[a]))
            else:
                s = arg_sql(a, pty)
                if s is None or a.startswith('(') or '.' in a.strip('.'):
                    inner = expr(a)
                    if inner and inner[0] == 's': s = inner[1]
                if s is None: return None
                sqls.append(s)
        return ('s', f"{fname}({', '.join(sqls)})")
    # a field of a row (a def, or a clerk applied inline — the clerk's first parameter names the table)
    m = re.match(r'^(.+)\.(\w+)$', e)
    if m and not e.startswith('.'):
        base = m.group(1); r = row_of(base)
        head = base.strip('()').split(' ')[0]
        t = short(defs[head][0]) if head in defs else None
        if t is None and snake(head) in funcs:
            t = next((tn for tn in tables if pnames[snake(head)] and snake(tn) + '_id' == pnames[snake(head)][0]), None)
        if r and t and t in tables and m.group(2) in dict(tables[t]):
            return ('s', f"(SELECT {column(t, m.group(2))} FROM {snake(t)} WHERE id = {r})")
    # a reader at a probe: through its face's function when a face is built on it, else its column
    m = re.match(r'^(\w+) (.+) \.(\w+)$', e)
    if m and m.group(1) in readers:
        t, _, arms = readers[m.group(1)]; r = row_of(m.group(2))
        face = next((f for f, rd in faces.items() if rd == m.group(1) and f in facefns and facefns[f][1] == 0), None)
        if r and face: return ('s', f"(SELECT {snake(m.group(3))} FROM {snake(t)}_as_{snake(face)}({r}))")
        if r and m.group(3) in arms: return ('s', f"(SELECT {column(t, arms[m.group(3)])} FROM {snake(t)} WHERE id = {r})")
    # a face applied to a row at a probe: a column of the face's function
    m = re.match(r'^\(?(\w+)((?: [^\s)]+)*)\)?\.obs (\S+) (\.\w+|\(\))$', e)
    if m and m.group(1) in facefns:
        t, n = facefns[m.group(1)]; r = row_of(m.group(3))
        args = m.group(2).split()
        if r and len(args) == n:
            col = 'unit' if m.group(4) == '()' else snake(m.group(4)[1:])
            argsql = ''.join(f', {arg_sql(a, "integer")}' for a in args)
            return ('s', f"(SELECT {col} FROM {snake(t)}_as_{snake(m.group(1))}({r}{argsql}))")
    # a sounding of a recital is the seat's reading — Witness's the_sounding_is_the_trails_reading
    # with Face's the_recital_walks_its_list
    m = re.match(r'^sound (\w+) (\S+) \(recite (.+)\)$', e)
    if m and m.group(1) in nameprobed:
        return expr(f"reads {m.group(1)} {m.group(3)} {m.group(2)}")
    # a seat's reading through a face whose probes are names: the face's reading at each name, in order
    m = re.match(r'^reads (\w+) (\S+) (.+)$', e)
    if m and m.group(1) in nameprobed:
        t, n = facefns[m.group(1)]; r = row_of(m.group(3)); l = arg_sql(m.group(2), 'integer[]')
        if r and l is not None:
            return ('s', f"ARRAY(SELECT {snake(t)}_as_{snake(m.group(1))}({r}, p) FROM unnest({l}) WITH ORDINALITY AS u(p, o) ORDER BY o)")
    # the first voice: whichever of a, b the list names first
    m = re.match(r'^firstOf \S+ (\S+) (\S+) (\S+)$', e)
    if m:
        a, b, l = arg_sql(m.group(1), 'integer'), arg_sql(m.group(2), 'integer'), arg_sql(m.group(3), 'integer[]')
        if a is not None and b is not None and l is not None:
            return ('s', f"coalesce((SELECT (x = {a}) FROM unnest({l}) WITH ORDINALITY AS u(x, o) WHERE (x = {a}) OR (x = {b}) ORDER BY o LIMIT 1), false)")
    # a seat's reading through a face: the view's columns
    m = re.match(r'^reads (\w+) (\w+) (.+)$', e)
    if m and m.group(1) in faces and m.group(2) in seats:
        t, _, arms = readers[faces[m.group(1)]]; r = row_of(m.group(3))
        if r:
            view = f"{snake(t)}_as_{snake(m.group(2))}"
            return ('t', [f"(SELECT {snake(p)} FROM {view} WHERE id = {r})" for p in seats[m.group(2)][1]])
    # every one of a list enrolled in another: containment (the lanes)
    m = re.match(r'^(\w+)\.all \(enrolled \S+ (\w+)\)$', e)
    if m:
        a = expr(m.group(1)) or (literal(defs[m.group(1)][1]) if m.group(1) in defs else None)
        b = expr(m.group(2)) or (literal(defs[m.group(2)][1]) if m.group(2) in defs else None)
        if a and b and a[0] == 's' and b[0] == 's': return ('s', f"({a[1]} <@ {b[1]})")
    # the turnstile: containment
    m = re.match(r'^everyone \S+ (.+)$', e)
    if m:
        t2 = toks_of(m.group(1))
        if len(t2) == 2:
            a = literal(t2[0]) if lit_list(t2[0]) is not None else expr(t2[0])
            b = literal(t2[1]) if lit_list(t2[1]) is not None else expr(t2[1])
            if a and b and a[0] == 's' and b[0] == 's': return ('s', f"({a[1]} <@ {b[1]})")
    # a length: a seat's, an earshot's, a reading's
    m = re.match(r'^(.+)\.length$', e)
    if m:
        x = m.group(1).strip()
        if x.startswith('(') and x.endswith(')'): x = x[1:-1].strip()
        if x in seats: return ('n', len(seats[x][1]))
        if x in defs and earshot_of(defs[x][1]) is not None:
            return ('n', sum(len(seats[s][1]) for s in earshot_of(defs[x][1])))
        inner = expr(x)
        if inner and inner[0] == 't': return ('n', len(inner[1]))
        if inner and inner[0] == 's': return ('s', f"cardinality({inner[1]})")
    # a probe in an earshot: a column of some seat's view
    m = re.match(r'^enrolled \S+ (\w+) \.(\w+)$', e)
    if m and m.group(1) in defs and earshot_of(defs[m.group(1)][1]) is not None:
        ss = earshot_of(defs[m.group(1)][1])
        face = re.match(r'^earshot (\w+)', defs[m.group(1)][1]).group(1)
        t, _, arms = readers[faces[face]]
        views = ', '.join(f"'{snake(t)}_as_{snake(s)}'" for s in ss)
        return ('s', f"EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name IN ({views}) AND column_name = '{snake(m.group(2))}')")
    # a member of any list: the list an expression
    m = re.match(r'^enrolled \S+ (.+) (\S+)$', e)
    if m:
        a = expr(m.group(1)) or (literal(m.group(1)) if lit_list(m.group(1)) is not None else None)
        b = expr(m.group(2)) or literal(m.group(2))
        if a and b and a[0] == 's' and b[0] in ('s', 'n'): return ('s', f"({b[1]} = ANY(SELECT unnest({a[1]})))")
    # an enum's own equality
    m = re.match(r'^(\w+)\.beq (.+) (\S+)$', e)
    if m and m.group(1) in enums:
        a, b = expr(m.group(2)), expr(m.group(3))
        if a and b and a[0] == 's' and b[0] == 's': return ('s', f"({a[1]} = {b[1]})")
    return None
def literal(rhs):
    rhs = rhs.strip()
    if rhs in ('true', 'false'): return ('s', rhs)
    if re.match(r'^\d+$', rhs): return ('n', int(rhs))
    l = lit_list(rhs)
    if l is not None:
        if l and all(x.startswith('[') for x in l): return ('t', [sql_array([num(y) for y in lit_list(x)]) for x in l])
        return ('s', sql_array([num(x) for x in l]))
    return None
def compare(a, b):
    if a[0] == 'n' and b[0] == 'n': return ('py', a[1] == b[1])
    if a[0] == 'n' and b[0] == 's': return ('sql', f"SELECT ({b[1]}) = {a[1]}")
    if a[0] == 's' and b[0] == 'n': return ('sql', f"SELECT ({a[1]}) = {b[1]}")
    if a[0] == 's' and b[0] == 's': return ('sql', f"SELECT ({a[1]}) = ({b[1]})")
    if a[0] == 't' and b[0] == 't' and len(a[1]) == len(b[1]):
        return ('sql', "SELECT " + " AND ".join(f"(({x}) = ({y}))" for x, y in zip(a[1], b[1])))
    return None
# the cast is seated once every reading is defined (a clerk's argument may be an expression)
seated = 0
for name, (ty, val) in defs.items():
    if is_table(ty) and val.startswith('⟨'):
        if seat_literal(short(ty), val, name) is not None: seated += 1; row_table[ids[name]] = ty
    elif elem(ty) and is_table(elem(ty)):
        lists[name] = [ids[x] if x in ids else seat_value(x, elem(ty)) for x in (lit_list(val) or [])]
    elif is_table(ty):
        r = row_of(val)
        if r: ids[name] = r; row_table[r] = ty; seated += 1
print(f"the cast: {seated} rows seated from the assay's defs")
replayed = identical = unread = 0
held, beyond = [], []
for g in re.findall(r'^#guard (.+)$', text, re.M):
    g = g.strip(); verdict = None
    m = re.match(r'^(.+?) (==|!=) (.+)$', g)
    if m:
        a = expr(m.group(1)); b = literal(m.group(3)) or expr(m.group(3))
        c = compare(a, b) if a and b else None
        if c:
            if c[0] == 'py': verdict = c[1] == (m.group(2) == '==')
            else:
                out, err = q(c[1]); verdict = (out == 't') == (m.group(2) == '==')
                if err and not out: verdict = None; held.append((g, err[:100]))
    else:
        a = expr(g)
        if a and a[0] == 's':
            out, err = q(f"SELECT ({a[1]})"); verdict = out == 't'
            if err and not out: verdict = None; held.append((g, err[:100]))
    if verdict is None:
        if not any(h[0] == g for h in held): unread += 1; beyond.append(g)
        continue
    replayed += 1
    if verdict: identical += 1
    else: held.append((g, 'parts'))
print(f'the treaty in SQL: {replayed} rows replayed, {identical} identical, {unread} beyond the fragment')
for g in beyond: print(f'  BEYOND: {g}')
for g, r in held: print(f'  PARTS: {g}  ->  {r}')
if held or replayed == 0: sys.exit(1)
PY2
