#!/usr/bin/env bash
# seat: a feature file — a model in its maintainer's own sentences — compiled to an assay in the
# house's form. every line is one declaration; a wall is a theorem with `sorry`, and the grow says
# whether the underworld reaches it or holds it by name; a `then` is a #guard, and the assay does
# not elaborate if it parts. statements are true for free until they conflict, and a conflict is
# paid at the gate. bin/counter seat <file.feature> > assays/<name>.lean
#
#   model Name                                     the namespace: Name.Treaty
#   a Role is one of: couple, planner, vendor      an enum, with its code and beq
#   a Room has: guests (a list of numbers), timeline (a list of numbers), done (a truth), n (a number)
#   the room reads: guests as guests, sheet as delivered      a face over Room at the Ask enum: probe as field
#   the couple sees: floorPlan, guestList | every Page         a rule handing each Role its Pages (seen / sees)
#   the couple edits: …                                        edited / edits
#   the caterer hears: timeline, sheet, confirmed              a seat: a list of Asks (catererSeat)
#   a Room may: withBach (bach becomes the argument)           a door: a field replaced
#   a Room may: withLine (ledger gets the argument first)      a door: a field prepended
#   wall: withBach changes nothing the couple hears            a theorem: the door is unheard at the seat
#   given demo is a Room with guests [1, 2], delivered [], …   a row of the cast
#   then the caterer hears [[10], [1, 2]] in demo              a #guard: the seat's reading
#   when demo withBach [43] is newBach                         a row: a door applied
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
src="${1:?a feature file}"
python3 - "$src" <<'PY'
import re, sys
lines = [l.rstrip() for l in open(sys.argv[1]) if l.strip() and not l.lstrip().startswith('#')]
name = 'Sheet'
enums, structs, faces, rules, seats, doors, walls, casts, thens, whens = {}, {}, {}, {}, {}, [], [], [], [], []
aliases, truths, ruleThens = {}, set(), []
def items(s): return [x.strip() for x in s.split(',') if x.strip()]
def ident(s): return re.sub(r'\s+(\w)', lambda m: m.group(1).upper(), s.strip())   # "best man" -> bestMan
def ty(t):
    t = t.strip().lower()
    if t in ('a number', 'a truth', 'a list of numbers'): return {'a number': 'Nat', 'a truth': 'Bool', 'a list of numbers': 'List Nat'}[t]
    e = next((k for k in enums if t == 'a ' + k.lower()), None)
    return e or 'Nat'
for l in lines:
    m = re.match(r'^model (\w+)$', l)
    if m: name = m.group(1); continue
    m = re.match(r'^an? (\w+) is one of: (.+)$', l)
    if m: enums[m.group(1)] = [ident(x) for x in items(m.group(2))]; continue
    m = re.match(r'^an? (\w+) is an? (\w+) who is (\w+)$', l)
    if m:
        # a vendor is a helper who is paid: the constructor retires, the truth is minted, and every
        # later mention of "the vendor" reads as "a paid helper"
        aliases[m.group(1)] = (ident(m.group(2)), m.group(3))
        truths.add(m.group(3))
        for e, cs in enums.items():
            if ident(m.group(1)) in cs: cs.remove(ident(m.group(1)))
        continue
    m = re.match(r'^an? (\w+) has: (.+)$', l)
    if m: structs[m.group(1)] = [(ident(f.strip()), ty(t)) for f, t in re.findall(r'(\w[\w ]*?)\s*\(([^)]*)\)', m.group(2))]; continue
    m = re.match(r'^the (\w+) reads: (.+)$', l)
    if m: faces[m.group(1)] = [(ident(a), ident(b)) for a, b in re.findall(r'(\w+) as (\w+)', m.group(2))]; continue
    m = re.match(r'^(?:the|an?) ([\w ]+?) (sees|edits): (.+)$', l)
    if m:
        who = m.group(1).strip(); key = None
        mm = re.match(r'^(un)?(\w+) (\w+)$', who)
        if mm and mm.group(3) and mm.group(2) in truths: key = (ident(mm.group(3)), mm.group(1) is None)
        elif ident(who) in aliases: key = (aliases[ident(who)][0], True)
        else: key = (ident(who), None)
        rules.setdefault(m.group(2), {})[key] = m.group(3).strip(); continue
    m = re.match(r'^the ([\w ]+?) hears: (.+)$', l)
    if m: seats[ident(m.group(1))] = [ident(x) for x in items(m.group(2))]; continue
    m = re.match(r'^an? (\w+) may: (\w+) \((\w+) (becomes the argument|gets the argument first)\)$', l)
    if m: doors.append((m.group(1), m.group(2), ident(m.group(3)), m.group(4))); continue
    m = re.match(r'^wall: (\w+) changes nothing the ([\w ]+?) hears$', l)
    if m: walls.append((m.group(1), ident(m.group(2)))); continue
    m = re.match(r'^given (\w+) is an? (\w+) with (.+)$', l)
    if m: casts.append((m.group(1), m.group(2), [(ident(f), v) for f, v in re.findall(r'(\w+) (\[[^\]]*\]|\d+|true|false)', m.group(3))])); continue
    m = re.match(r'^when (\w+) (\w+) (\[[^\]]*\]|\d+|true|false) is (\w+)$', l)
    if m: whens.append((m.group(4), m.group(2), m.group(1), m.group(3))); continue
    m = re.match(r'^then the ([\w ]+?) hears (\[.*\]) in (\w+)$', l)
    if m: thens.append((ident(m.group(1)), m.group(3), m.group(2))); continue
    m = re.match(r'^then (?:the|an?) ([\w ]+?) (does not see|sees|does not edit|edits) (\w+)$', l)
    if m: ruleThens.append((m.group(1).strip(), m.group(2), ident(m.group(3)))); continue
    sys.exit(f'seat: a line the grammar does not read: {l}')
out = ['import Witness', 'open Room Face Witness', 'set_option autoImplicit false', '', f'namespace {name}.Treaty', '']
for e, cs in enums.items():
    out.append(f'inductive {e} where'); out.append('  | ' + ' | '.join(cs)); out.append('')
    out.append(f'def {e}.code : {e} → Nat'); out.append('  ' + ' '.join(f'| .{c} => {i}' for i, c in enumerate(cs))); out.append('')
    out.append(f'def {e}.beq (a b : {e}) : Bool := Nat.beq a.code b.code'); out.append('')
    out.append(f'def {e[0].lower() + e[1:]}s : List {e} := [{", ".join("." + c for c in cs)}]'); out.append('')
for s, fs in structs.items():
    out.append(f'structure {s} where')
    for f, t in fs: out.append(f'  {f} : {t}')
    out.append('')
askEnum = next((e for e in enums if e not in [r for r in rules] and any(True for _ in faces)), None)
for room, arms in faces.items():
    S = room[0].upper() + room[1:]
    probe = next((e for e, cs in enums.items() if all(a in cs for a, _ in arms)), None)
    if not probe: sys.exit(f'seat: the {room} reads probes no enum names')
    out.append(f'def read{S} (r : {S}) : {probe} → List Nat');
    for a, b in arms: out.append(f'  | .{a} => r.{b}')
    out.append(''); out.append(f'def {room}Face : Face := ⟨{S}, {probe}, List Nat, read{S}⟩'); out.append('')
    faces[room] = (S, probe, arms)
for verb, arms in rules.items():
    fn = {'sees': 'seen', 'edits': 'edited'}[verb]
    roleE = next((e for e, cs in enums.items() if all(r in cs for r, _ in arms)), None)
    pageE = next((e for e in enums if e != roleE and any(any(x in enums[e] for x in [ident(y) for y in items(v)]) or v.startswith('every') for v in arms.values())), None)
    if not (roleE and pageE): sys.exit(f'seat: {verb} names roles or pages no enum has')
    withTruth = any(t is not None for _, t in arms)
    truth = next(iter(truths)) if truths else 'paid'
    def body(v): return f'{pageE[0].lower() + pageE[1:]}s' if v.startswith('every') else '[' + ', '.join('.' + ident(x) for x in items(v)) + ']'
    if withTruth:
        # one rule per side of the truth, each read by the kernel at every constructor, and the rule
        # over both as a cond between them
        T = truth[0].upper() + truth[1:]
        for side, tv in ((T, True), ('Un' + truth, False)):
            out.append(f'def {fn}{side} : {roleE} → List {pageE}')
            for r in enums[roleE]:
                out.append(f'  | .{r} => {body(arms[(r, None)] if (r, None) in arms else arms.get((r, tv), ""))}')
            out.append('')
        out.append(f'def {fn} (ρ : {roleE}) ({truth} : Bool) : List {pageE} := cond {truth} ({fn}{T} ρ) ({fn}Un{truth} ρ)'); out.append('')
        out.append(f'def {verb} (ρ : {roleE}) ({truth} : Bool) (p : {pageE}) : Bool := enrolled {pageE}.beq ({fn} ρ {truth}) p'); out.append('')
    else:
        out.append(f'def {fn} : {roleE} → List {pageE}')
        for r in enums[roleE]: out.append(f'  | .{r} => {body(arms.get((r, None), ""))}')
        out.append(''); out.append(f'def {verb} (ρ : {roleE}) (p : {pageE}) : Bool := enrolled {pageE}.beq ({fn} ρ) p'); out.append('')
for seat, ps in seats.items():
    probe = next((e for e, cs in enums.items() if all(p in cs for p in ps)), None)
    if not probe: sys.exit(f'seat: the {seat} hears probes no enum names')
    out.append(f'def {seat}Seat : List {probe} := [{", ".join("." + p for p in ps)}]'); out.append('')
for S, door, field, how in doors:
    fty = dict(structs.get(S, [])).get(field, 'List Nat')
    if how == 'becomes the argument':
        out.append(f'def {door} (r : {S}) (x : {fty}) : {S} := {{ r with {field} := x }}')
    else:
        out.append(f'def {door} (r : {S}) (x : Nat) : {S} := {{ r with {field} := x :: r.{field} }}')
    out.append('')
for n, S, fs in casts:
    order = [f for f, _ in structs[S]]
    vals = dict(fs)
    out.append(f'def {n} : {S} := ⟨{", ".join(vals.get(f, "[]") for f in order)}⟩')
for n, door, base, arg in whens:
    out.append(f'def {n} : {next((S for S, d, _, _ in doors if d == door), "Room")} := {door} {base} {arg}')
out.append('')
for seat, row, expect in thens:
    room = next(r for r in faces)
    out.append(f'def {seat}In{row[0].upper() + row[1:]} : List (List Nat) := reads {room}Face {seat}Seat {row}')
    out.append(f'#guard {seat}In{row[0].upper() + row[1:]} == {expect}')
for who, verb, page in ruleThens:
    mm = re.match(r'^(un)?(\w+) (\w+)$', who)
    if mm and mm.group(2) in truths: role, t = ident(mm.group(3)), ('false' if mm.group(1) else 'true')
    elif ident(who) in aliases: role, t = aliases[ident(who)][0], 'true'
    else: role, t = ident(who), None
    v = 'sees' if 'see' in verb else 'edits'; want = 'false' if verb.startswith('does not') else 'true'
    withTruth = any(tt is not None for _, tt in rules.get(v, {}))
    call = f'{v} .{role}' + ((f' {t}' if t is not None else ' true') if withTruth else '') + f' .{page}'
    out.append(f'#guard {call} == {want}')
out.append('')
for door, seat in walls:
    S = next((S for S, d, _, _ in doors if d == door), 'Room'); room = next(r for r, (s, _, _) in faces.items() if s == S)
    fty = next((dict(structs.get(S, [])).get(f, 'List Nat') if how == 'becomes the argument' else 'Nat') for S2, d, f, how in doors if d == door)
    out.append(f'theorem {door}_changes_nothing_the_{seat}_hears (r : {S}) (x : {fty}) :')
    out.append(f'    reads {room}Face {seat}Seat ({door} r x) = reads {room}Face {seat}Seat r := sorry')
    out.append('')
out.append(f'end {name}.Treaty')
print('\n'.join(out))
PY
