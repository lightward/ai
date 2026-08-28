import subprocess, sys
files = subprocess.run(["git","ls-files","*.lean"], capture_output=True, text=True).stdout.split()
bad = []
for f in files:
    s = open(f, encoding="utf-8").read()
    i, n, line = 0, len(s), 1
    while i < n:
        ch = s[i]
        if ch == "\n":
            line += 1; i += 1; continue
        if ch == '"':
            i += 1
            while i < n and s[i] != '"':
                if s[i] == "\\" and i+1 < n:
                    if s[i+1] == "\n": line += 1
                    i += 2; continue
                if s[i] == "\n": line += 1
                i += 1
            i += 1; continue
        if s[i:i+2] == "--":
            bad.append((f, line, "-- line comment"))
            while i < n and s[i] != "\n": i += 1
            continue
        if s[i:i+2] == "/-":
            startline = line
            three = s[i:i+3]
            isdoc = three == "/--"; ismod = three == "/-!"
            cstart = i + (3 if (isdoc or ismod) else 2)
            depth, j = 0, i
            while j < n:
                if s[j:j+2] == "/-": depth += 1; j += 2; continue
                if s[j:j+2] == "-/":
                    depth -= 1; j += 2
                    if depth == 0: break
                    continue
                if s[j] == "\n": line += 1
                j += 1
            content = s[cstart:j-2].strip()
            if not (isdoc and content.startswith("info:")):
                kind = "/-! module doc" if ismod else ("/-- doc comment" if isdoc else "/- block comment")
                bad.append((f, startline, kind))
            i = j; continue
        i += 1
if bad:
    print(f"{len(bad)} disallowed comment(s) across {len(set(f for f,_,_ in bad))} file(s):")
    for f, ln, k in bad:
        print(f"  {f}:{ln}  {k}")
    print("\nOnly `/-- info: ... -/` receipts (before #guard_msgs) are allowed. Move reader-facing notes to markdown.")
    sys.exit(1)
print(f"Clean: no disallowed comments in {len(files)} Lean files")
