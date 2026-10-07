#!/usr/bin/env python3
"""Check that every English verb entry's `levinClasses` equals the set of Levin classes whose
member lists (Linglib/Data/VerbClasses/Levin1993.json, read through `LevinClass.members`) carry its
citation form, less its `levinExcluded`. Exit status 1 on any mismatch."""
import re, sys, json, collections, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
data = json.loads((root / "Linglib/Data/VerbClasses/Levin1993.json").read_text(encoding="utf-8"))
enum = (root / "Linglib/Semantics/ArgumentStructure/LevinClass.lean").read_text(encoding="utf-8")
ctors = re.findall(r"^  \| (\w+)\s", enum.split("inductive LevinClass where")[1].split("deriving")[0],
                   re.M)
if len(ctors) != len(data["classes"]):
    sys.exit(f"{len(ctors)} LevinClass constructors but {len(data['classes'])} classes in the data")
verb2 = collections.defaultdict(set)
for ctor, cls in zip(ctors, data["classes"]):
    for w in cls["members"]:
        verb2[w].add(ctor)
frag = "\n".join(f.read_text() for f in sorted((root / "Linglib/Fragments/English/Verbs").glob("*.lean")))
blocks = re.split(r"(?=^(?:/--(?:(?!-/).)*?-/\n)?def \w+ : Verb)", frag, flags=re.M | re.S)
bad = 0
checked = 0
for b in blocks:
    m = re.search(r"^def (\w+) : Verb", b, re.M)
    f = re.search(r'form := "([^"]+)"', b)
    if not m or not f:
        continue
    def field(name):
        mm = re.search(name + r" := \{([\s\S]*?)\}", b)
        return set(re.findall(r"(?:LevinClass\.)?\.?(\w+)", mm.group(1))) if mm else set()
    checked += 1
    have, excl = field("levinClasses"), field("levinExcluded")
    want = verb2.get(f.group(1), set()) - excl
    if have != want:
        bad += 1
        print(f"{m.group(1)} ({f.group(1)}): entry {sorted(have)} vs lists {sorted(want)}")
print(f"checked {checked} entries, {bad} mismatches")
sys.exit(1 if bad else 0)
