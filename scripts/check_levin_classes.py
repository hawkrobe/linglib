#!/usr/bin/env python3
"""Check that every English verb entry's `levinClasses` equals the set of Levin classes whose
member lists (Linglib/Semantics/ArgumentStructure/LevinClass/Members.lean) carry its citation
form, less its `levinExcluded`. Exit status 1 on any mismatch."""
import re, sys, collections, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
members = (root / "Linglib/Semantics/ArgumentStructure/LevinClass/Members.lean").read_text()
body = members[members.index("def members : LevinClass → List String"):members.index("/-- The classes whose member lists carry the form.")]
verb2 = collections.defaultdict(set)
for ctor, lst in re.findall(r"\| \.(\w+) => \[([\s\S]*?)\]\n", body):
    for w in re.findall(r'"([^"]*)"', lst):
        verb2[w].add(ctor)
frag = (root / "Linglib/Fragments/English/Predicates.lean").read_text()
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
