#!/usr/bin/env python3
"""Generate typed basic-order-typology samples from canonical per-paper JSON.

A paper's classification of its language sample by dominant clause order, adposition type,
noun-dependent orders, and the further per-language properties it records, together with its
table of order types and the languages attesting each, is canonical JSON at
`Linglib/Data/OrderTypology/<Paper>.json`; this emits the kernel-reducible typed Lean module
`Linglib/Data/OrderTypology/<Paper>.lean` (`<Paper>.sample`, `<Paper>.types`). Mirrors
`gen_ud_deplength.py`: the generated Lean is never hand-edited — edit the JSON and re-run.

    python3 scripts/gen_order_typology.py Greenberg1963      # (re)generate
    python3 scripts/gen_order_typology.py --check [<Paper>]  # verify, no writes (CI)
    python3 scripts/gen_order_typology.py --all              # every JSON
"""
import sys, json, textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "OrderTypology"

SAMPLE_FIELDS = [
    ("verbPosition", "VerbPosition"), ("adposition", "Adposition"), ("genitive", "NounOrder"),
    ("adjective", "NounOrder"), ("demonstrative", "NounOrder"), ("numeral", "NounOrder"),
    ("rigidVerbFinal", "Bool"), ("questionParticleSentence", "Option SentencePlace"),
    ("questionParticleWord", "Option Placement"), ("questionWordFirst", "Bool"),
    ("auxiliary", "Option Placement"), ("adverbAdjective", "Option AdverbOrder"),
    ("comparison", "Option ComparisonOrder"), ("apposition", "Option Apposition"),
    ("relative", "Option NounOrder"), ("affixing", "Option Affixing"),
]
TYPE_FIELDS = [
    ("verbPosition", "VerbPosition"), ("adposition", "Adposition"), ("genitive", "NounOrder"),
    ("adjective", "NounOrder"),
]


def lit(value, ty: str) -> str:
    if ty == "Bool":
        return "true" if value else "false"
    if ty.startswith("Option "):
        return "none" if value is None else f"some .{value}"
    if value is None:
        raise ValueError(f"missing value of type {ty}")
    return f".{value}"


def sample_row(r: dict) -> str:
    fields = [f"language := {json.dumps(r['language'])}"]
    fields += [f"{k} := {lit(r[k], ty)}" for k, ty in SAMPLE_FIELDS]
    return "  { " + ",\n    ".join(fields) + " }"


def type_row(t: dict) -> str:
    fields = [f"index := {int(t['index'])}"]
    fields += [f"{k} := {lit(t[k], ty)}" for k, ty in TYPE_FIELDS]
    if t["attested"]:
        attested = textwrap.fill(", ".join(json.dumps(s) for s in t["attested"]), width=90,
                                 initial_indent="      ", subsequent_indent="      ")
        fields.append(f"attested := [\n{attested}]")
    else:
        fields.append("attested := []")
    return "  { " + ",\n    ".join(fields) + " }"


def render(paper: str, data: dict) -> str:
    sample = ",\n".join(sample_row(r) for r in data["sample"])
    types = ",\n".join(type_row(t) for t in data["types"])
    description = textwrap.fill(data["description"], width=100)
    return f"""import Linglib.Data.OrderTypology.Schema

/-!
# {paper} — basic order typology sample (generated)
[{data['bibkey']}]

Auto-generated from `Linglib/Data/OrderTypology/{paper}.json` by
`scripts/gen_order_typology.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

{description}
-/

namespace Data.OrderTypology.{paper}

open Data.OrderTypology

/-- The paper's language sample. -/
def sample : List SampleRow := [
{sample}]

/-- The paper's order types with the languages listed as attesting each. -/
def types : List OrderType := [
{types}]

end Data.OrderTypology.{paper}
"""


def generate(paper: str, check: bool) -> bool:
    src = DATA_DIR / f"{paper}.json"
    out = DATA_DIR / f"{paper}.lean"
    data = json.loads(src.read_text(encoding="utf-8"))
    text = render(paper, data)
    if check:
        ok = out.exists() and out.read_text(encoding="utf-8") == text
        print(f"[{'ok' if ok else 'STALE'}] {out.relative_to(ROOT)}")
        return ok
    out.write_text(text, encoding="utf-8")
    print(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)} "
          f"({len(data['sample'])} languages, {len(data['types'])} types)")
    return True


def main(argv: list) -> int:
    check = "--check" in argv
    args = [a for a in argv if not a.startswith("--")]
    if "--all" in argv or (check and not args):
        papers = sorted(p.stem for p in DATA_DIR.glob("*.json"))
    else:
        papers = args
    if not papers:
        print(__doc__)
        return 2
    ok = all([generate(p, check) for p in papers])
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
