#!/usr/bin/env python3
"""Generate typed hiatus resolution samples from canonical per-paper JSON.

A paper's survey of which vowel elides at each kind of juncture is canonical JSON at
`Linglib/Data/Hiatus/<Paper>.json`, grouped as the paper lists it: a juncture, the vowel that
elides, the languages reported, and those reported tentatively. This emits the kernel-reducible
typed Lean module `Linglib/Data/Hiatus/<Paper>.lean` (`<Paper>.rows`), one row per language and
group. Mirrors `gen_word_order.py`: the generated Lean is never hand-edited — edit the JSON and
re-run.

    python3 scripts/gen_hiatus.py Casali1997      # (re)generate
    python3 scripts/gen_hiatus.py --check [<Paper>]  # verify, no writes (CI)
    python3 scripts/gen_hiatus.py --all              # every JSON
"""
import sys, json, textwrap
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible, import_stmt  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "Hiatus"

JUNCTURES = {"lexicalLexical", "lexicalFunction", "prefixRoot", "rootSuffix"}
ELIDED = {"first", "second"}


def rows(data: dict) -> list:
    out = []
    for g in data["groups"]:
        if g["juncture"] not in JUNCTURES or g["elided"] not in ELIDED:
            raise ValueError(f"bad group {g['juncture']}/{g['elided']}")
        for language, tentative in ([(l, False) for l in g["languages"]]
                                    + [(l, True) for l in g["tentative"]]):
            out.append(f"  ⟨{json.dumps(language, ensure_ascii=False)}, .{g['juncture']}, "
                       f".{g['elided']}, {'true' if tentative else 'false'}⟩")
    return out


def render(paper: str, data: dict) -> str:
    body = ",\n".join(rows(data))
    description = textwrap.fill(data["description"], width=100)
    return f"""import Linglib.Data.Hiatus.Schema

/-!
# {paper} — hiatus resolution sample (generated)
[{data['bibkey']}]

Auto-generated from `Linglib/Data/Hiatus/{paper}.json` by
`scripts/gen_hiatus.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

{description}
-/

namespace Data.Hiatus.{paper}

open Data.Hiatus

/-- The paper's reports of which vowel elides, one row per language and juncture. -/
def rows : List ElisionRow := [
{body}]

end Data.Hiatus.{paper}
"""


def generate(paper: str, check: bool) -> bool:
    src = DATA_DIR / f"{paper}.json"
    out = DATA_DIR / f"{paper}.lean"
    data = json.loads(src.read_text(encoding="utf-8"))
    text = as_module_if_possible(render(paper, data))
    if check:
        ok = out.exists() and out.read_text(encoding="utf-8") == text
        print(f"[{'ok' if ok else 'STALE'}] {out.relative_to(ROOT)}")
        return ok
    out.write_text(text, encoding="utf-8")
    print(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)} ({len(rows(data))} rows)")
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
