module

public import Linglib.Data.Hiatus.Schema

/-!
# Mkochi2021 — hiatus resolution sample (generated)
[mkochi-2021]

Auto-generated from `Linglib/Data/Hiatus/Mkochi2021.json` by
`scripts/gen_hiatus.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

The kinds of juncture at which the paper reports elision of the second vowel in Malawian CiTonga: a
verb root and a final vowel or extension, two suffixes (two final vowels, or an extension and a
final vowel), and two enclitics.
-/

@[expose] public section

namespace Data.Hiatus.Mkochi2021

open Data.Hiatus

/-- The paper's reports of which vowel elides, one row per language and juncture. -/
def rows : List ElisionRow := [
  ⟨"CiTonga", .rootSuffix, .second, false⟩,
  ⟨"CiTonga", .suffixSuffix, .second, false⟩,
  ⟨"CiTonga", .cliticClitic, .second, false⟩]

end Data.Hiatus.Mkochi2021
