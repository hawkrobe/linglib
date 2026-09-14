import Linglib.Semantics.Evidential.Defs

/-!
# Saraguro Kichwa evidentiality

Saraguro Kichwa (Quechuan, Loja Province, Ecuador) has a three-way contrast in matrix
declaratives: direct *-rka* and reportative *-shka*, both also past tenses, and inferential
*-shi*. The discourse-sensitive enclitic *=mi*, whose analysis is contested across Quechuan
varieties, is not an evidential of this variety; [martinez-vera-2026] analyzes it in
`Studies/MartinezVera2026.lean`.

## References

* [aikhenvald-2004]
* [martinez-vera-2026]
-/

namespace Quechua.SaraguroKichwa.Evidentiality

open Evidential

/-- Direct *-rka*, reportative *-shka* and inferential *-shi*. -/
def evidentials : List Evidential :=
  [ { form := "-rka", exponent := .verbalAffix, covers := {.visual, .sensory} },
    { form := "-shka", exponent := .verbalAffix, covers := {.hearsay} },
    { form := "-shi", exponent := .verbalAffix, covers := {.inference, .assumption} } ]

end Quechua.SaraguroKichwa.Evidentiality
