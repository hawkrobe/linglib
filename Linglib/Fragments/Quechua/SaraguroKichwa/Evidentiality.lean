module

public import Linglib.Semantics.Evidential.Defs

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

@[expose] public section

namespace Quechua.SaraguroKichwa.Evidentiality

open Evidential

/-- The direct past *-rka* marks direct perceptual evidence. -/
def rka : Evidential := { form := "-rka", exponent := .verbalAffix, covers := {.visual, .sensory} }

/-- The reportative past *-shka* marks that the speaker was told. -/
def shka : Evidential := { form := "-shka", exponent := .verbalAffix, covers := {.hearsay} }

/-- The inferential *-shi* marks inference or assumption. -/
def shi : Evidential :=
  { form := "-shi", exponent := .verbalAffix, covers := {.inference, .assumption} }

/-- The evidentials of matrix declaratives are direct *-rka*, reportative *-shka* and inferential
*-shi*. -/
def evidentials : List Evidential := [rka, shka, shi]

end Quechua.SaraguroKichwa.Evidentiality
