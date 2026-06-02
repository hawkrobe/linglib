import Linglib.Semantics.Evidential.Defs

/-!
# Bulgarian Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Two-choice direct vs indirect via the aorist (direct) vs l-form (indirect)
contrast, fused with TAM. The best-known European language with grammatical
evidentials. Balkan Sprachbund. WALS and Aikhenvald agree.

Sister to `Fragments/Slavic/Bulgarian/Evidentials.lean` which holds the
@cite{cumming-2026} tense-evidential paradigm data.
-/

namespace Bulgarian.Evidentiality

/-! ### Typed evidential inventory

Bulgarian's 2-way contrast via aorist (direct) vs l-form (indirect),
fused with TAM. The l-form covers both inferential and reportative
meanings — represented here as the inferential kind (the dominant
inference function); reportative extensions are an Aikhenvald-style
semantic extension. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "aorist", exponent := .tamFusion },
    .inferential { form := "l-form", exponent := .tamFusion } ]

example : evidentials.length = 2 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Bulgarian.Evidentiality
