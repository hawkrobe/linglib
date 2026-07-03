import Linglib.Studies.VonFintelGillies2010
import Linglib.Data.Examples.VonFintelGillies2021

/-!
# von Fintel & Gillies (2021): Still Going Strong
[von-fintel-gillies-2021]

Follow-up to [von-fintel-gillies-2010]: the indirectness signal of *must*
is anti-knowledge, not anti-perception — direct-enough *knowledge* blocks
*must* even without perceptual evidence (Phil/Meryl dinner pair) — and
*can't φ* is incompatible with *it's possible that φ* (Observation 5).

## Main declarations

- `evidential_restriction_extends`: the 2010 felicity ↔ indirectness
  biconditional holds on the anti-knowledge rows
-/

namespace VonFintelGillies2021

open Data.Examples
open VonFintelGillies2010 (evidenceOf EvidenceType)

/-- Rows whose primary text is the modalized member of a bare/modal
    minimal pair. -/
def mustPairs : List LinguisticExample :=
  Examples.all.filter (·.feature? "kind" == some "must_pair")

/-- **Anti-knowledge**: the evidential restriction extends to rows where
    "direct" is direct-enough knowledge rather than perception. Phil, who
    checked everything himself, cannot say *Dinner must be ready* (ex. 24);
    Meryl, whose information is indirect, can (ex. 25). -/
theorem evidential_restriction_extends :
    ∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        (evidenceOf row).map EvidenceType.toCoarseSource ≠ some .direct := by
  decide

end VonFintelGillies2021
