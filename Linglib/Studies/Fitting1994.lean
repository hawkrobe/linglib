import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.Bilattice.Basic

/-!
# Kleene's three-valued logic as the consistent fragment of Belnap's FOUR
[fitting-1994]

[fitting-1994] ("Kleene's Three Valued Logics and Their Children") organizes
Kleene's logics as fragments of [belnap-1977]'s four-valued bilattice `FOUR`,
sliced by the *conflation* `−` (the knowledge-order involution): the strong
Kleene values are exactly those `x` with `x ≤_k −x` — the *consistent*
(non-glut) values.

`FOUR` and its two orders / negation / conflation are the shared substrate in
`Core.Logic.Bilattice`. Here we prove the slicing for linglib's `Truth3`
(Kleene's three-valued logic, [kleene-1952]): `ofTruth3` embeds `Truth3` onto the
consistent fragment of `FOUR`, matching the truth order (`Truth3`'s `≤` vs
`FOUR`'s `≤`), the knowledge order (`Truth3.toFlat`, i.e. `Flat Bool`, vs
`FOUR`'s `≤ₖ`), and negation. So the gap logic linglib uses for presupposition
is the `I`-free slice; the glut `I` is what trivalence excludes. The bilattice
route to natural-language entailment, implicature, and presupposition is
[schoter-1996] (see `Studies.Schoter1996`).

## Main results

* `Fitting1994.ofTruth3` — the embedding `Truth3 → FOUR`
* `Fitting1994.ofTruth3_consistent`, `consistent_range` — its image is exactly
  the consistent fragment
* `le_ofTruth3`, `kLE_ofTruth3`, `neg_ofTruth3`, `inf_ofTruth3`/`sup_ofTruth3`
  — `Truth3` is the consistent fragment of `FOUR` as a bilattice *logic*: both
  orders, negation, and the strong-Kleene connectives `∧`/`∨` as restrictions
  of `FOUR`'s truth meet/join
-/

open Trivalent (Truth3)
open Bilattice
open Bilattice.FOUR (U T F Consistent)

namespace Fitting1994

/-- The embedding of `Truth3` (Kleene-3) into `FOUR`: `indet ↦ ⊥`, `true ↦ T`,
`false ↦ F`. Its image is exactly the consistent fragment. -/
def ofTruth3 : Truth3 → FOUR
  | .indet => U
  | .true  => T
  | .false => F

theorem ofTruth3_injective : Function.Injective ofTruth3 := by
  intro a b; cases a <;> cases b <;> decide

theorem ofTruth3_consistent (a : Truth3) : Consistent (ofTruth3 a) := by
  cases a <;> decide

/-- The image of `ofTruth3` is the whole consistent fragment. -/
theorem consistent_range {x : FOUR} (hx : Consistent x) : ∃ a, ofTruth3 a = x := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b
  · exact ⟨.indet, rfl⟩
  · exact ⟨.false, rfl⟩
  · exact ⟨.true, rfl⟩
  · exact absurd hx (by decide)

/-- **Truth-order match**: `Truth3`'s truth order is `FOUR`'s, on the fragment. -/
theorem le_ofTruth3 (a b : Truth3) : a ≤ b ↔ ofTruth3 a ≤ ofTruth3 b := by
  cases a <;> cases b <;> decide

/-- **Knowledge-order match**: `Truth3`'s knowledge order (`Truth3.toFlat`, i.e.
`Flat Bool`) is `FOUR`'s knowledge order on the fragment. -/
theorem kLE_ofTruth3 (a b : Truth3) :
    Truth3.toFlat a ≤ Truth3.toFlat b ↔ ofTruth3 a ≤ₖ ofTruth3 b := by
  cases a <;> cases b <;> decide

/-- **Negation match**: Kleene negation is `FOUR`-negation on the fragment. -/
theorem neg_ofTruth3 (a : Truth3) :
    ofTruth3 (Truth3.neg a) = Product.neg (ofTruth3 a) := by
  cases a <;> rfl

/-- **Connective match, conjunction**: strong-Kleene `∧` (`Truth3`'s `⊓ = min`)
is the restriction of `FOUR`'s truth meet to the consistent fragment — the
fragment is a fragment *as a logic*, not just as a pair of posets
([fitting-1994]). -/
theorem inf_ofTruth3 (a b : Truth3) :
    ofTruth3 (a ⊓ b) = ofTruth3 a ⊓ ofTruth3 b := by
  cases a <;> cases b <;> decide

/-- **Connective match, disjunction**: strong-Kleene `∨` (`Truth3`'s `⊔ = max`)
is the restriction of `FOUR`'s truth join to the consistent fragment. -/
theorem sup_ofTruth3 (a b : Truth3) :
    ofTruth3 (a ⊔ b) = ofTruth3 a ⊔ ofTruth3 b := by
  cases a <;> cases b <;> decide

end Fitting1994
