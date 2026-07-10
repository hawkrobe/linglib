import Linglib.Core.Logic.Trivalent
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
`Core.Logic.Bilattice`. Here we prove the slicing for linglib's `Trivalent`
(Kleene's three-valued logic, [kleene-1952]): `ofTruth` embeds `Trivalent` onto the
consistent fragment of `FOUR`, matching the truth order (`Trivalent`'s `≤` vs
`FOUR`'s `≤`), the knowledge order (`Trivalent.toFlat`, i.e. `Flat Bool`, vs
`FOUR`'s `≤ₖ`), and negation. So the gap logic linglib uses for presupposition
is the `I`-free slice; the glut `I` is what trivalence excludes. The bilattice
route to natural-language entailment, implicature, and presupposition is
[schoter-1996] (see `Studies.Schoter1996`).

## Main results

* `Fitting1994.ofTruth` — the embedding `Trivalent → FOUR`
* `Fitting1994.ofTruth_consistent`, `consistent_range` — its image is exactly
  the consistent fragment
* `le_ofTruth`, `kLE_ofTruth`, `neg_ofTruth`, `inf_ofTruth`/`sup_ofTruth`
  — `Trivalent` is the consistent fragment of `FOUR` as a bilattice *logic*: both
  orders, negation, and the strong-Kleene connectives `∧`/`∨` as restrictions
  of `FOUR`'s truth meet/join
-/

open Bilattice
open Bilattice.FOUR (U T F Consistent)

namespace Fitting1994

/-- The embedding of `Trivalent` (Kleene-3) into `FOUR`: `indet ↦ ⊥`, `true ↦ T`,
`false ↦ F`. Its image is exactly the consistent fragment. -/
def ofTruth : Trivalent → FOUR
  | .indet => U
  | .true  => T
  | .false => F

theorem ofTruth_injective : Function.Injective ofTruth := by
  intro a b; cases a <;> cases b <;> decide

theorem ofTruth_consistent (a : Trivalent) : Consistent (ofTruth a) := by
  cases a <;> decide

/-- The image of `ofTruth` is the whole consistent fragment. -/
theorem consistent_range {x : FOUR} (hx : Consistent x) : ∃ a, ofTruth a = x := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b
  · exact ⟨.indet, rfl⟩
  · exact ⟨.false, rfl⟩
  · exact ⟨.true, rfl⟩
  · exact absurd hx (by decide)

/-- **Trivalent-order match**: `Trivalent`'s truth order is `FOUR`'s, on the fragment. -/
theorem le_ofTruth (a b : Trivalent) : a ≤ b ↔ ofTruth a ≤ ofTruth b := by
  cases a <;> cases b <;> decide

/-- **Knowledge-order match**: `Trivalent`'s knowledge order (`Trivalent.toFlat`, i.e.
`Flat Bool`) is `FOUR`'s knowledge order on the fragment. -/
theorem kLE_ofTruth (a b : Trivalent) :
    Trivalent.toFlat a ≤ Trivalent.toFlat b ↔ ofTruth a ≤ₖ ofTruth b := by
  cases a <;> cases b <;> decide

/-- **Negation match**: Kleene negation is `FOUR`-negation on the fragment. -/
theorem neg_ofTruth (a : Trivalent) :
    ofTruth (Trivalent.neg a) = Product.neg (ofTruth a) := by
  cases a <;> rfl

/-- **Connective match, conjunction**: strong-Kleene `∧` (`Trivalent`'s `⊓ = min`)
is the restriction of `FOUR`'s truth meet to the consistent fragment — the
fragment is a fragment *as a logic*, not just as a pair of posets
([fitting-1994]). -/
theorem inf_ofTruth (a b : Trivalent) :
    ofTruth (a ⊓ b) = ofTruth a ⊓ ofTruth b := by
  cases a <;> cases b <;> decide

/-- **Connective match, disjunction**: strong-Kleene `∨` (`Trivalent`'s `⊔ = max`)
is the restriction of `FOUR`'s truth join to the consistent fragment. -/
theorem sup_ofTruth (a b : Trivalent) :
    ofTruth (a ⊔ b) = ofTruth a ⊔ ofTruth b := by
  cases a <;> cases b <;> decide

end Fitting1994
