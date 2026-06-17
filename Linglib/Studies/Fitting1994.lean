import Linglib.Core.Logic.Truth3

/-!
# Kleene's three-valued logic as the consistent fragment of Belnap's FOUR
[fitting-1994]

[fitting-1994] ("Kleene's Three Valued Logics and Their Children") organizes
Kleene's logics as fragments of Belnap's four-valued bilattice `FOUR`, sliced by
the *conflation* `−` (the knowledge-order involution). His key observation: the
strong Kleene values are exactly those `x` with `x ≤_k −x`, i.e. information that
does not exceed its own conflation — the *consistent* (non-glut) values.

`FOUR` carries two orders — truth `≤_t` and knowledge `≤_k` — with negation `¬`
(truth inversion, swaps `true`/`false`) and conflation `−` (knowledge inversion,
swaps `⊥`/`⊤`). Here `FOUR = Bool × Bool` with coordinates `(for, against)`
(membership in the true- and false-extensions; [schoter-1996]'s evidence pairs,
transposed).

This file proves that linglib's `Truth3` (Kleene's three-valued logic,
[kleene-1952]) is exactly the consistent fragment of `FOUR`, in **both** orders:
`ofTruth3` embeds `Truth3` onto `{x // Consistent x}`, matching the truth order
(`Truth3`'s `≤`), the knowledge order (`Truth3.toFlat`, i.e. `Flat Bool`, from
the Kleene-bilattice grounding), and negation. So the gap logic linglib already
uses for presupposition is the `I`-free slice of the four-valued bilattice; the
glut `I` is what trivalence excludes. The bilattice route to natural-language
entailment, implicature, and presupposition is [schoter-1996].

## Main results

* `FOUR` — Belnap's four-valued bilattice, `(for, against)` pairs over `Bool`
* `FOUR.tLE`/`kLE`/`neg`/`conf` — truth & knowledge orders, negation, conflation
* `FOUR.Consistent` — the non-glut fragment `x ≤_k −x` (`= x ≠ I`)
* `Fitting1994.tLE_ofTruth3`, `kLE_ofTruth3`, `neg_ofTruth3` — `Truth3` is the
  consistent fragment of `FOUR` as a bilattice (both orders + negation)
-/

open Core.Duality

namespace Fitting1994

/-- Belnap's four-valued bilattice `FOUR`, as `(for, against)` pairs over `Bool`
(membership in the true- / false-extension). -/
abbrev FOUR := Bool × Bool

namespace FOUR

/-- `⊥`: neither true nor false — no information (a truth-value gap). -/
def U : FOUR := (false, false)
/-- `true`. -/
def T : FOUR := (true, false)
/-- `false`. -/
def F : FOUR := (false, true)
/-- `⊤`: both true and false — inconsistent (a truth-value glut). -/
def I : FOUR := (true, true)

/-- Truth order: `x ≤_t y` iff more evidence-for and less evidence-against. -/
@[reducible] def tLE (x y : FOUR) : Prop := x.1 ≤ y.1 ∧ y.2 ≤ x.2
/-- Knowledge order: `x ≤_k y` iff more evidence both ways (subset of info). -/
@[reducible] def kLE (x y : FOUR) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2
/-- Negation: truth inversion, swaps the two coordinates (`true ↔ false`). -/
def neg (x : FOUR) : FOUR := (x.2, x.1)
/-- Conflation `−`: knowledge inversion, `(a,b) ↦ (¬b, ¬a)` (swaps `⊥ ↔ ⊤`). -/
def conf (x : FOUR) : FOUR := (!x.2, !x.1)

/-- The *consistent* (non-glut) fragment: information does not exceed its own
conflation, `x ≤_k −x` — equivalently `x ≠ I` ([fitting-1994]). -/
@[reducible] def Consistent (x : FOUR) : Prop := kLE x (conf x)

@[simp] theorem consistent_iff (x : FOUR) : Consistent x ↔ x ≠ I := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

end FOUR

open FOUR

/-- The embedding of `Truth3` (Kleene-3) into `FOUR`: `indet ↦ ⊥`, `true ↦ T`,
`false ↦ F`. Its image is exactly the consistent fragment. -/
def ofTruth3 : Truth3 → FOUR
  | .indet => U
  | .true  => T
  | .false => F

theorem ofTruth3_injective : Function.Injective ofTruth3 := by
  intro a b h; cases a <;> cases b <;> simp_all [ofTruth3, U, T, F]

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
theorem tLE_ofTruth3 (a b : Truth3) : a ≤ b ↔ tLE (ofTruth3 a) (ofTruth3 b) := by
  cases a <;> cases b <;> decide

/-- **Knowledge-order match**: `Truth3`'s knowledge order (`Truth3.toFlat`, i.e.
`Flat Bool`) is `FOUR`'s knowledge order on the fragment. -/
theorem kLE_ofTruth3 (a b : Truth3) :
    Truth3.toFlat a ≤ Truth3.toFlat b ↔ kLE (ofTruth3 a) (ofTruth3 b) := by
  cases a <;> cases b <;> decide

/-- **Negation match**: Kleene negation is `FOUR`-negation on the fragment. -/
theorem neg_ofTruth3 (a : Truth3) : ofTruth3 (Truth3.neg a) = neg (ofTruth3 a) := by
  cases a <;> rfl

end Fitting1994
