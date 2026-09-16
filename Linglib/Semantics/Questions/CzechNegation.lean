import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Questions.Bias

/-!
# Negation positions in Czech polar questions

[stankova-2026] distinguishes three LF positions for the negative prefix of a Czech polar
question, inner (TP), medial (ModP) and outer (PolP), ordered by scope width and each
carrying its own evidential bias strength. Inner negation is the propositional operator that
licenses negative concord items by Agree ([zeijlstra-2004]); outer negation is the commitment
operator FALSUM ([repp-2013]). This file provides the positions and their bias strengths, the
Czech refinement of the `Question.PQForm` typology. The verb order realizing each position
lives in `Studies/StankovaSimik2025.lean` and the Table 1 diagnostics in
`Studies/Stankova2026.lean`.

## Main declarations

* `Position` — the three negation positions, linearly ordered by scope width.
* `Position.biasStrength` — the evidential bias strength of each position.

## References

* [stankova-2026]
* [zeijlstra-2004]
* [repp-2013]
-/

namespace Czech.Negation

open Question

/-- The LF positions of negation in a Czech polar question, ordered by scope width: inner
negation in TP is propositional negation, medial negation in ModP scopes over the evidential
modal, and outer negation in PolP is the commitment operator FALSUM ([stankova-2026]). -/
inductive Position where
  /-- Inner negation: propositional ¬p in TP, licensing negative concord items by Agree
      ([zeijlstra-2004]). -/
  | inner
  /-- Medial negation: over the evidential modal in ModP, part of the bias presupposition. -/
  | medial
  /-- Outer negation: FALSUM in PolP, high negation with obligatory focus. -/
  | outer
  deriving DecidableEq, Repr, Fintype

namespace Position

/-- Scope width: inner ↦ 0, medial ↦ 1, outer ↦ 2. -/
def toNat : Position → ℕ
  | .inner => 0
  | .medial => 1
  | .outer => 2

instance : LinearOrder Position :=
  LinearOrder.lift' toNat fun a b h => by cases a <;> cases b <;> simp_all [toNat]

/-- The evidential bias strength of a negation position: inner strong, medial weak, outer
none, FALSUM conveying epistemic rather than evidential bias ([stankova-2026]). -/
def biasStrength : Position → EvidentialBiasStrength
  | .inner => .strong
  | .medial => .weak
  | .outer => .none_

end Position

end Czech.Negation
