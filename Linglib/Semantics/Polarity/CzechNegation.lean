import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Questions.Bias

/-!
# Negation positions in Czech polar questions

[stankova-2026] distinguishes three LF positions for the negative prefix of a Czech polar
question, inner (TP), medial (ModP) and outer (PolP), ordered by scope width, and
fingerprints them by the polarity items and particles each admits (her Table 1). This file
provides the positions, the diagnostics, the table as the set of diagnostics each position
licenses, and the evidential bias strength of each position. The lexical entries live in the
Czech fragments.

## Main declarations

* `Position` — the three negation positions, linearly ordered by scope width.
* `Diagnostic` — the five Table 1 diagnostics.
* `Position.licensed`, `Position.Licenses` — Table 1 as the set of diagnostics a position
  licenses, and its membership predicate.
* `Position.licensed_injective` — the table fingerprints the positions.
* `Position.licenses_nciLicensed_iff` and its siblings — each column characterized by scope:
  the two polarity columns test whether negation is propositional, and are complementary.
* `Position.biasStrength` — the evidential bias strength of each position.

## References

* [stankova-2026]
* [zeijlstra-2004]
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

/-- The Table 1 diagnostics of a negation position. -/
inductive Diagnostic where
  /-- The negation admits a positive polarity item like *nějaký* 'some' in its scope. -/
  | ppiOutscoping
  /-- The negation licenses a negative concord item like *žádný* 'no'. -/
  | nciLicensed
  /-- The particle *náhodou* 'by chance' is compatible. -/
  | nahodou
  /-- The particle *ještě* 'yet, still' is compatible. -/
  | jeste
  /-- The particle *fakt* 'really' is compatible. -/
  | fakt
  deriving DecidableEq, Repr, Fintype

namespace Position

/-- Scope width: inner ↦ 0, medial ↦ 1, outer ↦ 2. -/
def toNat : Position → ℕ
  | .inner => 0
  | .medial => 1
  | .outer => 2

instance : LinearOrder Position :=
  LinearOrder.lift' toNat fun a b h => by cases a <;> cases b <;> simp_all [toNat]

/-! ### Table 1 -/

/-- [stankova-2026]'s Table 1: the diagnostics each negation position licenses. -/
def licensed : Position → Finset Diagnostic
  | .inner => {.nciLicensed, .jeste, .fakt}
  | .medial => {.ppiOutscoping, .fakt}
  | .outer => {.ppiOutscoping, .nahodou}

/-- A cell of Table 1: the position licenses the diagnostic. -/
abbrev Licenses (pos : Position) (d : Diagnostic) : Prop := d ∈ pos.licensed

/-- Table 1 fingerprints the positions: no two license the same diagnostics. -/
theorem licensed_injective : Function.Injective licensed := by decide

variable {pos : Position}

/-- Only propositional negation licenses a concord item, by Agree with the operator. -/
theorem licenses_nciLicensed_iff : pos.Licenses .nciLicensed ↔ pos = .inner := by
  cases pos <;> decide

/-- Every non-propositional negation admits a positive polarity item. -/
theorem licenses_ppiOutscoping_iff : pos.Licenses .ppiOutscoping ↔ pos ≠ .inner := by
  cases pos <;> decide

/-- The two polarity columns are complementary: both test whether negation is
propositional. -/
theorem licenses_ppiOutscoping_iff_not_nciLicensed :
    pos.Licenses .ppiOutscoping ↔ ¬ pos.Licenses .nciLicensed := by
  rw [licenses_ppiOutscoping_iff, licenses_nciLicensed_iff]

/-- *Náhodou* singles out FALSUM. -/
theorem licenses_nahodou_iff : pos.Licenses .nahodou ↔ pos = .outer := by
  cases pos <;> decide

/-- *Ještě* singles out propositional negation. -/
theorem licenses_jeste_iff : pos.Licenses .jeste ↔ pos = .inner := by
  cases pos <;> decide

/-- *Fakt* is repelled by FALSUM alone. -/
theorem licenses_fakt_iff : pos.Licenses .fakt ↔ pos ≠ .outer := by
  cases pos <;> decide

/-! ### Bias -/

/-- The evidential bias strength of a negation position: inner strong, medial weak, outer
none, FALSUM conveying epistemic rather than evidential bias ([stankova-2026]). -/
def biasStrength : Position → EvidentialBiasStrength
  | .inner => .strong
  | .medial => .weak
  | .outer => .none_

end Position

end Czech.Negation
