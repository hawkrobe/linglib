import Linglib.Theories.Semantics.Exhaustification.Innocent
import Linglib.Core.Logic.Truth3
import Mathlib.Tactic.DeriveFintype

/-!
# Trivalent Exhaustification
@cite{spector-sudo-2017}

Benjamin Spector and Yasutada Sudo, "Presupposed Ignorance and
Exhaustification: How Scalar Implicatures and Presuppositions Interact."
*Linguistics and Philosophy* 40, pp. 473–517.

## Core Operators

Two trivalent exhaustification operators extend bivalent EXH
(@cite{fox-2007}) to handle presupposition-bearing sentences:

- **EXH¹** (weak negation): `~ψ = true` when `ψ` is undefined →
  does NOT import presuppositions from alternatives
- **EXH²** (strong negation): `~ψ = #` when `ψ` is undefined →
  DOES import presuppositions from alternatives

Both reuse the same innocently excludable (IE) alternatives
computed by Fox's algorithm on the classical truth conditions.

## Connection to Presupposition Projection

@cite{wang-davidson-2026} show that this distinction is empirically
consequential for presupposition filtering across disjunction:
- EXH² + any projection theory predicts that exclusive disjunction
  increases projection (Type A)
- EXH¹ + any projection theory predicts no effect of exclusivity
  on projection (Type B)

Their Mandarin experiment finds no effect of exclusivity on filtering,
consistent with Type B (EXH¹).

## Design

This file is generic infrastructure, not a paper replication.
The IE computation reuses `Exhaustification.innocent.excluded`
(mathlib-canonical Finset version). The trivalent layer wraps the
bivalent IE result with `Truth3` semantics.
-/

namespace Exhaustification.Trivalent

open Core.Duality (Truth3 Prop3)
open Exhaustification (innocent predToFinset altsFromPreds)


-- ════════════════════════════════════════════════════════════════
-- § 1. Classical extraction
-- ════════════════════════════════════════════════════════════════

/-- Extract the classical (bivalent) truth conditions from a
    trivalent proposition: `true` maps to `true`; `false` and
    `indet` both map to `false`.

    The IE computation operates on these classical truth conditions —
    entailment, consistency, and maximality are all defined bivalently.
    The trivalent layer applies only *after* IE is computed.

    Pointwise lift of `Truth3.toBoolOrFalse`. -/
def classicalPart {W : Type} (p : W → Truth3) : W → Bool :=
  Truth3.toBoolOrFalse ∘ p


-- ════════════════════════════════════════════════════════════════
-- § 2. EXH¹ — weak-negation exhaustification
-- ════════════════════════════════════════════════════════════════

/-- Trivalent EXH¹ (weak negation).

    @cite{spector-sudo-2017}'s weak-negation operator (reproduced
    as (4)/(5) in @cite{wang-davidson-2026}):
    - Presupposes whatever φ presupposes: φ(w)=# → EXH¹(w)=#
    - Asserts φ and weakly negates all IE alternatives
    - Weak negation: `~# = true`, so alternatives' presuppositions
      do NOT project through EXH¹

    Type B in @cite{wang-davidson-2026}: predicts no effect of
    exclusivity on presupposition filtering. -/
def exh1 {W : Type} [Fintype W] [DecidableEq W] (alts : List (W → Truth3))
    (p : W → Truth3) : W → Truth3 :=
  let φF := predToFinset (classicalPart p)
  let altSet := altsFromPreds (alts.map classicalPart)
  let excluded := innocent.excluded altSet φF
  fun w => match p w with
    | .indet => .indet
    | .false => .false
    | .true =>
      -- Weak negation: ψ(w) ≠ true suffices (indet counts as "negated")
      if alts.all fun q =>
        if predToFinset (classicalPart q) ∈ excluded then q w != .true
        else true
      then .true
      else .false


-- ════════════════════════════════════════════════════════════════
-- § 3. EXH² — strong-negation exhaustification
-- ════════════════════════════════════════════════════════════════

/-- Trivalent EXH² (strong negation).

    @cite{spector-sudo-2017}'s strong-negation operator (reproduced
    as (6)/(7) in @cite{wang-davidson-2026}):
    - Presupposes whatever φ presupposes AND whatever the negated
      IE alternatives presuppose
    - Asserts φ and strongly negates all IE alternatives
    - Strong negation: `~# = #`, so alternatives' presuppositions
      DO project through EXH²

    Type A in @cite{wang-davidson-2026}: predicts that increasing
    exclusivity reduces presupposition filtering. -/
def exh2 {W : Type} [Fintype W] [DecidableEq W] (alts : List (W → Truth3))
    (p : W → Truth3) : W → Truth3 :=
  let φF := predToFinset (classicalPart p)
  let altSet := altsFromPreds (alts.map classicalPart)
  let excluded := innocent.excluded altSet φF
  fun w =>
    -- Strong negation: any IE alternative undefined → result undefined
    if alts.any fun q =>
      predToFinset (classicalPart q) ∈ excluded ∧ q w == .indet
    then .indet
    else match p w with
      | .indet => .indet
      | .false => .false
      | .true =>
        -- Strong negation: all IE alternatives must be false (not indet)
        if alts.all fun q =>
          if predToFinset (classicalPart q) ∈ excluded then q w == .false
          else true
        then .true
        else .false


-- ════════════════════════════════════════════════════════════════
-- § 4. Key properties
-- ════════════════════════════════════════════════════════════════

/-- EXH¹ preserves the presupposition of the prejacent:
    if φ(w) = #, then EXH¹(φ)(w) = #. -/
theorem exh1_preserves_presup {W : Type} [Fintype W] [DecidableEq W]
    (alts : List (W → Truth3)) (p : W → Truth3) (w : W)
    (h : p w = .indet) : exh1 alts p w = .indet := by
  unfold exh1; simp only [h]

/-- EXH² also preserves the prejacent's presupposition. -/
theorem exh2_preserves_presup {W : Type} [Fintype W] [DecidableEq W]
    (alts : List (W → Truth3)) (p : W → Truth3) (w : W)
    (h : p w = .indet) : exh2 alts p w = .indet := by
  unfold exh2; split <;> simp_all


-- ════════════════════════════════════════════════════════════════
-- § 5. Concrete verification: disjunction with presupposition
-- ════════════════════════════════════════════════════════════════

end Exhaustification.Trivalent
