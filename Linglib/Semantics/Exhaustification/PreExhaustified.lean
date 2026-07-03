/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Basic
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fintype.Basic

/-!
# Pre-exhaustified alternatives and proper strengthening
[chierchia-2013] [fox-2007]

The grammatical theory of implicature negates *pre-exhaustified* domain
alternatives: each alternative strengthened against its rivals before being
negated. For a family `A : ι → Prop`, the pre-exhaustification of `A i` is
"`A i` and no rival holds" — i.e. `A i` holds *uniquely*. Negating every
pre-exhaustified alternative is therefore exactly the claim that no
alternative holds uniquely (`forall_not_preExh_iff`): the combinatorial core
of free-choice effects — plain, modal ([chierchia-2013]), and epistemic
(ignorance inferences, [mihoc-2019]) — where the assertion supplies "at
least one region is live" and unique-truth failure spreads possibility
across all of them.

`ProperlyStrengthens` names the requirement some items impose on their
exhaustification: the result must be *strictly* stronger than the prejacent.
When every alternative is individually inconsistent with the prejacent,
exhaustification is vacuous and the requirement fails
(`not_properlyStrengthens_of_iff`) — the engine of anti-negativity
(positive-polarity) verdicts.

## Main definitions

- `preExh`: an alternative strengthened against its rivals
- `ProperlyStrengthens`: strict strengthening of a prejacent

## Main results

- `exists_preExh_iff_existsUnique`, `forall_not_preExh_iff`: negating all
  pre-exhaustified alternatives = no alternative holds uniquely
- `not_properlyStrengthens_of_iff`: vacuous exhaustification fails proper
  strengthening
-/

namespace Exhaustification

variable {ι α : Type*} {A : ι → Prop}

/-- Pre-exhaustification of alternative `i` against its rivals: `A i` holds
and no distinct alternative does. -/
def preExh (A : ι → Prop) (i : ι) : Prop :=
  A i ∧ ∀ j, j ≠ i → ¬ A j

instance [DecidableEq ι] [Fintype ι] [∀ i, Decidable (A i)] (i : ι) :
    Decidable (preExh A i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

/-- Some alternative is pre-exhaustifiedly true iff some alternative is
*uniquely* true. -/
theorem exists_preExh_iff_existsUnique : (∃ i, preExh A i) ↔ ∃! i, A i := by
  constructor
  · rintro ⟨i, hi, hunique⟩
    exact ⟨i, hi, fun j hj => by_contra fun hne => hunique j hne hj⟩
  · rintro ⟨i, hi, hunique⟩
    exact ⟨i, hi, fun j hne hj => hne (hunique j hj)⟩

/-- Negating every pre-exhaustified alternative is exactly the denial that
any alternative holds uniquely. -/
theorem forall_not_preExh_iff : (∀ i, ¬ preExh A i) ↔ ¬ ∃! i, A i := by
  rw [← exists_preExh_iff_existsUnique, not_exists]

/-- `strong` properly strengthens `weak`: it entails it, and excludes some
possibility `weak` leaves open. -/
def ProperlyStrengthens (strong weak : α → Prop) : Prop :=
  (∀ x, strong x → weak x) ∧ ∃ x, weak x ∧ ¬ strong x

/-- Vacuous exhaustification — the strengthened meaning coincides with the
prejacent — fails the proper-strengthening requirement. -/
theorem not_properlyStrengthens_of_iff {strong weak : α → Prop}
    (h : ∀ x, strong x ↔ weak x) : ¬ ProperlyStrengthens strong weak :=
  fun ⟨_, x, hw, hns⟩ => hns ((h x).mpr hw)

end Exhaustification
