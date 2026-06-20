import Linglib.Core.Optimization.Evaluation

/-!
# OT-named aliases for `Core.Optimization.Evaluation` primitives

The Core decls use neutral CS/ML naming: `LexMinProblem`,
`Lex (Fin n → Nat)`, `lexFinNatOf`, `lexFinNat_le_apply_zero`.

The OT-tradition names — `Tableau`, `ViolationProfile`, `t.optimal`,
`t.IsOptimal`, `buildViolationProfile` — are re-exported here as type
aliases / abbrevs so downstream OT code can keep its idiomatic
vocabulary without any change.

Any Phonology file using OT-tradition names should import this module
(rather than `Core.Optimization.Evaluation` directly).
-/

namespace Constraint

open Core.Optimization.Evaluation

/-- OT-named alias for `Lex (Fin n → Nat)` — fixed-length violation profile. -/
abbrev ViolationProfile (n : Nat) := Lex (Fin n → Nat)

/-- OT-named alias for `LexMinProblem`. -/
abbrev Tableau (C : Type*) [DecidableEq C] (n : Nat) := LexMinProblem C n

/-- OT-named alias for `LexMinProblem.IsLexMin`. -/
abbrev Tableau.IsOptimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) : Prop :=
  LexMinProblem.IsLexMin t c

/-- OT-named alias for `LexMinProblem.lexMins`. -/
abbrev Tableau.optimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : Finset C :=
  LexMinProblem.lexMins t

/-- OT-named alias for `LexMinProblem.exists_lexMin`. -/
theorem Tableau.exists_optimal {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : ∃ c, t.IsOptimal c :=
  LexMinProblem.exists_lexMin t

/-- OT-named alias for `LexMinProblem.mem_lexMins_iff`. -/
theorem Tableau.mem_optimal_iff {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c :=
  LexMinProblem.mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem Tableau.optimal_nonempty {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : t.optimal.Nonempty :=
  LexMinProblem.lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem Tableau.optimal_subset {C : Type*} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    c ∈ t.optimal → c ∈ t.candidates :=
  LexMinProblem.lexMins_subset t c

/-- OT-named alias for `lexFinNatOf`. -/
abbrev buildViolationProfile {C : Type*} {n : Nat}
    (constraints : Fin n → C → Nat) (c : C) : ViolationProfile n :=
  lexFinNatOf constraints c

/-- OT-named alias for `lexFinNat_le_apply_zero` (first-component
    extraction lemma). -/
theorem ViolationProfile.le_apply_zero {n : Nat}
    {a b : ViolationProfile (n + 1)} (h : a ≤ b) : a 0 ≤ b 0 :=
  Core.Optimization.Evaluation.lexFinNat_le_apply_zero h

end Constraint
