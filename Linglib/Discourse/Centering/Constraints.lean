import Linglib.Discourse.Centering.Basic
/-!
# Centering Theory — Constraint 1
@cite{poesio-stevenson-eugenio-hitzeman-2004} @cite{grosz-joshi-weinstein-1995}
PSDH §5.3.2's decomposition of GJW's Constraint 1 into CB Uniqueness
(at most one CB) and Entity Continuity (at least one CB). Strong C1 =
their conjunction (exactly one CB).
-/
set_option autoImplicit false
namespace Discourse.Centering
variable {E R : Type}
/-! ### CB Uniqueness, Entity Continuity, Strong C1 -/
/-- CB Uniqueness: the utterance pair has at most one CB. -/
def CBUniqueness [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length ≤ 1
/-- Entity Continuity: the utterance pair shares at least one CF entity. -/
def EntityContinuity [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length ≥ 1
/-- Strong Constraint 1: exactly one CB (Uniqueness ∧ Continuity). -/
def Constraint1Strong [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  (cbAll prev cur).length = 1
/-! ### Decidability -/
instance CBUniqueness.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (CBUniqueness prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length ≤ 1))
instance EntityContinuity.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (EntityContinuity prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length ≥ 1))
instance Constraint1Strong.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] (prev : Utterance E R) (cur : U) :
    Decidable (Constraint1Strong prev cur) :=
  inferInstanceAs (Decidable ((cbAll prev cur).length = 1))
/-! ### PSDH §5.3.2 decomposition theorem -/
/-- PSDH §5.3.2 decomposition: Strong C1 ↔ CB Uniqueness ∧ Continuity. -/
theorem strongC1_iff_uniqueness_and_continuity
    [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) :
    Constraint1Strong prev cur ↔ CBUniqueness prev cur ∧ EntityContinuity prev cur := by
  unfold Constraint1Strong CBUniqueness EntityContinuity
  omega
/-- Strong implies Weak: a unique CB implies at most one CB. -/
theorem strong_implies_uniqueness [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] {prev : Utterance E R} {cur : U}
    (h : Constraint1Strong prev cur) : CBUniqueness prev cur := by
  unfold Constraint1Strong at h
  unfold CBUniqueness
  omega
end Discourse.Centering
