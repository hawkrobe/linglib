import Linglib.Discourse.Centering.Basic
/-!
# Centering Theory — Rule 1 (Pronominalization Constraint)
@cite{grosz-joshi-weinstein-1995} @cite{gordon-grosz-gilliom-1993}
@cite{poesio-stevenson-eugenio-hitzeman-2004}
Three variants of Rule 1, each making a different empirical claim:
GJW 95 (conditional on any pronominalization), GJW 83 (conditional
on CB stability), Gordon (unconditional). Each is its own predicate
with implication theorems where they hold.
-/
set_option autoImplicit false
namespace Discourse.Centering
variable {E R : Type}
/-! ### Rule 1 (GJW 1995) — the standard formulation -/
/-- Rule 1 (GJW 95): if any element of `Cf(U_{i-1})` is pronominalized
    in `U_i`, then `Cb(U_i)` is pronominalized too. Vacuously satisfied
    when no Cb exists. -/
def Rule1GJW95 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    (∃ e ∈ prev.cf, pronominalizes cur e) → pronominalizes cur curCb
instance Rule1GJW95.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) :
    Decidable (Rule1GJW95 prev cur) := by
  unfold Rule1GJW95
  cases cb prev cur <;> infer_instance
/-! ### Rule 1 (GJW 1983) — conditional on CB stability -/
/-- Rule 1 (GJW 83): if the current CB equals the previous CB, use a
    pronoun. Conditional on CB stability; `prevCb` is an explicit
    parameter. -/
def Rule1GJW83 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) (prevCb : Option E) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    if prevCb = some curCb then pronominalizes cur curCb else True
instance Rule1GJW83.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) (prevCb : Option E) :
    Decidable (Rule1GJW83 prev cur prevCb) := by
  unfold Rule1GJW83
  cases cb prev cur <;> infer_instance
/-! ### Rule 1 (Gordon, Grosz, Gilliom 1993) — unconditional -/
/-- Rule 1 (Gordon, motivated by the repeated-name penalty,
    @cite{gordon-grosz-gilliom-1993}): the CB must always be
    pronominalized. Unconditional on what else is pronominalized. -/
def Rule1Gordon [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb => pronominalizes cur curCb
instance Rule1Gordon.decidable [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) :
    Decidable (Rule1Gordon prev cur) := by
  unfold Rule1Gordon
  cases cb prev cur <;> infer_instance
/-! ### Implication theorems -/
/-- Gordon ⇒ GJW 95: unconditional CB pronominalization implies the
    conditional version. One-directional (GJW 95 is vacuously true
    when no pronouns appear). -/
theorem Rule1Gordon_implies_GJW95 [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    {prev : Utterance E R} {cur : U}
    (h : Rule1Gordon prev cur) : Rule1GJW95 prev cur := by
  unfold Rule1Gordon at h
  unfold Rule1GJW95
  cases hcb : cb prev cur with
  | none => trivial
  | some curCb =>
    rw [hcb] at h
    intro _
    exact h
end Discourse.Centering
