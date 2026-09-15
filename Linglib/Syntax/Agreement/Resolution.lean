import Mathlib.Tactic.DeriveFintype
import Mathlib.Basic.Logic.Basic

/-!
# Resolution rules

This file defines resolution rules, which give the agreement form of a coordination from
its conjuncts, and their application in order.

A resolution rule has one of two shapes: at least one conjunct meets a condition, or every
conjunct does, and the rule then selects a form. A language's rules are ordered, the first
that applies selects the form, and a coordination to which no rule applies has no resolved
form, an ineffable coordination. The final rule is often unconditional, an "otherwise"
clause, and then every coordination has a form. The condition may read the conjuncts' feature
values, a syntactic rule, or their meanings, a semantic rule; the descriptor type is a
parameter.

## Main definitions

* `Agreement.ResolutionRule`: a rule, with its quantifier, its condition on a conjunct and
  the form it selects.
* `Agreement.ResolutionRule.Applies`: whether a rule applies to a list of conjuncts.
* `Agreement.ResolutionRule.resolve`: the form the first applicable rule of an ordered list
  selects.

## Main results

* `Agreement.ResolutionRule.resolve_otherwise_isSome`: rules ending in an unconditional
  rule resolve every coordination.

## References

* [corbett-1991] — chapter 9
* [givon-1970] — the resolution of gender conflicts in Bantu
* [corbett-2006] — the standard monograph on agreement
-/

namespace Agreement

/-- The two shapes of a resolution rule: at least one conjunct meets the condition, or every
conjunct does. -/
inductive ResolutionRule.Quantifier where
  | any
  | all
  deriving DecidableEq, Repr, Fintype

/-- A resolution rule: a condition on conjuncts, quantified one way or the other, and the
form it selects. -/
structure ResolutionRule (α G : Type*) where
  /-- Whether one conjunct or every conjunct must meet the condition. -/
  quant : ResolutionRule.Quantifier
  /-- The condition on a conjunct. -/
  pred : α → Prop
  [dec : DecidablePred pred]
  /-- The form the rule selects. -/
  out : G

attribute [instance] ResolutionRule.dec

namespace ResolutionRule

variable {α G : Type*}

/-- Whether the rule applies to a coordination. -/
def Applies (r : ResolutionRule α G) (cs : List α) : Prop :=
  match r.quant with
  | .any => ∃ c ∈ cs, r.pred c
  | .all => ∀ c ∈ cs, r.pred c

instance (r : ResolutionRule α G) (cs : List α) : Decidable (r.Applies cs) := by
  unfold Applies; cases r.quant <;> infer_instance

/-- The unconditional final rule. -/
def otherwise (g : G) : ResolutionRule α G := ⟨.all, λ _ => True, g⟩

theorem otherwise_applies (g : G) (cs : List α) : (otherwise g).Applies cs := λ _ _ => trivial

/-- Apply ordered rules: the first that applies selects the form; none applying, the
coordination has no resolved form. -/
def resolve : List (ResolutionRule α G) → List α → Option G
  | [], _ => none
  | r :: rs, cs => if r.Applies cs then some r.out else resolve rs cs

variable (r : ResolutionRule α G) (rs : List (ResolutionRule α G)) (cs : List α)

@[simp] theorem resolve_nil : resolve ([] : List (ResolutionRule α G)) cs = none := rfl

theorem resolve_cons_of_applies (h : r.Applies cs) : resolve (r :: rs) cs = some r.out := by
  simp [resolve, h]

theorem resolve_cons_of_not_applies (h : ¬ r.Applies cs) :
    resolve (r :: rs) cs = resolve rs cs := by
  simp [resolve, h]

/-- Rules ending in an unconditional rule resolve every coordination. -/
theorem resolve_otherwise_isSome (g : G) : (resolve (rs ++ [otherwise g]) cs).isSome := by
  induction rs with
  | nil => simp [resolve, otherwise_applies]
  | cons r rs ih => by_cases h : r.Applies cs <;> simp [resolve, h, ih]

end ResolutionRule

end Agreement
