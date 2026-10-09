module

public import Linglib.Morphology.DistributedMorphology.Neighborhood
public import Mathlib.Data.Multiset.AddSub

/-!
# Impoverishment

Impoverishment deletes features from a terminal before Vocabulary Insertion, the Distributed
Morphology mechanism for syncretism: a context that loses a distinguishing feature falls together
with its neighbor, and insertion retreats to the more general exponent (`winner?_retreat`). A rule
is evaluated at a `Neighborhood`, the focus terminal with the terminals beside it, so whether a
rule is paradigmatic, its condition reading the focus alone, is a theorem about the rule. On a
list bundle a rule erases one occurrence of its target, subtraction in the free commutative monoid
on the features that `DistributedMorphology/Fission.lean` decomposes.

## Main definitions

* `ImpoverishmentRule`: a decidable condition on a neighborhood and the target it deletes;
  `ImpoverishmentRule.apply` takes the deletion as a parameter.
* `ImpoverishmentRule.ofFocus`: the rule whose condition reads the focus alone.
* `ImpoverishmentRule.Paradigmatic`, `ImpoverishmentRule.Syntagmatic`: the condition factors
  through the focus, or reads the context.
* `runChain`: a rule sequence threaded through the focus.

## Main results

* `ImpoverishmentRule.paradigmatic_ofFocus`: a focus-only rule is paradigmatic.
* `ImpoverishmentRule.coe_apply_erase`, `ImpoverishmentRule.apply_erase_sublist`: on a list
  bundle a rule erases one occurrence of its target, so impoverishment only deletes.

## Implementation notes

The deletion is a parameter of `apply`, not of the rule, since a rule system shares it;
`Studies/Middleton2026.lean` deletes from the slots of the Taos agreement prefix. On the tree
carrier, impoverishment derives from fission and the coproduct
(`Studies/SenturiaMarcolli2025.lean`).

## References

* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

variable {Bundle Target : Type*}

/-- An Impoverishment rule deletes `target` from the focus of a neighborhood satisfying its
decidable `condition`. -/
structure ImpoverishmentRule (Bundle Target : Type*) where
  /-- The neighborhoods at which the rule fires. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]
  /-- The feature the rule deletes from the focus. -/
  target : Target

namespace ImpoverishmentRule

instance (rule : ImpoverishmentRule Bundle Target) : DecidablePred rule.condition := rule.decCond

/-- With the deletion `delete`, a rule removes its target from the focus where its condition
holds, and otherwise leaves the focus as it is. -/
def apply (delete : Bundle → Target → Bundle) (rule : ImpoverishmentRule Bundle Target)
    (n : Neighborhood Bundle) : Bundle :=
  if rule.condition n then delete n.focus rule.target else n.focus

/-- `ofFocus p target` deletes `target` wherever the focus satisfies `p`. -/
def ofFocus (p : Bundle → Prop) [DecidablePred p] (target : Target) :
    ImpoverishmentRule Bundle Target :=
  ⟨fun n ↦ p n.focus, target⟩

/-! ### Paradigmatic and syntagmatic rules

The structural counterpart of [arregi-nevins-2012]'s distinction between rules conditioned by a
single node and rules conditioned by its surroundings. -/

/-- A rule is **paradigmatic** iff its condition factors through the focus, two neighborhoods
with the same focus agreeing on it. -/
def Paradigmatic (r : ImpoverishmentRule Bundle Target) : Prop :=
  ∀ n₁ n₂ : Neighborhood Bundle, n₁.focus = n₂.focus → (r.condition n₁ ↔ r.condition n₂)

/-- A rule is **syntagmatic** iff it is not paradigmatic, so that its condition reads the
context. -/
def Syntagmatic (r : ImpoverishmentRule Bundle Target) : Prop := ¬ r.Paradigmatic

theorem paradigmatic_ofFocus (p : Bundle → Prop) [DecidablePred p] (target : Target) :
    (ofFocus p target).Paradigmatic := fun _ _ h ↦ by simp [ofFocus, h]

/-! ### List bundles -/

/-- Impoverishment only deletes. On a list bundle, erasing the target leaves a sublist of the
focus. -/
theorem apply_erase_sublist {α : Type*} [BEq α] (rule : ImpoverishmentRule (List α) α)
    (n : Neighborhood (List α)) : (rule.apply List.erase n).Sublist n.focus := by
  unfold apply
  split
  · exact List.erase_sublist
  · exact .refl _

/-- In the free commutative monoid on the features, a rule erases one occurrence of its target
from the focus where its condition holds. -/
theorem coe_apply_erase {α : Type*} [DecidableEq α] (rule : ImpoverishmentRule (List α) α)
    (n : Neighborhood (List α)) :
    (↑(rule.apply List.erase n) : Multiset α) =
      if rule.condition n then (n.focus : Multiset α).erase rule.target else n.focus := by
  unfold apply
  split <;> simp

end ImpoverishmentRule

/-! ### Rule chains -/

/-- A chain applies a list of rules to a neighborhood, threading the focus through each step while
holding the context fixed. -/
def runChain {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rules : List R) (n : Neighborhood Bundle) : Bundle :=
  rules.foldl (init := n.focus) fun focus rule ↦ apply rule { n with focus }

/-- Concatenated chains run sequentially, the second chain starting where the first left off. -/
theorem runChain_append {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rs₁ rs₂ : List R) (n : Neighborhood Bundle) :
    runChain apply (rs₁ ++ rs₂) n =
      runChain apply rs₂ { n with focus := runChain apply rs₁ n } := by
  simp only [runChain, List.foldl_append]

/-- The empty chain is the identity on the focus. -/
@[simp] theorem runChain_nil {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (n : Neighborhood Bundle) : runChain apply [] n = n.focus := rfl

end DistributedMorphology
