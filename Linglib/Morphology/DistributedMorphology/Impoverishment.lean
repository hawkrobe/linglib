import Linglib.Syntax.Minimalist.Features

/-!
# Impoverishment

Impoverishment deletes features from a terminal before Vocabulary
Insertion — the Distributed Morphology mechanism for syncretism: a
context that loses a distinguishing feature falls together with its
neighbor at VI, forcing retreat to the more general exponent. A rule is
evaluated against a `Neighborhood` — the focus terminal plus its
adjacent terminals — and the focus/context split makes the
paradigmatic/syntagmatic distinction structural: a rule whose condition
factors through the focus is paradigmatic as a theorem about the rule,
not an annotation. Deletion only removes: every dimension of the output
is the input's value or absent (`chain_pointwise`), which is what makes
the post-impoverishment VI winner the retreat-to-the-general exponent
(`winner?_retreat`).

## Main definitions

* `Neighborhood` — the local context a postsyntactic rule inspects
* `ImpoverishmentRule` — a conditioned feature deletion, parametric in
  the bundle and target types; `ImpoverishmentRule.apply` instantiates
  it with a deletion operation
* `ImpoverishmentRule.Paradigmatic`, `ImpoverishmentRule.Syntagmatic` —
  condition factors through the focus, or genuinely reads context
* `deleteFeature`, `chain` — the Minimalist-bundle instantiation and
  its rule chains

## Main statements

* `ImpoverishmentRule.paradigmatic_isParadigmatic` — rules built focus-only
  are paradigmatic by construction
* `chain_pointwise` — impoverishment only deletes: chains never
  introduce or alter feature values
* `runChain_append` — chains compose sequentially (the ground for the
  strict-vs-interleaved equivalence in `Middleton2026`)

## Implementation notes

The rule is parametric so that non-Minimalist bundle types (a future
DM `Terminal`) instantiate it; the deletion operation is a parameter of
`apply`, not of the rule, since it is shared across a rule system.
`Middleton2026`'s `MetathesisRule` follows the same template with a
different rewrite. On the tree carrier, impoverishment is derivable
from fission and the coproduct (`Studies/SenturiaMarcolli2025.lean`).

## References

* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [G. Scott, *Pronoun reduction in Mam*][scott-2023]
-/

namespace DistributedMorphology

open Minimalist

/-! ### Neighborhoods -/

/-- The local context a postsyntactic rule may inspect. The `focus`
bundle is the terminal targeted for rewriting; `leftCtx` and `rightCtx`
are the surrounding terminals, nearest first. The zipper view of a
whole spell-out domain is `Spellout.lean`'s `mapNeighborhoods`.

Splitting `focus` from context makes the paradigmatic/syntagmatic
distinction structural: a condition that only inspects `focus` is
paradigmatic by construction; one that reads `leftCtx` or `rightCtx` is
syntagmatic. -/
structure Neighborhood (Bundle : Type*) where
  focus    : Bundle
  leftCtx  : List Bundle := []
  rightCtx : List Bundle := []
  deriving Repr

/-- A bundle, viewed as a context-free neighborhood. -/
def Neighborhood.ofBundle {Bundle : Type*} (fb : Bundle) : Neighborhood Bundle :=
  { focus := fb }

/-! ### Impoverishment rules -/

variable {Bundle Target : Type*}

/-- An Impoverishment rule: delete `target` from the focus terminal when
`condition` holds over the neighborhood. The condition is `Prop`-valued
with a `DecidablePred` witness carried alongside, so applications reduce
by `decide` on concrete inputs; the deletion operation itself is
supplied to `ImpoverishmentRule.apply`. -/
structure ImpoverishmentRule (Bundle Target : Type*) where
  /-- Does this rule apply at the given neighborhood? -/
  condition : Neighborhood Bundle → Prop
  /-- Decidability witness, exposed as an instance (see below). -/
  decCond : DecidablePred condition
  /-- What is deleted from the focus bundle. -/
  target : Target

/-- Expose the rule's decidability as an instance so that
`if rule.condition n then ... else ...` elaborates. -/
instance (rule : ImpoverishmentRule Bundle Target) (n : Neighborhood Bundle) :
    Decidable (rule.condition n) := rule.decCond n

/-- Apply a rule at a neighborhood, deleting with `delete`: when the
condition holds, the focus loses the target; otherwise it is
unchanged. -/
def ImpoverishmentRule.apply (delete : Bundle → Target → Bundle)
    (rule : ImpoverishmentRule Bundle Target) (n : Neighborhood Bundle) : Bundle :=
  if rule.condition n then delete n.focus rule.target else n.focus

/-! ### Paradigmatic and syntagmatic rules

The structural counterpart of [arregi-nevins-2012]'s distinction
between rules conditioned by a single node and rules conditioned by the
node's surroundings — a theorem about a rule, not a flag. -/

/-- A rule is **paradigmatic** iff its condition factors through the
focus bundle: any two neighborhoods with the same focus agree on the
condition. -/
def ImpoverishmentRule.Paradigmatic (r : ImpoverishmentRule Bundle Target) : Prop :=
  ∀ n₁ n₂ : Neighborhood Bundle,
    n₁.focus = n₂.focus → (r.condition n₁ ↔ r.condition n₂)

/-- A rule is **syntagmatic** iff it is not paradigmatic: some
neighborhoods agree on focus but disagree on the condition, so the
condition genuinely depends on context. -/
def ImpoverishmentRule.Syntagmatic (r : ImpoverishmentRule Bundle Target) : Prop :=
  ¬ r.Paradigmatic

/-- Build a paradigmatic rule from a focus-only Boolean check; the
`Paradigmatic` proof is `paradigmatic_isParadigmatic`. -/
def ImpoverishmentRule.paradigmatic (focusCheck : Bundle → Bool) (target : Target) :
    ImpoverishmentRule Bundle Target where
  condition n := focusCheck n.focus = true
  decCond n := inferInstanceAs (Decidable (focusCheck n.focus = true))
  target := target

/-- A rule built by `paradigmatic` is paradigmatic by construction. -/
theorem ImpoverishmentRule.paradigmatic_isParadigmatic (focusCheck : Bundle → Bool)
    (target : Target) : (ImpoverishmentRule.paradigmatic focusCheck target).Paradigmatic := by
  intro n₁ n₂ hfoc
  simp only [ImpoverishmentRule.paradigmatic, hfoc]

/-- Build a (potentially) syntagmatic rule from a full-neighborhood
Boolean check. Whether the result is genuinely syntagmatic depends on
`cond` — verify with a separate `Syntagmatic` proof if needed. -/
def ImpoverishmentRule.syntagmatic (cond : Neighborhood Bundle → Bool) (target : Target) :
    ImpoverishmentRule Bundle Target where
  condition n := cond n = true
  decCond n := inferInstanceAs (Decidable (cond n = true))
  target := target

/-! ### Rule chains -/

/-- Generic postsyntactic chain: apply a list of rules to a
neighborhood, threading the *focus* bundle through each step while
holding the surrounding context fixed. One cycle of Impoverishment and
one cycle of Metathesis (`Middleton2026`) share this shape. -/
def runChain {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rules : List R) (n : Neighborhood Bundle) : Bundle :=
  rules.foldl (init := n.focus)
    (λ focusAcc rule => apply rule { n with focus := focusAcc })

/-- Concatenated chains run sequentially: the second chain starts where
the first left off. This underwrites the strict-vs-interleaved
equivalence (`Middleton2026.runStrict_eq_interleaved_paraSyn`). -/
theorem runChain_append {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rs₁ rs₂ : List R) (n : Neighborhood Bundle) :
    runChain apply (rs₁ ++ rs₂) n =
      runChain apply rs₂ { n with focus := runChain apply rs₁ n } := by
  simp only [runChain, List.foldl_append]

/-- The empty chain is the identity on the focus. -/
@[simp] theorem runChain_nil {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (n : Neighborhood Bundle) : runChain apply [] n = n.focus := rfl

/-! ### The Minimalist-bundle instantiation

Deletion on `Minimalist.FeatureBundle` zeroes the target's dimension
slot. A rule whose focus might carry a different value of that
dimension should guard in its `condition`: deletion is by dimension,
not by value match. -/

/-- Delete the target's dimension from a bundle: set its slot to
`absent`. -/
def deleteFeature (fb : FeatureBundle) (target : FeatureVal) : FeatureBundle :=
  Function.update fb target.dimension .absent

/-- Apply an Impoverishment rule at a neighborhood of Minimalist
bundles. -/
def applyImpoverishment (rule : ImpoverishmentRule FeatureBundle FeatureVal)
    (n : Neighborhood FeatureBundle) : FeatureBundle :=
  rule.apply deleteFeature n

/-- Apply a sequence of impoverishment rules. Specializes `runChain`. -/
def applyImpoverishmentChain (rules : List (ImpoverishmentRule FeatureBundle FeatureVal))
    (n : Neighborhood FeatureBundle) : FeatureBundle :=
  runChain applyImpoverishment rules n

/-- `applyImpoverishmentChain` distributes over list concatenation. -/
theorem applyImpoverishmentChain_append
    (rs₁ rs₂ : List (ImpoverishmentRule FeatureBundle FeatureVal))
    (n : Neighborhood FeatureBundle) :
    applyImpoverishmentChain (rs₁ ++ rs₂) n =
      applyImpoverishmentChain rs₂
        { n with focus := applyImpoverishmentChain rs₁ n } :=
  runChain_append _ _ _ _

/-- Convenience: apply a rule to a bare focus bundle with no
surrounding context, for paradigmatic rules where context is
irrelevant. -/
def ImpoverishmentRule.applyToBundle
    (rule : ImpoverishmentRule FeatureBundle FeatureVal)
    (fb : FeatureBundle) : FeatureBundle :=
  applyImpoverishment rule (Neighborhood.ofBundle fb)

/-! ### Impoverishment only deletes

Each dimension of an impoverished bundle is the input's value or
absent: rules and chains never introduce or alter feature content —
the monotone destructiveness that forces retreat to the more general
exponent at VI. -/

/-- Deletion leaves every dimension as it was, or absent. -/
theorem deleteFeature_pointwise (fb : FeatureBundle) (target : FeatureVal)
    (d : FeatureType) :
    deleteFeature fb target d = fb d ∨ deleteFeature fb target d = .absent := by
  by_cases h : d = target.dimension
  · subst h; right; simp [deleteFeature]
  · left; simp [deleteFeature, Function.update_of_ne h]

/-- One rule application leaves every dimension as it was, or absent. -/
theorem applyImpoverishment_pointwise
    (rule : ImpoverishmentRule FeatureBundle FeatureVal)
    (n : Neighborhood FeatureBundle) (d : FeatureType) :
    applyImpoverishment rule n d = n.focus d
      ∨ applyImpoverishment rule n d = .absent := by
  unfold applyImpoverishment ImpoverishmentRule.apply
  split
  · exact deleteFeature_pointwise n.focus rule.target d
  · exact .inl rfl

/-- A chain leaves every dimension as it was, or absent. -/
theorem chain_pointwise (rules : List (ImpoverishmentRule FeatureBundle FeatureVal))
    (n : Neighborhood FeatureBundle) (d : FeatureType) :
    applyImpoverishmentChain rules n d = n.focus d
      ∨ applyImpoverishmentChain rules n d = .absent := by
  induction rules generalizing n with
  | nil => exact .inl rfl
  | cons r rs ih =>
    have hstep := applyImpoverishment_pointwise r n d
    have htail := ih { n with focus := applyImpoverishment r n }
    rcases htail with h | h <;> rw [applyImpoverishmentChain] at h ⊢ <;>
      simp only [runChain, List.foldl_cons] at h ⊢
    · rcases hstep with h' | h'
      · exact .inl (h.trans h')
      · exact .inr (h.trans h')
    · exact .inr h

/-- Deleting a feature twice is deleting it once. -/
theorem deleteFeature_idempotent (fb : FeatureBundle) (target : FeatureVal) :
    deleteFeature (deleteFeature fb target) target = deleteFeature fb target := by
  simp only [deleteFeature, Function.update_idem]

/-! ### Redundancy-based impoverishment -/

/-- A feature is redundant when it is recoverable from another source,
such as agreement morphology on the verb. This is the mechanism
underlying pronoun reduction in Mam ([scott-2023]): when all features
of the pronominal base are also expressed by agreement, the base is
deleted at PF. -/
def allRecoverable (recoverable pronFeatures : List FeatureVal) : Bool :=
  pronFeatures.all (λ f => recoverable.any (f.sameType ·))

/-- Build a redundancy-based Impoverishment rule. The condition only
inspects the focus bundle, so the rule is paradigmatic by
construction. -/
def redundancyRule (source : List FeatureVal) (target : FeatureVal) :
    ImpoverishmentRule FeatureBundle FeatureVal :=
  .paradigmatic
    (λ fb => allRecoverable source
      ((FeatureBundle.toGramFeatures fb).map GramFeature.featureType))
    target

/-- Redundancy rules are paradigmatic. -/
theorem redundancyRule_isParadigmatic (source : List FeatureVal)
    (target : FeatureVal) : (redundancyRule source target).Paradigmatic :=
  ImpoverishmentRule.paradigmatic_isParadigmatic _ _

end DistributedMorphology
