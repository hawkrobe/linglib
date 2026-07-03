import Mathlib.Data.Set.Basic
import Linglib.Core.Order.SimilarityOrdering

/-!
# Conditional operators

[lewis-1973] [stalnaker-1968]

The basic conditional operators. A conditional operator sends an antecedent
and a consequent (propositions qua `Set W`) to the proposition expressed by
the conditional; rival theories differ in the carrier the operator is derived
from. Comparisons and non-entailments between operators are stated over this
shared signature.

## Main definitions

- `materialImp p q`: the truth-functional conditional; `w ∈ materialImp p q`
  iff `w ∈ p → w ∈ q`.
- `strictImp access p q`: the strict conditional over an accessibility map
  `access : I → Set W` (a modal base); `i ∈ strictImp access p q` iff
  `access i ∩ p ⊆ q`.
- `variablyStrictImp sim allWorlds p q`: the [stalnaker-1968] / [lewis-1973]
  variably strict conditional — vacuously true without antecedent worlds,
  otherwise some closest antecedent world settles the consequent.
- `conditionalPerfection p q`: the perfected ("only if") reading,
  `materialImp pᶜ qᶜ`.

## Main results

- `strictImp_anti_left`: antecedent strengthening — valid for the strict
  conditional, the signature property variably strict semantics rejects.
- `mem_strictImp_of_subset` / `not_subset_of_mem_strictImp`: a strict
  conditional whose consequent exhausts the domain is trivially true; a true
  non-trivial one has an antecedent that excludes a live world
  ([stalnaker-1975], [von-fintel-1999], [mizuno-2024]).
- `strict_implies_material` / `variably_strict_implies_material`: both modal
  operators refine the material conditional (under reflexivity / centering).
- `perfection_not_entailed` / `perfection_not_entailed_variablyStrict`:
  conditional perfection is not entailed, even variably strictly — it is a
  pragmatic inference ([grusdt-lassiter-franke-2022]).

The Kratzer restrictor conditional (necessity over a restricted
conversational background) lives in `Conditionals/Restrictor.lean`, which
bridges to `strictImp` via `conditionalNecessity_iff_mem_strictImp`.
-/

namespace Semantics.Conditionals

open Core.Order (SimilarityOrdering)

variable {I W : Type*} {access : I → Set W} {p p' q q' : Set W} {i : I} {w : W}

/-! ### Material conditional -/

/-- The material conditional: true wherever the antecedent fails or the
consequent holds (`pᶜ ∪ q`). Classical semantics keeps this literal meaning
and derives its apparent exceptions pragmatically
([grusdt-lassiter-franke-2022]). -/
def materialImp (p q : Set W) : Set W := {w | w ∈ p → w ∈ q}

@[simp]
theorem mem_materialImp : w ∈ materialImp p q ↔ (w ∈ p → w ∈ q) := Iff.rfl

/-- Contraposition, valid for the material conditional. [stalnaker-1975] (§4)
observes that it fails for indicative conditionals under his semantics — see
`Studies/Stalnaker1975`. -/
theorem contraposition : materialImp p q ⊆ materialImp qᶜ pᶜ :=
  λ _ h hq hp => hq (h hp)

/-! ### Strict conditional -/

/-- The strict conditional over an accessibility map: the consequent holds
throughout the accessible antecedent worlds, `access i ∩ p ⊆ q`. The
evaluation points `I` may differ from the worlds `W` quantified over — e.g. a
historical modal base `WorldTimeIndex W T → Set W` evaluates at world-time
indices ([condoravdi-2002]); the classical case is `I = W`. -/
def strictImp (access : I → Set W) (p q : Set W) : Set I :=
  {i | access i ∩ p ⊆ q}

@[simp]
theorem mem_strictImp : i ∈ strictImp access p q ↔ access i ∩ p ⊆ q := Iff.rfl

/-- The quantifier reading of the strict conditional. -/
theorem mem_strictImp_forall :
    i ∈ strictImp access p q ↔ ∀ w ∈ access i, w ∈ p → w ∈ q :=
  ⟨λ h _ hw hp => h ⟨hw, hp⟩, λ h w hw => h w hw.1 hw.2⟩

/-- The strict conditional is monotone in its consequent. -/
theorem strictImp_mono_right (hq : q ⊆ q') :
    strictImp access p q ⊆ strictImp access p q' :=
  λ _ h => h.trans hq

/-- **Antecedent strengthening**: the strict conditional is antitone in its
antecedent — the signature property of strict (and material) conditionals
that variably strict semantics rejects ([lewis-1973] Sobel sequences). -/
theorem strictImp_anti_left (hp : p' ⊆ p) :
    strictImp access p q ⊆ strictImp access p' q :=
  λ _ h => (Set.inter_subset_inter (Set.Subset.refl _) hp).trans h

/-- **Triviality**: when the consequent already holds throughout the
accessible worlds, the strict conditional holds for *any* antecedent — the
if-clause does no work ([stalnaker-1975], [von-fintel-1999]; the
Anderson-conditional application is [mizuno-2024] §2). -/
theorem mem_strictImp_of_subset (h : access i ⊆ q) :
    i ∈ strictImp access p q :=
  Set.inter_subset_left.trans h

/-- **Informativity**: a true strict conditional whose consequent is *not*
trivial over the accessible worlds has an antecedent that excludes at least
one accessible world (`Set.not_subset` gives the witness form)
([mizuno-2024] §2). -/
theorem not_subset_of_mem_strictImp
    (hm : i ∈ strictImp access p q) (hq : ¬ access i ⊆ q) :
    ¬ access i ⊆ p :=
  λ hp => hq (λ _ hw => hm ⟨hw, hp hw⟩)

/-- With reflexive access, the strict conditional refines the material one. -/
theorem strict_implies_material {R : W → Set W} (h_refl : w ∈ R w)
    (h : w ∈ strictImp R p q) : w ∈ materialImp p q :=
  λ hp => h ⟨h_refl, hp⟩

/-! ### Variably strict conditional -/

/-- The variably strict conditional ([stalnaker-1968] / [lewis-1973]):
vacuously true if the domain has no antecedent worlds; otherwise true iff
some antecedent world settles the consequent throughout all antecedent
worlds at least as close. (`SimilarityOrdering` and its constructors live in
`Core.Order.SimilarityOrdering`.) -/
def variablyStrictImp (sim : SimilarityOrdering W) (allWorlds p q : Set W) :
    Set W :=
  {w | allWorlds ∩ p = ∅ ∨
    ∃ w' ∈ allWorlds ∩ p, ∀ w'' ∈ allWorlds ∩ p, sim.closer w w'' w' → w'' ∈ q}

@[simp]
theorem mem_variablyStrictImp {sim : SimilarityOrdering W} {allWorlds : Set W} :
    w ∈ variablyStrictImp sim allWorlds p q ↔
      allWorlds ∩ p = ∅ ∨
        ∃ w' ∈ allWorlds ∩ p, ∀ w'' ∈ allWorlds ∩ p,
          sim.closer w w'' w' → w'' ∈ q :=
  Iff.rfl

/-- With centered similarity, the variably strict conditional refines the
material one at antecedent worlds: `w` is its own unique closest antecedent
world, so the consequent must hold there. -/
theorem variably_strict_implies_material {sim : SimilarityOrdering W}
    {allWorlds : Set W} (hw : w ∈ allWorlds) (hp : w ∈ p)
    (h_centered : sim.isCentered)
    (h : w ∈ variablyStrictImp sim allWorlds p q) : w ∈ materialImp p q := by
  intro _
  rcases h with h_empty | ⟨w', _, h_close⟩
  · exact absurd h_empty (Set.nonempty_iff_ne_empty.mp ⟨w, hw, hp⟩)
  · rcases eq_or_ne w w' with rfl | h_ne
    · exact h_close w ⟨hw, hp⟩ (sim.closer_refl w w)
    · exact h_close w ⟨hw, hp⟩ (h_centered w w' h_ne).1

/-! ### Conditional perfection -/

/-- Conditional perfection: the strengthened converse reading of a
conditional ("if not A, not C"), as `materialImp pᶜ qᶜ`. Observed
pragmatically but not entailed (`perfection_not_entailed`);
[grusdt-lassiter-franke-2022] derive it as an RSA implicature. -/
def conditionalPerfection (p q : Set W) : Set W := materialImp pᶜ qᶜ

/-- Conditional perfection is not entailed: the material conditional can
hold (vacuously, at an antecedent-false world) where its perfection fails. -/
theorem perfection_not_entailed :
    ∃ (W : Type) (p q : Set W) (w : W),
      w ∈ materialImp p q ∧ w ∉ conditionalPerfection p q :=
  ⟨Bool, {w | w = true}, Set.univ, false, λ _ => trivial,
    λ h => h Bool.false_ne_true trivial⟩

/-- Perfection is not entailed even variably strictly: the
[stalnaker-1968] / [lewis-1973] semantics is stronger than material
implication, yet still does not entail the converse. -/
theorem perfection_not_entailed_variablyStrict :
    ∃ (W : Type) (sim : SimilarityOrdering W) (domain p q : Set W) (w : W),
      w ∈ variablyStrictImp sim domain p q ∧ w ∉ conditionalPerfection p q :=
  ⟨Bool,
    ⟨λ _ => Preorder.ofLE (λ _ _ => True) (λ _ => trivial)
      (λ _ _ _ _ _ => trivial), λ _ _ _ => .isTrue trivial⟩,
    Set.univ, {w | w = true}, Set.univ, false,
    Or.inr ⟨true, ⟨Set.mem_univ _, rfl⟩, λ _ _ _ => trivial⟩,
    λ h => h Bool.false_ne_true trivial⟩

end Semantics.Conditionals
