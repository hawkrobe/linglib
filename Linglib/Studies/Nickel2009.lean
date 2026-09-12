import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Quantification.Generic
import Linglib.Studies.Cohen1999

/-!
# Nickel (2009): Generics and the Ways of Normality

This file formalizes the argument of [nickel-2009] from conjunctive generics against
majority-based accounts of the generic operator. *Elephants live in Africa and Asia* is
sentential conjunction, *elephants live in Africa and elephants live in Asia*, and is true
although no majority of elephants lives in either place, so the probabilistic operator of
[cohen-1999a] predicts it false (`cohen_fails_elephant_asia`). Normality comes in ways: a
characterizing sentence is true when there is a way of being normal in the respect the
predicate determines such that every individual normal in that way satisfies the predicate
(`nickelGEN`), so each conjunct of a conjunctive generic may draw on its own way
(`nickelConjunctiveGEN`, `nickel_handles_elephant_conjunction`,
`bears_nickel_succeeds`), and the ways are incompatible without the conjunction entailing
that anything lives in both places (`ways_incompatible`).

## Implementation notes

The ways are indices selecting the individuals that count as normal, the actual-extension
proxy for the paper's respects of normality and its inductive targets; the counterfactual
element the paper notes it needs when no individual is normal in a way is not represented,
so the operator holds vacuously in that case. The comparison with Cohen's operator runs
over one shared toy model, with the habitats as the alternative set.

## References

* [nickel-2009]
* [cohen-1999a]
-/

namespace Nickel2009

open Quantification (everyOn countOn thresholdGtOn)

/-! ### Ways of Being Normal -/

/-- A way of being normal — an index selecting which entities count as "normal"
    for a given generalization. Different generic claims can appeal to different
    normality ways. -/
structure NormalcyWay where
  id : Nat
  deriving DecidableEq, Repr

/-- An entity in the domain of a generic. -/
structure Entity where
  id : Nat
  deriving DecidableEq, Repr

/-! ### Nickel's GEN

GEN as `everyOn` (the relativized restricted universal) under an existential over
normality ways — `Quantification.everyOn` is the canonical generalized quantifier,
so the only Nickel-specific apparatus is the `∃`-over-ways wrapper. -/

/-- Nickel's GEN with way-indexed normality: there is a way of being normal such
    that every entity normal in that way (and satisfying the restrictor) satisfies
    the scope. The existential over ways lets different conjuncts of a conjunctive
    generic use different ways. -/
def nickelGEN {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    [∀ w, DecidablePred (λ e => normalIn e w)] : Prop :=
  ∃ w ∈ ways, everyOn entities (λ e => restrictor e ∧ normalIn e w) scope

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    [∀ w, DecidablePred (λ e => normalIn e w)] :
    Decidable (nickelGEN entities normalIn ways restrictor scope) := by
  unfold nickelGEN; infer_instance

/-- Conjunctive generic: both `GEN[A][F₁]` and `GEN[A][F₂]` hold, potentially via
    different normality ways. -/
def nickelConjunctiveGEN {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay)
    (restrictor scope1 scope2 : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope1] [DecidablePred scope2]
    [∀ w, DecidablePred (λ e => normalIn e w)] : Prop :=
  nickelGEN entities normalIn ways restrictor scope1 ∧
  nickelGEN entities normalIn ways restrictor scope2

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) (restrictor scope1 scope2 : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope1] [DecidablePred scope2]
    [∀ w, DecidablePred (λ e => normalIn e w)] :
    Decidable (nickelConjunctiveGEN entities normalIn ways restrictor scope1 scope2) := by
  unfold nickelConjunctiveGEN; infer_instance

/-- Normality ways are pairwise incompatible: no entity is normal in two distinct
    ways. The paper (p. 643) states this holds "usually (perhaps always)"; here it
    is a property of the toy model, not a commitment of the account. -/
def waysIncompatible {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay)
    [∀ w, DecidablePred (λ e => normalIn e w)] : Prop :=
  ∀ e ∈ entities, ∀ w₁ ∈ ways, ∀ w₂ ∈ ways,
    w₁ ≠ w₂ → ¬ (normalIn e w₁ ∧ normalIn e w₂)

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) [∀ w, DecidablePred (λ e => normalIn e w)] :
    Decidable (waysIncompatible entities normalIn ways) := by
  unfold waysIncompatible; infer_instance

/-! ### The Elephant Example (2b/11) -/

section Elephants

/-- 10 elephants: 6 African (ids 0–5), 4 Asian (ids 6–9). -/
def elephants : Finset Entity := ((List.range 10).map (λ n => (⟨n⟩ : Entity))).toFinset

abbrev isElephant : Entity → Prop := λ _ => True
abbrev livesInAfrica : Entity → Prop := λ e => e.id < 6
abbrev livesInAsia : Entity → Prop := λ e => e.id ≥ 6

def africanWay : NormalcyWay := ⟨1⟩
def asianWay : NormalcyWay := ⟨2⟩
def ways : Finset NormalcyWay := {africanWay, asianWay}

/-- Normal in the African way = African elephants; in the Asian way = Asian. -/
abbrev elephantNormalIn : Entity → NormalcyWay → Prop := λ e w =>
  (w.id = 1 ∧ e.id < 6) ∨ (w.id = 2 ∧ e.id ≥ 6)

end Elephants

/-! ### The Bears Example (2a) -/

section Bears

/-- 20 bears across 4 continents (5 each): NA 0–4, SA 5–9, EU 10–14, AS 15–19.
    The majority view fails for ALL four habitat conjuncts (each is 5/20 = 25%). -/
def bears : Finset Entity := ((List.range 20).map (λ n => (⟨n⟩ : Entity))).toFinset

abbrev isBear : Entity → Prop := λ _ => True
abbrev bearNA : Entity → Prop := λ e => e.id < 5
abbrev bearSA : Entity → Prop := λ e => e.id ≥ 5 ∧ e.id < 10
abbrev bearEU : Entity → Prop := λ e => e.id ≥ 10 ∧ e.id < 15
abbrev bearAS : Entity → Prop := λ e => e.id ≥ 15

/-- The disjunction of the habitat alternatives: every bear lives somewhere. -/
abbrev bearHabitat : Entity → Prop := λ e => bearNA e ∨ bearSA e ∨ bearEU e ∨ bearAS e

def bearWays : Finset NormalcyWay := {⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩}

abbrev bearNormalIn : Entity → NormalcyWay → Prop := λ e w =>
  (w.id = 1 ∧ e.id < 5) ∨ (w.id = 2 ∧ e.id ≥ 5 ∧ e.id < 10) ∨
  (w.id = 3 ∧ e.id ≥ 10 ∧ e.id < 15) ∨ (w.id = 4 ∧ e.id ≥ 15)

end Bears

/-! ### Key Theorems -/

/-- Nickel's view succeeds for the elephant conjunction: Africa is witnessed by the
    African way, Asia by the Asian way. -/
theorem nickel_handles_elephant_conjunction :
    nickelConjunctiveGEN elephants elephantNormalIn ways
      isElephant livesInAfrica livesInAsia := by decide

/-- The bears example (2a): Nickel's view succeeds for all four habitat conjuncts. -/
theorem bears_nickel_succeeds :
    nickelGEN bears bearNormalIn bearWays isBear bearNA ∧
    nickelGEN bears bearNormalIn bearWays isBear bearSA ∧
    nickelGEN bears bearNormalIn bearWays isBear bearEU ∧
    nickelGEN bears bearNormalIn bearWays isBear bearAS := by decide

/-- Normality ways are pairwise incompatible in both toy models. -/
theorem ways_incompatible :
    waysIncompatible elephants elephantNormalIn ways ∧
    waysIncompatible bears bearNormalIn bearWays := by decide

/-! ### The majority view fails where Nickel's succeeds

The headline contrast, a theorem over a **shared** model citing [cohen-1999a]'s
`gen` directly, with the habitats as the alternative set. The majority view fails
on the conjunction because the Asia conjunct has prevalence 4/10 < 1/2; Nickel's
view succeeds. Per the chronology rule this comparison lives in the later paper
(Nickel 2009 > Cohen 1999), which is the one that draws it. -/

/-- Cohen's majority GEN is false for "Elephants live in Asia" (prevalence 4/10). -/
theorem cohen_fails_elephant_asia :
    ¬ Cohen1999.gen elephants isElephant
      (λ e => livesInAfrica e ∨ livesInAsia e) livesInAsia := by
  rw [Cohen1999.gen_iff_thresholdGt _ _ _ _ (by decide)]
  decide

/-- **Cohen vs Nickel on the conjunctive generic, over one shared model.** The
    majority view fails (Asia is a minority habitat) while Nickel's way-indexed view
    succeeds — exactly the divergence Nickel's paper draws against Cohen. -/
theorem cohen_fails_nickel_succeeds_on_conjunction :
    ¬ Cohen1999.gen elephants isElephant
      (λ e => livesInAfrica e ∨ livesInAsia e) livesInAsia ∧
    nickelConjunctiveGEN elephants elephantNormalIn ways
      isElephant livesInAfrica livesInAsia := by
  refine ⟨cohen_fails_elephant_asia, ?_⟩
  decide

/-- The bears conjunction (2a) fails even harder for the majority view: every one of
    the four habitats is a 25% minority. -/
theorem cohen_fails_all_bear_habitats :
    ¬ Cohen1999.gen bears isBear bearHabitat bearNA ∧
    ¬ Cohen1999.gen bears isBear bearHabitat bearSA ∧
    ¬ Cohen1999.gen bears isBear bearHabitat bearEU ∧
    ¬ Cohen1999.gen bears isBear bearHabitat bearAS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [Cohen1999.gen_iff_thresholdGt _ _ _ _ (by decide)]; decide

/-! ### Connection to Traditional GEN -/

/-- Nickel's GEN with a single normality way reduces to the relativized restricted
    universal `everyOn` (traditional GEN): the way-existential is trivial, leaving
    `∀ x. (restrictor(x) ∧ normalIn(x, w)) → scope(x)`. -/
theorem nickel_single_way_is_everyOn {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (w : NormalcyWay)
    (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    [∀ w, DecidablePred (λ e => normalIn e w)] :
    nickelGEN entities normalIn {w} restrictor scope ↔
      everyOn entities (λ e => restrictor e ∧ normalIn e w) scope := by
  simp [nickelGEN]

/-! ### Generic-quantifier interface -/

/-- Nickel's `nickelGEN` over the whole carrier is exactly the ways-of-normality
    generalized quantifier `Quantification.genWays` — its `GQ`-interface form,
    the [nickel-2009] instance of the shared schema in `Quantification.Generic`. -/
theorem nickelGEN_univ_eq_genWays {α : Type*} [Fintype α]
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] [∀ w, DecidablePred (λ e => normalIn e w)] :
    nickelGEN Finset.univ normalIn ways R S ↔ Quantification.genWays normalIn ways R S := by
  simp only [nickelGEN, Quantification.genWays, everyOn, and_comm]

/-!
## Summary: Three Views of Normality

| View | Normality | GEN formula | Handles elephants? |
|------|-----------|-------------|-------------------|
| [cohen-1999a] | Probability > 0.5 | P(Q\|P) > 0.5 | No |
| [nickel-2009] | Ways of being normal | ∃w. ∀x. (A(x) ∧ normal(x,w)) → Q(x) | Yes |

Cohen's probability view is formalized in `Studies/Cohen1999.lean`; the divergence
on conjunctive generics is `cohen_fails_nickel_succeeds_on_conjunction` above.
-/

end Nickel2009
