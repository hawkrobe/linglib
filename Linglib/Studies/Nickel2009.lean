import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Quantification.Generic
import Linglib.Studies.Cohen1999

/-!
# [nickel-2009]: Generics and the ways of normality

Bernhard Nickel, "Generics and the ways of normality",
*Linguistics and Philosophy* 31 (2009), 629–648.

## The Problem: Conjunctive Generics

Nickel criticizes majority-based views of generics (including
[cohen-1999a]'s probability-based GEN) by showing they cannot
handle conjunctive generics like:

    (2b) Elephants live in Africa and Asia.

If (2b) is equivalent to the sentential conjunction:

    Elephants live in Africa AND Elephants live in Asia.

then a majority-based view would require both conjuncts to hold with
prevalence > 0.5 over the same domain. But African elephants and Asian
elephants are disjoint populations — most elephants can't live in BOTH
places. So the majority view predicts the conjunction is false, contrary
to speaker judgments. (Nickel's running example is the elephants (2b/11);
example (2a), "Bears live in North America, South America, Europe, and
Asia", is the more dramatic four-continent variant.)

## Nickel's Solution: Ways of Being Normal

Nickel proposes that normality is not a single binary predicate but
comes in multiple **ways**. For the elephant case:

- **Way w₁**: normal w.r.t. habitat → lives in Africa
- **Way w₂**: normal w.r.t. habitat → lives in Asia

GEN existentially quantifies over ways of being normal, then
universally quantifies over the As that are normal in that way (p. 643):

    G(A;F) is true iff there is a way w of being an F-normal A such that
    all As that are w are F.

i.e. `∃w. ∀x. (A(x) ∧ normalIn(x, w)) → F(x)`. Conjunctive generics can
then use different normality ways for each conjunct.

Nickel notes (p. 643) that these truth-conditions "don't account yet for
a situation in which there aren't any F-normal As… we need to introduce a
counterfactual element. However, for the purposes of this paper, we can
ignore this complication." The formalization below inherits that: `nickelGEN`
holds vacuously when no entity is normal in any way. The way-existential is
modeled by its actual-extension proxy (the modal/inductive-target content of
"a respect of normality" is abstracted away).
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
    [∀ w, DecidablePred (fun e => normalIn e w)] : Prop :=
  ∃ w ∈ ways, everyOn entities (fun e => restrictor e ∧ normalIn e w) scope

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    [∀ w, DecidablePred (fun e => normalIn e w)] :
    Decidable (nickelGEN entities normalIn ways restrictor scope) := by
  unfold nickelGEN; infer_instance

/-- Conjunctive generic: both `GEN[A][F₁]` and `GEN[A][F₂]` hold, potentially via
    different normality ways. -/
def nickelConjunctiveGEN {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay)
    (restrictor scope1 scope2 : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope1] [DecidablePred scope2]
    [∀ w, DecidablePred (fun e => normalIn e w)] : Prop :=
  nickelGEN entities normalIn ways restrictor scope1 ∧
  nickelGEN entities normalIn ways restrictor scope2

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) (restrictor scope1 scope2 : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope1] [DecidablePred scope2]
    [∀ w, DecidablePred (fun e => normalIn e w)] :
    Decidable (nickelConjunctiveGEN entities normalIn ways restrictor scope1 scope2) := by
  unfold nickelConjunctiveGEN; infer_instance

/-- Normality ways are pairwise incompatible: no entity is normal in two distinct
    ways. The paper (p. 643) states this holds "usually (perhaps always)"; here it
    is a property of the toy model, not a commitment of the account. -/
def waysIncompatible {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay)
    [∀ w, DecidablePred (fun e => normalIn e w)] : Prop :=
  ∀ e ∈ entities, ∀ w₁ ∈ ways, ∀ w₂ ∈ ways,
    w₁ ≠ w₂ → ¬ (normalIn e w₁ ∧ normalIn e w₂)

instance {α : Type*} (entities : Finset α) (normalIn : α → NormalcyWay → Prop)
    (ways : Finset NormalcyWay) [∀ w, DecidablePred (fun e => normalIn e w)] :
    Decidable (waysIncompatible entities normalIn ways) := by
  unfold waysIncompatible; infer_instance

/-! ### The Elephant Example (2b/11) -/

section Elephants

/-- 10 elephants: 6 African (ids 0–5), 4 Asian (ids 6–9). -/
def elephants : Finset Entity := ((List.range 10).map (fun n => (⟨n⟩ : Entity))).toFinset

abbrev isElephant : Entity → Prop := fun _ => True
abbrev livesInAfrica : Entity → Prop := fun e => e.id < 6
abbrev livesInAsia : Entity → Prop := fun e => e.id ≥ 6

def africanWay : NormalcyWay := ⟨1⟩
def asianWay : NormalcyWay := ⟨2⟩
def ways : Finset NormalcyWay := {africanWay, asianWay}

/-- Normal in the African way = African elephants; in the Asian way = Asian. -/
abbrev elephantNormalIn : Entity → NormalcyWay → Prop := fun e w =>
  (w.id = 1 ∧ e.id < 6) ∨ (w.id = 2 ∧ e.id ≥ 6)

end Elephants

/-! ### The Bears Example (2a) -/

section Bears

/-- 20 bears across 4 continents (5 each): NA 0–4, SA 5–9, EU 10–14, AS 15–19.
    The majority view fails for ALL four habitat conjuncts (each is 5/20 = 25%). -/
def bears : Finset Entity := ((List.range 20).map (fun n => (⟨n⟩ : Entity))).toFinset

abbrev isBear : Entity → Prop := fun _ => True
abbrev bearNA : Entity → Prop := fun e => e.id < 5
abbrev bearSA : Entity → Prop := fun e => e.id ≥ 5 ∧ e.id < 10
abbrev bearEU : Entity → Prop := fun e => e.id ≥ 10 ∧ e.id < 15
abbrev bearAS : Entity → Prop := fun e => e.id ≥ 15

def bearWays : Finset NormalcyWay := {⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩}

abbrev bearNormalIn : Entity → NormalcyWay → Prop := fun e w =>
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

The headline contrast, now a theorem over a **shared** model citing
[cohen-1999a]'s `cohenGEN` directly (not a local re-implementation). The majority
view fails on the conjunction because the Asia conjunct has prevalence 4/10 < 1/2;
Nickel's view succeeds. Per the chronology rule this comparison lives in the later
paper (Nickel 2009 > Cohen 1999), which is the one that draws it. -/

/-- Cohen's majority GEN is false for "Elephants live in Asia" (prevalence 4/10). -/
theorem cohen_fails_elephant_asia :
    ¬ Cohen1999.cohenGEN elephants isElephant livesInAsia := by
  rw [Cohen1999.cohen_iff_thresholdGt elephants isElephant livesInAsia (by decide)]
  decide

/-- **Cohen vs Nickel on the conjunctive generic, over one shared model.** The
    majority view fails (Asia is a minority habitat) while Nickel's way-indexed view
    succeeds — exactly the divergence Nickel's paper draws against Cohen. -/
theorem cohen_fails_nickel_succeeds_on_conjunction :
    ¬ Cohen1999.cohenGEN elephants isElephant livesInAsia ∧
    nickelConjunctiveGEN elephants elephantNormalIn ways
      isElephant livesInAfrica livesInAsia := by
  refine ⟨cohen_fails_elephant_asia, ?_⟩
  decide

/-- The bears conjunction (2a) fails even harder for the majority view: every one of
    the four habitats is a 25% minority. -/
theorem cohen_fails_all_bear_habitats :
    ¬ Cohen1999.cohenGEN bears isBear bearNA ∧
    ¬ Cohen1999.cohenGEN bears isBear bearSA ∧
    ¬ Cohen1999.cohenGEN bears isBear bearEU ∧
    ¬ Cohen1999.cohenGEN bears isBear bearAS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [Cohen1999.cohen_iff_thresholdGt _ _ _ (by decide)]; decide

/-! ### Connection to Traditional GEN -/

/-- Nickel's GEN with a single normality way reduces to the relativized restricted
    universal `everyOn` (traditional GEN): the way-existential is trivial, leaving
    `∀ x. (restrictor(x) ∧ normalIn(x, w)) → scope(x)`. -/
theorem nickel_single_way_is_everyOn {α : Type*} (entities : Finset α)
    (normalIn : α → NormalcyWay → Prop) (w : NormalcyWay)
    (restrictor scope : α → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    [∀ w, DecidablePred (fun e => normalIn e w)] :
    nickelGEN entities normalIn {w} restrictor scope ↔
      everyOn entities (fun e => restrictor e ∧ normalIn e w) scope := by
  simp [nickelGEN]

/-! ### Generic-quantifier interface -/

/-- Nickel's `nickelGEN` over the whole carrier is exactly the ways-of-normality
    generalized quantifier `Quantification.genWays` — its `GQ`-interface form,
    the [nickel-2009] instance of the shared schema in `Quantification.Generic`. -/
theorem nickelGEN_univ_eq_genWays {α : Type*} [Fintype α]
    (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] [∀ w, DecidablePred (fun e => normalIn e w)] :
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
