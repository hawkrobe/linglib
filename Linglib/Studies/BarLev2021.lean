import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Semantics.Exhaustification.Operators.InnocentInclusion
import Linglib.Semantics.Plurality.Implicature
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Semantics.Homogeneity.Plural
import Linglib.Studies.Magri2014
import Mathlib.Data.Set.Basic

/-!
# Bar-Lev (2021): An Implicature Account of Homogeneity and Non-Maximality

[bar-lev-2021]

An Implicature Account of Homogeneity and Non-Maximality.
Linguistics and Philosophy 44:1045–1097.

## Core Contribution

Bar-Lev derives homogeneity, universality, and non-maximality for plural
definites from a single mechanism: **exhaustification with subdomain
alternatives** via the Exh^{IE+II} operator of [bar-lev-fox-2020].

The key ingredients:

1. **∃-PL** (existential pluralization): The basic meaning of a plural
   definite like "the kids laughed" is *existential*: at least one kid
   laughed. This operator is defined in `ExistentialPL.lean`.

2. **Subdomain alternatives**: Replacing the domain variable D with
   subsets D' ⊆ D generates alternatives that are NOT closed under
   conjunction — structurally parallel to free choice disjunction
   ([fox-2007]).

3. **Exh^{IE+II}**: The same exhaustivity operator that derives free
   choice from ◇(A ∨ B) derives universality from ∃-PL. Since the
   subdomain alternatives are not closed under ∧, no non-prejacent
   alternative is innocently excludable, and all are innocently
   includable.

## Structural Parallel with Free Choice

This file proves that the Exh^{IE+II} derivation for homogeneity is
structurally isomorphic to the free choice derivation in
`Studies/BarLevFox2020.lean`:

| Free Choice              | Homogeneity                     |
|--------------------------|----------------------------------|
| FCWorld (5 worlds)       | HomWorld (4 worlds)              |
| ◇(A ∨ B) (prejacent)    | someLaughed (∃-PL)               |
| {◇(A∨B), ◇A, ◇B, ◇(A∧B)} | {someLaughed, kellyL, janeL}  |
| ◇A ∧ ◇B ∉ ALT           | kellyL ∧ janeL ∉ ALT            |
| IE = {◇(A∧B)}           | IE = ∅                           |
| II = {◇A, ◇B}           | II = {kellyL, janeL}             |
| Free choice              | Universal reading                |

## Asymmetry of Positive and Negative

A key prediction: the positive and negative cases are *not symmetric*.

- **Positive** "the kids laughed": existential basic meaning, strengthened
  to universal by Exh^{IE+II} (implicature).
- **Negative** "the kids didn't laugh": ¬∃ = ∀¬ from basic semantics
  alone — no strengthening needed.

This asymmetry is derived in `negative_universal` below.

TODO: derive a `Generalizations.HomogeneityGap.GapPredict` implementation
from the exhaustification account and prove divergence theorems vs rivals.
-/

namespace BarLev2021

open Exhaustification

-- ============================================================
-- SECTION 1: World Type and Propositions
-- ============================================================

/-- Possible worlds for a two-atom plurality {Kelly, Jane} and a
    predicate P (e.g., "laughed"). -/
inductive HomWorld where
  | neither  : HomWorld  -- Neither laughed
  | onlyKelly : HomWorld -- Only Kelly laughed
  | onlyJane : HomWorld  -- Only Jane laughed
  | both     : HomWorld  -- Both laughed
  deriving DecidableEq, Repr, Inhabited

/-- Kelly laughed (subdomain alternative for D = {Kelly}). -/
def kellyLaughed : Set HomWorld
  | .neither => False
  | .onlyKelly => True
  | .onlyJane => False
  | .both => True

/-- Jane laughed (subdomain alternative for D = {Jane}). -/
def janeLaughed : Set HomWorld
  | .neither => False
  | .onlyKelly => False
  | .onlyJane => True
  | .both => True

/-- The prejacent: ∃-PL_{D={Kelly,Jane}} P (the kids) = "some kid laughed."
    This is the basic existential meaning of "the kids laughed." -/
def someLaughed : Set HomWorld
  | .neither => False
  | .onlyKelly => True
  | .onlyJane => True
  | .both => True


-- ============================================================
-- SECTION 1b: Grounding in ∃-PL
-- ============================================================

/-!
## Grounding in `ExistentialPL.lean`

The propositions above are *instances* of the `existPL` operator from
`ExistentialPL.lean`. We make this connection structural: each proposition
is provably equivalent to `existPL` applied with the appropriate domain
variable D.
-/

open Semantics.Plurality.Implicature (existPL existPL_full existPL_singleton)

/-- The two atoms of the plurality "the kids". -/
inductive Kid where | kelly | jane
  deriving DecidableEq, Repr

/-- The predicate "laughed" as a function of atoms and worlds. -/
def laughed : Kid → HomWorld → Prop
  | .kelly => kellyLaughed
  | .jane  => janeLaughed

instance laughed.instDecidable : ∀ k w, Decidable (laughed k w) := by
  intro k w
  cases k <;> cases w <;> unfold laughed kellyLaughed janeLaughed <;> infer_instance

/-- The plurality "the kids" = {Kelly, Jane}. -/
def theKids : Finset Kid := {.kelly, .jane}

/-- **Grounding**: `someLaughed` is the ∃-PL operator applied with full
    domain variable D = theKids. -/
theorem someLaughed_eq_existPL :
    ∀ w, someLaughed w ↔ existPL theKids laughed theKids w := by
  intro w; constructor
  · intro h
    cases w with
    | neither => exact absurd h id
    | onlyKelly => exact ⟨.kelly, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, trivial⟩
    | onlyJane => exact ⟨.jane, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)),
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), trivial⟩
    | both => exact ⟨.kelly, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, trivial⟩
  · rintro ⟨a, _, _, hP⟩
    cases a with
    | kelly => cases w <;> simp_all [someLaughed, laughed, kellyLaughed]
    | jane => cases w <;> simp_all [someLaughed, laughed, janeLaughed]

/-- **Grounding**: `kellyLaughed` is ∃-PL with singleton domain D = {Kelly}. -/
theorem kellyLaughed_eq_existPL :
    ∀ w, kellyLaughed w ↔ existPL {Kid.kelly} laughed theKids w := by
  intro w; constructor
  · intro h; exact ⟨.kelly, Finset.mem_insert_self _ _,
      Finset.mem_singleton_self _, h⟩
  · rintro ⟨a, _, hC, hP⟩
    have := Finset.mem_singleton.mp hC
    subst this; exact hP

/-- **Grounding**: `janeLaughed` is ∃-PL with singleton domain D = {Jane}. -/
theorem janeLaughed_eq_existPL :
    ∀ w, janeLaughed w ↔ existPL {Kid.jane} laughed theKids w := by
  intro w; constructor
  · intro h; exact ⟨.jane, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)),
      Finset.mem_singleton_self _, h⟩
  · rintro ⟨a, _, hC, hP⟩
    have := Finset.mem_singleton.mp hC
    subst this; exact hP


-- ============================================================
-- SECTION 2: Alternative Set and Non-Closure
-- ============================================================

/-- The subdomain alternative set.

    Full domain variable D = {Kelly, Jane}. Subdomain alternatives
    arise from D' ⊆ D:
    - D' = {Kelly, Jane}: someLaughed (= prejacent)
    - D' = {Kelly}: kellyLaughed
    - D' = {Jane}: janeLaughed
    - D' = ∅: trivially true (excluded as non-informative)

    Crucially, the *conjunction* kellyLaughed ∧ janeLaughed is NOT in
    this set — the alternatives are not closed under ∧. -/
def homAlt : Set (Set HomWorld) :=
  {someLaughed, kellyLaughed, janeLaughed}

/-- The prejacent: ∃-PL with full domain. -/
def homPrejacent : Set HomWorld := someLaughed

/-- The subdomain alternatives are NOT closed under conjunction.

    kellyLaughed ∧ janeLaughed (= "both laughed") is not equivalent
    to any member of homAlt. This is the structural property that
    enables the Exh^{IE+II} derivation, parallel to free choice. -/
theorem hom_not_closed :
    ¬(∀ (X : Set (Set HomWorld)), X ⊆ homAlt → (⋂₀ X) ∈ homAlt) := by
  intro h
  have hX : ({kellyLaughed, janeLaughed} : Set (Set HomWorld)) ⊆ homAlt := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp
  have hconj := h {kellyLaughed, janeLaughed} hX
  simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at hconj
  rcases hconj with heq | heq | heq
  · -- ⋂₀ {kellyL, janeL} = someLaughed: at onlyKelly, janeL false
    have : ¬(⋂₀ ({kellyLaughed, janeLaughed} : Set _)) .onlyKelly :=
      fun hc => hc janeLaughed (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋂₀ {kellyL, janeL} = kellyLaughed: at onlyKelly, janeL false but kellyL true
    have : ¬(⋂₀ ({kellyLaughed, janeLaughed} : Set _)) .onlyKelly :=
      fun hc => hc janeLaughed (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋂₀ {kellyL, janeL} = janeLaughed: at onlyJane, kellyL false but janeL true
    have : ¬(⋂₀ ({kellyLaughed, janeLaughed} : Set _)) .onlyJane :=
      fun hc => hc kellyLaughed (Set.mem_insert_iff.mpr (Or.inl rfl))
    rw [heq] at this; exact this trivial


-- ============================================================
-- SECTION 3: IE Analysis — Nothing Is Innocently Excludable
-- ============================================================

/-!
## IE Computation

For φ = someLaughed and ALT = {someLaughed, kellyLaughed, janeLaughed}:

There are two MC-sets (maximal sets of negated alternatives consistent
with the prejacent):
- MC₁ = {φ, janeLaughedᶜ} — witness: onlyKelly
- MC₂ = {φ, kellyLaughedᶜ} — witness: onlyJane

The IE set is {a ∈ ALT : aᶜ ∈ every MC-set}. The intersection
MC₁ ∩ MC₂ = {φ}, and since φᶜ is never in an MC-set (contradicts
the prejacent), **no alternative is innocently excludable**.

More precisely: kellyLaughedᶜ ∉ MC₁ and janeLaughedᶜ ∉ MC₂, so neither
individual alternative is in IE. And someLaughed = φ cannot be IE-excluded
by definition.

This contrasts with free choice, where ◇(A ∧ B) IS IE-excludable.
The difference: homAlt has only 3 elements (no conjunction member),
while fcALT has 4 (including ◇(A ∧ B)).
-/

private theorem homAlt_finite : Set.Finite homAlt :=
  Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))

private theorem homPrejacent_sat : ∃ w, homPrejacent w := ⟨.onlyKelly, trivial⟩

/-- Cover lemma: someLaughed ∧ ¬kellyLaughed ∧ ¬janeLaughed is inconsistent. -/
private theorem hom_cover : ∀ u, someLaughed u → ¬kellyLaughed u → ¬janeLaughed u → False :=
  fun u => by cases u <;> simp [someLaughed, kellyLaughed, janeLaughed]

/-- MC-set that omits kellyLaughedᶜ (contains janeLaughedᶜ). Witness: onlyKelly. -/
private theorem mc_set_without_neg_kelly :
    IsMCSet homAlt homPrejacent {homPrejacent, janeLaughedᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · left; rfl
      · right; exact ⟨janeLaughed, by simp [homAlt], rfl⟩
    · exact ⟨.onlyKelly, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl
        · exact trivial
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · -- someLaughedᶜ contradicts homPrejacent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (someLaughedᶜ) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · -- kellyLaughedᶜ + janeLaughedᶜ + someLaughed is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hom_cover u
          (hu homPrejacent (hsub (Set.mem_insert _ _)))
          (hu (kellyLaughedᶜ) hψ')
          (hu (janeLaughedᶜ) (hsub (Set.mem_insert_of_mem _ rfl)))
      · exact Set.mem_insert_of_mem _ rfl

/-- MC-set that omits janeLaughedᶜ (contains kellyLaughedᶜ). Witness: onlyJane. -/
private theorem mc_set_without_neg_jane :
    IsMCSet homAlt homPrejacent {homPrejacent, kellyLaughedᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · left; rfl
      · right; exact ⟨kellyLaughed, by simp [homAlt], rfl⟩
    · exact ⟨.onlyJane, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl
        · exact trivial
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (someLaughedᶜ) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ rfl
      · -- janeLaughedᶜ + kellyLaughedᶜ + someLaughed is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hom_cover u
          (hu homPrejacent (hsub (Set.mem_insert _ _)))
          (hu (kellyLaughedᶜ) (hsub (Set.mem_insert_of_mem _ rfl)))
          (hu (janeLaughedᶜ) hψ')

/-- someLaughed is not innocently excludable (it's the prejacent). -/
private theorem someLaughed_not_ie :
    ¬IsInnocentlyExcludable homAlt homPrejacent someLaughed :=
  not_isInnocentlyExcludable_of_phi_subset homAlt_finite homPrejacent_sat
    (Set.Subset.refl _)

/-- kellyLaughed is NOT innocently excludable.

    kellyLaughedᶜ ∉ MC₁ = {homPrejacent, janeLaughedᶜ}, because
    kellyLaughedᶜ ≠ homPrejacent (differ at .neither) and
    kellyLaughedᶜ ≠ janeLaughedᶜ (differ at .onlyKelly). -/
private theorem kellyLaughed_not_ie :
    ¬IsInnocentlyExcludable homAlt homPrejacent kellyLaughed := by
  refine mc_set_without_neg_kelly.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => Eq.mp (congrFun h .neither) id,
         fun h => Eq.mpr (congrFun h .onlyKelly) id trivial⟩

/-- janeLaughed is NOT innocently excludable.

    janeLaughedᶜ ∉ MC₂ = {homPrejacent, kellyLaughedᶜ}, because
    janeLaughedᶜ ≠ homPrejacent (differ at .neither) and
    janeLaughedᶜ ≠ kellyLaughedᶜ (differ at .onlyJane). -/
private theorem janeLaughed_not_ie :
    ¬IsInnocentlyExcludable homAlt homPrejacent janeLaughed := by
  refine mc_set_without_neg_jane.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => Eq.mp (congrFun h .neither) id,
         fun h => Eq.mpr (congrFun h .onlyJane) id trivial⟩

/-- **Nothing is innocently excludable** in the homogeneity configuration.

    This is the key difference from free choice, where ◇(A ∧ B) IS
    IE-excludable. Here, the alternatives lack a conjunction member
    entirely, so neither individual alternative can be consistently
    excluded from all MC-sets. -/
theorem nothing_ie (q : Set HomWorld)
    (hqIE : IsInnocentlyExcludable homAlt homPrejacent q) : False := by
  have hq_in := hqIE.1
  simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at hq_in
  rcases hq_in with rfl | rfl | rfl
  · exact someLaughed_not_ie hqIE
  · exact kellyLaughed_not_ie hqIE
  · exact janeLaughed_not_ie hqIE


-- ============================================================
-- SECTION 4: II Analysis — Both Alternatives Are Includable
-- ============================================================

/-!
## II Computation

Since IE = ∅ (nothing is excludable), the II constraint set is just
{someLaughed} (the prejacent, with no IE negations).

All members of homAlt hold at .both, so adding any target to an
II-compatible set R preserves II-compatibility (witness: .both).

Result: II = {kellyLaughed, janeLaughed} (and someLaughed, but the
prejacent is already asserted).
-/

/-- All elements of homAlt are true at .both. -/
private theorem all_hold_at_both :
    ∀ ψ ∈ homAlt, ψ HomWorld.both := by
  intro ψ hψ
  simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
  rcases hψ with rfl | rfl | rfl <;> trivial

/-- For any II-compatible R, adding a target ∈ homAlt preserves II-compatibility.

    Since nothing is IE-excludable (`nothing_ie`), the IE negation set is empty,
    and the witness .both satisfies everything in homAlt. -/
private theorem extend_hom_II
    (target : Set HomWorld)
    (htarget_alt : target ∈ homAlt)
    (R : Set (Set HomWorld))
    (hRcompat : IsIICompatible homAlt homPrejacent R) (_hNotIn : target ∉ R) :
    IsIICompatible homAlt homPrejacent (R ∪ {target}) := by
  constructor
  · intro x hx
    rcases hx with hxR | hxT
    · exact hRcompat.1 hxR
    · rw [Set.mem_singleton_iff.mp hxT]; exact htarget_alt
  · -- Witness: .both satisfies everything
    refine ⟨.both, fun ψ hψ => ?_⟩
    rcases hψ with hψ_left | hψ_right
    · rcases hψ_left with hψ_φ | hψ_ie
      · rw [Set.mem_singleton_iff.mp hψ_φ]; exact trivial
      · -- IE negation: impossible since nothing is IE
        obtain ⟨q, hqIE, _⟩ := hψ_ie
        exact absurd hqIE (fun h => nothing_ie q h)
    · rcases hψ_right with hψR | hψT
      · exact all_hold_at_both ψ (hRcompat.1 hψR)
      · rw [Set.mem_singleton_iff.mp hψT]; exact all_hold_at_both target htarget_alt

/-- A target ∈ homAlt is innocently includable. -/
private theorem target_in_hom_II
    (target : Set HomWorld)
    (htarget_alt : target ∈ homAlt) :
    IsInnocentlyIncludable homAlt homPrejacent target := by
  constructor
  · exact htarget_alt
  · intro R ⟨hRcompat, hRmax⟩
    by_contra hNotIn
    have hext := extend_hom_II target htarget_alt R hRcompat hNotIn
    exact hNotIn (hRmax (R ∪ {target}) hext Set.subset_union_left
      (Set.mem_union_right R rfl))

/-- kellyLaughed is innocently includable. -/
theorem kellyLaughed_ii :
    IsInnocentlyIncludable homAlt homPrejacent kellyLaughed :=
  target_in_hom_II kellyLaughed (by simp [homAlt])

/-- janeLaughed is innocently includable. -/
theorem janeLaughed_ii :
    IsInnocentlyIncludable homAlt homPrejacent janeLaughed :=
  target_in_hom_II janeLaughed (by simp [homAlt])


-- ============================================================
-- SECTION 5: Main Theorems
-- ============================================================

/-- **Universality from Exh^{IE+II}**: exhaustified "the kids laughed"
    entails that both Kelly and Jane laughed.

    Exh^{IE+II}(∃-PL_C(laughed)(the kids)) ⊢ ∀ x ∈ {K,J}. laughed(x)

    This is the homogeneity derivation: the universal reading of a
    plural definite arises as an implicature, not from basic semantics.

    Compare `free_choice` in `Studies/BarLevFox2020.lean`. -/
theorem universality :
    ∀ w, exhIEII homAlt homPrejacent w → kellyLaughed w ∧ janeLaughed w := by
  intro w ⟨_, _, hII⟩
  exact ⟨hII kellyLaughed kellyLaughed_ii, hII janeLaughed janeLaughed_ii⟩

/-- **Negative asymmetry**: Under negation, the universal reading comes
    for free from the basic (existential) semantics:
    ¬∃x. laughed(x) ⊢ ∀x. ¬laughed(x).

    No exhaustification needed — this is just the classical equivalence
    ¬∃ = ∀¬. This asymmetry between positive and negative is a key
    prediction that distinguishes the implicature account from trivalent
    theories (where both polarities are symmetric). -/
theorem negative_universal :
    ∀ w, ¬someLaughed w → ¬kellyLaughed w ∧ ¬janeLaughed w :=
  fun w h => ⟨fun hk => h (by cases w <;> simp_all [someLaughed, kellyLaughed]),
              fun hj => h (by cases w <;> simp_all [someLaughed, janeLaughed])⟩


-- ============================================================
-- SECTION 6: Homogeneity Gap (Derived)
-- ============================================================

/-- In a gap scenario (some but not all laughed), the positive sentence
    is false (universality fails) and the negative sentence is false
    (existence holds). This non-complementarity IS the homogeneity gap. -/
theorem gap_both_false :
    ∀ w, someLaughed w → ¬(kellyLaughed w ∧ janeLaughed w) →
      -- Positive (strengthened) is false
      ¬(exhIEII homAlt homPrejacent w) ∧
      -- Negative (basic) is false
      ¬(¬someLaughed w) := by
  intro w hsome hnotall
  exact ⟨fun hexh => hnotall (universality w hexh), not_not.mpr hsome⟩

/-- Witness: onlyKelly is a gap scenario. -/
theorem onlyKelly_is_gap :
    someLaughed .onlyKelly ∧ ¬(kellyLaughed .onlyKelly ∧ janeLaughed .onlyKelly) :=
  ⟨trivial, fun ⟨_, h⟩ => h⟩

/-- Witness: onlyJane is a gap scenario. -/
theorem onlyJane_is_gap :
    someLaughed .onlyJane ∧ ¬(kellyLaughed .onlyJane ∧ janeLaughed .onlyJane) :=
  ⟨trivial, fun ⟨h, _⟩ => h⟩


-- ============================================================
-- SECTION 7: Non-Maximality via Pruning
-- ============================================================

/-!
## Non-Maximality via Pruning

[bar-lev-2021] §5 derives non-maximal readings via **pruning**: when
context makes certain subdomain alternatives irrelevant, they are
removed from ALT before exhaustification. With fewer alternatives,
Exh^{IE+II} produces a weaker (non-maximal) reading.

The pruning spectrum for a 2-atom plurality {Kelly, Jane}:

| ALT                          | Result                         |
|------------------------------|--------------------------------|
| {φ, kellyL, janeL} (full)   | Universal (both laughed)       |
| {φ, janeL} (kelly pruned)   | janeL excluded by IE           |
| {φ, kellyL} (jane pruned)   | kellyL excluded by IE          |
| {φ} (fully pruned)          | Existential (some kid laughed) |

Note: with only 2 atoms, partial pruning yields *exclusive* readings
(IE excludes the remaining alternative), not intermediate non-maximal
readings. True non-maximality (e.g., "7 of 10 kids laughed" counting
as "the kids laughed") requires ≥3 atoms, where pruning some but not
all individual alternatives weakens the II result to something between
existential and universal.

In a fire-hazard-style context ([kriz-2015]), the distinction
between "all kids laughed" and "some kids laughed" is irrelevant,
so ALL individual alternatives are pruned. Exh is then vacuous and
the existential basic meaning surfaces directly.
-/

/-- Fully pruned alternative set: only the prejacent remains. -/
def prunedAlt : Set (Set HomWorld) := {someLaughed}

/-- With a fully pruned alternative set, Exh^{IE+II} reduces to the
    basic existential meaning (no strengthening occurs). -/
theorem pruned_existential :
    ∀ w, exhIEII prunedAlt homPrejacent w → someLaughed w := by
  intro w ⟨hφ, _, _⟩; exact hφ

/-- The converse: the basic meaning suffices for Exh with pruned alternatives. -/
theorem existential_suffices_pruned :
    ∀ w, someLaughed w → exhIEII prunedAlt homPrejacent w := by
  intro w hφ
  refine ⟨hφ, fun q hq => ?_, fun r hr => ?_⟩
  · -- IE: q ∈ prunedAlt means q = someLaughed, which is not IE-excludable
    exfalso
    have hqeq := hq.1
    simp only [prunedAlt, Set.mem_singleton_iff] at hqeq
    subst hqeq
    obtain ⟨E, hMC⟩ := exists_MCset prunedAlt homPrejacent
      (Set.finite_singleton _) ⟨.onlyKelly, trivial⟩
    obtain ⟨u, hu⟩ := hMC.1.2.2
    exact hu (someLaughedᶜ) (hq.2 E hMC) (hu homPrejacent hMC.1.1)
  · -- II: r ∈ prunedAlt means r = someLaughed, which holds by hφ
    have := hr.1
    simp only [prunedAlt, Set.mem_singleton_iff] at this
    rw [this]; exact hφ

/-- Pruning strictly weakens the reading: the universal reading (full ALT)
    entails the existential reading (pruned ALT), but not vice versa. -/
theorem pruning_weakens :
    (∀ w, exhIEII homAlt homPrejacent w → someLaughed w) ∧
    ¬(∀ w, someLaughed w → exhIEII homAlt homPrejacent w) := by
  constructor
  · intro w ⟨hφ, _, _⟩; exact hφ
  · intro h; exact (universality .onlyKelly (h .onlyKelly trivial)).2

/-- Partially pruned alternative set: kellyLaughed removed, janeLaughed retained.

    With this ALT = {φ, janeLaughed}, there is a single MC-set
    {φ, janeLaughedᶜ} (witness: onlyKelly). So janeLaughed ∈ IE, and
    Exh^{IE}(φ) = someLaughed ∧ ¬janeLaughed. The 2-atom case yields
    *exclusive* readings under partial pruning, not weakened universals.
    True non-maximal readings require ≥3 atoms. -/
def partialPrunedAlt : Set (Set HomWorld) := {someLaughed, janeLaughed}

/-- MC-set for partialPrunedAlt: {homPrejacent, janeLaughedᶜ}.
    With ALT = {someLaughed, janeLaughed}, the only compatible negation
    is janeLaughedᶜ since someLaughedᶜ contradicts the prejacent. -/
private theorem mc_partial :
    IsMCSet partialPrunedAlt homPrejacent {homPrejacent, janeLaughedᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · left; rfl
      · right; exact ⟨janeLaughed, by simp [partialPrunedAlt], rfl⟩
    · exact ⟨.onlyKelly, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl
        · exact trivial
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [partialPrunedAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (someLaughedᶜ) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ rfl

/-- someLaughed is not IE-excludable for partialPrunedAlt. -/
private theorem someLaughed_not_ie_partial :
    ¬IsInnocentlyExcludable partialPrunedAlt homPrejacent someLaughed := by
  refine mc_partial.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => Eq.mp (congrFun h .neither) id,
         fun h => Eq.mpr (congrFun h .onlyKelly) id trivial⟩

/-- janeLaughed IS IE-excludable for partialPrunedAlt.
    janeLaughedᶜ is in every MC-set: if E omits janeLaughedᶜ, E can be
    extended (since someLaughedᶜ is the only other option and contradicts φ),
    violating maximality. -/
private theorem janeLaughed_ie_partial :
    IsInnocentlyExcludable partialPrunedAlt homPrejacent janeLaughed := by
  refine ⟨Set.mem_insert_of_mem _ rfl, fun E hMC => ?_⟩
  by_contra hNotIn
  have hcompat : IsCompatible partialPrunedAlt homPrejacent (E ∪ {janeLaughedᶜ}) := by
    refine ⟨Or.inl hMC.1.1, ?_, ?_⟩
    · intro ψ hψ
      rcases hψ with hψE | hψS
      · exact hMC.1.2.1 ψ hψE
      · right
        exact ⟨janeLaughed, Set.mem_insert_of_mem _ rfl, Set.mem_singleton_iff.mp hψS⟩
    · refine ⟨.onlyKelly, fun ψ hψ => ?_⟩
      rcases hψ with hψE | hψS
      · rcases hMC.1.2.1 ψ hψE with rfl | ⟨a, ha, rfl⟩
        · exact trivial
        · simp only [partialPrunedAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · exfalso; obtain ⟨u, hu⟩ := hMC.1.2.2
            exact hu (someLaughedᶜ) hψE (hu homPrejacent hMC.1.1)
          · exact absurd hψE hNotIn
      · rw [Set.mem_singleton_iff.mp hψS]; exact id
  exact hNotIn (hMC.2 _ hcompat Set.subset_union_left (Set.subset_union_right rfl))

/-- Partial pruning (removing kellyLaughed) does not yield universality.

    Counterexample: .onlyKelly satisfies Exh^{IE+II} (janeLaughed is
    IE-excluded and someLaughed is II-included) but not the universal
    kellyLaughed ∧ janeLaughed. -/
theorem partial_pruning_not_universal :
    ¬(∀ w, exhIEII partialPrunedAlt homPrejacent w →
      kellyLaughed w ∧ janeLaughed w) := by
  intro h
  suffices hexh : exhIEII partialPrunedAlt homPrejacent .onlyKelly from
    (h .onlyKelly hexh).2
  refine ⟨trivial, ?_, ?_⟩
  · -- IE: for all IE-excludable q, ¬q .onlyKelly
    intro q hq
    have hqAlt := hq.1
    simp only [partialPrunedAlt] at hqAlt
    rcases hqAlt with rfl | rfl
    · exact absurd hq someLaughed_not_ie_partial
    · exact id
  · -- II: for all II-includable r, r .onlyKelly
    intro r hr
    have hrAlt := hr.1
    simp only [partialPrunedAlt] at hrAlt
    rcases hrAlt with rfl | rfl
    · exact trivial
    · exfalso
      have hmi : IsMISet partialPrunedAlt homPrejacent {someLaughed} := by
        constructor
        · constructor
          · intro x hx; simp only [Set.mem_singleton_iff] at hx
            rw [hx]; exact Set.mem_insert _ _
          · refine ⟨.onlyKelly, fun ψ hψ => ?_⟩
            rcases hψ with hψ_left | hψ_R
            · rcases hψ_left with hψ_φ | hψ_ie
              · rw [Set.mem_singleton_iff.mp hψ_φ]; exact trivial
              · obtain ⟨q, hqIE, rfl⟩ := hψ_ie
                have hqAlt := hqIE.1
                simp only [partialPrunedAlt] at hqAlt
                rcases hqAlt with rfl | rfl
                · exact absurd hqIE someLaughed_not_ie_partial
                · exact id
            · rw [Set.mem_singleton_iff.mp hψ_R]; exact trivial
        · intro R' hR'compat hsub r' hr'
          have hr'Alt := hR'compat.1 hr'
          simp only [partialPrunedAlt] at hr'Alt
          rcases hr'Alt with rfl | rfl
          · exact rfl
          · exfalso
            obtain ⟨u, hu⟩ := hR'compat.2
            exact hu (janeLaughedᶜ)
              (Or.inl (Or.inr ⟨janeLaughed, janeLaughed_ie_partial, rfl⟩))
              (hu janeLaughed (Or.inr hr'))
      have hmem := hr.2 _ hmi
      simp only [Set.mem_singleton_iff] at hmem
      exact Eq.mpr (congrFun hmem .onlyKelly) trivial


-- ============================================================
-- SECTION 8: Bridges to Empirical Data
-- ============================================================

open Generalizations.HomogeneityGap (allData)

/-- The account against the pooled unembedded homogeneity-gap data
    ([kriz-chemla-2015], [kriz-2015], [agha-jeretic-2022]): `.indet` is
    observed in gap cells of both polarities — the non-complementarity
    derived in `gap_both_false` — and only there (baseline cells are
    bivalent, as `universality` and `negative_universal` require). -/
theorem matches_pooled_gap_data :
    ((allData.any fun d =>
        d.polarity == .positive && d.scenario == .gap && d.observed == .indet) = true) ∧
    ((allData.any fun d =>
        d.polarity == .negative && d.scenario == .gap && d.observed == .indet) = true) ∧
    ((allData.filter (fun d => d.scenario != .gap)).all
        (fun d => d.observed != .indet) = true) :=
  ⟨by decide, by decide, by decide⟩

/-- For plural-definite rows ([kriz-2015], [kriz-chemla-2015]), no gap
    cell observes clear falsity: those cells resolve to `.indet` (the
    gap, `gap_both_false`) or `.true` (a non-maximal reading, derived
    by pruning — `pruned_existential`), never `.false`. The restriction
    matters: [agha-jeretic-2022]'s strong-necessity rows (*have to*)
    observe `.false` in the positive gap cell — strong modals are
    gap-free, outside this account's plural-definite scope. -/
theorem plural_definite_gap_cells_never_false :
    (allData.filter (fun d =>
        d.scenario == .gap && d.source.bibkey != "agha-jeretic-2022")).all
      (fun d => d.observed != .false) = true := by decide


-- ============================================================
-- SECTION 9: Comparison with Magri (2014)
-- ============================================================

/-!
## Comparison with [magri-2014]

Both Magri and Bar-Lev derive universality from exhaustification of an
existential basic meaning. The key differences:

1. **Magri**: Uses double exhaustification (EXH(EXH(THE))) with
   non-transitive Horn-mateness to block THE from excluding ALL directly.

2. **Bar-Lev**: Uses single Exh^{IE+II} with subdomain alternatives.
   The key insight is that subdomain alternatives are not closed under ∧,
   which is what triggers II (Innocent Inclusion).

Bar-Lev's approach is more economical (one application of Exh, not two)
and unifies homogeneity with free choice through a shared structural
property (non-closure under ∧).
-/

/-- Both theories agree that the basic meaning is existential and
    the strengthened meaning is universal. The key structural difference:
    Magri requires *two* applications of EXH (double exhaustification via
    non-transitive Horn-mateness), while Bar-Lev requires *one* application
    of Exh^{IE+II} (the richer operator compensates for fewer iterations).
    Bar-Lev's approach also unifies homogeneity with free choice through
    the shared structural property of non-closure under ∧. -/
theorem magri_agreement :
    -- Both start from existential basic meaning
    Magri2014.primalMeaning .mystery = Magri2014.someMeaning ∧
    -- Both derive universal reading in UE
    Magri2014.effectiveInterpretation .primal .positive = .strong :=
  ⟨rfl, rfl⟩


-- ============================================================
-- SECTION 10: "All" Removes Homogeneity
-- ============================================================

/-!
## How "All" Removes Homogeneity

[bar-lev-2021] §8.3: "all the kids laughed" does not display
homogeneity because `all` universally quantifies over the plurality,
eliminating the domain variable D. Without D, there are no subdomain
alternatives, so Exh^{IE+II} is vacuous — the universal reading is
the *basic* meaning, not an implicature. Since it's not an implicature,
it can't be weakened by pruning, which is why "all" blocks
non-maximality.

Empirically, an `all`-quantified sentence is judged clearly false in
the gap scenario where its bare-definite counterpart is neither true
nor false ([kriz-2015]). [kriz-2016]'s gap removal (`Prop3.metaAssert`) derives the same
prediction by collapsing the truth-value gap into the negative
extension — a different mechanism, same empirical effect.
-/

/-- Without subdomain alternatives, exhaustification is vacuous:
    the prejacent passes through unchanged. This models the effect
    of `all`, which eliminates the domain variable D. -/
theorem all_exh_vacuous :
    ∀ w, exhIEII {homPrejacent} homPrejacent w ↔ someLaughed w := by
  intro w; constructor
  · intro ⟨hφ, _, _⟩; exact hφ
  · intro hφ
    exact (existential_suffices_pruned w hφ)


-- ============================================================
-- SECTION 11: Comparison with Križ (2016)
-- ============================================================

/-!
## Comparison with [kriz-2016] (Trivalent Account)

[kriz-2016] and [kriz-spector-2021] derive homogeneity from
trivalent semantics: plural predication yields a three-valued denotation
(true/false/gap), and non-maximality arises when the gap is pragmatically
exploitable. The two accounts differ in:

| Property | Bar-Lev (implicature) | Križ (trivalent) |
|----------|----------------------|------------------|
| Basic meaning | existential (∃-PL) | trivalent (T/F/gap) |
| Universal reading | implicature (Exh^{IE+II}) | semantic (true extension) |
| Non-maximality | pruning alternatives | pragmatic gap exploitation |
| Positive/negative | **asymmetric** | symmetric |
| "All" removes gap | eliminates C variable | collapses gap (metaAssert) |

### Key Distinguishing Prediction: Asymmetry

The most important empirical difference concerns the **status** of the
universal inference under negation:

- **Bar-Lev**: Positive universality is an *implicature* (cancelable
  via pruning). Negative universality is *semantic* (¬∃ = ∀¬, no
  implicature involved). The two polarities are fundamentally asymmetric.

- **Križ**: Both positive and negative universality arise from the same
  source (gap collapse). The gap is symmetric: it exists for both
  "the kids laughed" and "the kids didn't laugh." Non-maximality is
  available for both polarities.

This asymmetry is captured by `negative_universal` above: under
negation, the universal reading follows from basic semantics without
exhaustification. Križ's trivalent account would instead derive both
through the gap mechanism symmetrically.
-/

/-- The positive–negative asymmetry: positive universality *requires*
    exhaustification, while negative universality does not.

    This is a distinguishing prediction of the implicature account:
    `universality` needs the full Exh^{IE+II} machinery, but
    `negative_universal` is a simple logical entailment. In the trivalent
    account ([kriz-2016]), both arise from the gap structure. -/
theorem positive_negative_asymmetry :
    -- Positive: exhaustification is necessary (without it, universality fails)
    (∃ w, someLaughed w ∧ ¬(kellyLaughed w ∧ janeLaughed w)) ∧
    -- Negative: universality is automatic (no exhaustification)
    (∀ w, ¬someLaughed w → ¬kellyLaughed w ∧ ¬janeLaughed w) := by
  exact ⟨⟨.onlyKelly, trivial, fun ⟨_, h⟩ => h⟩, negative_universal⟩


-- ============================================================
-- SECTION 12: Formal divergence with Križ (2016)
-- ============================================================

/-! The §11 prose comparison is upgraded here to a kernel-checked divergence
theorem: lift the BarLev `Set HomWorld` predicates into Bool-valued versions,
instantiate Križ's `barePlural` over them, and demonstrate that at the
gap-world `onlyKelly`:

- Križ's bare-plural is `.indet` (gap), and its Strong-Kleene negation is
  ALSO `.indet` (gap). So Križ's `gap_enables_nonmax` makes non-maximal
  use of the *negation* available in principle.
- Bar-Lev's `negative_universal` (above) makes `¬someLaughed` straightforwardly
  bivalent — at `onlyKelly` it's FALSE (since some kid did laugh). No gap
  to exploit, so non-maximal use of negation is forbidden.

The two predictions cannot both be right: this is the kernel-visible form
of the §11 polarities-symmetric vs. polarities-asymmetric disagreement. -/

/-- At `onlyKelly`, Križ's bare-plural denotation of "the kids laughed" is
    a homogeneity gap (.indet) — Kelly laughed, Jane didn't. -/
theorem kriz_bare_kids_onlyKelly_gap :
    Semantics.Homogeneity.barePlural laughed theKids
      .onlyKelly = .indet := by decide

/-- Križ's Strong-Kleene negation of a gap is also a gap. So the negation
    "the kids didn't laugh" at `onlyKelly` is `.indet` under Križ. -/
theorem kriz_neg_bare_kids_onlyKelly_gap :
    Trivalent.neg
      (Semantics.Homogeneity.barePlural laughed theKids
        .onlyKelly) = .indet := by
  rw [kriz_bare_kids_onlyKelly_gap]; decide

/-- Bar-Lev's `negative_universal` derives `¬someLaughed` as bivalent:
    at `onlyKelly`, `¬someLaughed .onlyKelly` is FALSE (Kelly laughed). -/
theorem barlev_neg_someLaughed_onlyKelly_false :
    ¬ ¬ someLaughed .onlyKelly :=
  fun h => h trivial

/-- **Križ vs. Bar-Lev formal divergence on negative non-maximality**.
    At the gap-world `onlyKelly`:

    - **Križ**: negation of "the kids laughed" is `.indet` (Strong-Kleene
      preserves the gap). So `gap_enables_nonmax` makes non-maximal use of
      the *negation* in principle available — symmetric with the positive.
    - **Bar-Lev**: `¬someLaughed` is straightforwardly bivalent (¬∃ = ∀¬).
      At `onlyKelly`, `¬someLaughed` is FALSE — no gap to exploit. The
      negation cannot be used non-maximally — asymmetric with positive.

    The two clauses below cannot both be the right semantics for "the kids
    didn't laugh" at `onlyKelly`. The theorem's existence packages the
    formal disagreement that §11 §`positive_negative_asymmetry` describes
    in prose. -/
theorem kriz_vs_barlev_negative_nonmax :
    Trivalent.neg
      (Semantics.Homogeneity.barePlural laughed theKids
        .onlyKelly) = .indet ∧
    ¬ ¬ someLaughed .onlyKelly :=
  ⟨kriz_neg_bare_kids_onlyKelly_gap, barlev_neg_someLaughed_onlyKelly_false⟩


end BarLev2021
