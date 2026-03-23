import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Theories.Semantics.Lexical.Plural.ExistentialPL
import Linglib.Phenomena.Plurals.Homogeneity
import Linglib.Phenomena.Plurals.NonMaximality
import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Phenomena.Plurals.Studies.Magri2014

/-!
# Bar-Lev (2021): An Implicature Account of Homogeneity and Non-Maximality

@cite{bar-lev-2021}

An Implicature Account of Homogeneity and Non-Maximality.
Linguistics and Philosophy 44:1045–1097.

## Core Contribution

Bar-Lev derives homogeneity, universality, and non-maximality for plural
definites from a single mechanism: **exhaustification with subdomain
alternatives** via the Exh^{IE+II} operator of @cite{bar-lev-fox-2020}.

The key ingredients:

1. **∃-PL** (existential pluralization): The basic meaning of a plural
   definite like "the kids laughed" is *existential*: at least one kid
   laughed. This operator is defined in `ExistentialPL.lean`.

2. **Subdomain alternatives**: Replacing the domain variable D with
   subsets D' ⊆ D generates alternatives that are NOT closed under
   conjunction — structurally parallel to free choice disjunction
   (@cite{fox-2007}).

3. **Exh^{IE+II}**: The same exhaustivity operator that derives free
   choice from ◇(A ∨ B) derives universality from ∃-PL. Since the
   subdomain alternatives are not closed under ∧, no non-prejacent
   alternative is innocently excludable, and all are innocently
   includable.

## Structural Parallel with Free Choice

This file proves that the Exh^{IE+II} derivation for homogeneity is
structurally isomorphic to the free choice derivation in
`InnocentInclusion.lean`:

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
-/

namespace Phenomena.Plurals.Studies.BarLev2021

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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Kelly laughed (subdomain alternative for D = {Kelly}). -/
def kellyLaughed : Prop' HomWorld
  | .neither => False
  | .onlyKelly => True
  | .onlyJane => False
  | .both => True

/-- Jane laughed (subdomain alternative for D = {Jane}). -/
def janeLaughed : Prop' HomWorld
  | .neither => False
  | .onlyKelly => False
  | .onlyJane => True
  | .both => True

/-- The prejacent: ∃-PL_{D={Kelly,Jane}} P (the kids) = "some kid laughed."
    This is the basic existential meaning of "the kids laughed." -/
def someLaughed : Prop' HomWorld
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

open Semantics.Lexical.Plural.ExistentialPL (existPL existPL_full existPL_singleton)

/-- The two atoms of the plurality "the kids". -/
inductive Kid where | kelly | jane
  deriving DecidableEq, BEq, Repr

/-- The predicate "laughed" as a function of atoms and worlds. -/
def laughed : Kid → HomWorld → Prop
  | .kelly => kellyLaughed
  | .jane  => janeLaughed

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
def homAlt : Set (Prop' HomWorld) :=
  {someLaughed, kellyLaughed, janeLaughed}

/-- The prejacent: ∃-PL with full domain. -/
def homPrejacent : Prop' HomWorld := someLaughed

/-- The subdomain alternatives are NOT closed under conjunction.

    kellyLaughed ∧ janeLaughed (= "both laughed") is not equivalent
    to any member of homAlt. This is the structural property that
    enables the Exh^{IE+II} derivation, parallel to free choice. -/
theorem hom_not_closed :
    ¬(∀ (X : Set (Prop' HomWorld)), X ⊆ homAlt → (⋀ X) ∈ homAlt) := by
  intro h
  have hX : ({kellyLaughed, janeLaughed} : Set (Prop' HomWorld)) ⊆ homAlt := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp
  have hconj := h {kellyLaughed, janeLaughed} hX
  simp only [homAlt, Set.mem_insert_iff, Set.mem_singleton_iff] at hconj
  rcases hconj with heq | heq | heq
  · -- ⋀{kellyL, janeL} = someLaughed: at onlyKelly, janeL false
    have : ¬(⋀ ({kellyLaughed, janeLaughed} : Set _)) .onlyKelly :=
      fun hc => hc janeLaughed (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋀{kellyL, janeL} = kellyLaughed: at onlyKelly, janeL false but kellyL true
    have : ¬(⋀ ({kellyLaughed, janeLaughed} : Set _)) .onlyKelly :=
      fun hc => hc janeLaughed (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋀{kellyL, janeL} = janeLaughed: at onlyJane, kellyL false but janeL true
    have : ¬(⋀ ({kellyLaughed, janeLaughed} : Set _)) .onlyJane :=
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
- MC₁ = {φ, ∼janeLaughed} — witness: onlyKelly
- MC₂ = {φ, ∼kellyLaughed} — witness: onlyJane

The IE set is {a ∈ ALT : ∼a ∈ every MC-set}. The intersection
MC₁ ∩ MC₂ = {φ}, and since ∼φ is never in an MC-set (contradicts
the prejacent), **no alternative is innocently excludable**.

More precisely: ∼kellyLaughed ∉ MC₁ and ∼janeLaughed ∉ MC₂, so neither
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

/-- MC-set that omits ∼kellyLaughed (contains ∼janeLaughed). Witness: onlyKelly. -/
private theorem mc_set_without_neg_kelly :
    isMCSet homAlt homPrejacent {homPrejacent, ∼janeLaughed} := by
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
      · -- ∼someLaughed contradicts homPrejacent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (∼someLaughed) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · -- ∼kellyLaughed + ∼janeLaughed + someLaughed is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hom_cover u
          (hu homPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼kellyLaughed) hψ')
          (hu (∼janeLaughed) (hsub (Set.mem_insert_of_mem _ rfl)))
      · exact Set.mem_insert_of_mem _ rfl

/-- MC-set that omits ∼janeLaughed (contains ∼kellyLaughed). Witness: onlyJane. -/
private theorem mc_set_without_neg_jane :
    isMCSet homAlt homPrejacent {homPrejacent, ∼kellyLaughed} := by
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
        exact hu (∼someLaughed) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ rfl
      · -- ∼janeLaughed + ∼kellyLaughed + someLaughed is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hom_cover u
          (hu homPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼kellyLaughed) (hsub (Set.mem_insert_of_mem _ rfl)))
          (hu (∼janeLaughed) hψ')

/-- someLaughed is not innocently excludable (it's the prejacent). -/
private theorem someLaughed_not_ie :
    ¬isInnocentlyExcludable homAlt homPrejacent someLaughed := by
  intro ⟨_, hIE⟩
  obtain ⟨E, hMC⟩ := exists_MCset homAlt homPrejacent homAlt_finite homPrejacent_sat
  obtain ⟨u, hu⟩ := hMC.1.2.2
  exact hu (∼someLaughed) (hIE E hMC) (hu homPrejacent hMC.1.1)

/-- kellyLaughed is NOT innocently excludable.

    ∼kellyLaughed ∉ MC₁ = {homPrejacent, ∼janeLaughed}, because
    ∼kellyLaughed ≠ homPrejacent (differ at .neither) and
    ∼kellyLaughed ≠ ∼janeLaughed (differ at .onlyKelly). -/
private theorem kellyLaughed_not_ie :
    ¬isInnocentlyExcludable homAlt homPrejacent kellyLaughed := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼kellyLaughed ∉ ({homPrejacent, ∼janeLaughed} : Set (Prop' HomWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mpr (congrFun h .onlyKelly) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_kelly)

/-- janeLaughed is NOT innocently excludable.

    ∼janeLaughed ∉ MC₂ = {homPrejacent, ∼kellyLaughed}, because
    ∼janeLaughed ≠ homPrejacent (differ at .neither) and
    ∼janeLaughed ≠ ∼kellyLaughed (differ at .onlyJane). -/
private theorem janeLaughed_not_ie :
    ¬isInnocentlyExcludable homAlt homPrejacent janeLaughed := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼janeLaughed ∉ ({homPrejacent, ∼kellyLaughed} : Set (Prop' HomWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mpr (congrFun h .onlyJane) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_jane)

/-- **Nothing is innocently excludable** in the homogeneity configuration.

    This is the key difference from free choice, where ◇(A ∧ B) IS
    IE-excludable. Here, the alternatives lack a conjunction member
    entirely, so neither individual alternative can be consistently
    excluded from all MC-sets. -/
theorem nothing_ie (q : Prop' HomWorld)
    (hqIE : isInnocentlyExcludable homAlt homPrejacent q) : False := by
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
    (target : Prop' HomWorld)
    (htarget_alt : target ∈ homAlt)
    (R : Set (Prop' HomWorld))
    (hRcompat : isIICompatible homAlt homPrejacent R) (_hNotIn : target ∉ R) :
    isIICompatible homAlt homPrejacent (R ∪ {target}) := by
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
    (target : Prop' HomWorld)
    (htarget_alt : target ∈ homAlt) :
    isInnocentlyIncludable homAlt homPrejacent target := by
  constructor
  · exact htarget_alt
  · intro R ⟨hRcompat, hRmax⟩
    by_contra hNotIn
    have hext := extend_hom_II target htarget_alt R hRcompat hNotIn
    exact hNotIn (hRmax (R ∪ {target}) hext Set.subset_union_left
      (Set.mem_union_right R rfl))

/-- kellyLaughed is innocently includable. -/
theorem kellyLaughed_ii :
    isInnocentlyIncludable homAlt homPrejacent kellyLaughed :=
  target_in_hom_II kellyLaughed (by simp [homAlt])

/-- janeLaughed is innocently includable. -/
theorem janeLaughed_ii :
    isInnocentlyIncludable homAlt homPrejacent janeLaughed :=
  target_in_hom_II janeLaughed (by simp [homAlt])


-- ============================================================
-- SECTION 5: Main Theorems
-- ============================================================

/-- **Universality from Exh^{IE+II}**: exhaustified "the kids laughed"
    entails that both Kelly and Jane laughed.

    Exh^{IE+II}(∃-PL_C(laughed)(the kids)) ⊢ ∀ x ∈ {K,J}. laughed(x)

    This is the homogeneity derivation: the universal reading of a
    plural definite arises as an implicature, not from basic semantics.

    Compare `free_choice` in `InnocentInclusion.lean`. -/
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

@cite{bar-lev-2021} §5 derives non-maximal readings via **pruning**: when
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

In the fire hazard context (`NonMaximality.lean`), the distinction
between "all kids laughed" and "some kids laughed" is irrelevant,
so ALL individual alternatives are pruned. Exh is then vacuous and
the existential basic meaning surfaces directly.
-/

/-- Fully pruned alternative set: only the prejacent remains. -/
def prunedAlt : Set (Prop' HomWorld) := {someLaughed}

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
    exact hu (∼someLaughed) (hq.2 E hMC) (hu homPrejacent hMC.1.1)
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
    {φ, ∼janeLaughed} (witness: onlyKelly). So janeLaughed ∈ IE, and
    Exh^{IE}(φ) = someLaughed ∧ ¬janeLaughed. The 2-atom case yields
    *exclusive* readings under partial pruning, not weakened universals.
    True non-maximal readings require ≥3 atoms. -/
def partialPrunedAlt : Set (Prop' HomWorld) := {someLaughed, janeLaughed}

/-- MC-set for partialPrunedAlt: {homPrejacent, ∼janeLaughed}.
    With ALT = {someLaughed, janeLaughed}, the only compatible negation
    is ∼janeLaughed since ∼someLaughed contradicts the prejacent. -/
private theorem mc_partial :
    isMCSet partialPrunedAlt homPrejacent {homPrejacent, ∼janeLaughed} := by
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
        exact hu (∼someLaughed) hψ' (hu homPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ rfl

/-- someLaughed is not IE-excludable for partialPrunedAlt. -/
private theorem someLaughed_not_ie_partial :
    ¬isInnocentlyExcludable partialPrunedAlt homPrejacent someLaughed := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼someLaughed ∉ ({homPrejacent, ∼janeLaughed} : Set (Prop' HomWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mpr (congrFun h .onlyKelly) id trivial⟩
  exact hNotIn (hIE _ mc_partial)

/-- janeLaughed IS IE-excludable for partialPrunedAlt.
    ∼janeLaughed is in every MC-set: if E omits ∼janeLaughed, E can be
    extended (since ∼someLaughed is the only other option and contradicts φ),
    violating maximality. -/
private theorem janeLaughed_ie_partial :
    isInnocentlyExcludable partialPrunedAlt homPrejacent janeLaughed := by
  refine ⟨Set.mem_insert_of_mem _ rfl, fun E hMC => ?_⟩
  by_contra hNotIn
  have hcompat : isCompatible partialPrunedAlt homPrejacent (E ∪ {∼janeLaughed}) := by
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
            exact hu (∼someLaughed) hψE (hu homPrejacent hMC.1.1)
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
      have hmi : isMISet partialPrunedAlt homPrejacent {someLaughed} := by
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
            exact hu (∼janeLaughed)
              (Or.inl (Or.inr ⟨janeLaughed, janeLaughed_ie_partial, rfl⟩))
              (hu janeLaughed (Or.inr hr'))
      have hmem := hr.2 _ hmi
      simp only [Set.mem_singleton_iff] at hmem
      exact Eq.mpr (congrFun hmem .onlyKelly) trivial


-- ============================================================
-- SECTION 8: Bridges to Empirical Data
-- ============================================================

open Phenomena.Plurals.Homogeneity (switchesExample conjunctionExample)
open Phenomena.Plurals.Multiplicity (MonotonicityParallel pluralSingularParallel
  PluralTheory implicaturePrediction)

/-- Bar-Lev's theory predicts the full truth-value pattern for the
    switches example: universal in ALL, denial in NONE, gap in between.
    This matches the empirical judgments in `Homogeneity.lean`. -/
theorem matches_switches_data :
    switchesExample.positiveInAll = .clearlyTrue ∧
    switchesExample.negativeInAll = .clearlyFalse ∧
    switchesExample.positiveInNone = .clearlyFalse ∧
    switchesExample.negativeInNone = .clearlyTrue ∧
    switchesExample.positiveInGap = .neitherTrueNorFalse ∧
    switchesExample.negativeInGap = .neitherTrueNorFalse :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bar-Lev's theory is an implicature account: multiplicity inferences
    arise via the same mechanism as scalar implicatures, predicting
    uniform monotonicity sensitivity. -/
theorem is_implicature_account :
    implicaturePrediction.childrenComputeFewer = true ∧
    implicaturePrediction.multiplicityCorrelatesWithSI = true ∧
    implicaturePrediction.accountsForPolarityAsymmetry = true :=
  ⟨rfl, rfl, rfl⟩


-- ============================================================
-- SECTION 9: Comparison with Magri (2014)
-- ============================================================

/-!
## Comparison with @cite{magri-2014}

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

@cite{bar-lev-2021} §8.3: "all the kids laughed" does not display
homogeneity because `all` universally quantifies over the plurality,
eliminating the domain variable D. Without D, there are no subdomain
alternatives, so Exh^{IE+II} is vacuous — the universal reading is
the *basic* meaning, not an implicature. Since it's not an implicature,
it can't be weakened by pruning, which is why "all" blocks
non-maximality.

This connects to `Homogeneity.lean`'s `HomogeneityRemover.all` and to
@cite{kriz-2016}'s `removeGap` (which collapses the truth-value gap
into the negative extension — a different mechanism but the same
empirical prediction).
-/

open Phenomena.Plurals.Homogeneity (HomogeneityRemover allRemovesHomogeneity
  HomogeneityRemovalDatum)

/-- Bar-Lev's theory predicts that "all" removes homogeneity: the
    `allRemovesHomogeneity` datum records that the gap scenario yields
    `.clearlyFalse` for "all the doors are open" (vs `.neitherTrueNorFalse`
    for the bare plural). This aligns with Bar-Lev's mechanism: "all"
    eliminates subdomain alternatives, making the universal reading
    semantic (not an implicature) and therefore non-cancelable. -/
theorem all_removes_homogeneity_prediction :
    allRemovesHomogeneity.remover = .all ∧
    allRemovesHomogeneity.homogeneousJudgment = .neitherTrueNorFalse ∧
    allRemovesHomogeneity.preciseJudgment = .clearlyFalse :=
  ⟨rfl, rfl, rfl⟩

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
## Comparison with @cite{kriz-2016} (Trivalent Account)

@cite{kriz-2016} and @cite{kriz-spector-2021} derive homogeneity from
trivalent semantics: plural predication yields a three-valued denotation
(true/false/gap), and non-maximality arises when the gap is pragmatically
exploitable. The two accounts differ in:

| Property | Bar-Lev (implicature) | Križ (trivalent) |
|----------|----------------------|------------------|
| Basic meaning | existential (∃-PL) | trivalent (T/F/gap) |
| Universal reading | implicature (Exh^{IE+II}) | semantic (true extension) |
| Non-maximality | pruning alternatives | pragmatic gap exploitation |
| Positive/negative | **asymmetric** | symmetric |
| "All" removes gap | eliminates C variable | collapses gap (removeGap) |

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
    account (@cite{kriz-2016}), both arise from the gap structure. -/
theorem positive_negative_asymmetry :
    -- Positive: exhaustification is necessary (without it, universality fails)
    (∃ w, someLaughed w ∧ ¬(kellyLaughed w ∧ janeLaughed w)) ∧
    -- Negative: universality is automatic (no exhaustification)
    (∀ w, ¬someLaughed w → ¬kellyLaughed w ∧ ¬janeLaughed w) := by
  exact ⟨⟨.onlyKelly, trivial, fun ⟨_, h⟩ => h⟩, negative_universal⟩


end Phenomena.Plurals.Studies.BarLev2021
