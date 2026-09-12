import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Set.Card
import Linglib.Semantics.Mereology

/-!
# Landman (2020): Iceberg Semantics for Mass Nouns and Count Nouns

This file formalizes the core of [landman-2020], over a complete Boolean algebra: an
interpretation is an i-set, a body together with a base that generates it under sum, and the
mass–count distinction lives in the base, an i-set being count when its base is disjoint and
neat when its base is atomistic with disjoint base-atoms. Counting rests on disjointness rather
than on Boolean atomicity, the mathematical heart of the book: over a disjoint base, membership
in a sum is membership in the summands (`mem_iff_le_sSup_of_disjoint`), so every plurality is
recovered from its distribution set and the cardinality of a sum is the number of generators
summed (`card_sSup`). Count i-sets are neat (`ISet.IsCount.isNeat`), the Head Principle makes
mass and count compositional since a complex inherits disjointness from its head
(`ISet.headBase_disjoint`), pluralization leaves the base fixed and so preserves countness
(`ISet.plur_isCount`), number-neutral nouns such as *poultry* are neat but mass, and an atomless
base is mess.

## Implementation notes

The section locators are the book's: distribution sets and cardinality in the fifth chapter,
the Head Principle and its lemma, the white cats example that carries pluralization, the
definitions of count, mass, neat, and mess i-sets and their lemma in the sixth, the neat mass
nouns in the seventh, and the mess types in the eighth. The sum closure `star` takes sums of
arbitrary subsets, so the closure of the empty set is the null element, and the mereological
apparatus of overlap and disjointness is that of `Semantics/Mereology`, which
[sutton-filip-2021] shares. Neatness is the book's atomisticity of the base, which it
substitutes for the base-atomicity of [landman-2011] and [landman-2016].

## References

* [landman-2020]
* [landman-2011], [landman-2016], [sutton-filip-2021]
-/

namespace Landman2020

open Mereology (OverlapPred DisjointPred)

variable {B : Type*} [CompleteBooleanAlgebra B]

/-! ### Boolean background (ch. 2)

`star X` is closure under arbitrary sums — `*X = {b : ∃ Y ⊆ X, b = ⊔Y}`,
so `*∅ = {⊥}`. Mereological overlap is non-null meet. `plus Z` is `Z⁺`
(`Z` minus the null element); `atomsIn Z` is the set of minimal elements
of `Z⁺` — *Z-atoms*, relativized to `Z`, not Boolean atoms. -/

/-- Closure of `X` under arbitrary sums. -/
def star (X : Set B) : Set B := {b | ∃ Y ⊆ X, b = sSup Y}

theorem subset_star {X : Set B} : X ⊆ star X :=
  λ x hx => ⟨{x}, Set.singleton_subset_iff.mpr hx, sSup_singleton.symm⟩

theorem sSup_mem_star {X Y : Set B} (h : Y ⊆ X) : sSup Y ∈ star X :=
  ⟨Y, h, rfl⟩

theorem star_mono {X Y : Set B} (h : X ⊆ Y) : star X ⊆ star Y :=
  λ _ ⟨Z, hZ, hb⟩ => ⟨Z, hZ.trans h, hb⟩

theorem sSup_star_eq {X : Set B} : sSup (star X) = sSup X :=
  le_antisymm
    (sSup_le λ _ ⟨_, hY, hb⟩ => hb ▸ sSup_le_sSup hY)
    (sSup_le_sSup subset_star)

theorem star_empty : star (∅ : Set B) = {⊥} := by
  ext b
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [Set.subset_empty_iff.mp hY, sSup_empty]
    rfl
  · rintro rfl
    exact ⟨∅, Set.Subset.rfl, sSup_empty.symm⟩

/-- `star` is idempotent: a sum of sums of `X`-elements is a sum of
    `X`-elements. -/
theorem star_star {X : Set B} : star (star X) = star X := by
  refine Set.Subset.antisymm ?_ subset_star
  rintro b ⟨Y, hY, rfl⟩
  classical
  choose Z hZsub hZsup using λ y (hy : y ∈ Y) => hY hy
  refine ⟨⋃ (y : B) (hy : y ∈ Y), Z y hy, ?_, le_antisymm ?_ ?_⟩
  · simp only [Set.iUnion_subset_iff]
    exact hZsub
  · refine sSup_le λ y hy => ?_
    rw [hZsup y hy]
    refine sSup_le_sSup λ w hw => ?_
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hw⟩⟩
  · refine sSup_le λ w hw => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hw
    obtain ⟨hyY, hwZ⟩ := Set.mem_iUnion.mp hy
    calc w ≤ sSup (Z y hyY) := le_sSup hwZ
      _ = y := (hZsup y hyY).symm
      _ ≤ sSup Y := le_sSup hyY

/-- Mereological overlap: a non-null common part. -/
def mOverlap (x y : B) : Prop := x ⊓ y ≠ ⊥

/-- `Z⁺`: `Z` minus the null element. -/
def plus (Z : Set B) : Set B := Z \ {⊥}

/-- The `Z`-atoms: minimal elements of `Z⁺` (ch. 2; relativized to
    `Z`, not Boolean atoms). -/
def atomsIn (Z : Set B) : Set B :=
  {z ∈ plus Z | ∀ y ∈ plus Z, y ≤ z → y = z}

/-- `Z` is atomistic: every element of `Z⁺` is the sum of the `Z`-atoms
    below it (the book's `ATOM_{Z,b} = (b] ∩ ATOM_Z` and `b = ⊔ATOM_{Z,b}`). -/
def Atomistic (Z : Set B) : Prop :=
  ∀ b ∈ plus Z, b = sSup (Set.Iic b ∩ atomsIn Z)

/-- In a ⊥-free disjoint set everything is minimal: `ATOM_Z = Z`
    (§6.1.2 Lemma, step 2: a disjoint base is its own set of
    base-atoms). -/
theorem atomsIn_eq_of_disjoint {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) : atomsIn Z = Z := by
  ext z
  constructor
  · rintro ⟨⟨hz, _⟩, _⟩
    exact hz
  · intro hz
    have hzbot : z ∉ ({⊥} : Set B) :=
      λ h => hbot (Set.mem_singleton_iff.mp h ▸ hz)
    refine ⟨⟨hz, hzbot⟩, ?_⟩
    rintro y ⟨hy, hybot⟩ hle
    by_contra hne
    refine hZ ⟨y, hy, z, hz, hne, ?_⟩
    show y ⊓ z ≠ ⊥
    rw [inf_eq_left.mpr hle]
    exact λ h => hybot (Set.mem_singleton_iff.mpr h)

/-! ### Counting from disjointness (ch. 5)

Mountain semantics counts in terms of Boolean atoms; Iceberg semantics
observes that **disjointness** of the base is what makes counting
correct. The distribution set `D_Z(x) = (x] ∩ Z` recovers `x` exactly
when `Z` is disjoint — by frame distributivity, an element of a disjoint
`Z` is below a sum of `Z`-elements only by being one of them. -/

/-- The distribution set `D_Z(x) = (x] ∩ Z` (§5.2). -/
def partsIn (Z : Set B) (x : B) : Set B := {z ∈ Z | z ≤ x}

/-- **Membership in a sum is membership in the summands** (for disjoint,
    ⊥-free `Z`): `z ≤ ⊔Y ↔ z ∈ Y`. The frame law
    `z ⊓ ⊔Y = ⨆ y ∈ Y, z ⊓ y` reduces a stray `z` to a sum of nulls. -/
theorem mem_iff_le_sSup_of_disjoint {Z Y : Set B}
    (hZ : DisjointPred mOverlap Z) (hbot : ⊥ ∉ Z) (hY : Y ⊆ Z)
    {z : B} (hz : z ∈ Z) : z ≤ sSup Y ↔ z ∈ Y := by
  refine ⟨λ hle => ?_, λ h => le_sSup h⟩
  by_contra hzY
  have hzbot : z ≠ ⊥ := λ h => hbot (h ▸ hz)
  apply hzbot
  have h1 : z = z ⊓ sSup Y := (inf_eq_left.mpr hle).symm
  rw [inf_sSup_eq] at h1
  rw [h1]
  refine le_antisymm (iSup_le λ y => iSup_le λ hy => le_of_eq ?_) bot_le
  by_contra hne
  exact hZ ⟨z, hz, y, hY hy, λ he => hzY (he ▸ hy), hne⟩

/-- The distribution set of a sum of `Z`-elements is exactly the set
    summed: counting reads the parts off correctly. -/
theorem partsIn_sSup {Z Y : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) (hY : Y ⊆ Z) : partsIn Z (sSup Y) = Y := by
  ext z
  simp only [partsIn, Set.mem_sep_iff]
  constructor
  · rintro ⟨hz, hle⟩
    exact (mem_iff_le_sSup_of_disjoint hZ hbot hY hz).mp hle
  · intro hz
    exact ⟨hY hz, le_sSup hz⟩

/-- Every element of `*Z` is the sum of its distribution set. -/
theorem sSup_partsIn {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) {x : B} (hx : x ∈ star Z) :
    sSup (partsIn Z x) = x := by
  obtain ⟨Y, hY, rfl⟩ := hx
  rw [partsIn_sSup hZ hbot hY]

/-- Distribution is injective on `*Z`: a plurality is determined by what
    it distributes to. **Disjointness, not atomicity, is what counting
    needs** — the central claim of Iceberg semantics, as a theorem. -/
theorem partsIn_injOn {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) : Set.InjOn (partsIn Z) (star Z) :=
  λ x hx x' hx' h => by
    rw [← sSup_partsIn hZ hbot hx, ← sSup_partsIn hZ hbot hx', h]

/-- `card_Z(x) = |D_Z(x)|` (§5.2; presupposes `Z` disjoint, which is
    what `partsIn_injOn` certifies as sufficient). -/
noncomputable def card (Z : Set B) (x : B) : ℕ := (partsIn Z x).ncard

/-! ### Cardinality over a disjoint base -/

/-- Over a disjoint base, the cardinality of a sum is the number of generators summed. -/
theorem card_sSup {Z Y : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) (hY : Y ⊆ Z) : card Z (sSup Y) = Y.ncard := by
  rw [card, partsIn_sSup hZ hbot hY]

/-- A generator counts as one. -/
theorem card_self {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) {z : B} (hz : z ∈ Z) : card Z z = 1 := by
  have h := card_sSup hZ hbot (Set.singleton_subset_iff.mpr hz)
  rw [sSup_singleton] at h
  rw [h, Set.ncard_singleton]

/-- A sum of two distinct generators counts as two. -/
theorem card_pair {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) {z₁ z₂ : B} (h₁ : z₁ ∈ Z) (h₂ : z₂ ∈ Z)
    (hne : z₁ ≠ z₂) : card Z (z₁ ⊔ z₂) = 2 := by
  have h := card_sSup hZ hbot (Y := {z₁, z₂}) (by
    rintro y (rfl | rfl) <;> assumption)
  rw [sSup_pair] at h
  rw [h, Set.ncard_pair hne]

/-! ### I-sets and count – mass – neat – mess (§6.1) -/

/-- An i-set: a body and a base that generates it under sum
    (§5.1/§6.1.2: `body(X) ⊆ *base(X)` and `⊔body(X) = ⊔base(X)`). -/
structure ISet (B : Type*) [CompleteBooleanAlgebra B] where
  /-- The standard denotation. -/
  body : Set B
  /-- The generating set: the things that count as one. -/
  base : Set B
  body_subset_star : body ⊆ star base
  sSup_body_eq : sSup body = sSup base

namespace ISet

/-- The singular null i-set ⟨∅, ∅⟩ (§6.1.2 Lemma). -/
def nullEmpty : ISet B :=
  ⟨∅, ∅, Set.empty_subset _, rfl⟩

/-- The plural null i-set ⟨{⊥}, ∅⟩ (§6.1.2 Lemma; `*∅ = {⊥}`). -/
def nullBot : ISet B :=
  ⟨{⊥}, ∅, by simp [star_empty], by rw [sSup_singleton, sSup_empty]⟩

/-- An i-set is null iff its base is empty. -/
def IsNull (X : ISet B) : Prop := X.base = ∅

/-- Count: the base is disjoint (§6.1.2). -/
def IsCount (X : ISet B) : Prop := DisjointPred mOverlap X.base

/-- Mass: if non-null then not count (§6.1.2; the null i-sets are
    both count and mass). -/
def IsMass (X : ISet B) : Prop := ¬X.IsNull → ¬X.IsCount

/-- Neat: the base is atomistic with disjoint base-atoms — the book's
    §6.1.2 definition, which explicitly replaces the base-atomicity of
    [landman-2011]/[landman-2016] by base-atomisticity. -/
def IsNeat (X : ISet B) : Prop :=
  Atomistic X.base ∧ DisjointPred mOverlap (atomsIn X.base)

/-- Mess: if non-null then not neat. -/
def IsMess (X : ISet B) : Prop := ¬X.IsNull → ¬X.IsNeat

/-- An empty-based i-set has body `∅` or `{⊥}`: the two null i-sets are
    the only ones (§6.1.2 Lemma). -/
theorem body_eq_of_base_empty (X : ISet B) (h : X.base = ∅) :
    X.body = ∅ ∨ X.body = {⊥} := by
  have hsub : X.body ⊆ {⊥} := by
    rw [← star_empty, ← h]
    exact X.body_subset_star
  exact Set.subset_singleton_iff_eq.mp hsub

/-- **Count i-sets are neat** (§6.1.2 Lemma, claim 2): a ⊥-free
    disjoint base is its own set of base-atoms, and trivially
    atomistic. -/
theorem IsCount.isNeat {X : ISet B} (hX : X.IsCount)
    (hbot : ⊥ ∉ X.base) : X.IsNeat := by
  have hatoms : atomsIn X.base = X.base := atomsIn_eq_of_disjoint hX hbot
  constructor
  · intro b hb
    rw [hatoms]
    exact le_antisymm (le_sSup ⟨le_refl b, hb.1⟩) (sSup_le λ y hy => hy.1)
  · rw [hatoms]
    exact hX

/-! ### The Head Principle (§5.3)

`base(α) = (body(α)] ∩ base(H)`: the base of a complex NP is the base of
its *head*, restricted to the parts of the complex's body. The
accompanying Lemma is one line — `base(α) ⊆ base(H)` — and gives the
compositionality of mass/count: a complex NP with a count head is
count. -/

/-- The head-principle base: the head's base elements that are parts of
    the complex's body. -/
def headBase (bodyC : Set B) (H : ISet B) : Set B :=
  {b ∈ H.base | b ≤ sSup bodyC}

/-- §5.3 Lemma, verbatim: "If `base(H)` is disjoint then `base(α)` is
    disjoint. Proof: `base(α) ⊆ base(H)`. ∎" -/
theorem headBase_disjoint {bodyC : Set B} {H : ISet B}
    (hH : DisjointPred mOverlap H.base) :
    DisjointPred mOverlap (headBase bodyC H) :=
  Mereology.DisjointPred.anti mOverlap (Set.sep_subset _ _) hH

/-! ### Pluralization (§5.4, the white cats example)

`plur(P) = ⟨*body(P), (*body(P)] ∩ base(P)⟩`. Since
`⊔*body(P) = ⊔body(P) = ⊔base(P)`, the head-principle restriction is
vacuous: pluralization leaves the base fixed — in the worked *white cats*
example, `base(WHITE CATS) = base(WHITE CAT) = CAT ∩ WHITE`. -/

/-- Pluralization: close the body under sum; the base stays. -/
def plur (P : ISet B) : ISet B where
  body := star P.body
  base := P.base
  body_subset_star := λ b hb => by
    rw [← star_star (X := P.base)]
    exact star_mono P.body_subset_star hb
  sSup_body_eq := by rw [sSup_star_eq, P.sSup_body_eq]

/-- The book's `(*body(P)] ∩ base(P)` is just `base(P)`: every base
    element is a part of the total body, so the head-principle
    restriction is vacuous under pluralization. -/
theorem plur_base_eq_headBase (P : ISet B) :
    (P.plur).base = headBase (P.plur).body P := by
  unfold plur headBase
  ext b
  simp only [Set.mem_sep_iff, iff_self_and]
  intro hb
  rw [sSup_star_eq, P.sSup_body_eq]
  exact le_sSup hb

/-- Pluralization preserves countness: the mass/count nature of a noun is
    unaffected by number morphology — it lives in the base. -/
theorem plur_isCount {P : ISet B} (hP : P.IsCount) : (P.plur).IsCount :=
  hP

end ISet

/-! ### The noun classes (ch. 7–8)

Number-neutral neat mass nouns (*poultry*, *livestock*, §7.1): the
singular/plural distinction is not articulated — `⟨*X₀, *X₀⟩` for a
disjoint `X₀` (the book's `DOM-BIRD`). The base overlaps (so: mass), but its
atoms are exactly `X₀` (so: neat). Mess mass nouns (*water*, §8.1.5): the
base has no minimal elements at all, so atomisticity fails outright. -/

/-- A sum-closure properly overlaps once there are two distinct ⊥-free
    generators: `x₀` and `x₀ ⊔ x₁` are distinct members of `*X₀` sharing
    the part `x₀`. Hence number-neutral nouns are **mass**. -/
theorem star_overlapPred {X₀ : Set B} (hbot : ⊥ ∉ X₀)
    (hdisj : DisjointPred mOverlap X₀) {x₀ x₁ : B}
    (h₀ : x₀ ∈ X₀) (h₁ : x₁ ∈ X₀) (hne : x₀ ≠ x₁) :
    OverlapPred mOverlap (star X₀) := by
  have hsup : x₀ ⊔ x₁ ∈ star X₀ := by
    refine ⟨{x₀, x₁}, ?_, sSup_pair.symm⟩
    rintro y (rfl | rfl) <;> assumption
  refine ⟨x₀, subset_star h₀, x₀ ⊔ x₁, hsup, ?_, ?_⟩
  · intro he
    have hle : x₁ ≤ x₀ := he ▸ le_sup_right
    refine hdisj ⟨x₁, h₁, x₀, h₀, λ h => hne h.symm, ?_⟩
    show x₁ ⊓ x₀ ≠ ⊥
    rw [inf_eq_left.mpr hle]
    exact λ h => hbot (h ▸ h₁)
  · show x₀ ⊓ (x₀ ⊔ x₁) ≠ ⊥
    rw [inf_sup_self]
    exact λ h => hbot (h ▸ h₀)

/-- The number-neutral neat mass i-set `⟨*X₀, *X₀⟩` (§7.1: *poultry*
    with `X₀ = DOM-BIRD`). -/
def numberNeutral (X₀ : Set B) : ISet B where
  body := star X₀
  base := star X₀
  body_subset_star := subset_star
  sSup_body_eq := rfl

/-- The atoms of a sum-closure are the generators: for ⊥-free disjoint
    `X₀`, `ATOM_{*X₀} = X₀`. -/
theorem atomsIn_star_of_disjoint {X₀ : Set B}
    (hdisj : DisjointPred mOverlap X₀) (hbot : ⊥ ∉ X₀) :
    atomsIn (star X₀) = X₀ := by
  ext z
  constructor
  · rintro ⟨⟨hzstar, hzbot⟩, hmin⟩
    obtain ⟨Y, hY, rfl⟩ := hzstar
    obtain ⟨y, hyY, hybot⟩ : ∃ y ∈ Y, y ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hzbot (Set.mem_singleton_iff.mpr (sSup_eq_bot.mpr hcon))
    have heq : y = sSup Y :=
      hmin y ⟨subset_star (hY hyY),
        λ h => hybot (Set.mem_singleton_iff.mp h)⟩ (le_sSup hyY)
    exact heq ▸ hY hyY
  · intro hz
    have hzbot : z ∉ ({⊥} : Set B) :=
      λ h => hbot (Set.mem_singleton_iff.mp h ▸ hz)
    refine ⟨⟨subset_star hz, hzbot⟩, ?_⟩
    rintro y ⟨hystar, hybot⟩ hle
    obtain ⟨Y, hY, rfl⟩ := hystar
    obtain ⟨x', hx'Y, hx'bot⟩ : ∃ x' ∈ Y, x' ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hybot (Set.mem_singleton_iff.mpr (sSup_eq_bot.mpr hcon))
    have hx'le : x' ≤ z := le_trans (le_sSup hx'Y) hle
    have hx'z : x' = z := by
      by_contra hne
      refine hdisj ⟨x', hY hx'Y, z, hz, hne, ?_⟩
      show x' ⊓ z ≠ ⊥
      rw [inf_eq_left.mpr hx'le]
      exact hx'bot
    exact le_antisymm hle (hx'z ▸ le_sSup hx'Y)

/-- Number-neutral nouns are **neat**: the base `*X₀` overlaps, but it is
    atomistic over the disjoint generator set `X₀` (§7.1: *poultry*
    is a neat mass i-set). -/
theorem numberNeutral_isNeat {X₀ : Set B}
    (hdisj : DisjointPred mOverlap X₀) (hbot : ⊥ ∉ X₀) :
    (numberNeutral X₀).IsNeat := by
  have hatoms : atomsIn (star X₀) = X₀ :=
    atomsIn_star_of_disjoint hdisj hbot
  refine ⟨?_, ?_⟩
  · rintro b ⟨hbstar, hbbot⟩
    obtain ⟨Y, hY, rfl⟩ := hbstar
    show sSup Y = sSup (Set.Iic (sSup Y) ∩ atomsIn (star X₀))
    rw [hatoms]
    refine le_antisymm (sSup_le λ y hy => ?_) (sSup_le ?_)
    · rcases eq_or_ne y ⊥ with rfl | hyne
      · exact bot_le
      · exact le_sSup ⟨le_sSup hy, hY hy⟩
    · rintro y ⟨hyle, _⟩
      exact hyle
  · show DisjointPred mOverlap (atomsIn (star X₀))
    rw [hatoms]
    exact hdisj

/-- A non-trivial atomless base is **mess** (§8.1.5: *water*'s base
    has no minimal elements — space can always be shaved off a region
    containing a molecule — so atomisticity fails). -/
theorem not_neat_of_atomless {X : ISet B} (h : atomsIn X.base = ∅)
    {b : B} (hb : b ∈ X.base) (hbne : b ≠ ⊥) : ¬X.IsNeat := by
  rintro ⟨hatomistic, -⟩
  have hbplus : b ∈ plus X.base :=
    ⟨hb, λ h' => hbne (Set.mem_singleton_iff.mp h')⟩
  have := hatomistic b hbplus
  rw [h, Set.inter_empty, sSup_empty] at this
  exact hbne this

end Landman2020
