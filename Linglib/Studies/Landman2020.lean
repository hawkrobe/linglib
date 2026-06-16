import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Set.Card
import Linglib.Semantics.Mereology

/-!
# Landman (2020) — Iceberg Semantics for Mass Nouns and Count Nouns
[landman-2020]

Formalizes the formal core of:

  Landman, F. (2020). *Iceberg Semantics for Mass Nouns and Count Nouns:
  A New Framework for Boolean Semantics*. Studies in Linguistics and
  Philosophy 105. Springer.

## The framework

Mountain semantics (Link-style Boolean semantics, [link-1983]) grounds
counting in *atomicity*: singular count nouns denote sets of Boolean
atoms. Iceberg semantics replaces this vertical picture with a horizontal
one: every interpretation is an **i-set** ⟨body, base⟩ where the base
*generates* the body under sum, and the mass/count distinction lives in
the base — **count iff the base is disjoint** (§6.1.2); mass and count
are perspectives on the same stuff, and Boolean atoms play no role.

## Main results (all generic over a complete Boolean algebra)

* `ISet`, the two null i-sets, and `ISet.body_eq_of_base_empty` (the
  nulls are exactly the empty-based i-sets — his §6.1.2 Lemma).
* **Counting is correct given disjointness, not atomicity** (the
  mathematical heart of ch. 5): for a disjoint, ⊥-free `Z`, membership in
  a sum of `Z`-elements is membership in the summands
  (`mem_iff_le_sSup_of_disjoint`, by frame distributivity), so every
  element of `*Z` is recovered from its distribution set
  (`sSup_partsIn`), the distribution map is injective (`partsIn_injOn`),
  and `card` counts correctly.
* `atomsIn_eq_of_disjoint` (a ⊥-free disjoint set is all-minimal) and the
  §6.1.2 Lemma `ISet.IsCount.isNeat`: **count i-sets are neat** — with
  the book's *atomisticity* definition of neat, which §6.1.2 explicitly
  substitutes for the base-atomicity of [landman-2011]/[landman-2016].
* **The Head Principle** (§5.3): `base(α) = (body α] ∩ base(H)`, and its
  Lemma — disjointness inherits from head to complex
  (`ISet.headBase_disjoint`) — making mass/count *compositional*.
* `ISet.plur` leaves the base fixed (`ISet.plur_base_eq_headBase`), so
  pluralization preserves countness (`ISet.plur_isCount`) — the generic
  content of the §5.4 *white cats* computation, where
  `(*body(P)] ∩ base(P) = base(P)`.
* The noun classes: number-neutral neat mass nouns (*poultry*,
  `⟨*X₀, *X₀⟩`, §7.1) are neat (`numberNeutral_isNeat`) but their base
  overlaps (`star_overlapPred`, hence mass); atomless bases are mess
  (*water*, §8.1.5: `not_neat_of_atomless`).

## Connections

* The disjointness machinery is `Semantics/Mereology`'s
  `OverlapPred`/`DisjointPred`/`nullSchema` (shared with
  [sutton-filip-2021], whose counting bases are this book's bases and
  whose individuation schemas select among its perspectives —
  `Mereology.IsMaxDisjointIn`).
* Mountain semantics' pluralization `*` is the Link closure of
  `Semantics/Plurality/Algebra.lean`; Iceberg's `star` is its
  complete-join generalization (sums of arbitrary subsets, so
  `*∅ = {⊥}`).
* The base-perspective on mass/count is the semantic ground for keeping
  countability out of the `Number` value space
  (`Features/Number/Basic.lean`): count/mass classifies *bases*; number
  values classify referents.
-/

set_option autoImplicit false

namespace Landman2020

open Mereology (OverlapPred DisjointPred)

variable {B : Type*} [CompleteBooleanAlgebra B]

/-! ### Boolean background (his ch. 2)

`star X` is closure under arbitrary sums — `*X = {b : ∃ Y ⊆ X, b = ⊔Y}`,
so `*∅ = {⊥}`. Mereological overlap is non-null meet. `plus Z` is `Z⁺`
(`Z` minus the null element); `atomsIn Z` is the set of minimal elements
of `Z⁺` — *Z-atoms*, relativized to `Z`, not Boolean atoms. -/

/-- Closure of `X` under arbitrary sums. -/
def star (X : Set B) : Set B := {b | ∃ Y ⊆ X, b = sSup Y}

theorem subset_star {X : Set B} : X ⊆ star X :=
  fun x hx => ⟨{x}, Set.singleton_subset_iff.mpr hx, sSup_singleton.symm⟩

theorem sSup_mem_star {X Y : Set B} (h : Y ⊆ X) : sSup Y ∈ star X :=
  ⟨Y, h, rfl⟩

theorem star_mono {X Y : Set B} (h : X ⊆ Y) : star X ⊆ star Y :=
  fun _ ⟨Z, hZ, hb⟩ => ⟨Z, hZ.trans h, hb⟩

theorem sSup_star_eq {X : Set B} : sSup (star X) = sSup X :=
  le_antisymm
    (sSup_le fun _ ⟨Y, hY, hb⟩ => hb ▸ sSup_le_sSup hY)
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
  choose Z hZsub hZsup using fun y (hy : y ∈ Y) => hY hy
  refine ⟨⋃ (y : B) (hy : y ∈ Y), Z y hy, ?_, le_antisymm ?_ ?_⟩
  · simp only [Set.iUnion_subset_iff]
    exact hZsub
  · refine sSup_le fun y hy => ?_
    rw [hZsup y hy]
    refine sSup_le_sSup fun w hw => ?_
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hw⟩⟩
  · refine sSup_le fun w hw => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hw
    obtain ⟨hyY, hwZ⟩ := Set.mem_iUnion.mp hy
    calc w ≤ sSup (Z y hyY) := le_sSup hwZ
      _ = y := (hZsup y hyY).symm
      _ ≤ sSup Y := le_sSup hyY

/-- Mereological overlap: a non-null common part. -/
def mOverlap (x y : B) : Prop := x ⊓ y ≠ ⊥

/-- `Z⁺`: `Z` minus the null element. -/
def plus (Z : Set B) : Set B := Z \ {⊥}

/-- The `Z`-atoms: minimal elements of `Z⁺` (his ch. 2; relativized to
    `Z`, not Boolean atoms). -/
def atomsIn (Z : Set B) : Set B :=
  {z ∈ plus Z | ∀ y ∈ plus Z, y ≤ z → y = z}

/-- `Z` is atomistic: every element of `Z⁺` is the sum of the `Z`-atoms
    below it (his `ATOM_{Z,b} = (b] ∩ ATOM_Z` and `b = ⊔ATOM_{Z,b}`). -/
def Atomistic (Z : Set B) : Prop :=
  ∀ b ∈ plus Z, b = sSup (Set.Iic b ∩ atomsIn Z)

/-- In a ⊥-free disjoint set everything is minimal: `ATOM_Z = Z`
    (his §6.1.2 Lemma, step 2: a disjoint base is its own set of
    base-atoms). -/
theorem atomsIn_eq_of_disjoint {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) : atomsIn Z = Z := by
  ext z
  constructor
  · rintro ⟨⟨hz, _⟩, _⟩
    exact hz
  · intro hz
    have hzbot : z ∉ ({⊥} : Set B) :=
      fun h => hbot (Set.mem_singleton_iff.mp h ▸ hz)
    refine ⟨⟨hz, hzbot⟩, ?_⟩
    rintro y ⟨hy, hybot⟩ hle
    by_contra hne
    refine hZ ⟨y, hy, z, hz, hne, ?_⟩
    show y ⊓ z ≠ ⊥
    rw [inf_eq_left.mpr hle]
    exact fun h => hybot (Set.mem_singleton_iff.mpr h)

/-! ### Counting from disjointness (his ch. 5)

Mountain semantics counts in terms of Boolean atoms; Iceberg semantics
observes that **disjointness** of the base is what makes counting
correct. The distribution set `D_Z(x) = (x] ∩ Z` recovers `x` exactly
when `Z` is disjoint — by frame distributivity, an element of a disjoint
`Z` is below a sum of `Z`-elements only by being one of them. -/

/-- The distribution set `D_Z(x) = (x] ∩ Z` (his §5.2). -/
def partsIn (Z : Set B) (x : B) : Set B := {z ∈ Z | z ≤ x}

/-- **Membership in a sum is membership in the summands** (for disjoint,
    ⊥-free `Z`): `z ≤ ⊔Y ↔ z ∈ Y`. The frame law
    `z ⊓ ⊔Y = ⨆ y ∈ Y, z ⊓ y` reduces a stray `z` to a sum of nulls. -/
theorem mem_iff_le_sSup_of_disjoint {Z Y : Set B}
    (hZ : DisjointPred mOverlap Z) (hbot : ⊥ ∉ Z) (hY : Y ⊆ Z)
    {z : B} (hz : z ∈ Z) : z ≤ sSup Y ↔ z ∈ Y := by
  refine ⟨fun hle => ?_, fun h => le_sSup h⟩
  by_contra hzY
  have hzbot : z ≠ ⊥ := fun h => hbot (h ▸ hz)
  apply hzbot
  have h1 : z = z ⊓ sSup Y := (inf_eq_left.mpr hle).symm
  rw [inf_sSup_eq] at h1
  rw [h1]
  refine le_antisymm (iSup_le fun y => iSup_le fun hy => le_of_eq ?_) bot_le
  by_contra hne
  exact hZ ⟨z, hz, y, hY hy, fun he => hzY (he ▸ hy), hne⟩

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
  fun x hx x' hx' h => by
    rw [← sSup_partsIn hZ hbot hx, ← sSup_partsIn hZ hbot hx', h]

/-- `card_Z(x) = |D_Z(x)|` (his §5.2; presupposes `Z` disjoint, which is
    what `partsIn_injOn` certifies as sufficient). -/
noncomputable def card (Z : Set B) (x : B) : ℕ := (partsIn Z x).ncard

/-! ### Exact numbers: the junction with [harbour-2014]

[harbour-2014] (30) characterizes the exact number values over a
generating set of atoms as cardinality classes — singular `|x| = 1`,
dual `|x| = 2`, trial `|x| = 3` — with (31) the successor-like function
that extends them. This book's `card` certifies precisely that counting:
over a disjoint base, the cardinality of a sum is the number of
generators summed. Two frameworks formalized from their own primary
sources, agreeing on one counting operation by theorem. -/

/-- Over a disjoint base, the Landman cardinality of a sum is the number
    of generators summed — [harbour-2014]'s (30) cardinality classes are
    `card`-classes. -/
theorem card_sSup {Z Y : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) (hY : Y ⊆ Z) : card Z (sSup Y) = Y.ncard := by
  rw [card, partsIn_sSup hZ hbot hY]

/-- A generator counts as one (Harbour's singular: `|x| = 1`). -/
theorem card_self {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) {z : B} (hz : z ∈ Z) : card Z z = 1 := by
  have h := card_sSup hZ hbot (Set.singleton_subset_iff.mpr hz)
  rw [sSup_singleton] at h
  rw [h, Set.ncard_singleton]

/-- A sum of two distinct generators counts as two (Harbour's dual:
    `|x| = 2` — the value `Number.interp` assigns the minimal
    non-atoms). -/
theorem card_pair {Z : Set B} (hZ : DisjointPred mOverlap Z)
    (hbot : ⊥ ∉ Z) {z₁ z₂ : B} (h₁ : z₁ ∈ Z) (h₂ : z₂ ∈ Z)
    (hne : z₁ ≠ z₂) : card Z (z₁ ⊔ z₂) = 2 := by
  have h := card_sSup hZ hbot (Y := {z₁, z₂}) (by
    rintro y (rfl | rfl) <;> assumption)
  rw [sSup_pair] at h
  rw [h, Set.ncard_pair hne]

/-! ### I-sets and count – mass – neat – mess (his §6.1) -/

/-- An i-set: a body and a base that generates it under sum
    (his §5.1/§6.1.2: `body(X) ⊆ *base(X)` and `⊔body(X) = ⊔base(X)`). -/
structure ISet (B : Type*) [CompleteBooleanAlgebra B] where
  /-- The standard denotation. -/
  body : Set B
  /-- The generating set: the things that count as one. -/
  base : Set B
  body_subset_star : body ⊆ star base
  sSup_body_eq : sSup body = sSup base

namespace ISet

/-- The singular null i-set ⟨∅, ∅⟩ (his §6.1.2 Lemma). -/
def nullEmpty : ISet B :=
  ⟨∅, ∅, Set.empty_subset _, rfl⟩

/-- The plural null i-set ⟨{⊥}, ∅⟩ (his §6.1.2 Lemma; `*∅ = {⊥}`). -/
def nullBot : ISet B :=
  ⟨{⊥}, ∅, by simp [star_empty], by rw [sSup_singleton, sSup_empty]⟩

/-- An i-set is null iff its base is empty. -/
def IsNull (X : ISet B) : Prop := X.base = ∅

/-- Count: the base is disjoint (his §6.1.2). -/
def IsCount (X : ISet B) : Prop := DisjointPred mOverlap X.base

/-- Mass: if non-null then not count (his §6.1.2; the null i-sets are
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
    the only ones (his §6.1.2 Lemma). -/
theorem body_eq_of_base_empty (X : ISet B) (h : X.base = ∅) :
    X.body = ∅ ∨ X.body = {⊥} := by
  have hsub : X.body ⊆ {⊥} := by
    rw [← star_empty, ← h]
    exact X.body_subset_star
  exact Set.subset_singleton_iff_eq.mp hsub

/-- **Count i-sets are neat** (his §6.1.2 Lemma, claim 2): a ⊥-free
    disjoint base is its own set of base-atoms, and trivially
    atomistic. -/
theorem IsCount.isNeat {X : ISet B} (hX : X.IsCount)
    (hbot : ⊥ ∉ X.base) : X.IsNeat := by
  have hatoms : atomsIn X.base = X.base := atomsIn_eq_of_disjoint hX hbot
  constructor
  · intro b hb
    rw [hatoms]
    exact le_antisymm (le_sSup ⟨le_refl b, hb.1⟩) (sSup_le fun y hy => hy.1)
  · rw [hatoms]
    exact hX

/-! ### The Head Principle (his §5.3)

`base(α) = (body(α)] ∩ base(H)`: the base of a complex NP is the base of
its *head*, restricted to the parts of the complex's body. The
accompanying Lemma is one line — `base(α) ⊆ base(H)` — and gives the
compositionality of mass/count: a complex NP with a count head is
count. -/

/-- The head-principle base: the head's base elements that are parts of
    the complex's body. -/
def headBase (bodyC : Set B) (H : ISet B) : Set B :=
  {b ∈ H.base | b ≤ sSup bodyC}

/-- His §5.3 Lemma, verbatim: "If `base(H)` is disjoint then `base(α)` is
    disjoint. Proof: `base(α) ⊆ base(H)`. ∎" -/
theorem headBase_disjoint {bodyC : Set B} {H : ISet B}
    (hH : DisjointPred mOverlap H.base) :
    DisjointPred mOverlap (headBase bodyC H) :=
  Mereology.DisjointPred.anti mOverlap (Set.sep_subset _ _) hH

/-! ### Pluralization (his §5.4)

`plur(P) = ⟨*body(P), (*body(P)] ∩ base(P)⟩`. Since
`⊔*body(P) = ⊔body(P) = ⊔base(P)`, the head-principle restriction is
vacuous: pluralization leaves the base fixed — in the worked *white cats*
example, `base(WHITE CATS) = base(WHITE CAT) = CAT ∩ WHITE`. -/

/-- Pluralization: close the body under sum; the base stays. -/
def plur (P : ISet B) : ISet B where
  body := star P.body
  base := P.base
  body_subset_star := fun b hb => by
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

/-! ### The noun classes (his ch. 7–8)

Number-neutral neat mass nouns (*poultry*, *livestock*, §7.1): the
singular/plural distinction is not articulated — `⟨*X₀, *X₀⟩` for a
disjoint `X₀` (his `DOM-BIRD`). The base overlaps (so: mass), but its
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
    refine hdisj ⟨x₁, h₁, x₀, h₀, fun h => hne h.symm, ?_⟩
    show x₁ ⊓ x₀ ≠ ⊥
    rw [inf_eq_left.mpr hle]
    exact fun h => hbot (h ▸ h₁)
  · show x₀ ⊓ (x₀ ⊔ x₁) ≠ ⊥
    rw [inf_sup_self]
    exact fun h => hbot (h ▸ h₀)

/-- The number-neutral neat mass i-set `⟨*X₀, *X₀⟩` (his §7.1: *poultry*
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
      push_neg at hcon
      exact hzbot (Set.mem_singleton_iff.mpr (sSup_eq_bot.mpr hcon))
    have heq : y = sSup Y :=
      hmin y ⟨subset_star (hY hyY),
        fun h => hybot (Set.mem_singleton_iff.mp h)⟩ (le_sSup hyY)
    exact heq ▸ hY hyY
  · intro hz
    have hzbot : z ∉ ({⊥} : Set B) :=
      fun h => hbot (Set.mem_singleton_iff.mp h ▸ hz)
    refine ⟨⟨subset_star hz, hzbot⟩, ?_⟩
    rintro y ⟨hystar, hybot⟩ hle
    obtain ⟨Y, hY, rfl⟩ := hystar
    obtain ⟨x', hx'Y, hx'bot⟩ : ∃ x' ∈ Y, x' ≠ ⊥ := by
      by_contra hcon
      push_neg at hcon
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
    atomistic over the disjoint generator set `X₀` (his §7.1: *poultry*
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
    refine le_antisymm (sSup_le fun y hy => ?_) (sSup_le ?_)
    · rcases eq_or_ne y ⊥ with rfl | hyne
      · exact bot_le
      · exact le_sSup ⟨le_sSup hy, hY hy⟩
    · rintro y ⟨hyle, _⟩
      exact hyle
  · show DisjointPred mOverlap (atomsIn (star X₀))
    rw [hatoms]
    exact hdisj

/-- A non-trivial atomless base is **mess** (his §8.1.5: *water*'s base
    has no minimal elements — space can always be shaved off a region
    containing a molecule — so atomisticity fails). -/
theorem not_neat_of_atomless {X : ISet B} (h : atomsIn X.base = ∅)
    {b : B} (hb : b ∈ X.base) (hbne : b ≠ ⊥) : ¬X.IsNeat := by
  rintro ⟨hatomistic, -⟩
  have hbplus : b ∈ plus X.base :=
    ⟨hb, fun h' => hbne (Set.mem_singleton_iff.mp h')⟩
  have := hatomistic b hbplus
  rw [h, Set.inter_empty, sSup_empty] at this
  exact hbne this

end Landman2020
