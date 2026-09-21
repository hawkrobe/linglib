/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Linglib.Core.Order.Monotone.Monovary

/-!
# Non-crossing constraint for two-layer association lines

A `Finset (ι × κ)` of links between two ordered tiers is **non-crossing**
when `k₁ < k₂ → i₁ ≤ i₂` for any two links `(k₁, i₁)`, `(k₂, i₂)` — i.e. the
index coordinates monovary, which in a two-layer drawing is exactly the
absence of crossing segments; equivalently (over linear tiers), the
componentwise order is total on the link set, [yli-jyra-2015]'s edge-order
axiom. This is the discrete-index
[goldsmith-1976] / [sagey-1986] No-Crossing Constraint ([sagey-1988] derives
it from association-as-temporal-overlap) and the canonical
filter on autosegmental GEN.

## Main definitions

* `IsNonCrossing links`: the link set monovaries (`[Preorder]`-general).
* `Crosses a b` / `IndexCrosses links p`: two links cross; `p` crosses some link
  already in `links` — the decidable GEN filter.
* `leftBound links m` / `rightBound links m` / `window links m`: the nearest index linked
  on either side of an upper node `m`, and the interval between them.

## Main results

* `isNonCrossing_insert_iff_not_indexCrosses`: a candidate may be added iff it
  crosses nothing (`IsNonCrossing.insert_of_not_indexCrosses` is the GEN direction).
* `isNonCrossing_image` / `IsNonCrossing.image_monotone`: `IsNonCrossing` commutes
  with `Finset.image`, and survives monotone reindexing of the upper coordinate.
* `isNonCrossing_insert_iff_mem_window`: a candidate may be added iff its index lies in its
  node's window; `IsNonCrossing.union_of_leftBound` / `union_of_rightBound`: spreading to the
  nearest index on one side never crosses.
-/

@[expose] public section

namespace Autosegmental

variable {ι ι' κ κ' : Type*}

/-! ### Set-level non-crossing property (via mathlib `MonovaryOn`) -/

section Preorder
variable [Preorder ι] [Preorder κ] {links : Finset (ι × κ)}

/-- The link set has no crossings: its two index coordinates monovary. -/
def IsNonCrossing (links : Finset (ι × κ)) : Prop :=
  MonovaryOn Prod.snd Prod.fst (↑links : Set (ι × κ))

/-- `IsNonCrossing` in elementary form. -/
theorem isNonCrossing_iff : IsNonCrossing links ↔
    ∀ l₁ ∈ links, ∀ l₂ ∈ links, l₁.1 < l₂.1 → l₁.2 ≤ l₂.2 := Iff.rfl

@[simp] theorem isNonCrossing_empty : IsNonCrossing (∅ : Finset (ι × κ)) := by simp [IsNonCrossing]

@[simp] theorem isNonCrossing_singleton (p : ι × κ) : IsNonCrossing {p} := by simp [IsNonCrossing]

/-- A pair is non-crossing iff its two links agree in tier- and backbone-order. -/
theorem isNonCrossing_pair [DecidableEq ι] [DecidableEq κ] (a b : ι × κ) :
    IsNonCrossing {a, b} ↔ (a.1 < b.1 → a.2 ≤ b.2) ∧ (b.1 < a.1 → b.2 ≤ a.2) := by
  simp [IsNonCrossing, monovaryOn_insert]

/-- A subset of a non-crossing link set is non-crossing. -/
theorem IsNonCrossing.subset {s t : Finset (ι × κ)} (hst : s ⊆ t)
    (h : IsNonCrossing t) : IsNonCrossing s :=
  MonovaryOn.subset (Finset.coe_subset.mpr hst) h

/-- Inserting `p` keeps non-crossing iff `p` crosses no existing link: the
    insert-algebra form, `Set.pairwise_insert` specialised to `IsNonCrossing`
    via `monovaryOn_insert`. -/
theorem isNonCrossing_insert_iff [DecidableEq ι] [DecidableEq κ] (p : ι × κ) :
    IsNonCrossing (insert p links) ↔
      IsNonCrossing links ∧ ∀ q ∈ links, IsNonCrossing {p, q} := by
  simp [IsNonCrossing, monovaryOn_insert]

/-- Non-crossing on a union: each part is, and no link of one crosses a link of the other.
    The `Set.pairwise_union` shape, via `monovaryOn_union`. -/
theorem isNonCrossing_union_iff [DecidableEq ι] [DecidableEq κ] {s t : Finset (ι × κ)} :
    IsNonCrossing (s ∪ t) ↔
      IsNonCrossing s ∧ IsNonCrossing t ∧ ∀ a ∈ s, ∀ b ∈ t, IsNonCrossing {a, b} := by
  simp [IsNonCrossing, monovaryOn_union, monovaryOn_insert]

instance [DecidableLT ι] [DecidableLE κ] : Decidable (IsNonCrossing links) :=
  decidable_of_iff _ isNonCrossing_iff.symm

end Preorder

/-! ### Reindexing along `Finset.image` -/

section Image
variable [Preorder ι'] [Preorder κ'] [DecidableEq ι'] [DecidableEq κ'] {links : Finset (ι × κ)}

/-- `IsNonCrossing` transports across a `Finset.image`: the image link set is
    non-crossing iff the index coordinates monovary after reindexing by `f`. The
    `Finset` companion of `monovaryOn_image`, and the single place the definition
    is unfolded against an image. -/
theorem isNonCrossing_image (f : ι × κ → ι' × κ') :
    IsNonCrossing (links.image f) ↔
      MonovaryOn (Prod.snd ∘ f) (Prod.fst ∘ f) (↑links : Set (ι × κ)) := by
  simp only [IsNonCrossing, Finset.coe_image, monovaryOn_image]

end Image

section ImageMonotone
variable [LinearOrder ι] [Preorder ι'] [Preorder κ] [DecidableEq ι'] [DecidableEq κ]
  {links : Finset (ι × κ)} {ρ : ι → ι'}

/-- Pushing a non-crossing link set forward along a **monotone** map on the upper
    (first) coordinate keeps it non-crossing: the autosegmental analogue of
    `SimpleGraph.map` along a monotone vertex map. The upper index needs a
    `LinearOrder` (the run-collapse domain is `ℕ`) so that `ρ` reflects `<`. Used to
    lift planarity through the OCP run-collapse `ρ` (`Autosegmental/Collapse.lean`). -/
theorem IsNonCrossing.image_monotone (hρ : Monotone ρ) (h : IsNonCrossing links) :
    IsNonCrossing (links.image (Prod.map ρ id)) := by
  rw [isNonCrossing_image]; grind [IsNonCrossing, MonovaryOn, Monotone.reflect_lt]

end ImageMonotone

/-! ### Relational composition through a shared tier

Association relations compose through a shared middle tier — the `Finset`
companion of `SetRel.comp`. Planarity is **not** closed under composition:
fan-in followed by fan-out at a single middle position (an autosegment
multiply-linked from above whose position multiply-links onward) composes to a
crossing — see the counterexample below. It is closed when the middle tier does
not fan through, in either direction: `IsNonCrossing.relComp_of_injOn_fst`
(no fan-out) and `IsNonCrossing.relComp_of_injOn_snd` (no fan-in). -/

section RelComp
variable {μ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- Relational composition of link sets through a shared middle tier. -/
def relComp (R : Finset (ι × κ)) (S : Finset (κ × μ)) : Finset (ι × μ) :=
  ((R ×ˢ S).filter fun p => p.1.2 = p.2.1).image fun p => (p.1.1, p.2.2)

@[simp] theorem mem_relComp {R : Finset (ι × κ)} {S : Finset (κ × μ)} {p : ι × μ} :
    p ∈ relComp R S ↔ ∃ j, (p.1, j) ∈ R ∧ (j, p.2) ∈ S := by
  simp only [relComp, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨i, j⟩, ⟨j', k⟩⟩, ⟨⟨hR, hS⟩, hj⟩, rfl⟩
    dsimp only at hj ⊢
    exact ⟨j', hj ▸ hR, hS⟩
  · rintro ⟨j, hR, hS⟩
    exact ⟨((p.1, j), (j, p.2)), ⟨⟨hR, hS⟩, rfl⟩, rfl⟩

theorem relComp_assoc [DecidableEq ν] (R : Finset (ι × κ)) (S : Finset (κ × μ))
    (T : Finset (μ × ν)) : relComp (relComp R S) T = relComp R (relComp S T) := by
  ext ⟨i, l⟩
  simp only [mem_relComp]
  grind

variable [Preorder ι] [PartialOrder κ] [Preorder μ]
  {R : Finset (ι × κ)} {S : Finset (κ × μ)}

/-- Composition preserves non-crossing when the middle tier does not fan out:
    `S` is functional on middle positions (`Set.InjOn Prod.fst`), so a middle tie
    forces equal outputs. -/
theorem IsNonCrossing.relComp_of_injOn_fst (hR : IsNonCrossing R) (hS : IsNonCrossing S)
    (h : Set.InjOn Prod.fst (S : Set (κ × μ))) : IsNonCrossing (relComp R S) := by
  rw [isNonCrossing_iff] at hR hS ⊢
  rintro ⟨i₁, k₁⟩ h₁ ⟨i₂, k₂⟩ h₂ hlt
  obtain ⟨j₁, hR₁, hS₁⟩ := mem_relComp.mp h₁
  obtain ⟨j₂, hR₂, hS₂⟩ := mem_relComp.mp h₂
  rcases (hR _ hR₁ _ hR₂ hlt).lt_or_eq with hj | hj
  · exact hS _ hS₁ _ hS₂ hj
  · have hkk : (j₁, k₁) = (j₂, k₂) :=
      h (Finset.mem_coe.mpr hS₁) (Finset.mem_coe.mpr hS₂) hj
    injection hkk with _ hk
    exact le_of_eq hk

/-- Composition preserves non-crossing when the middle tier does not fan in:
    `R` is injective onto middle positions (`Set.InjOn Prod.snd`), so a middle tie
    contradicts the strict order on inputs. -/
theorem IsNonCrossing.relComp_of_injOn_snd (hR : IsNonCrossing R) (hS : IsNonCrossing S)
    (h : Set.InjOn Prod.snd (R : Set (ι × κ))) : IsNonCrossing (relComp R S) := by
  rw [isNonCrossing_iff] at hR hS ⊢
  rintro ⟨i₁, k₁⟩ h₁ ⟨i₂, k₂⟩ h₂ hlt
  obtain ⟨j₁, hR₁, hS₁⟩ := mem_relComp.mp h₁
  obtain ⟨j₂, hR₂, hS₂⟩ := mem_relComp.mp h₂
  rcases (hR _ hR₁ _ hR₂ hlt).lt_or_eq with hj | hj
  · exact hS _ hS₁ _ hS₂ hj
  · have hii : (i₁, j₁) = (i₂, j₂) :=
      h (Finset.mem_coe.mpr hR₁) (Finset.mem_coe.mpr hR₂) hj
    injection hii with hi _
    exact absurd (hi ▸ hlt) (lt_irrefl _)

/-- Planarity is **not** closed under bare relational composition: fan-in (upper
    `0` and `1` both linked to middle `0`) followed by fan-out (middle `0` linked
    onward to `0` and `1`) composes to the complete, crossing relation. -/
example : IsNonCrossing ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)) ∧
    IsNonCrossing ({(0, 0), (0, 1)} : Finset (ℕ × ℕ)) ∧
    ¬ IsNonCrossing (relComp ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)) {(0, 0), (0, 1)}) := by
  decide

end RelComp

/-! ### The crossing relation and the GEN filter -/

section Candidate
variable [Preorder ι] [Preorder κ] [DecidableEq ι] [DecidableEq κ]
  {links : Finset (ι × κ)} {a b p : ι × κ}

/-- Two links **cross**: as a pair they fail to be non-crossing (equivalently their
    endpoints straddle in opposite tier- and backbone-order — `crosses_iff`). -/
def Crosses (a b : ι × κ) : Prop := ¬ IsNonCrossing {a, b}

/-- `p` crosses some link already in `links` — the decidable GEN filter. -/
def IndexCrosses (links : Finset (ι × κ)) (p : ι × κ) : Prop := ∃ l ∈ links, Crosses p l

instance [DecidableLT ι] [DecidableLE κ] : Decidable (Crosses a b) :=
  inferInstanceAs (Decidable (¬ IsNonCrossing {a, b}))

instance [DecidableLT ι] [DecidableLE κ] : Decidable (IndexCrosses links p) :=
  inferInstanceAs (Decidable (∃ l ∈ links, Crosses p l))

/-- Crossing is symmetric: `{a, b}` is the same pair as `{b, a}`. -/
theorem crosses_comm : Crosses a b ↔ Crosses b a := by rw [Crosses, Crosses, Finset.pair_comm]

/-- `p` crosses nothing iff it is pairwise non-crossing with every existing link. -/
theorem not_indexCrosses_iff :
    ¬ IndexCrosses links p ↔ ∀ l ∈ links, IsNonCrossing {p, l} := by
  simp only [IndexCrosses, Crosses, not_exists, not_and, not_not]

/-- Adding `p` keeps non-crossing iff it crosses no existing link: the GEN-filter
    form of `isNonCrossing_insert_iff`. -/
theorem isNonCrossing_insert_iff_not_indexCrosses :
    IsNonCrossing (insert p links) ↔ IsNonCrossing links ∧ ¬ IndexCrosses links p := by
  rw [isNonCrossing_insert_iff, not_indexCrosses_iff]

/-- GEN direction of `isNonCrossing_insert_iff_not_indexCrosses`. -/
theorem IsNonCrossing.insert_of_not_indexCrosses
    (hNC : IsNonCrossing links) (hNX : ¬ IndexCrosses links p) :
    IsNonCrossing (insert p links) :=
  isNonCrossing_insert_iff_not_indexCrosses.mpr ⟨hNC, hNX⟩

end Candidate

section CandidateLinear
variable [Preorder ι] [LinearOrder κ] [DecidableEq ι] [DecidableEq κ]
  {links : Finset (ι × κ)} {a b p : ι × κ}

/-- `Crosses` in elementary order form: one link's endpoints straddle the other's
    in opposite order. -/
theorem crosses_iff :
    Crosses a b ↔ (a.1 < b.1 ∧ b.2 < a.2) ∨ (b.1 < a.1 ∧ a.2 < b.2) := by
  rw [Crosses, isNonCrossing_pair]; grind

/-- `IndexCrosses` in elementary index-ordering form. -/
theorem indexCrosses_iff :
    IndexCrosses links p ↔
      ∃ l ∈ links, (p.1 < l.1 ∧ l.2 < p.2) ∨ (l.1 < p.1 ∧ p.2 < l.2) := by
  simp only [IndexCrosses, crosses_iff]

end CandidateLinear

/-! ### The window of a node

For an upper node `m`, `leftIndices` and `rightIndices` are the lower indices linked from
nodes left and right of `m`. In a non-crossing set every left index lies at or before every
right index, so the indices `m` may link to without crossing form an interval, its
**window**, from the nearest left index `leftBound` to the nearest right index `rightBound`:
`isNonCrossing_insert_iff_mem_window` is the GEN filter as an interval, and
`IsNonCrossing.union_of_leftBound` / `union_of_rightBound` are local spreading, to the
nearest linked index on one side, which never crosses. -/

section Window
variable [Preorder ι] [DecidableLT ι] [LinearOrder κ] (links : Finset (ι × κ)) (m : ι)

/-- The indices linked from nodes left of `m`. -/
def leftIndices : Finset κ := (links.filter (·.1 < m)).image (·.2)

/-- The indices linked from nodes right of `m`. -/
def rightIndices : Finset κ := (links.filter (m < ·.1)).image (·.2)

/-- The nearest index linked from a node left of `m`. -/
def leftBound : WithBot κ := (leftIndices links m).max

/-- The nearest index linked from a node right of `m`. -/
def rightBound : WithTop κ := (rightIndices links m).min

/-- The indices `m` may link to without crossing. -/
def window : Set κ := {j | leftBound links m ≤ j ∧ ↑j ≤ rightBound links m}

variable {links m} {j x y : κ}

@[simp] theorem mem_leftIndices : x ∈ leftIndices links m ↔ ∃ n < m, (n, x) ∈ links := by
  simp [leftIndices, Prod.exists, and_comm]

@[simp] theorem mem_rightIndices :
    x ∈ rightIndices links m ↔ ∃ n, m < n ∧ (n, x) ∈ links := by
  simp [rightIndices, Prod.exists, and_comm]

instance : DecidablePred (· ∈ window links m) := fun j ↦
  inferInstanceAs (Decidable (leftBound links m ≤ j ∧ ↑j ≤ rightBound links m))

theorem mem_window_iff : j ∈ window links m ↔
    (∀ x ∈ leftIndices links m, x ≤ j) ∧ ∀ x ∈ rightIndices links m, j ≤ x := by
  simp [window, leftBound, rightBound, Finset.max_le_iff, Finset.le_min_iff]

theorem notMem_window_of_mem_leftIndices (hx : x ∈ leftIndices links m) (h : j < x) :
    j ∉ window links m := fun hj ↦ absurd h (not_lt.2 ((mem_window_iff.1 hj).1 x hx))

theorem notMem_window_of_mem_rightIndices (hx : x ∈ rightIndices links m) (h : x < j) :
    j ∉ window links m := fun hj ↦ absurd h (not_lt.2 ((mem_window_iff.1 hj).2 x hx))

/-- The GEN filter is membership in the window. -/
theorem not_indexCrosses_iff_mem_window [DecidableEq ι] :
    ¬ IndexCrosses links (m, j) ↔ j ∈ window links m := by
  simp only [indexCrosses_iff, mem_window_iff, mem_leftIndices, mem_rightIndices, not_exists,
    not_or, not_and, not_lt, forall_exists_index, and_imp, Prod.forall]
  grind

theorem isNonCrossing_insert_iff_mem_window [DecidableEq ι] :
    IsNonCrossing (insert (m, j) links) ↔ IsNonCrossing links ∧ j ∈ window links m := by
  rw [isNonCrossing_insert_iff_not_indexCrosses, not_indexCrosses_iff_mem_window]

/-- In a non-crossing set the window is an interval: every index linked left of `m` lies at
    or before every index linked right of it. -/
theorem IsNonCrossing.left_le_right (h : IsNonCrossing links) (hx : x ∈ leftIndices links m)
    (hy : y ∈ rightIndices links m) : x ≤ y := by
  obtain ⟨n, hn, hx⟩ := mem_leftIndices.1 hx
  obtain ⟨n', hn', hy⟩ := mem_rightIndices.1 hy
  exact isNonCrossing_iff.1 h _ hx _ hy (hn.trans hn')

/-- The nearest left index lies in the window. -/
theorem IsNonCrossing.mem_window_of_leftBound_eq (h : IsNonCrossing links)
    (hj : leftBound links m = j) : j ∈ window links m :=
  mem_window_iff.2 ⟨fun _ hx ↦ Finset.le_max_of_eq hx hj,
    fun _ hy ↦ h.left_le_right (Finset.mem_of_max hj) hy⟩

/-- The nearest right index lies in the window. -/
theorem IsNonCrossing.mem_window_of_rightBound_eq (h : IsNonCrossing links)
    (hj : rightBound links m = j) : j ∈ window links m :=
  mem_window_iff.2 ⟨fun _ hx ↦ h.left_le_right hx (Finset.mem_of_min hj),
    fun _ hy ↦ Finset.min_le_of_eq hy hj⟩

theorem leftIndices_mono : Monotone (leftIndices links) := by
  intro _ _ hm x hx
  obtain ⟨n, hn, hx⟩ := mem_leftIndices.1 hx
  exact mem_leftIndices.2 ⟨n, hn.trans_le hm, hx⟩

theorem rightIndices_anti : Antitone (rightIndices links) := by
  intro _ _ hm x hx
  obtain ⟨n, hn, hx⟩ := mem_rightIndices.1 hx
  exact mem_rightIndices.2 ⟨n, hm.trans_lt hn, hx⟩

theorem leftBound_mono : Monotone (leftBound links) := fun _ _ hm ↦
  Finset.max_mono (leftIndices_mono hm)

theorem rightBound_mono : Monotone (rightBound links) := fun _ _ hm ↦
  Finset.min_mono (rightIndices_anti hm)

/-- Local spreading to the left: lines from any nodes to the nearest index linked left of
    each cross neither one another nor the links of a non-crossing set. -/
theorem IsNonCrossing.union_of_leftBound [DecidableEq ι] (h : IsNonCrossing links)
    {s : Finset (ι × κ)}
    (hs : ∀ p ∈ s, leftBound links p.1 = p.2) : IsNonCrossing (links ∪ s) := by
  refine isNonCrossing_union_iff.2
    ⟨h, isNonCrossing_iff.2 fun p hp q hq hpq ↦ ?_, fun a ha b hb ↦ ?_⟩
  · exact WithBot.coe_le_coe.1
      ((hs p hp).symm.trans_le ((leftBound_mono hpq.le).trans_eq (hs q hq)))
  · obtain ⟨hl, hr⟩ := mem_window_iff.1 (h.mem_window_of_leftBound_eq (hs b hb))
    exact (isNonCrossing_pair a b).2 ⟨fun hab ↦ hl _ (mem_leftIndices.2 ⟨a.1, hab, ha⟩),
      fun hba ↦ hr _ (mem_rightIndices.2 ⟨a.1, hba, ha⟩)⟩

/-- Local spreading to the right: lines from any nodes to the nearest index linked right of
    each cross neither one another nor the links of a non-crossing set. -/
theorem IsNonCrossing.union_of_rightBound [DecidableEq ι] (h : IsNonCrossing links)
    {s : Finset (ι × κ)}
    (hs : ∀ p ∈ s, rightBound links p.1 = p.2) : IsNonCrossing (links ∪ s) := by
  refine isNonCrossing_union_iff.2
    ⟨h, isNonCrossing_iff.2 fun p hp q hq hpq ↦ ?_, fun a ha b hb ↦ ?_⟩
  · exact WithTop.coe_le_coe.1
      ((hs p hp).symm.trans_le ((rightBound_mono hpq.le).trans_eq (hs q hq)))
  · obtain ⟨hl, hr⟩ := mem_window_iff.1 (h.mem_window_of_rightBound_eq (hs b hb))
    exact (isNonCrossing_pair a b).2 ⟨fun hab ↦ hl _ (mem_leftIndices.2 ⟨a.1, hab, ha⟩),
      fun hba ↦ hr _ (mem_rightIndices.2 ⟨a.1, hba, ha⟩)⟩

end Window

/-! ### Link shift (the concatenation offset)

The coordinate offset that places a morpheme's links past the preceding tiers under
concatenation ([jardine-heinz-2015]). Shared by the bipartite `Graph` and the n-tier
`MultiGraph`, which apply it to their one / each tier-pair respectively. -/

/-- Shift a link's two endpoints by `(δ₁, δ₂)`. -/
def shiftLink (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + δ₁, p.2 + δ₂)

@[simp] theorem shiftLink_apply (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) :
    shiftLink δ₁ δ₂ p = (p.1 + δ₁, p.2 + δ₂) := rfl

@[simp] theorem shiftLink_zero : shiftLink 0 0 = (id : ℕ × ℕ → ℕ × ℕ) := by funext p; simp

theorem shiftLink_comp (a₁ a₂ b₁ b₂ : ℕ) :
    shiftLink a₁ a₂ ∘ shiftLink b₁ b₂ = shiftLink (a₁ + b₁) (a₂ + b₂) := by
  funext p; simp only [Function.comp_apply, shiftLink_apply, Prod.mk.injEq]; omega

/-- Shifting a link set preserves non-crossing: `shiftLink` is a coordinatewise
    order-embedding, so via `isNonCrossing_image` it preserves monovariance. -/
theorem isNonCrossing_image_shiftLink (s : Finset (ℕ × ℕ)) (δ₁ δ₂ : ℕ) :
    IsNonCrossing (s.image (shiftLink δ₁ δ₂)) ↔ IsNonCrossing s := by
  grind [isNonCrossing_image, IsNonCrossing, MonovaryOn, shiftLink]

end Autosegmental
