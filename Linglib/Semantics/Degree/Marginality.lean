/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Comparable
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.RelClasses
public import Linglib.Core.Algebra.Order.Archimedean.Class

/-!
# Marginal and large differences

Dinis and Jacinto's ML theory describes degrees ordered by smaller than together with a relation
of being marginally smaller. A degree is largely smaller than another when it is smaller but not
marginally so. An ML scale is a linear order with a marginally-smaller-than relation obeying the
five axioms of [dinis-jacinto-2026], which simplify the original theory of
[dinis-jacinto-2025].

Largely smaller than is a strict weak order, and its incomparability relation is at most
marginal difference. The degrees therefore fall into order-connected blocks of marginally
different degrees, no block having an endpoint that faces another block, and every such
partition of a linear order is an ML scale (`MLScale.ofSetoid`). Two families of examples are
lexicographic pairs of a block and a location within it (`MLScale.lex`), among them the
representative model `ℚ ×ₗ ℤ`, and the differences lying in an order-connected subgroup of an
ordered group (`MLScale.ofAddSubgroup`), such as the infinitesimals among the hyperreals.

## Main definitions

* `Degree.MLScale`: an ML scale, with `MLScale.L` largely smaller than and
  `MLScale.AtMostMarginal` at most marginal difference.
* `Degree.MLScale.ofSetoid`, `Degree.MLScale.lex`, `Degree.MLScale.ofAddSubgroup`: ML scales
  from order-connected partitions, lexicographic pairs, and order-connected subgroups.
* `Degree.MLScale.rep`: the representative model.
* `Degree.MLScale.IsMLModel`: the eleven axioms of the original theory, along a strict weak
  order with both relations primitive.
* `Degree.MLScale.IsHom`: a homomorphism of ML scales.

## Main results

* `Degree.MLScale.instIsStrictWeakOrderL`, `Degree.MLScale.atMostMarginal_iff_incompRel`:
  largely smaller than is a strict weak order whose incomparability is at most marginal
  difference.
* `Degree.MLScale.L.infinite_setOf`, `Degree.MLScale.instIsEmpty`: infinitely many degrees lie
  between largely different ones, so no conditionally complete order carries an ML scale.
* `Degree.MLScale.ofSetoid_atMostMarginalSetoid`: every ML scale is the scale of its blocks.
* `Degree.MLScale.isHom_lex_iff`: a map into a lexicographic ML scale is a homomorphism exactly
  when its block coordinate pulls back largely smaller than and its location coordinate grows
  along marginal steps.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
-/

@[expose] public section

namespace Degree

/-- An ML scale is a linear order with a relation of being marginally smaller, subject to the
five axioms of ML theory, where `x` is largely smaller than `y` when `x < y ∧ ¬ M x y`. -/
structure MLScale (α : Type*) [LinearOrder α] where
  /-- `x` is marginally smaller than `y`. -/
  M : α → α → Prop
  /-- Axiom 1 says that some element is largely smaller than another. -/
  exists_large : ∃ x y, x < y ∧ ¬ M x y
  /-- Axiom 2 says that marginally smaller than implies smaller than. -/
  lt_of_m : ∀ ⦃x y⦄, M x y → x < y
  /-- Axiom 3, M-irrelevance, says that when `x` is marginally smaller than `y`, whatever is
  largely smaller than `y` is largely smaller than `x`, and `y` is largely smaller than whatever
  `x` is largely smaller than. -/
  irrelevance : ∀ ⦃x y⦄ z, M x y →
    (z < y ∧ ¬ M z y → z < x ∧ ¬ M z x) ∧ (x < z ∧ ¬ M x z → y < z ∧ ¬ M y z)
  /-- Axiom 4 says that whatever is smaller than something largely smaller than `z` is largely
  smaller than `z`, and whatever is largely smaller than something smaller than `z` is largely
  smaller than `z`. -/
  extends_lt : ∀ ⦃x y⦄ z, x < y →
    (y < z ∧ ¬ M y z → x < z ∧ ¬ M x z) ∧ (z < x ∧ ¬ M z x → z < y ∧ ¬ M z y)
  /-- Axiom 5, Decomposition, says that a large difference is a marginal step followed by a
  large one, and a large one followed by a marginal step. -/
  decomposition : ∀ ⦃x y⦄, x < y ∧ ¬ M x y →
    (∃ z, M x z ∧ z < y ∧ ¬ M z y) ∧ ∃ w, M w y ∧ x < w ∧ ¬ M x w

namespace MLScale

variable {α : Type*} [LinearOrder α] (ml : MLScale α)

/-- `x` is largely smaller than `y` when it is smaller but not marginally smaller. -/
def L (x y : α) : Prop := x < y ∧ ¬ ml.M x y

/-- Two degrees differ at most marginally when they are equal or one is marginally smaller than
the other. -/
def AtMostMarginal : α → α → Prop := Relation.ReflGen (Relation.SymmGen ml.M)

variable {ml} {x y z : α}

@[grind =]
theorem atMostMarginal_iff : ml.AtMostMarginal x y ↔ x = y ∨ ml.M x y ∨ ml.M y x :=
  (Relation.reflGen_iff _ _ _).trans (or_congr_left eq_comm)

@[grind →]
theorem M.lt (h : ml.M x y) : x < y := ml.lt_of_m h

@[grind →]
theorem L.lt (h : ml.L x y) : x < y := h.1

theorem M.not_l (h : ml.M x y) : ¬ ml.L x y := fun h' ↦ h'.2 h

theorem m_or_l_of_lt (h : x < y) : ml.M x y ∨ ml.L x y := (em _).imp_right (⟨h, ·⟩)

theorem L.of_lt_of_l (hxy : x < y) (h : ml.L y z) : ml.L x z := (ml.extends_lt z hxy).1 h

theorem L.trans_lt (h : ml.L x y) (hyz : y < z) : ml.L x z := (ml.extends_lt x hyz).2 h

theorem L.trans (hxy : ml.L x y) (hyz : ml.L y z) : ml.L x z := hxy.trans_lt hyz.lt

/-- Marginal steps do not accrue to a large difference. -/
theorem M.trans (hxy : ml.M x y) (hyz : ml.M y z) : ml.M x z := by
  grind [ml.irrelevance, M.lt]

/-- What lies between marginally different degrees is marginally different from each. -/
theorem M.bounded (hxz : ml.M x z) (hxy : x < y) (hyz : y < z) : ml.M x y ∧ ml.M y z := by
  grind [ml.extends_lt]

instance : IsTrans α ml.M := ⟨fun _ _ _ ↦ M.trans⟩

instance : Std.Asymm ml.L := ⟨fun _ _ h h' ↦ h.lt.asymm h'.lt⟩

/-- Largely smaller than is negatively transitive. When one degree is largely smaller than
another, any third degree is largely greater than the first or largely smaller than the
second. -/
instance : IsOrderConnected α ml.L where
  conn a b c h := by
    rcases le_or_gt b a with hba | hab
    · exact .inr (hba.eq_or_lt.elim (· ▸ h) (L.of_lt_of_l · h))
    rcases le_or_gt c b with hcb | hbc
    · exact .inl (hcb.eq_or_lt.elim (· ▸ h) h.trans_lt)
    exact (m_or_l_of_lt hab).elim
      (fun hm ↦ (m_or_l_of_lt hbc).imp (fun hm' ↦ absurd (hm.trans hm') h.2) id) .inl

instance instIsStrictWeakOrderL : IsStrictWeakOrder α ml.L :=
  isStrictWeakOrder_of_isOrderConnected

/-- At most marginal difference is incomparability under largely smaller than. -/
theorem atMostMarginal_iff_incompRel : ml.AtMostMarginal x y ↔ IncompRel ml.L x y := by
  simp only [AtMostMarginal, Relation.reflGen_iff, Relation.SymmGen, IncompRel]
  grind [m_or_l_of_lt, M.not_l]

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := Relation.ReflGen.refl

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  atMostMarginal_iff_incompRel.2 (atMostMarginal_iff_incompRel.1 h).symm

theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z :=
  atMostMarginal_iff_incompRel.2 <| IsStrictWeakOrder.incomp_trans _ _ _
    (atMostMarginal_iff_incompRel.1 hxy) (atMostMarginal_iff_incompRel.1 hyz)

variable (ml) in
/-- At most marginal difference is an equivalence relation, sameness for present purposes. -/
def atMostMarginalSetoid : Setoid α :=
  ⟨ml.AtMostMarginal, ⟨AtMostMarginal.refl, AtMostMarginal.symm, AtMostMarginal.trans⟩⟩

theorem AtMostMarginal.l_congr_left (h : ml.AtMostMarginal x y) : ml.L x z ↔ ml.L y z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ y _ h').resolve_left h.1,
    fun h' ↦ (IsOrderConnected.conn _ x _ h').resolve_left h.2⟩

theorem AtMostMarginal.l_congr_right (h : ml.AtMostMarginal y z) : ml.L x y ↔ ml.L x z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.2,
    fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.1⟩

/-- Marginally smaller than is smaller than within a block. -/
theorem m_iff_lt_and_atMostMarginal : ml.M x y ↔ x < y ∧ ml.AtMostMarginal x y := by
  grind [atMostMarginal_iff_incompRel, IncompRel, L]

/-- A block of at most marginally different degrees is order-connected. -/
theorem ordConnected_setOf_atMostMarginal (x : α) :
    {y | ml.AtMostMarginal x y}.OrdConnected :=
  ⟨fun y hy z hz w ⟨hyw, hwz⟩ ↦ by
    rcases hyw.eq_or_lt with rfl | hyw; · exact hy
    rcases hwz.eq_or_lt with rfl | hwz; · exact hz
    have hyz := m_iff_lt_and_atMostMarginal.2 ⟨hyw.trans hwz, hy.symm.trans hz⟩
    exact hy.trans (.single (.inl (hyz.bounded hyw hwz).1))⟩

/-- When `x` is largely smaller than `y`, infinitely many degrees lie marginally above `x` and
largely below `y`, since Decomposition gives each such degree a marginally greater one. -/
theorem L.infinite_setOf (h : ml.L x y) : {z | ml.M x z ∧ ml.L z y}.Infinite := fun hfin ↦ by
  obtain ⟨z₀, hz₀⟩ := (ml.decomposition h).1
  obtain ⟨z, ⟨hxz, hzy⟩, hmax⟩ := hfin.exists_maximal ⟨z₀, hz₀⟩
  obtain ⟨w, hzw, hwy⟩ := (ml.decomposition hzy).1
  exact (hmax ⟨hxz.trans hzw, hwy⟩ hzw.lt.le).not_gt hzw.lt

/-- Largely different degrees are infinitely far apart. -/
theorem L.infinite_Ioo (h : ml.L x y) : (Set.Ioo x y).Infinite :=
  h.infinite_setOf.mono fun _ hz ↦ ⟨hz.1.lt, hz.2.lt⟩

/-- The degrees largely greater than a given one form an upper set. -/
theorem isUpperSet_setOf_l (x : α) : IsUpperSet {y | ml.L x y} :=
  fun _ _ hle h ↦ hle.eq_or_lt.elim (· ▸ h) h.trans_lt

/-- No conditionally complete linear order carries an ML scale. The supremum of the degrees above
`x` and largely below `y` would lie in the block of `y`, and a degree marginally below it would be
a smaller upper bound. -/
instance instIsEmpty {α : Type*} [ConditionallyCompleteLinearOrder α] : IsEmpty (MLScale α) := by
  refine ⟨fun ml ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := ml.exists_large
  set S := {z | x < z ∧ ml.L z y}
  obtain ⟨z₀, hxz₀, hz₀y⟩ := (ml.decomposition hxy).1
  have hS : S.Nonempty := ⟨z₀, hxz₀.lt, hz₀y⟩
  have hb : BddAbove S := ⟨y, fun z hz ↦ hz.2.lt.le⟩
  have hxl : x < sSup S := hxz₀.lt.trans_le (le_csSup hb ⟨hxz₀.lt, hz₀y⟩)
  have hly : ml.AtMostMarginal (sSup S) y := atMostMarginal_iff_incompRel.2
    ⟨fun h ↦ by
      obtain ⟨w, hlw, hwy⟩ := (ml.decomposition h).1
      exact (le_csSup hb ⟨hxl.trans hlw.lt, hwy⟩).not_gt hlw.lt,
    fun h ↦ (csSup_le hS fun z hz ↦ hz.2.lt.le).not_gt h.lt⟩
  obtain ⟨w, hwl, -, hxw⟩ := (ml.decomposition (hly.l_congr_right.2 hxy)).2
  exact (csSup_le hS fun a ha ↦
    ((ml.irrelevance a hwl).1 (hly.l_congr_right.2 ha.2)).1.le).not_gt hwl.lt

/-! ### The original axioms -/

/-- The eleven axioms of [dinis-jacinto-2025] on marginally and largely smaller than, `M` and
`L`, along a strict weak order `R`, both relations primitive. -/
structure IsMLModel {β : Type*} (R M L : β → β → Prop) : Prop where
  isStrictWeakOrder : IsStrictWeakOrder β R
  exists_l : ∃ x y, L x y
  r_of_m : ∀ ⦃x y⦄, M x y → R x y
  r_of_l : ∀ ⦃x y⦄, L x y → R x y
  m_trans : ∀ ⦃x y z⦄, M x y → M y z → M x z
  not_l_of_m : ∀ ⦃x y⦄, M x y → ¬ L x y
  irrelevance : ∀ ⦃x y⦄ z, M x y → (L z y → L z x) ∧ (L x z → L y z)
  l_of_r_of_l : ∀ ⦃x y z⦄, R x y → L y z → L x z
  l_of_l_of_r : ∀ ⦃x y z⦄, L x y → R y z → L x z
  m_or_l_of_r : ∀ ⦃x y⦄, R x y → M x y ∨ L x y
  decomposition : ∀ ⦃x y⦄, L x y → (∃ z, M x z ∧ L z y) ∧ ∃ w, M w y ∧ L x w
  m_bounded : ∀ ⦃x y z⦄, M x z → R x y → R y z → M x y ∧ M y z

/-- Along a linear order, largely smaller than is smaller than but not marginally smaller
than. -/
theorem IsMLModel.l_iff {M L : α → α → Prop} (h : IsMLModel (· < ·) M L) :
    L x y ↔ x < y ∧ ¬ M x y := by
  grind [h.r_of_l, h.not_l_of_m, h.m_or_l_of_r]

/-! ### Constructions -/

/-- A partition of a linear order into order-connected blocks, at least two of them and none
with an endpoint facing another block, is an ML scale whose marginal differences are the
differences within a block. -/
def ofSetoid (s : Setoid α) (hconv : ∀ x, {y | s x y}.OrdConnected) (hne : ∃ x y, ¬ s x y)
    (hgt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ z, x < z ∧ s x z)
    (hlt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ w, w < y ∧ s w y) : MLScale α where
  M x y := x < y ∧ s x y
  exists_large := by
    obtain ⟨x, y, h⟩ := hne
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact ⟨x, y, hxy, fun h' ↦ h h'.2⟩
    · exact absurd (s.refl x) h
    · exact ⟨y, x, hxy, fun h' ↦ h (s.symm h'.2)⟩
  lt_of_m _ _ h := h.1
  irrelevance x y z hxy := by
    have hc := hconv x
    refine ⟨fun ⟨hzy, hn⟩ ↦ ⟨lt_of_not_ge fun hxz ↦ hn ⟨hzy, ?_⟩,
      fun h ↦ hn ⟨hzy, s.trans h.2 hxy.2⟩⟩, fun ⟨hxz, hn⟩ ↦ ⟨lt_of_not_ge fun hzy ↦
      hn ⟨hxz, hc.out (s.refl x) hxy.2 ⟨hxz.le, hzy⟩⟩, fun h ↦ hn ⟨hxz, s.trans hxy.2 h.2⟩⟩⟩
    exact s.trans (s.symm (hc.out (s.refl x) hxy.2 ⟨hxz, hzy.le⟩)) hxy.2
  extends_lt x y z hxy :=
    ⟨fun ⟨hyz, hn⟩ ↦ ⟨hxy.trans hyz, fun h ↦ hn ⟨hyz,
      s.trans (s.symm ((hconv x).out (s.refl x) h.2 ⟨hxy.le, hyz.le⟩)) h.2⟩⟩,
    fun ⟨hzx, hn⟩ ↦ ⟨hzx.trans hxy, fun h ↦ hn ⟨hzx,
      s.trans h.2 ((hconv y).out (s.symm h.2) (s.refl y) ⟨hzx.le, hxy.le⟩)⟩⟩⟩
  decomposition x y h := by
    have hn : ¬ s x y := fun hs ↦ h.2 ⟨h.1, hs⟩
    obtain ⟨z, hxz, hsz⟩ := hgt h.1 hn
    obtain ⟨w, hwy, hsw⟩ := hlt h.1 hn
    exact ⟨⟨z, ⟨hxz, hsz⟩, lt_of_not_ge fun hyz ↦ hn ((hconv x).out (s.refl x) hsz ⟨h.1.le, hyz⟩),
        fun hm ↦ hn (s.trans hsz hm.2)⟩,
      ⟨w, ⟨hwy, hsw⟩, lt_of_not_ge fun hwx ↦ hn (s.symm ((hconv y).out (s.symm hsw) (s.refl y)
        ⟨hwx, h.1.le⟩)), fun hm ↦ hn (s.trans hm.2 hsw)⟩⟩

@[ext]
theorem ext {ml ml' : MLScale α} (h : ∀ x y, ml.M x y ↔ ml'.M x y) : ml = ml' := by
  cases ml; cases ml'
  congr
  exact funext₂ fun x y ↦ propext (h x y)

/-- Every ML scale is the scale of its partition into blocks of at most marginally different
degrees. -/
theorem ofSetoid_atMostMarginalSetoid :
    ofSetoid ml.atMostMarginalSetoid ordConnected_setOf_atMostMarginal
      (let ⟨x, y, h⟩ := ml.exists_large; ⟨x, y, fun h' ↦ h.2 (m_iff_lt_and_atMostMarginal.2
        ⟨h.1, h'⟩)⟩)
      (fun _ _ hxy hn ↦ let ⟨z, hz, _⟩ := (ml.decomposition ⟨hxy, fun hm ↦ hn (.single
        (.inl hm))⟩).1; ⟨z, hz.lt, .single (.inl hz)⟩)
      (fun _ _ hxy hn ↦ let ⟨w, hw, _⟩ := (ml.decomposition ⟨hxy, fun hm ↦ hn (.single
        (.inl hm))⟩).2; ⟨w, hw.lt, .single (.inl hw)⟩) = ml :=
  ext fun _ _ ↦ m_iff_lt_and_atMostMarginal.symm

section Lex

variable (β γ : Type*) [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ]

/-- Lexicographic pairs of a block and a location form an ML scale in which one pair is
marginally smaller than another when they share a block and its location is smaller. -/
def lex : MLScale (β ×ₗ γ) :=
  ofSetoid (Setoid.ker fun p ↦ (ofLex p).1)
    (fun x ↦ by
      convert (Set.ordConnected_singleton (a := (ofLex x).1)).preimage_mono
        Prod.Lex.monotone_fst_ofLex using 1
      ext
      simp [Setoid.ker_def, eq_comm])
    (let ⟨a, b, hab⟩ := exists_pair_ne β; let ⟨c⟩ := ‹Nonempty γ›
      ⟨toLex (a, c), toLex (b, c), hab⟩)
    (fun x _ _ _ ↦ let ⟨c, hc⟩ := exists_gt (ofLex x).2
      ⟨toLex ((ofLex x).1, c), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hc⟩), rfl⟩)
    (fun _ y _ _ ↦ let ⟨d, hd⟩ := exists_lt (ofLex y).2
      ⟨toLex ((ofLex y).1, d), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hd⟩), rfl⟩)

variable {β γ}

theorem lex_m_iff {x y : β ×ₗ γ} :
    (lex β γ).M x y ↔ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 := by
  change x < y ∧ (ofLex x).1 = (ofLex y).1 ↔ _
  grind [Prod.Lex.lt_iff]

theorem lex_l_iff {x y : β ×ₗ γ} : (lex β γ).L x y ↔ (ofLex x).1 < (ofLex y).1 := by
  change x < y ∧ ¬ (x < y ∧ (ofLex x).1 = (ofLex y).1) ↔ _
  grind [Prod.Lex.lt_iff]

end Lex

/-- The representative model orders rational-integer pairs lexicographically, and one pair is
marginally smaller than another when their first coordinates agree and its second coordinate is
smaller. -/
abbrev rep : MLScale (ℚ ×ₗ ℤ) := lex ℚ ℤ

section AddSubgroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The differences lying in an order-connected subgroup that is neither trivial nor everything
are the marginal differences of an ML scale. -/
def ofAddSubgroup (H : AddSubgroup G) (hconv : (H : Set G).OrdConnected) (hbot : H ≠ ⊥)
    (htop : H ≠ ⊤) : MLScale G :=
  ofSetoid (QuotientAddGroup.leftRel H)
    (fun x ↦ by
      simp only [QuotientAddGroup.leftRel_apply]
      exact hconv.preimage_mono (f := fun y ↦ -x + y) fun _ _ h ↦ by simpa using h)
    (by
      obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
        by_contra! h
        exact htop (eq_top_iff.2 fun g _ ↦ h g)
      exact ⟨0, g, by simpa [QuotientAddGroup.leftRel_apply] using hg⟩)
    (fun x _ _ _ ↦ by
      obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
      exact ⟨x + h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩)
    (fun _ y _ _ ↦ by
      obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
      exact ⟨y - h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩)

theorem ofAddSubgroup_m_iff {H : AddSubgroup G} {hconv hbot htop} {x y : G} :
    (ofAddSubgroup H hconv hbot htop).M x y ↔ x < y ∧ y - x ∈ H := by
  simp [ofAddSubgroup, ofSetoid, QuotientAddGroup.leftRel_apply, neg_add_eq_sub]

end AddSubgroup

/-! ### Homomorphisms -/

/-- A homomorphism of ML scales preserves and reflects smaller than and marginally smaller
than. -/
structure IsHom {β : Type*} [LinearOrder β] (ml : MLScale α) (ml' : MLScale β) (f : α → β) :
    Prop where
  strictMono : StrictMono f
  m_iff : ∀ x y, ml'.M (f x) (f y) ↔ ml.M x y

theorem IsHom.l_iff {β : Type*} [LinearOrder β] {ml' : MLScale β} {f : α → β}
    (hf : ml.IsHom ml' f) : ml'.L (f x) (f y) ↔ ml.L x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.m_iff x y))

section Lex

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ] {f : α → β ×ₗ γ}

/-- A map into a lexicographic ML scale is a homomorphism exactly when its block coordinate
pulls back largely smaller than and its location coordinate grows along marginal steps. -/
theorem isHom_lex_iff :
    ml.IsHom (lex β γ) f ↔ (∀ x y, ml.L x y ↔ (ofLex (f x)).1 < (ofLex (f y)).1) ∧
      ∀ ⦃x y⦄, ml.M x y → (ofLex (f x)).2 < (ofLex (f y)).2 := by
  refine ⟨fun hf ↦ ⟨fun x y ↦ hf.l_iff.symm.trans lex_l_iff,
    fun x y h ↦ (lex_m_iff.1 ((hf.m_iff x y).2 h)).2⟩, fun ⟨hL, hM⟩ ↦ ?_⟩
  have hfst (x y : α) : (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y := by
    rw [atMostMarginal_iff_incompRel, IncompRel, hL, hL]
    grind
  refine ⟨fun x y hxy ↦ ?_, fun x y ↦ ?_⟩
  · rw [Prod.Lex.lt_iff, hfst]
    grind [m_or_l_of_lt]
  · rw [lex_m_iff, hfst]
    grind

theorem IsHom.fst_eq_fst_iff (hf : ml.IsHom (lex β γ) f) :
    (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y := by
  rw [atMostMarginal_iff_incompRel, IncompRel, ← hf.l_iff, ← hf.l_iff, lex_l_iff, lex_l_iff]
  grind

end Lex

end MLScale

end Degree
