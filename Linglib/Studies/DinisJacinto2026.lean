module

public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Comparable
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.RelClasses

/-!
# Dinis and Jacinto (2026): Marginality scales for gradable adjectives

Dinis and Jacinto give the degrees of a vague gradable adjective the structure of their theory
of marginal and large differences, ML theory, simplified to a linear order with one primitive,
*marginally smaller than*. A degree is largely smaller than another when it is smaller but not
marginally so. As in Kennedy's semantics, an adjective measures objects at circumstances of
evaluation by degrees, and the comparative compares degrees; as in Fara's, the positive form
holds of an object whose degree is largely greater than the standard of comparison.

Largely smaller than is a strict weak order, and its incomparability relation is at most
marginal difference, the paper's sameness for present purposes. The degrees therefore fall into
blocks of marginally different degrees, and the positive form cannot tell apart degrees in one
block. The representative model lays out integer-indexed locations in rational-indexed blocks,
and every countable, finitely marginal ML scale embeds in it. Between largely different degrees
lie infinitely many, so no conditionally complete order, such as the naturals or the reals,
carries an ML scale.

## Main statements

* `MLScale.instIsStrictWeakOrderL`, `MLScale.atMostMarginal_iff_incompRel`: largely smaller than
  is a strict weak order whose incomparability is at most marginal difference.
* `MLScale.not_isTrans_symmGen_m`, `MLScale.not_isTrans_symmGen_l`: neither marginal nor large
  difference is transitive.
* `MLScale.L.infinite_setOf`, `MLScale.instIsEmptyOfConditionallyCompleteLinearOrder`: largely
  different degrees are infinitely far apart, so neither the naturals nor the reals carry an
  ML scale.
* `MLScale.exists_isHom_rep`: every countable, finitely marginal ML scale embeds in the
  representative model.
* `MLScale.comparative_of_positive_of_not_positive`: an object that leaves the positive form's
  extension has become smaller on the scale, which the two-scale alternative does not predict
  (`MLScale.exists_twoScale_not_comparative`).
* `MLScale.AtMostMarginal.positive_iff`, `MLScale.clustered_positive`: at most marginally
  different degrees are alike for the positive form, Fara's similarity constraint, so its
  extension is clustered and tolerant.
* `MLScale.exists_large_step_of_soritical`: a Soritical sequence for the positive form has a
  large step.
* `MLScale.setOf_positive_eq_gt_over`: under a representation, the positive form is the strict
  comparison of the block coordinate with the standard's block.

## Implementation notes

* The strict order is the `<` of a `LinearOrder`, and the five axioms are those of Figure 1
  with largely smaller than unfolded; `M` and `L` keep the paper's letters. A homomorphism into
  another ML scale preserves and reflects smaller than and marginally smaller than, as in
  [dinis-jacinto-2025]; over linear orders it is strictly monotone, so injective.
* A measure function takes a circumstance of evaluation and an object to a degree. The context
  enters only through the standard of comparison and the scale, which are held fixed.
* The text calls marginal difference transitive and large difference possibly intransitive
  (p. 106). Marginally smaller than and at most marginal difference are transitive, while
  marginal difference, being symmetric and irreflexive, is not, and large difference never is.
* The uniqueness theorem of [dinis-jacinto-2025] is not formalized; the paper does not use it.

## References

* [dinis-jacinto-2026]
* [dinis-jacinto-2025]
* [fara-2000]
* [kennedy-1999]
* [kennedy-2007]
-/

@[expose] public section

namespace DinisJacinto2026

variable {α : Type*} [LinearOrder α]

/-! ### ML theory -/

/-- An ML scale is a linear order with a primitive relation of being marginally smaller, subject
to the five axioms of ML theory (Figure 1), where `x` is largely smaller than `y` when
`x < y ∧ ¬ M x y`. -/
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

variable (ml : MLScale α)

/-- `x` is largely smaller than `y` when it is smaller but not marginally smaller,
Definition 2.1. -/
def L (x y : α) : Prop := x < y ∧ ¬ ml.M x y

/-- Two degrees differ at most marginally when they are equal or one is marginally smaller than
the other, Definition 2.3. -/
def AtMostMarginal : α → α → Prop := Relation.ReflGen (Relation.SymmGen ml.M)

variable {ml} {x y z : α}

theorem M.lt (h : ml.M x y) : x < y := ml.lt_of_m h

theorem L.lt (h : ml.L x y) : x < y := h.1

theorem M.not_l (h : ml.M x y) : ¬ ml.L x y := fun h' ↦ h'.2 h

theorem m_or_l_of_lt (h : x < y) : ml.M x y ∨ ml.L x y := (em _).imp_right (⟨h, ·⟩)

/-- Axiom 4, first half. -/
theorem L.of_lt_of_l (hxy : x < y) (h : ml.L y z) : ml.L x z := (ml.extends_lt z hxy).1 h

/-- Axiom 4, second half. -/
theorem L.trans_lt (h : ml.L x y) (hyz : y < z) : ml.L x z := (ml.extends_lt x hyz).2 h

theorem L.trans (hxy : ml.L x y) (hyz : ml.L y z) : ml.L x z := hxy.trans_lt hyz.lt

/-- M-transitivity, Theorem 2.2: marginal steps do not accrue to a large difference. -/
theorem M.trans (hxy : ml.M x y) (hyz : ml.M y z) : ml.M x z :=
  by_contra fun h ↦ ((ml.irrelevance z hxy).2 ⟨hxy.lt.trans hyz.lt, h⟩).2 hyz

/-- M-boundedness, Theorem 2.2: what lies between marginally different degrees is marginally
different from each. -/
theorem M.bounded (hxz : ml.M x z) (hxy : x < y) (hyz : y < z) : ml.M x y ∧ ml.M y z :=
  ⟨by_contra fun h ↦ (L.trans_lt ⟨hxy, h⟩ hyz).2 hxz,
    by_contra fun h ↦ (L.of_lt_of_l hxy ⟨hyz, h⟩).2 hxz⟩

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
  rw [AtMostMarginal, Relation.reflGen_iff, Relation.SymmGen]
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro (rfl | h | h)
    · exact .rfl
    · exact ⟨h.not_l, fun h' ↦ h'.lt.asymm h.lt⟩
    · exact ⟨fun h' ↦ h'.lt.asymm h.lt, h.not_l⟩
  · rcases lt_trichotomy x y with h | rfl | h
    · exact .inr (.inl (not_not.1 fun hm ↦ h₁ ⟨h, hm⟩))
    · exact .inl rfl
    · exact .inr (.inr (not_not.1 fun hm ↦ h₂ ⟨h, hm⟩))

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := Relation.ReflGen.refl

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  atMostMarginal_iff_incompRel.2 (atMostMarginal_iff_incompRel.1 h).symm

theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z :=
  atMostMarginal_iff_incompRel.2 <| IsStrictWeakOrder.incomp_trans _ _ _
    (atMostMarginal_iff_incompRel.1 hxy) (atMostMarginal_iff_incompRel.1 hyz)

variable (ml) in
/-- Sameness for present purposes, at most marginal difference as an equivalence relation. -/
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
theorem m_iff_lt_and_atMostMarginal : ml.M x y ↔ x < y ∧ ml.AtMostMarginal x y :=
  ⟨fun h ↦ ⟨h.lt, .single (.inl h)⟩,
    fun ⟨hlt, h⟩ ↦ not_not.1 fun hm ↦ (atMostMarginal_iff_incompRel.1 h).1 ⟨hlt, hm⟩⟩

/-- A block of at most marginally different degrees is order-connected, by M-boundedness. -/
theorem ordConnected_setOf_atMostMarginal (x : α) :
    {y | ml.AtMostMarginal x y}.OrdConnected :=
  ⟨fun y hy z hz w ⟨hyw, hwz⟩ ↦ by
    rcases hyw.eq_or_lt with rfl | hyw; · exact hy
    rcases hwz.eq_or_lt with rfl | hwz; · exact hz
    have hyz := m_iff_lt_and_atMostMarginal.2 ⟨hyw.trans hwz, hy.symm.trans hz⟩
    exact hy.trans (.single (.inl (hyz.bounded hyw hwz).1))⟩

/-- Marginal difference is not transitive, since it is symmetric and irreflexive and
Decomposition makes some degree marginally smaller than another. -/
theorem not_isTrans_symmGen_m : ¬ IsTrans α (Relation.SymmGen ml.M) := fun ⟨htr⟩ ↦ by
  obtain ⟨x, y, h⟩ := ml.exists_large
  obtain ⟨z, hxz, -⟩ := (ml.decomposition h).1
  exact (htr x z x (.inl hxz) (.inr hxz)).elim (fun h ↦ h.lt.false) fun h ↦ h.lt.false

/-- Large difference is never transitive, strengthening the counterexample of fn. 9. By
Decomposition, a degree marginally above `x` and largely below `y` differs largely from `y`, as
`x` does, but not from `x`. -/
theorem not_isTrans_symmGen_l : ¬ IsTrans α (Relation.SymmGen ml.L) := fun ⟨htr⟩ ↦ by
  obtain ⟨x, y, h⟩ := ml.exists_large
  obtain ⟨z, hxz, hzy⟩ := (ml.decomposition h).1
  exact (htr x y z (.inl h) (.inr hzy)).elim hxz.not_l fun h' ↦ h'.lt.asymm hxz.lt

/-! ### Nonstandardness -/

/-- When `x` is largely smaller than `y`, infinitely many degrees lie marginally above `x` and
largely below `y`, since Decomposition gives each such degree a marginally greater one. -/
theorem L.infinite_setOf (h : ml.L x y) : {z | ml.M x z ∧ ml.L z y}.Infinite := fun hfin ↦ by
  obtain ⟨z₀, hz₀⟩ := (ml.decomposition h).1
  obtain ⟨z, ⟨hxz, hzy⟩, hmax⟩ := hfin.exists_maximal ⟨z₀, hz₀⟩
  obtain ⟨w, hzw, hwy⟩ := (ml.decomposition hzy).1
  exact (hmax ⟨hxz.trans hzw, hwy⟩ hzw.lt.le).not_gt hzw.lt

/-- Largely different degrees are infinitely far apart (§6.2). -/
theorem L.infinite_Ioo (h : ml.L x y) : (Set.Ioo x y).Infinite :=
  h.infinite_setOf.mono fun _ hz ↦ ⟨hz.1.lt, hz.2.lt⟩

/-- No conditionally complete linear order carries an ML scale, so ML theory has no model on the
naturals or the reals (fn. 7). The proof is that of [dinis-jacinto-2025]: the supremum of the
degrees marginally above `x` and largely below `y` would lie in the block of `y`, and a degree
marginally below it would be a smaller upper bound. -/
instance instIsEmptyOfConditionallyCompleteLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : IsEmpty (MLScale α) := by
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

example : IsEmpty (MLScale ℕ) := inferInstance

/-! ### The representative model -/

section Lex

theorem lt_and_not_lex_iff {β γ : Type*} [LinearOrder β] [LinearOrder γ] {x y : β ×ₗ γ} :
    x < y ∧ ¬ ((ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2) ↔
      (ofLex x).1 < (ofLex y).1 := by
  rw [Prod.Lex.lt_iff]
  exact ⟨fun ⟨h, hm⟩ ↦ h.resolve_right hm, fun h ↦ ⟨.inl h, fun hm ↦ h.ne hm.1⟩⟩

variable (β γ : Type*) [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ]

/-- Lexicographic pairs of a block and a location form an ML scale in which one pair is
marginally smaller than another when they share a block and its location is smaller. -/
def lex : MLScale (β ×ₗ γ) where
  M x y := (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2
  exists_large := by
    obtain ⟨a, b, hab⟩ := exists_pair_lt β
    obtain ⟨c⟩ := ‹Nonempty γ›
    exact ⟨toLex (a, c), toLex (b, c), lt_and_not_lex_iff.2 hab⟩
  lt_of_m _ _ h := Prod.Lex.lt_iff.2 (.inr h)
  irrelevance _ _ _ hxy :=
    ⟨fun h ↦ lt_and_not_lex_iff.2 ((lt_and_not_lex_iff.1 h).trans_eq hxy.1.symm),
      fun h ↦ lt_and_not_lex_iff.2 (hxy.1.symm.trans_lt (lt_and_not_lex_iff.1 h))⟩
  extends_lt _ _ _ hxy :=
    ⟨fun h ↦ lt_and_not_lex_iff.2
        ((Prod.Lex.monotone_fst _ _ hxy.le).trans_lt (lt_and_not_lex_iff.1 h)),
      fun h ↦ lt_and_not_lex_iff.2
        ((lt_and_not_lex_iff.1 h).trans_le (Prod.Lex.monotone_fst _ _ hxy.le))⟩
  decomposition x y h := by
    obtain ⟨c, hc⟩ := exists_gt (ofLex x).2
    obtain ⟨d, hd⟩ := exists_lt (ofLex y).2
    have h' := lt_and_not_lex_iff.1 h
    exact ⟨⟨toLex ((ofLex x).1, c), ⟨rfl, hc⟩, lt_and_not_lex_iff.2 h'⟩,
      ⟨toLex ((ofLex y).1, d), ⟨rfl, hd⟩, lt_and_not_lex_iff.2 h'⟩⟩

variable {β γ} in
theorem lex_l_iff {x y : β ×ₗ γ} : (lex β γ).L x y ↔ (ofLex x).1 < (ofLex y).1 :=
  lt_and_not_lex_iff

end Lex

/-- The representative model of Definition 3.1 orders rational-integer pairs
lexicographically, and one pair is marginally smaller than another when their first coordinates
agree and its second coordinate is smaller. -/
abbrev rep : MLScale (ℚ ×ₗ ℤ) := lex ℚ ℤ

/-! ### Representation -/

/-- A homomorphism of ML scales preserves and reflects smaller than and marginally smaller
than. -/
structure IsHom {β : Type*} [LinearOrder β] (ml : MLScale α) (ml' : MLScale β) (f : α → β) :
    Prop where
  strictMono : StrictMono f
  m_iff : ∀ x y, ml'.M (f x) (f y) ↔ ml.M x y

theorem IsHom.l_iff {β : Type*} [LinearOrder β] {ml' : MLScale β} {f : α → β}
    (hf : ml.IsHom ml' f) : ml'.L (f x) (f y) ↔ ml.L x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.m_iff x y))

variable (ml) in
/-- `y` is a weakly marginal successor of `x` when `x` is marginally smaller than `y` and no
degree marginally above `x` is marginally below `y`, Definition 4.4 of [dinis-jacinto-2025]. -/
def MarginalSucc (x y : α) : Prop := ml.M x y ∧ ∀ z, ml.M x z → ¬ ml.M z y

variable (ml) in
/-- An ML scale is finitely marginal when finitely many weakly marginal successions lead from
any degree to any marginally greater one, Definition 4.5 of [dinis-jacinto-2025] (fn. 15). -/
def FinitelyMarginal : Prop := ∀ ⦃x y⦄, ml.M x y → Relation.TransGen ml.MarginalSucc x y

theorem MarginalSucc.Icc_subset (h : ml.MarginalSucc x y) : Set.Icc x y ⊆ {x, y} :=
  fun z ⟨hxz, hzy⟩ ↦ by
    rcases hxz.eq_or_lt with rfl | hxz; · exact .inl rfl
    rcases hzy.eq_or_lt with rfl | hzy; · exact .inr rfl
    exact absurd (h.1.bounded hxz hzy).2 (h.2 z (h.1.bounded hxz hzy).1)

/-- In a finitely marginal ML scale, the closed interval between at most marginally different
degrees is finite. -/
theorem FinitelyMarginal.finite_Icc (hf : ml.FinitelyMarginal) (h : ml.AtMostMarginal x y) :
    (Set.Icc x y).Finite := by
  rcases h with _ | h | h
  · simp
  · obtain hc := hf h
    clear h
    induction hc with
    | single hs => exact (Set.toFinite _).subset hs.Icc_subset
    | tail _ hs ih =>
      exact (ih.union ((Set.toFinite _).subset hs.Icc_subset)).subset Set.Icc_subset_Icc_union_Icc
  · simp [h.lt]

/-- Every countable, finitely marginal ML scale embeds in the representative model, the
representation theorem of [dinis-jacinto-2025] that the paper invokes (p. 111). A block goes to
the rational assigned to its representative by an order embedding of the representatives into
`ℚ`, and a degree's location is its signed distance from the representative of its block. -/
theorem exists_isHom_rep [Countable α] (hf : ml.FinitelyMarginal) :
    ∃ f : α → ℚ ×ₗ ℤ, ml.IsHom rep f := by
  classical
  let r : α → α := fun x ↦ (Quotient.mk ml.atMostMarginalSetoid x).out
  have hr (x : α) : ml.AtMostMarginal (r x) x := Quotient.mk_out (s := ml.atMostMarginalSetoid) _
  have hr_eq (x y : α) : r x = r y ↔ ml.AtMostMarginal x y := Quotient.out_inj.trans Quotient.eq
  have : Countable (Set.range r) := (Set.countable_range r).to_subtype
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := Set.range r) (β := ℚ)
  let F : α → ℚ := fun x ↦ e ⟨r x, x, rfl⟩
  have hF_eq (x y : α) : F x = F y ↔ ml.AtMostMarginal x y :=
    e.eq_iff_eq.trans (Subtype.ext_iff.trans (hr_eq x y))
  have hF (x y : α) : F x < F y ↔ ml.L x y := by
    refine e.lt_iff_lt.trans (Subtype.mk_lt_mk.trans ⟨fun h ↦ by_contra fun hl ↦ ?_, fun h ↦ ?_⟩)
    · by_cases hl' : ml.L y x
      · exact h.asymm ((hr y).l_congr_left.2 ((hr x).l_congr_right.2 hl')).lt
      · exact h.ne ((hr_eq x y).2 (atMostMarginal_iff_incompRel.2 ⟨hl, hl'⟩))
    · exact ((hr x).l_congr_left.2 ((hr y).l_congr_right.2 h)).lt
  let G : α → ℤ := fun x ↦ (Set.Ico (r x) x).ncard - (Set.Ico x (r x)).ncard
  have hG (x y : α) (hxy : ml.M x y) : G x < G y := by
    have hrxy : r x = r y := (hr_eq x y).2 (.single (.inl hxy))
    simp only [G, hrxy]
    have f₁ : (Set.Ico (r y) y).Finite := (hf.finite_Icc (hr y)).subset Set.Ico_subset_Icc_self
    have f₂ : (Set.Ico x (r y)).Finite :=
      (hf.finite_Icc (hrxy ▸ (hr x).symm)).subset Set.Ico_subset_Icc_self
    have h₁ := Set.ncard_le_ncard (Set.Ico_subset_Ico_right hxy.lt.le) f₁
    have h₂ := Set.ncard_le_ncard (Set.Ico_subset_Ico_left hxy.lt.le) f₂
    rcases le_or_gt (r y) x with hbx | hxb
    · have := Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset
        (Set.Ico_subset_Ico_right hxy.lt.le)).2 ⟨x, ⟨hbx, hxy.lt⟩, fun h ↦ h.2.false⟩) f₁
      omega
    · have := Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset
        (Set.Ico_subset_Ico_left hxy.lt.le)).2 ⟨x, ⟨le_rfl, hxb⟩, fun h ↦ h.1.not_gt hxy.lt⟩) f₂
      omega
  refine ⟨fun x ↦ toLex (F x, G x), ⟨fun x y hxy ↦ ?_, fun x y ↦ ?_⟩⟩
  · rcases m_or_l_of_lt hxy with hm | hl
    · exact Prod.Lex.lt_iff.2 (.inr ⟨(hF_eq x y).2 (.single (.inl hm)), hG x y hm⟩)
    · exact Prod.Lex.lt_iff.2 (.inl ((hF x y).2 hl))
  · refine ⟨fun ⟨he, hlt⟩ ↦ ?_, fun hm ↦ ⟨(hF_eq x y).2 (.single (.inl hm)), hG x y hm⟩⟩
    rcases (hF_eq x y).1 he with _ | hm | hm
    · exact absurd hlt (lt_irrefl _)
    · exact hm
    · exact absurd (hG y x hm) hlt.not_gt

/-! ### The marginality scales account -/

section Account

variable {C O : Type*} (ml) (μ : C → O → α)

/-- The comparative holds when the object `x` at circumstance `u` is greater on the scale
than the object `y` at circumstance `v`. -/
def Comparative (u : C) (x : O) (v : C) (y : O) : Prop := μ v y < μ u x

/-- The positive form, after Fara, holds when the standard of comparison is largely smaller
than the object's degree at the circumstance. -/
def Positive (norm : α) (w : C) (x : O) : Prop := ml.L norm (μ w x)

variable {ml μ} {norm : α} {w u v : C} {a b : O}

/-- An object in the positive form's extension exceeds the standard of comparison. -/
theorem setOf_positive_subset_gt_over :
    {x | ml.Positive μ norm w x} ⊆ Degree.Comparison.gt.over (μ w) norm :=
  fun _ h ↦ h.lt

/-- An object whose degree exceeds the standard only marginally is not in the positive form's
extension (Figure 5). -/
theorem not_positive_of_m (h : ml.M norm (μ w a)) : ¬ ml.Positive μ norm w a := h.not_l

/-- The degrees largely greater than a standard form an upper set. -/
theorem isUpperSet_setOf_l (x : α) : IsUpperSet {d | ml.L x d} :=
  fun _ _ hle h ↦ hle.eq_or_lt.elim (· ▸ h) h.trans_lt

/-- An object in the positive form's extension at one circumstance and out of it at another is
greater on the scale at the first, the case of Charles III (§5.4). -/
theorem comparative_of_positive_of_not_positive (h₁ : ml.Positive μ norm u a)
    (h₂ : ¬ ml.Positive μ norm v a) : Comparative μ u a v a :=
  lt_of_not_ge fun h ↦ h₂ (isUpperSet_setOf_l norm h h₁)

/-- Objects whose degrees differ at most marginally are both in the positive form's extension
or both out of it, Fara's similarity constraint (§6.1). -/
theorem AtMostMarginal.positive_iff (h : ml.AtMostMarginal (μ w a) (μ w b)) :
    ml.Positive μ norm w a ↔ ml.Positive μ norm w b :=
  h.l_congr_right

/-- However many marginal steps separate two objects' degrees, the objects are alike for the
positive form (§6.1). -/
theorem positive_iff_of_reflTransGen (h : Relation.ReflTransGen ml.M (μ w a) (μ w b)) :
    ml.Positive μ norm w a ↔ ml.Positive μ norm w b := by
  rw [Relation.reflTransGen_eq_reflGen] at h
  exact AtMostMarginal.positive_iff (h.mono fun _ _ ↦ .inl)

/-- In a Soritical sequence for the positive form, ordered by degree, whose first member is out
of the extension and whose last member is in it, some member is largely greater than its
predecessor, the nonstandard primitivist solution to the Sorites (§3, §6.1). -/
theorem exists_large_step_of_soritical {l : List O} (hl : l.IsChain fun x y ↦ μ w x < μ w y)
    (hne : l ≠ []) (h₁ : ¬ ml.Positive μ norm w (l.head hne))
    (h₂ : ml.Positive μ norm w (l.getLast hne)) :
    ∃ l₁ l₂ x y, l = l₁ ++ x :: y :: l₂ ∧ ml.L (μ w x) (μ w y) := by
  by_contra! h
  have hm : l.IsChain fun x y ↦ ml.M (μ w x) (μ w y) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.2 fun _ _ _ _ e ↦
      (m_or_l_of_lt (List.isChain_iff_forall_rel_of_append_cons_cons.1 hl e)).resolve_right
        (h _ _ _ _ e)
  exact h₁ ((positive_iff_of_reflTransGen
    ((List.relationReflTransGen_of_exists_isChain l hm hne).lift (μ w) fun _ _ ↦ id)).2 h₂)

variable (ml) in
/-- A property is clustered when something has it iff its degree differs at most marginally
from the degree of something that has it (§3). -/
def Clustered (B : O → Prop) (δ : O → α) : Prop :=
  ∀ x, B x ↔ ∃ y, B y ∧ ml.AtMostMarginal (δ y) (δ x)

/-- Clustered degrees imply degree tolerance. An object whose degree is marginally greater than
that of an object without the property lacks it, and an object whose degree is marginally
smaller than that of an object with the property has it (§3). The ML axioms are not needed. -/
theorem Clustered.tolerance {B : O → Prop} {δ : O → α} (h : ml.Clustered B δ) :
    (¬ B a → ml.M (δ a) (δ b) → ¬ B b) ∧ (B a → ml.M (δ b) (δ a) → B b) :=
  ⟨fun ha hm hb ↦ ha ((h a).2 ⟨b, hb, .single (.inr hm)⟩),
    fun ha hm ↦ (h b).2 ⟨a, ha, .single (.inr hm)⟩⟩

/-- The positive form's extension is clustered, so the marginality scales account implies the
nonstandard primitivist principle of §3. -/
theorem clustered_positive : ml.Clustered (ml.Positive μ norm w) (μ w) := fun _ ↦
  ⟨fun h ↦ ⟨_, h, .refl _⟩, fun ⟨_, hy, hxy⟩ ↦ (AtMostMarginal.positive_iff hxy).1 hy⟩

/-- Under a representation, the positive form is the strict comparison of an object's block
with the standard's block. -/
theorem setOf_positive_eq_gt_over {f : α → ℚ ×ₗ ℤ} (hf : ml.IsHom rep f) :
    {x | ml.Positive μ norm w x} =
      Degree.Comparison.gt.over (fun x ↦ (ofLex (f (μ w x))).1) (ofLex (f norm)).1 :=
  Set.ext fun _ ↦ hf.l_iff.symm.trans lex_l_iff

/-- If a representation places the standard and Ronaldo in block `0` and Zidane in block `1`,
then Zidane is balder than Ronaldo, and Zidane is bald where Ronaldo, though balder than the
standard, is not (§5.2). -/
theorem zidane_ronaldo {f : α → ℚ ×ₗ ℤ} (hf : ml.IsHom rep f) {zidane ronaldo : O}
    (hz : (ofLex (f (μ w zidane))).1 = 1) (hr : (ofLex (f (μ w ronaldo))).1 = 0)
    (hn : (ofLex (f norm)).1 = 0) :
    Comparative μ w zidane w ronaldo ∧ ml.Positive μ norm w zidane ∧
      ¬ ml.Positive μ norm w ronaldo :=
  ⟨(hf.l_iff.1 (lex_l_iff.2 (by rw [hz, hr]; exact zero_lt_one))).lt,
    hf.l_iff.1 (lex_l_iff.2 (by rw [hz, hn]; exact zero_lt_one)),
    fun h ↦ (lex_l_iff.1 (hf.l_iff.2 h)).ne (hn.trans hr.symm)⟩

end Account

/-- The two-scale alternative of §5.4 reads the comparative off precise degrees `ρ` and the
positive form off vague degrees `τ w` of precise degrees. When the agent's interests change, it
lets an object leave the positive form's extension without having been greater on the precise
scale. -/
theorem exists_twoScale_not_comparative : ∃ (ρ : Bool → Unit → ℕ) (τ : Bool → ℕ → ℚ ×ₗ ℤ),
    rep.Positive (fun w x ↦ τ w (ρ w x)) (toLex (0, 0)) true () ∧
      ¬ rep.Positive (fun w x ↦ τ w (ρ w x)) (toLex (0, 0)) false () ∧
      ¬ Comparative ρ true () false () :=
  ⟨fun _ _ ↦ 0, fun w _ ↦ toLex (if w then 1 else 0, 0), lex_l_iff.2 zero_lt_one,
    fun h ↦ lt_irrefl (0 : ℚ) (lex_l_iff.1 h), lt_irrefl 0⟩

end MLScale

end DinisJacinto2026
