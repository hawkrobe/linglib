module

public import Linglib.Core.Order.CountableDenseLinearOrder
public import Linglib.Core.Order.SuccPred.LinearLocallyFinite
public import Linglib.Semantics.Degree.Marginality
public import Mathlib.Analysis.Real.Hyperreal

/-!
# Dinis and Jacinto (2025): A Theory of Marginal and Large Difference

Dinis and Jacinto propose ML theory, eleven axioms on marginally and largely smaller than along a
strict weak order, and give it a measurement theory. Every model is infinite, since a large
difference decomposes into a marginal step and a further large difference, and the theory has no
model on the naturals or the reals, but it has models in nonstandard analysis, where a marginal
difference is an infinitesimal one. Every countable, finitely marginal model maps homomorphically
into the representative model of rational-indexed blocks of integer-indexed locations, and any
two such maps differ by a transformation that rescales blocks and locations within blocks. In a
Sorites whose series is infinite, being bald as not being largely less bald than the last member
makes the premises jointly satisfiable.

## Main statements

* `DinisJacinto2025.infinite_of_mlScale`: every ML scale is infinite.
* `DinisJacinto2025.infinitesimal_m_iff`, `DinisJacinto2025.finite_m_iff`: infinitesimal and
  finite differences of hyperreals are the marginal differences of ML scales.
* `DinisJacinto2025.exists_isHom_rep`: every countable, finitely marginal ML scale maps
  homomorphically into the representative model; `DinisJacinto2025.exists_isHom_lex_rat`: every
  countable one maps into rational-indexed blocks of rational-indexed locations.
* `DinisJacinto2025.IsHom.comp_cautiouslyMonotone`,
  `DinisJacinto2025.IsHom.exists_cautiouslyMonotone`: representations are unique up to cautiously
  monotone-increasing transformations.
* `DinisJacinto2025.Bald.tolerance`, `DinisJacinto2025.not_transGen_m`: baldness is tolerant,
  and no finite chain of marginal steps leads from someone not bald to the last member.

## Implementation notes

* The eleven axioms are `Degree.MLScale.IsMLModel`. The project's ML scales are those of
  [dinis-jacinto-2026], over a linear order with marginally smaller than primitive, and the
  results here are stated for them; a homomorphism then preserves and reflects smaller than and
  marginally smaller than, and is injective.
* The nonstandard models are mathlib's hyperreals, infinitesimal differences being those of
  positive archimedean class. The finite-difference reading of Dean and Itzhaki (§5, §6), stated
  for nonstandard integers, is taken on the hyperreals.

## TODO

* The arithmetical model `ℑ1` of §3.2 and the model `ℜ` with an initial block of §4.3 need a
  nonstandard model of arithmetic, which mathlib lacks.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
* [dean-2018]
* [itzhaki-2021]
-/

@[expose] public section

namespace DinisJacinto2025

open Degree MLScale

variable {α : Type*} [LinearOrder α] {ml : MLScale α} {x y : α}

/-! ### Infinitude -/

/-- Every ML scale is infinite (p. 521). -/
theorem infinite_of_mlScale (ml : MLScale α) : Infinite α :=
  let ⟨_, _, h⟩ := ml.exists_large
  Set.infinite_univ_iff.1 ((L.infinite_Ioo h).mono (Set.subset_univ _))

example : IsEmpty (MLScale ℕ) := inferInstance

example : IsEmpty (MLScale ℝ) := inferInstance

/-! ### Nonstandard models -/

open ArchimedeanClass Hyperreal

/-- The hyperreals with infinitesimal differences marginal, the model `ℑ2` of Theorem 3.1. -/
noncomputable def infinitesimal : MLScale ℝ* :=
  ofAddSubgroup (ballAddSubgroup 0) (ordConnected_ballAddSubgroup 0)
    (fun h ↦ by
      have : ε ∈ ballAddSubgroup (0 : ArchimedeanClass ℝ*) :=
        (mem_ballAddSubgroup_iff (by simp)).2 archimedeanClassMk_epsilon_pos
      simp_all [epsilon_ne_zero])
    (fun h ↦ by
      have : (1 : ℝ*) ∈ ballAddSubgroup (0 : ArchimedeanClass ℝ*) := h ▸ AddSubgroup.mem_top _
      simp at this)

theorem infinitesimal_m_iff {x y : ℝ*} : infinitesimal.M x y ↔ x < y ∧ 0 < mk (y - x) := by
  rw [infinitesimal, ofAddSubgroup_m_iff, mem_ballAddSubgroup_iff (by simp)]

/-- The hyperreals with finite differences marginal, the reading of Dean (§5) and of Itzhaki
(§6). -/
noncomputable def finite : MLScale ℝ* :=
  ofAddSubgroup (closedBallAddSubgroup 0) (ordConnected_closedBallAddSubgroup 0)
    (fun h ↦ by
      have : (1 : ℝ*) ∈ closedBallAddSubgroup (0 : ArchimedeanClass ℝ*) := by
        simp
      simp_all)
    (fun h ↦ by
      have : ω ∈ closedBallAddSubgroup (0 : ArchimedeanClass ℝ*) := h ▸ AddSubgroup.mem_top _
      exact (mem_closedBallAddSubgroup_iff.1 this).not_gt archimedeanClassMk_omega_neg)

theorem finite_m_iff {x y : ℝ*} : finite.M x y ↔ x < y ∧ 0 ≤ mk (y - x) := by
  rw [finite, ofAddSubgroup_m_iff, mem_closedBallAddSubgroup_iff]

example : infinitesimal.M 0 ε ∧ infinitesimal.L 0 1 :=
  ⟨infinitesimal_m_iff.2 ⟨epsilon_pos, by simp [archimedeanClassMk_epsilon_pos]⟩,
    zero_lt_one, fun h ↦ by simpa using (infinitesimal_m_iff.1 h).2⟩

example : finite.M 0 1 ∧ finite.L 0 ω :=
  ⟨finite_m_iff.2 ⟨zero_lt_one, by simp⟩, omega_pos,
    fun h ↦ (finite_m_iff.1 h).2.not_gt (by simp [archimedeanClassMk_omega_neg])⟩

/-! ### Representation -/

variable (ml) in
/-- `y` is a weakly marginal successor of `x` when `x` is marginally smaller than `y` and no
degree marginally above `x` is marginally below `y` (Definition 4.4). -/
def MarginalSucc (x y : α) : Prop := ml.M x y ∧ ∀ z, ml.M x z → ¬ ml.M z y

variable (ml) in
/-- An ML scale is finitely marginal when finitely many weakly marginal successions lead from
any degree to any marginally greater one (Definition 4.5). -/
def FinitelyMarginal : Prop := ∀ ⦃x y⦄, ml.M x y → Relation.TransGen (MarginalSucc ml) x y

theorem MarginalSucc.Icc_subset (h : MarginalSucc ml x y) : Set.Icc x y ⊆ {x, y} :=
  fun z ⟨hxz, hzy⟩ ↦ by
    rcases hxz.eq_or_lt with rfl | hxz; · exact .inl rfl
    rcases hzy.eq_or_lt with rfl | hzy; · exact .inr rfl
    exact absurd (h.1.bounded hxz hzy).2 (h.2 z (h.1.bounded hxz hzy).1)

/-- In a finitely marginal ML scale, the closed interval between at most marginally different
degrees is finite. -/
theorem FinitelyMarginal.finite_Icc (hf : FinitelyMarginal ml) (h : ml.AtMostMarginal x y) :
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

/-- In a finitely marginal ML scale, every block is locally finite. -/
theorem FinitelyMarginal.finite_Icc_block (hf : FinitelyMarginal ml)
    (q : Quotient ml.atMostMarginalSetoid) (a b : {y // ⟦y⟧ = q}) : (Set.Icc a b).Finite :=
  (hf.finite_Icc (Quotient.exact (a.2.trans b.2.symm))).preimage Subtype.val_injective.injOn

/-- When every block embeds in `γ`, the degrees can be given locations in `γ` that grow along
marginal steps. -/
theorem exists_lt_of_m {γ : Type*} [Preorder γ]
    (h : ∀ q : Quotient ml.atMostMarginalSetoid, ∃ g : {y // ⟦y⟧ = q} → γ, StrictMono g) :
    ∃ G : α → γ, ∀ ⦃x y⦄, ml.M x y → G x < G y := by
  choose g hg using h
  have e (z : α) (q) (h : ⟦z⟧ = q) : g ⟦z⟧ ⟨z, rfl⟩ = g q ⟨z, h⟩ := by subst h; rfl
  refine ⟨fun z ↦ g ⟦z⟧ ⟨z, rfl⟩, fun x y h ↦ ?_⟩
  have hxy : (⟦x⟧ : Quotient ml.atMostMarginalSetoid) = ⟦y⟧ := Quotient.sound (.single (.inl h))
  simp only [e x _ hxy]
  exact hg _ h.lt

/-- Every countable, finitely marginal ML scale maps homomorphically into the representative
model (Theorem 4.7). -/
theorem exists_isHom_rep [Countable α] (hf : FinitelyMarginal ml) :
    ∃ f : α → ℚ ×ₗ ℤ, ml.IsHom rep f := by
  obtain ⟨F, hF⟩ := Order.exists_rat_rel_iff_lt ml.L
  obtain ⟨G, hG⟩ := exists_lt_of_m fun q ↦ by
    let := LocallyFiniteOrder.ofFiniteIcc (hf.finite_Icc_block q)
    obtain ⟨e⟩ := nonempty_orderEmbedding_int {y // ⟦y⟧ = q}
    exact ⟨e, e.strictMono⟩
  exact ⟨fun x ↦ toLex (F x, G x), isHom_lex_iff.2 ⟨hF, hG⟩⟩

/-- Every countable ML scale maps homomorphically into rational-indexed blocks of
rational-indexed locations (§4.4). -/
theorem exists_isHom_lex_rat [Countable α] : ∃ f : α → ℚ ×ₗ ℚ, ml.IsHom (lex ℚ ℚ) f := by
  obtain ⟨F, hF⟩ := Order.exists_rat_rel_iff_lt ml.L
  obtain ⟨G, hG⟩ := exists_lt_of_m (γ := ℚ) fun q ↦ by
    obtain ⟨e⟩ := Order.embedding_from_countable_to_dense {y : α // ⟦y⟧ = q} ℚ
    exact ⟨e, e.strictMono⟩
  exact ⟨fun x ↦ toLex (F x, G x), isHom_lex_iff.2 ⟨hF, hG⟩⟩

/-! ### Uniqueness -/

section Uniqueness

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- A transformation of a set of pairs is cautiously monotone-increasing when it maps blocks by
one strictly increasing map and the locations within each block by strictly increasing maps
(Definition 4.8). -/
def CautiouslyMonotone (X : Set (β ×ₗ γ)) (τ : β ×ₗ γ → β ×ₗ γ) : Prop :=
  ∃ (f : β → β) (g : β → γ → γ), StrictMonoOn f ((fun p ↦ (ofLex p).1) '' X) ∧
    (∀ a, StrictMonoOn (g a) {b | toLex (a, b) ∈ X}) ∧
    ∀ p ∈ X, τ p = toLex (f (ofLex p).1, g (ofLex p).1 (ofLex p).2)

variable [Nontrivial β] [Nonempty γ] [NoMaxOrder γ] [NoMinOrder γ]

/-- A representation composed with a cautiously monotone-increasing transformation is a
representation (Theorem 4.9). -/
theorem IsHom.comp_cautiouslyMonotone {h : α → β ×ₗ γ} (hh : ml.IsHom (lex β γ) h)
    {τ : β ×ₗ γ → β ×ₗ γ} (hτ : CautiouslyMonotone (Set.range h) τ) :
    ml.IsHom (lex β γ) (τ ∘ h) := by
  obtain ⟨f, g, hf, hg, hτ⟩ := hτ
  obtain ⟨hL, hM⟩ := isHom_lex_iff.1 hh
  refine isHom_lex_iff.2 ⟨fun x y ↦ ?_, fun x y hxy ↦ ?_⟩
  · simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, hL]
    exact (hf.lt_iff_lt ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, rfl⟩).symm
  · have he : (ofLex (h x)).1 = (ofLex (h y)).1 := hh.fst_eq_fst_iff.2 (.single (.inl hxy))
    simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, he]
    exact hg _ (by simp [← he]) ⟨y, rfl⟩ (hM hxy)

/-- Any two representations differ by a cautiously monotone-increasing transformation
(Theorem 4.9). -/
theorem IsHom.exists_cautiouslyMonotone {h u : α → β ×ₗ γ} (hh : ml.IsHom (lex β γ) h)
    (hu : ml.IsHom (lex β γ) u) : ∃ τ, CautiouslyMonotone (Set.range h) τ ∧ u = τ ∘ h := by
  obtain ⟨hhL, -⟩ := isHom_lex_iff.1 hh
  obtain ⟨huL, huM⟩ := isHom_lex_iff.1 hu
  let f := Function.extend (fun x ↦ (ofLex (h x)).1) (fun x ↦ (ofLex (u x)).1) id
  let g (a : β) (b : γ) : γ :=
    Function.extend (fun x ↦ ofLex (h x)) (fun x ↦ (ofLex (u x)).2) Prod.snd (a, b)
  have hf (x : α) : f (ofLex (h x)).1 = (ofLex (u x)).1 :=
    Function.FactorsThrough.extend_apply
      (fun _ _ he ↦ hu.fst_eq_fst_iff.2 (hh.fst_eq_fst_iff.1 he)) _ x
  have hg (x : α) : g (ofLex (h x)).1 (ofLex (h x)).2 = (ofLex (u x)).2 :=
    ((ofLex.injective.comp hh.strictMono.injective).factorsThrough _).extend_apply _ x
  refine ⟨fun p ↦ toLex (f (ofLex p).1, g (ofLex p).1 (ofLex p).2),
    ⟨f, g, ?_, fun a ↦ ?_, fun _ _ ↦ rfl⟩, funext fun x ↦ by rw [Function.comp_apply, hf, hg]; rfl⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩ hxy
    rw [hf, hf, ← huL, hhL]
    exact hxy
  · rintro b₁ ⟨x, hx⟩ b₂ ⟨y, hy⟩ hb
    have := huM ((hh.m_iff x y).1 (by rw [hx, hy]; exact lex_m_iff.2 ⟨rfl, hb⟩))
    simp only [← hg, hx, hy, ofLex_toLex] at this ⊢
    exact this

end Uniqueness

/-! ### The Sorites -/

section Sorites

variable (ml) in
/-- In the Sorites of §5, to be bald is not to be largely less bald than the last member `e` of
the series. -/
def Bald (e x : α) : Prop := ¬ ml.L x e

variable {e : α}

/-- Whatever is balder than the last member is bald. -/
theorem bald_of_le (h : e ≤ x) : Bald ml e x := fun hl ↦ (hl.lt.trans_le h).false

/-- Baldness is tolerant. What is marginally balder than someone not bald is not bald, and what
is marginally less bald than someone bald is bald. -/
theorem Bald.tolerance :
    (¬ Bald ml e x → ml.M x y → ¬ Bald ml e y) ∧ (Bald ml e x → ml.M y x → Bald ml e y) := by
  unfold Bald
  grind [ml.irrelevance, L]

/-- No finite chain of marginal steps leads from someone not bald to the last member, so a
series in which each member is marginally balder than the one before satisfies the premises of
the Sorites only if it is infinite. -/
theorem not_transGen_m (hx : ¬ Bald ml e x) : ¬ Relation.TransGen ml.M x e := fun h ↦ by
  rw [Relation.transGen_eq_self] at h
  exact h.not_l (not_not.1 hx)

example : ¬ Bald rep (toLex (1, 0)) (toLex (0, 0)) ∧ Bald rep (toLex (1, 0)) (toLex (1, 0)) :=
  ⟨not_not.2 (lex_l_iff.2 zero_lt_one), bald_of_le le_rfl⟩

end Sorites

end DinisJacinto2025
