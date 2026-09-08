import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Defs.Unbundled
import Linglib.Core.Order.TotalPreorder

/-!
# Dimensional aggregation

A multidimensional predicate applies to an object, or ranks two objects, according to how the
objects stand on several underlying dimensions. Two aggregation vocabularies share this file.

*Rules*, in the value-function framework of [sen-1970] as [dambrosio-hedden-2024] transposes it
to dimensions: a profile assigns each object its vector of dimensional values, and a rule sends
profiles to an overall relation on the objects, read `x ⪰ y`. Sen's informational requirements
are invariance under a class of transformation vectors (strictly increasing maps, common-unit
positive affine maps, similarities). Arrow's conditions ([arrow-1950]) and the strong Pareto,
Pareto-indifference and anonymity conditions are predicates on rules. Four classical rules are
stated with the conditions they meet or fail: majority ([may-1952]) meets every Arrow condition
but weak-ordering outputs, which Condorcet's cycle refutes; the Pareto rule ([weymark-1984]) is
a quasi-ordering that leaves every trade-off incomparable; the utilitarian rule meets every
Arrow condition but ordinal invariance, failing even ratio-scale invariance; the Cobb–Douglas
rule ([tsui-weymark-1997]) is ratio-scale invariant on non-negative profiles.

*Scores* for the positive form: a weighted sum of dimensional measures ([waldon-etal-2023]),
its normalisation by the host's spatial extent ([tham-2025], [solt-2018-proportional]), and
the multiplicative composition of [sassoon-fadlon-2017].

## Implementation notes

* A rule is total on profiles, so Arrow's unrestricted-domain condition is built in; a domain
  restriction, such as the non-negative profiles the Cobb–Douglas rule needs, is a hypothesis
  of the statement.
* Outputs are bare relations, because majority rule is not transitive; a weak-ordering-valued
  rule bundles into `Core.Order.TotalPreorder`. `AsymmRel` is the strict part of a relation and
  mathlib's `AntisymmRel` its indifference part.

## TODO

* The scores index dimensions by lists. Restating them over `ι → K`, so that the utilitarian
  rule compares `weightedScore`s, awaits the cleanse of their consumers.

## References

* [K. J. Arrow, *A difficulty in the concept of social welfare* (1951)][arrow-1950]
* [J. D'Ambrosio and B. Hedden, *Multidimensional adjectives* (2024)][dambrosio-hedden-2024]
* [K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision* (1952)][may-1952]
* [G. W. Sassoon and J. Fadlon, *The role of dimensions in classification under predicates
  predicts their status in degree constructions* (2017)][sassoon-fadlon-2017]
* [A. K. Sen, *Collective choice and social welfare* (1970)][sen-1970]
* [S. Solt, *Proportional comparatives and relative scales* (2018)][solt-2018-proportional]
* [S. W. Tham, *Multidimensionality and the scalar components of physical disturbance
  predicates* (2025)][tham-2025]
* [K.-Y. Tsui and J. A. Weymark, *Social welfare orderings for ratio-scale measurable
  utilities* (1997)][tsui-weymark-1997]
* [B. Waldon, C. Condoravdi, B. Levin and J. Degen, *On the context dependence of artifact
  noun interpretation* (2023)][waldon-etal-2023]
* [J. A. Weymark, *Arrow's theorem with social quasi-orderings* (1984)][weymark-1984]
-/

/-- The asymmetric part of a relation: `r a b` and not `r b a`. Mathlib's `AntisymmRel r` is
the symmetric part. -/
def AsymmRel {α : Type*} (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {α : Type*} (r : α → α → Prop) [DecidableRel r] (a b : α) :
    Decidable (AsymmRel r a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem AsymmRel.trans_le {α : Type*} {r : α → α → Prop} [IsTrans α r] {a b c : α}
    (h : AsymmRel r a b) (h' : r b c) : AsymmRel r a c :=
  ⟨IsTrans.trans _ _ _ h.1 h', λ hca => h.2 (IsTrans.trans _ _ _ h' hca)⟩

theorem AsymmRel.le_trans {α : Type*} {r : α → α → Prop} [IsTrans α r] {a b c : α}
    (h : r a b) (h' : AsymmRel r b c) : AsymmRel r a c :=
  ⟨IsTrans.trans _ _ _ h h'.1, λ hca => h'.2 (IsTrans.trans _ _ _ hca h)⟩

namespace Degree.Aggregation

open Finset

variable {ι α K : Type*}

/-- A profile: each object's vector of values, one per dimension. -/
abbrev Profile (ι α K : Type*) := α → ι → K

/-- An aggregation rule: a relation on the objects, read `x ⪰ y`, for each profile. -/
abbrev Rule (ι α K : Type*) := Profile ι α K → α → α → Prop

/-- Apply a vector of transformations, one per dimension, to a profile. -/
def Profile.transform (f : ι → K → K) (v : Profile ι α K) : Profile ι α K :=
  λ x i => f i (v x i)

/-! ### Informational invariance -/

/-- Invariance of a rule under a class of transformation vectors. -/
def Invariant (T : Set (ι → K → K)) (a : Rule ι α K) : Prop :=
  ∀ f ∈ T, ∀ v, a (v.transform f) = a v

theorem Invariant.mono {S T : Set (ι → K → K)} (h : S ⊆ T) {a : Rule ι α K}
    (ha : Invariant T a) : Invariant S a :=
  λ f hf => ha f (h hf)

/-- Vectors of strictly increasing transformations; invariance under them is ordinal
non-comparability. -/
def ordinal [Preorder K] : Set (ι → K → K) := {f | ∀ i, StrictMono (f i)}

section Cardinal

variable [Semiring K] [PartialOrder K]

/-- Common-unit positive affine transformation vectors; invariance under them is cardinal unit
comparability. -/
def cardinalUnit : Set (ι → K → K) :=
  {f | ∃ a : K, 0 < a ∧ ∃ b : ι → K, ∀ i t, f i t = a * t + b i}

/-- Similarity transformation vectors; invariance under them is ratio-scale
non-comparability. -/
def ratio : Set (ι → K → K) := {f | ∃ a : ι → K, (∀ i, 0 < a i) ∧ ∀ i t, f i t = a i * t}

variable [IsStrictOrderedRing K]

theorem cardinalUnit_subset_ordinal : cardinalUnit ⊆ (ordinal : Set (ι → K → K)) := by
  rintro f ⟨a, ha, b, hf⟩ i s t hst
  simp only [hf]
  exact add_lt_add_left (mul_lt_mul_of_pos_left hst ha) _

theorem ratio_subset_ordinal : ratio ⊆ (ordinal : Set (ι → K → K)) := by
  rintro f ⟨a, ha, hf⟩ i s t hst
  simp only [hf]
  exact mul_lt_mul_of_pos_left hst (ha i)

end Cardinal

/-! ### Conditions on rules -/

section Conditions

variable (a : Rule ι α K)

/-- Pareto indifference: objects with the same vector of values are indifferent. -/
def ParetoIndifferent : Prop := ∀ v x y, v x = v y → AntisymmRel (a v) x y

/-- Independence of irrelevant alternatives: the verdict on a pair depends only on the vectors
of that pair. -/
def Independent : Prop := ∀ v w x y, v x = w x → v y = w y → (a v x y ↔ a w x y)

/-- Every output is transitive. -/
def Transitive : Prop := ∀ v, IsTrans α (a v)

/-- Every output is complete. -/
def Complete : Prop := ∀ v, Std.Total (a v)

/-- Every output is a weak ordering, a complete preorder. -/
def WeakOrderValued : Prop := Transitive a ∧ Complete a

/-- Every output is a quasi-ordering, a preorder. -/
def QuasiOrderValued : Prop := ∀ v, IsPreorder α (a v)

/-- Anonymity: permuting the dimensions leaves the output unchanged. -/
def Anonymous : Prop := ∀ (σ : Equiv.Perm ι) v, a (λ x => v x ∘ σ) = a v

variable {a}

/-- The output of a weak-ordering-valued rule at a profile, as a bundled total preorder. -/
def WeakOrderValued.toTotalPreorder (h : WeakOrderValued a) (v : Profile ι α K) :
    Core.Order.TotalPreorder α :=
  haveI := h.1 v
  haveI := h.2 v
  ⟨a v, IsPreorder.mk, h.2 v⟩

theorem WeakOrderValued.lt_toTotalPreorder (h : WeakOrderValued a) (v : Profile ι α K) :
    (h.toTotalPreorder v).lt = AsymmRel (a v) :=
  rfl

theorem WeakOrderValued.quasiOrderValued (h : WeakOrderValued a) : QuasiOrderValued a :=
  λ v =>
    haveI := h.1 v
    haveI := h.2 v
    IsPreorder.mk

variable (a) [Preorder K]

/-- Weak Pareto: an object ranked strictly above another on every dimension is strictly
preferred. -/
def WeakPareto : Prop := ∀ v x y, (∀ i, v y i < v x i) → AsymmRel (a v) x y

/-- Strong Pareto: an object ranked weakly above another on every dimension is weakly
preferred, and strictly so if some dimension ranks it strictly above. -/
def StrongPareto : Prop :=
  ∀ v x y, v y ≤ v x → a v x y ∧ ((∃ i, v y i < v x i) → AsymmRel (a v) x y)

/-- Dimension `i` is a dictator: its strict rankings are the strict overall rankings. -/
def IsDictator (i : ι) : Prop := ∀ v x y, v y i < v x i → AsymmRel (a v) x y

/-- No dimension is a dictator. -/
def NonDictatorial : Prop := ∀ i, ¬ IsDictator a i

end Conditions

/-! ### Majority rule -/

section Majority

variable [Fintype ι] [LinearOrder K]

/-- Majority rule: `x ⪰ y` iff at least as many dimensions rank `x` weakly above `y` as rank
`y` weakly above `x`. -/
def majority : Rule ι α K := λ v x y => #{i | v x i ≤ v y i} ≤ #{i | v y i ≤ v x i}

instance (v : Profile ι α K) : DecidableRel (majority v) := λ _ _ => by
  unfold majority; infer_instance

theorem majority_weakPareto [Nonempty ι] : WeakPareto (majority : Rule ι α K) := by
  intro v x y h
  have h₁ : ({i | v x i ≤ v y i} : Finset ι) = ∅ := filter_false_of_mem λ i _ => (h i).not_ge
  have h₂ : ({i | v y i ≤ v x i} : Finset ι) = univ := filter_true_of_mem λ i _ => (h i).le
  simp [AsymmRel, majority, h₁, h₂, Fintype.card_ne_zero]

theorem majority_independent : Independent (majority : Rule ι α K) := by
  intro v w x y hx hy
  simp only [majority, hx, hy]

theorem majority_ordinalInvariant : Invariant ordinal (majority : Rule ι α K) := by
  intro f hf v
  funext x y
  simp only [majority, Profile.transform, (hf _).le_iff_le]

theorem majority_anonymous : Anonymous (majority : Rule ι α K) := by
  intro σ v
  funext x y
  have h : ∀ z w : α, #{i | v z (σ i) ≤ v w (σ i)} = #{i | v z i ≤ v w i} :=
    λ z w => card_equiv σ (by simp)
  simp only [majority, Function.comp_apply, h]

theorem majority_paretoIndifferent : ParetoIndifferent (majority : Rule ι α K) := by
  intro v x y h
  simp [AntisymmRel, majority, h]

theorem majority_nonDictatorial [Nontrivial ι] [Nontrivial α] [Nontrivial K] :
    NonDictatorial (majority : Rule ι α K) := by
  intro i hi
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  obtain ⟨k, k', hk⟩ : ∃ k k' : K, k < k' := by
    obtain ⟨k, k', h⟩ := exists_pair_ne K
    exact h.lt_or_gt.elim (λ h => ⟨k, k', h⟩) (λ h => ⟨k', k, h⟩)
  classical
  let v : Profile ι α K := λ z l => if (z = x ∧ l = i) ∨ (z = y ∧ l = j) then k' else k
  have hv : v y i < v x i := by simp [v, hxy.symm, hj.symm, hk]
  have e₁ : ({l | v x l ≤ v y l} : Finset ι) = univ.erase i := by
    rw [← filter_ne']
    refine filter_congr λ l _ => ?_
    by_cases hl : l = i <;> by_cases hl' : l = j <;>
      simp [v, hl, hl', hxy, hxy.symm, hj, hj.symm, hk.le, hk.not_ge]
  have e₂ : ({l | v y l ≤ v x l} : Finset ι) = univ.erase j := by
    rw [← filter_ne']
    refine filter_congr λ l _ => ?_
    by_cases hl : l = i <;> by_cases hl' : l = j <;>
      simp [v, hl, hl', hxy, hxy.symm, hj, hj.symm, hk.le, hk.not_ge]
  have hcard : #(univ.erase i) = #(univ.erase j) := by
    rw [card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _)]
  have := hi v x y hv
  simp only [AsymmRel, majority, e₁, e₂, hcard, le_refl, not_true, and_false] at this

/-- Condorcet's profile: three dimensions ranking three objects cyclically. -/
def condorcet : Profile (Fin 3) (Fin 3) ℕ := ![![2, 0, 1], ![1, 2, 0], ![0, 1, 2]]

/-- Condorcet's paradox: majority rule ranks the three objects in a strict cycle. -/
theorem majority_condorcet :
    AsymmRel (majority condorcet) 0 1 ∧ AsymmRel (majority condorcet) 1 2 ∧
      AsymmRel (majority condorcet) 2 0 := by
  decide

/-- Majority rule does not output transitive relations. -/
theorem not_transitive_majority : ¬ Transitive (majority : Rule (Fin 3) (Fin 3) ℕ) := by
  intro h
  obtain ⟨h₀₁, h₁₂, h₂₀⟩ := majority_condorcet
  exact h₂₀.2 ((h condorcet).trans 0 1 2 h₀₁.1 h₁₂.1)

end Majority

/-! ### The Pareto rule -/

section Pareto

variable [Preorder K]

/-- The Pareto rule: `x ⪰ y` iff every dimension ranks `x` weakly above `y`. -/
def paretoRule : Rule ι α K := λ v x y => v y ≤ v x

theorem paretoRule_quasiOrderValued : QuasiOrderValued (paretoRule : Rule ι α K) :=
  λ _ => { refl := λ _ => le_rfl, trans := λ _ _ _ h h' => h'.trans h }

theorem paretoRule_strongPareto : StrongPareto (paretoRule : Rule ι α K) :=
  λ _ _ _ h => ⟨h, λ ⟨i, hi⟩ => ⟨h, λ h' => (h' i).not_gt hi⟩⟩

theorem paretoRule_paretoIndifferent : ParetoIndifferent (paretoRule : Rule ι α K) :=
  λ _ _ _ h => ⟨h.ge, h.le⟩

theorem paretoRule_independent : Independent (paretoRule : Rule ι α K) := by
  intro v w x y hx hy
  simp only [paretoRule, hx, hy]

theorem paretoRule_anonymous : Anonymous (paretoRule : Rule ι α K) := by
  intro σ v
  funext x y
  simp only [paretoRule, Pi.le_def, Function.comp_apply]
  exact propext ⟨λ h i => by simpa using h (σ.symm i), λ h i => h _⟩

/-- A trade-off, one dimension ranking `x` strictly above `y` and another `y` above `x`, is
incomparable under the Pareto rule. -/
theorem paretoRule_incomparable {v : Profile ι α K} {x y : α} {i j : ι} (hi : v y i < v x i)
    (hj : v x j < v y j) : ¬ paretoRule v x y ∧ ¬ paretoRule v y x :=
  ⟨λ h => (h j).not_gt hj, λ h => (h i).not_gt hi⟩

end Pareto

theorem paretoRule_ordinalInvariant [LinearOrder K] :
    Invariant ordinal (paretoRule : Rule ι α K) := by
  intro f hf v
  funext x y
  simp only [paretoRule, Profile.transform, Pi.le_def, (hf _).le_iff_le]

/-! ### The utilitarian rule -/

section Utilitarian

variable [Fintype ι] [Field K] [LinearOrder K]

/-- The utilitarian rule with weights `c`: `x ⪰ y` iff the weighted sum of values favours
`x`. -/
def utilitarian (c : ι → K) : Rule ι α K := λ v x y => c ⬝ᵥ v y ≤ c ⬝ᵥ v x

variable (c : ι → K)

theorem utilitarian_weakOrderValued : WeakOrderValued (utilitarian c : Rule ι α K) :=
  ⟨λ _ => ⟨λ _ _ _ h h' => h'.trans h⟩, λ _ => ⟨λ _ _ => le_total _ _⟩⟩

theorem utilitarian_paretoIndifferent : ParetoIndifferent (utilitarian c : Rule ι α K) := by
  intro v x y h
  simp [AntisymmRel, utilitarian, h]

theorem utilitarian_independent : Independent (utilitarian c : Rule ι α K) := by
  intro v w x y hx hy
  simp only [utilitarian, hx, hy]

variable [IsStrictOrderedRing K]

theorem utilitarian_weakPareto (hc : ∀ i, 0 ≤ c i) (hpos : ∃ i, 0 < c i) :
    WeakPareto (utilitarian c : Rule ι α K) := by
  intro v x y h
  obtain ⟨i, hi⟩ := hpos
  have : c ⬝ᵥ v y < c ⬝ᵥ v x :=
    sum_lt_sum (λ i _ => mul_le_mul_of_nonneg_left (h i).le (hc i))
      ⟨i, mem_univ _, mul_lt_mul_of_pos_left (h i) hi⟩
  exact ⟨this.le, this.not_ge⟩

theorem utilitarian_cardinalUnitInvariant :
    Invariant cardinalUnit (utilitarian c : Rule ι α K) := by
  rintro f ⟨s, hs, b, hf⟩ v
  funext x y
  have key : ∀ z, (v.transform f) z = s • v z + b := λ z => funext λ i => by
    simp [Profile.transform, hf]
  simp only [utilitarian, key, dotProduct_add, dotProduct_smul, smul_eq_mul,
    add_le_add_iff_right, mul_le_mul_iff_of_pos_left hs]

theorem utilitarian_nonDictatorial [Nontrivial α] (h₂ : ∀ i, ∃ j, j ≠ i ∧ 0 < c j) :
    NonDictatorial (utilitarian c : Rule ι α K) := by
  intro i hi
  obtain ⟨j, hji, hj⟩ := h₂ i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  let v : Profile ι α K := λ z =>
    if z = x then Pi.single i (c j) else if z = y then Pi.single j (c i + c j) else 0
  have hv : v y i < v x i := by simp [v, hxy.symm, hji.symm, hj]
  have hx : c ⬝ᵥ v x = c i * c j := by simp [v]
  have hy : c ⬝ᵥ v y = c j * (c i + c j) := by simp [v, hxy.symm]
  have := (hi v x y hv).1
  simp only [utilitarian, hx, hy, mul_add, mul_comm (c j) (c i)] at this
  exact (lt_add_of_pos_right _ (mul_pos hj hj)).not_ge this

/-- With two positive weights the utilitarian rule is not even ratio-scale invariant: rescaling
one dimension breaks a tie. -/
theorem not_ratioInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant ratio (utilitarian c : Rule ι α K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  let v : Profile ι α K := λ z =>
    if z = x then Pi.single i (c j) else if z = y then Pi.single j (c i) else 0
  let f : ι → K → K := λ l t => if l = j then 2 * t else t
  have hf : f ∈ ratio := ⟨λ l => if l = j then 2 else 1,
    λ l => by dsimp only; split_ifs <;> norm_num, λ l t => by simp only [f]; split_ifs <;> simp⟩
  have hx : (v.transform f) x = Pi.single i (c j) := funext λ l => by
    simp only [Profile.transform, v, f, if_true, Pi.single_apply]
    split_ifs <;> simp_all
  have hy : (v.transform f) y = Pi.single j (2 * c i) := funext λ l => by
    simp only [Profile.transform, v, f, hxy.symm, if_false, if_true, Pi.single_apply]
    split_ifs <;> simp_all
  have := congrFun (congrFun (h f hf v) x) y
  simp only [utilitarian, hx, hy, v, if_true, hxy.symm, if_false, dotProduct_single,
    mul_comm (c j) (c i), eq_iff_iff] at this
  have hpos := mul_pos hi hj
  exact (this.2 le_rfl).not_gt (by linarith)

theorem not_ordinalInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant ordinal (utilitarian c : Rule ι α K) :=
  λ h => not_ratioInvariant_utilitarian c hij hi hj (h.mono ratio_subset_ordinal)

end Utilitarian

/-! ### The Cobb–Douglas rule -/

section CobbDouglas

variable [Fintype ι] (c : ι → ℝ)

/-- The Cobb–Douglas rule with exponents `c`: `x ⪰ y` iff the weighted geometric product of
values favours `x`. -/
def cobbDouglas : Rule ι α ℝ := λ v x y => ∏ i, v y i ^ c i ≤ ∏ i, v x i ^ c i

theorem cobbDouglas_weakOrderValued : WeakOrderValued (cobbDouglas c : Rule ι α ℝ) :=
  ⟨λ _ => ⟨λ _ _ _ h h' => h'.trans h⟩, λ _ => ⟨λ _ _ => le_total _ _⟩⟩

theorem cobbDouglas_paretoIndifferent : ParetoIndifferent (cobbDouglas c : Rule ι α ℝ) := by
  intro v x y h
  simp [AntisymmRel, cobbDouglas, h]

theorem cobbDouglas_independent : Independent (cobbDouglas c : Rule ι α ℝ) := by
  intro v w x y hx hy
  simp only [cobbDouglas, hx, hy]

/-- On non-negative profiles the Cobb–Douglas rule is ratio-scale invariant. -/
theorem cobbDouglas_transform_of_nonneg {f : ι → ℝ → ℝ} (hf : f ∈ ratio) {v : Profile ι α ℝ}
    (hv : ∀ x i, 0 ≤ v x i) : cobbDouglas c (v.transform f) = cobbDouglas c v := by
  obtain ⟨s, hs, hf⟩ := hf
  funext x y
  simp only [cobbDouglas, Profile.transform, hf, Real.mul_rpow (hs _).le (hv _ _),
    prod_mul_distrib]
  exact propext (mul_le_mul_iff_of_pos_left (prod_pos λ i _ => Real.rpow_pos_of_pos (hs i) _))

end CobbDouglas

/-! ### Arrow's theorem -/

section Arrow

variable [LinearOrder K] {a : Rule ι α K}

/-- `G` is decisive: whenever every dimension in `G` ranks `x` strictly above `y`, the rule
ranks `x` strictly above `y`. -/
def Decisive (a : Rule ι α K) (G : Finset ι) : Prop :=
  ∀ v x y, (∀ i ∈ G, v y i < v x i) → AsymmRel (a v) x y

/-- `G` is decisive for the pair `x, y`. -/
def DecisiveOn (a : Rule ι α K) (G : Finset ι) (x y : α) : Prop :=
  ∀ v, (∀ i ∈ G, v y i < v x i) → AsymmRel (a v) x y

/-- `G` is almost decisive for the pair `x, y`: it prevails when every dimension outside `G`
ranks `y` strictly above `x`. -/
def AlmostDecisiveOn (a : Rule ι α K) (G : Finset ι) (x y : α) : Prop :=
  ∀ v, (∀ i ∈ G, v y i < v x i) → (∀ i ∉ G, v x i < v y i) → AsymmRel (a v) x y

theorem DecisiveOn.almost {G : Finset ι} {x y : α} (h : DecisiveOn a G x y) :
    AlmostDecisiveOn a G x y :=
  λ v hG _ => h v hG

theorem decisive_of_decisiveOn {G : Finset ι} (hne : G.Nonempty)
    (h : ∀ x y, x ≠ y → DecisiveOn a G x y) : Decisive a G := by
  intro v x y hv
  rcases eq_or_ne x y with rfl | hxy
  · obtain ⟨i, hi⟩ := hne
    exact absurd (hv i hi) (lt_irrefl _)
  · exact h x y hxy v hv

variable [Field K] [IsStrictOrderedRing K]

/-- Under ordinal invariance and independence, the verdict on a pair depends only on how each
dimension orders the pair. -/
theorem iff_of_pattern (hO : Invariant ordinal a) (hI : Independent a)
    {v w : Profile ι α K} {x y : α}
    (h : ∀ i, (v x i < v y i ↔ w x i < w y i) ∧ (v y i < v x i ↔ w y i < w x i)) :
    a v x y ↔ a w x y := by
  let f : Profile ι α K → ι → K → K := λ u i t =>
    if u x i = u y i then t - u x i else (t - u x i) / |u y i - u x i|
  have hf : ∀ u, f u ∈ ordinal := λ u => by
    intro i s t hst
    dsimp only [f]
    split_ifs with h
    · exact sub_lt_sub_right hst _
    · exact div_lt_div_of_pos_right (sub_lt_sub_right hst _)
        (abs_pos.2 (sub_ne_zero.2 (Ne.symm h)))
  have hx : ∀ u : Profile ι α K, Profile.transform (f u) u x = 0 := λ u => funext λ i => by
    simp only [Profile.transform, f]
    split_ifs <;> simp
  have hy : ∀ u : Profile ι α K, Profile.transform (f u) u y =
      λ i => if u x i < u y i then 1 else if u y i < u x i then -1 else 0 := λ u =>
    funext λ i => by
      simp only [Profile.transform, f]
      rcases lt_trichotomy (u x i) (u y i) with hlt | heq | hgt
      · rw [if_neg hlt.ne, if_pos hlt, abs_of_pos (sub_pos.2 hlt), div_self (sub_pos.2 hlt).ne']
      · simp [heq]
      · rw [if_neg hgt.ne', if_neg (lt_asymm hgt), if_pos hgt, abs_of_neg (sub_neg.2 hgt),
          div_neg, div_self (sub_neg.2 hgt).ne]
  have hyw : Profile.transform (f v) v y = Profile.transform (f w) w y := by
    rw [hy, hy]
    funext i
    simp only [(h i).1, (h i).2]
  calc a v x y ↔ a (v.transform (f v)) x y := by rw [hO (f v) (hf v) v]
    _ ↔ a (w.transform (f w)) x y := hI _ _ x y (by rw [hx, hx]) hyw
    _ ↔ a w x y := by rw [hO (f w) (hf w) w]

/-- Field expansion, first half: a group almost decisive for `x, y` is decisive for `x, z`. -/
theorem decisiveOn_of_almost (hW : WeakOrderValued a) (hP : WeakPareto a) (hI : Independent a)
    {G : Finset ι} {x y : α} (hxy : x ≠ y) (h : AlmostDecisiveOn a G x y) {z : α}
    (hzy : z ≠ y) : DecisiveOn a G x z := by
  intro v hv
  classical
  let v' : Profile ι α K := λ w i =>
    if w = y then (if i ∈ G then (v x i + v z i) / 2 else max (v x i) (v z i) + 1) else v w i
  have hx : v' x = v x := funext λ i => by simp [v', hxy]
  have hz : v' z = v z := funext λ i => by simp [v', hzy]
  have hG : ∀ i ∈ G, v' y i < v' x i := λ i hi => by
    simp only [v', if_true, if_neg hxy, if_pos hi]
    linarith [hv i hi]
  have hG' : ∀ i ∉ G, v' x i < v' y i := λ i hi => by
    simp only [v', if_true, if_neg hxy, if_neg hi]
    linarith [le_max_left (v x i) (v z i)]
  have hyz : ∀ i, v' z i < v' y i := λ i => by
    by_cases hi : i ∈ G
    · simp only [v', if_true, if_neg hzy, if_pos hi]
      linarith [hv i hi]
    · simp only [v', if_true, if_neg hzy, if_neg hi]
      linarith [le_max_right (v x i) (v z i)]
  have := hW.1 v'
  have h₃ : AsymmRel (a v') x z := (h v' hG hG').trans_le (hP v' y z hyz).1
  exact ⟨(hI v' v x z hx hz).1 h₃.1, λ hzx' => h₃.2 ((hI v' v z x hz hx).2 hzx')⟩

/-- Field expansion, second half: a group almost decisive for `x, y` is decisive for `z, y`. -/
theorem decisiveOn_of_almost' (hW : WeakOrderValued a) (hP : WeakPareto a) (hI : Independent a)
    {G : Finset ι} {x y : α} (hxy : x ≠ y) (h : AlmostDecisiveOn a G x y) {z : α}
    (hzx : z ≠ x) : DecisiveOn a G z y := by
  intro v hv
  classical
  let v' : Profile ι α K := λ w i =>
    if w = x then (if i ∈ G then (v z i + v y i) / 2 else min (v z i) (v y i) - 1) else v w i
  have hz : v' z = v z := funext λ i => by simp [v', hzx]
  have hy : v' y = v y := funext λ i => by simp [v', hxy.symm]
  have hzx' : ∀ i, v' x i < v' z i := λ i => by
    by_cases hi : i ∈ G
    · simp only [v', if_true, if_neg hzx, if_pos hi]
      linarith [hv i hi]
    · simp only [v', if_true, if_neg hzx, if_neg hi]
      linarith [min_le_left (v z i) (v y i)]
  have hG : ∀ i ∈ G, v' y i < v' x i := λ i hi => by
    simp only [v', if_true, if_neg hxy.symm, if_pos hi]
    linarith [hv i hi]
  have hG' : ∀ i ∉ G, v' x i < v' y i := λ i hi => by
    simp only [v', if_true, if_neg hxy.symm, if_neg hi]
    linarith [min_le_right (v z i) (v y i)]
  have := hW.1 v'
  have h₃ : AsymmRel (a v') z y := (hP v' z x hzx').trans_le (h v' hG hG').1
  exact ⟨(hI v' v z y hz hy).1 h₃.1, λ hyz => h₃.2 ((hI v' v y z hy hz).2 hyz)⟩

variable [Fintype α]

/-- Field expansion: with three or more objects, a group almost decisive for one pair is
decisive for every pair. -/
theorem decisiveOn_of_almost_of_ne (hW : WeakOrderValued a) (hP : WeakPareto a)
    (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) {G : Finset ι} {x y : α} (hxy : x ≠ y)
    (h : AlmostDecisiveOn a G x y) {u w : α} (huw : u ≠ w) : DecisiveOn a G u w := by
  have A : ∀ p q, p ≠ q → AlmostDecisiveOn a G p q → ∀ r, r ≠ p → r ≠ q →
      DecisiveOn a G p r ∧ DecisiveOn a G r q :=
    λ p q hpq hpq' r hrp hrq =>
      ⟨decisiveOn_of_almost hW hP hI hpq hpq' hrq, decisiveOn_of_almost' hW hP hI hpq hpq' hrp⟩
  obtain ⟨z, hzx, hzy⟩ : ∃ z, z ≠ x ∧ z ≠ y := by
    by_contra hz
    push Not at hz
    classical
    have hsub : (Finset.univ : Finset α) ⊆ {x, y} := λ z _ => by
      rcases eq_or_ne z x with rfl | hzx
      · simp
      · simp [hz z hzx]
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    simp only [Finset.card_univ, Finset.card_singleton] at this
    omega
  have hxz : DecisiveOn a G x z := (A x y hxy h z hzx hzy).1
  have hzy' : DecisiveOn a G z y := (A x y hxy h z hzx hzy).2
  have hxy' : DecisiveOn a G x y := (A x z hzx.symm hxz.almost y hxy.symm hzy.symm).1
  have hyz : DecisiveOn a G y z := (A x z hzx.symm hxz.almost y hxy.symm hzy.symm).2
  have hzx' : DecisiveOn a G z x := (A z y hzy hzy'.almost x hzx.symm hxy).1
  have key : ∀ u, ∃ q, q ≠ u ∧ DecisiveOn a G u q := λ u => by
    rcases eq_or_ne u x with rfl | hux
    · exact ⟨y, hxy.symm, hxy'⟩
    rcases eq_or_ne u y with rfl | huy
    · exact ⟨z, hzy, hyz⟩
    rcases eq_or_ne u z with rfl | huz
    · exact ⟨x, hzx.symm, hzx'⟩
    · exact ⟨y, huy.symm, (A x y hxy h u hux huy).2⟩
  obtain ⟨q, hqu, hq⟩ := key u
  rcases eq_or_ne w q with rfl | hwq
  · exact hq
  · exact (A u q hqu.symm hq.almost w huw.symm hwq).1

/-- Group contraction: a decisive group with two or more dimensions has a decisive proper
subgroup. -/
theorem exists_decisive_ssubset (hO : Invariant ordinal a) (hW : WeakOrderValued a)
    (hP : WeakPareto a) (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) {G : Finset ι}
    (hG : Decisive a G) (h₂ : 2 ≤ G.card) : ∃ G' ⊂ G, Decisive a G' := by
  classical
  obtain ⟨i, hi⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := (Fintype.two_lt_card_iff (α := α)).1 (by omega)
  let v : Profile ι α K := λ w j =>
    if j = i then (if w = x then 2 else if w = y then 1 else 0)
    else if j ∈ G then (if w = y then 2 else if w = z then 1 else 0)
    else (if w = z then 2 else if w = x then 1 else 0)
  have hv : ∀ j, (v x j < v z j ↔ j ≠ i) ∧ (v z j < v x j ↔ j = i) ∧
      (v y j < v x j ↔ j ∉ G ∨ j = i) ∧ (v x j < v y j ↔ j ∈ G ∧ j ≠ i) := λ j => by
    by_cases hji : j = i
    · subst hji
      simp [v, hxy.symm, hxz.symm, hyz.symm, hi]
    · by_cases hj : j ∈ G <;> simp [v, hji, hj, hxy, hxz, hyz, hxy.symm, hyz.symm]
  have hyz' : AsymmRel (a v) y z := hG v y z λ j hj => by
    by_cases hji : j = i
    · subst hji; simp [v, hxz.symm, hxy.symm, hyz.symm]
    · simp [v, hji, hj, hyz.symm]
  have := hW.1 v
  by_cases hxz' : AsymmRel (a v) x z
  · refine ⟨{i}, Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 hi, ?_⟩, ?_⟩
    · rintro rfl
      simp at h₂
    · refine decisive_of_decisiveOn ⟨i, Finset.mem_singleton_self i⟩ λ p q hpq =>
        decisiveOn_of_almost_of_ne hW hP hI h₃ hxz ?_ hpq
      intro u hu hu'
      have hpat : ∀ j, (u x j < u z j ↔ v x j < v z j) ∧ (u z j < u x j ↔ v z j < v x j) := by
        intro j
        rw [(hv j).1, (hv j).2.1]
        rcases eq_or_ne j i with rfl | hji
        · have := hu j (Finset.mem_singleton_self j)
          exact ⟨⟨λ h => absurd h (lt_asymm this), λ h => absurd rfl h⟩,
            ⟨λ _ => rfl, λ _ => this⟩⟩
        · have := hu' j (by simpa using hji)
          exact ⟨⟨λ _ => hji, λ _ => this⟩, ⟨λ h => absurd h (lt_asymm this), λ h => absurd h hji⟩⟩
      exact ⟨(iff_of_pattern hO hI hpat).2 hxz'.1,
        λ h' => hxz'.2 ((iff_of_pattern hO hI λ j => ⟨(hpat j).2, (hpat j).1⟩).1 h')⟩
  · have hzx : a v z x := by
      by_contra hzx
      exact hxz' ⟨((hW.2 v).total x z).resolve_right hzx, hzx⟩
    have hyx : AsymmRel (a v) y x := hyz'.trans_le hzx
    refine ⟨G.erase i, Finset.erase_ssubset hi, ?_⟩
    have hne : (G.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hi]; omega
    refine decisive_of_decisiveOn hne λ p q hpq =>
      decisiveOn_of_almost_of_ne hW hP hI h₃ hxy.symm ?_ hpq
    intro u hu hu'
    have hpat : ∀ j, (u y j < u x j ↔ v y j < v x j) ∧ (u x j < u y j ↔ v x j < v y j) := by
      intro j
      rw [(hv j).2.2.1, (hv j).2.2.2]
      by_cases hj : j ∈ G.erase i
      · have := hu j hj
        rw [Finset.mem_erase] at hj
        exact ⟨⟨λ h => absurd h (lt_asymm this),
            λ h => absurd (h.resolve_right hj.1) (λ h' => h' hj.2)⟩,
          ⟨λ _ => ⟨hj.2, hj.1⟩, λ _ => this⟩⟩
      · have := hu' j hj
        rw [Finset.mem_erase, not_and_or, not_not] at hj
        exact ⟨⟨λ _ => hj.symm, λ _ => this⟩,
          ⟨λ h => absurd h (lt_asymm this),
            λ h => absurd h (λ h' => hj.elim (λ e => h'.2 e) (λ e => e h'.1))⟩⟩
    exact ⟨(iff_of_pattern hO hI hpat).2 hyx.1,
      λ h' => hyx.2 ((iff_of_pattern hO hI λ j => ⟨(hpat j).2, (hpat j).1⟩).1 h')⟩

variable [Fintype ι]

/-- Arrow's theorem: with three or more objects, a rule that is ordinally invariant, outputs
weak orderings, respects weak Pareto and is independent has a dictator. -/
theorem exists_isDictator (hO : Invariant ordinal a) (hW : WeakOrderValued a)
    (hP : WeakPareto a) (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) :
    ∃ i, IsDictator a i := by
  classical
  obtain ⟨x⟩ := Fintype.card_pos_iff.1 (show 0 < Fintype.card α by omega)
  have huniv : Decisive a Finset.univ := λ v p q h => hP v p q λ i => h i (Finset.mem_univ i)
  obtain ⟨G, hG, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset ι)).filter (Decisive a)) Finset.card ⟨_, by simpa using huniv⟩
  rw [Finset.mem_filter] at hG
  have hne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := hG.2 (λ _ _ => 0) x x (by simp)
    exact this.2 this.1
  have hcard : G.card = 1 := by
    by_contra h
    obtain ⟨G', hG', hdec⟩ := exists_decisive_ssubset hO hW hP hI h₃ hG.2
      (by have := hne.card_pos; omega)
    have := hmin G' (by simpa using hdec)
    exact absurd (Finset.card_lt_card hG') (not_lt.2 this)
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
  exact ⟨i, λ v p q h => hG.2 v p q λ j hj => (Finset.mem_singleton.1 hj) ▸ h⟩

/-- Arrow's theorem as an impossibility: no rule meets all of Arrow's conditions. -/
theorem arrow (h₃ : 3 ≤ Fintype.card α) (a : Rule ι α K) :
    ¬ (Invariant ordinal a ∧ WeakOrderValued a ∧ WeakPareto a ∧ Independent a ∧
      NonDictatorial a) :=
  λ ⟨hO, hW, hP, hI, hD⟩ => let ⟨i, hi⟩ := exists_isDictator hO hW hP hI h₃; hD i hi

end Arrow

/-! ### Scores for the positive form -/

section Scores

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Lift Bool dimension predicates to `K`-valued measure functions.
    Each `d : α → Bool` becomes `λ x => if d x then 1 else 0`. -/
def boolMeasures (dims : List (α → Bool)) : List (α → K) :=
  dims.map (λ d x => if d x then 1 else 0)

/-- Weighted score: Σᵢ wᵢ · fᵢ(x), where each fᵢ : α → K is a
    measure function along one dimension ([waldon-etal-2023]'s eq. (8)). -/
def weightedScore (weights : List K) (measures : List (α → K)) (x : α) : K :=
  (weights.zip measures).foldl (λ acc (w, f) => acc + w * f x) 0

/-- Spatially-normalized weighted score: (Σᵢ wᵢ·fᵢ(x)) / s(x).

    [tham-2025] eq. 47b for physical disturbance adjectives. The
    `measures` track per-dimension EXTENT of disturbance (e.g., total
    crack length, depth-weighted area); the `spatial` measure tracks the
    host entity's SPATIAL EXTENT. A small disturbance on a small host can
    score the same as a large disturbance on a large host — boundedness
    of the scale comes from the denominator, not from any single
    dimension. Returns `0` when `spatial x = 0` (avoiding division by
    zero); callers should ensure `spatial x ≠ 0` for meaningful results. -/
def spatialNormalizedScore (weights : List K) (measures : List (α → K))
    (spatial : α → K) (x : α) : K :=
  if spatial x = 0 then 0 else weightedScore weights measures x / spatial x

/-- Spatially-normalized weighted binding (Bool dimensions): x is F iff
    its spatially-normalized weighted score over Bool-lifted measures
    exceeds threshold θ. -/
def spatialNormalizedBinding (weights : List K) (θ : K)
    (dims : List (α → Bool)) (spatial : α → K) (x : α) : Bool :=
  decide (spatialNormalizedScore weights (boolMeasures dims) spatial x ≥ θ)

/-- The spatial-normalization reduces to plain weighted score when
    `spatial x = 1` (constant unit host extent). -/
@[simp]
theorem spatialNormalizedScore_unit (weights : List K) (measures : List (α → K))
    (x : α) :
    spatialNormalizedScore weights measures (λ _ => 1) x =
      weightedScore weights measures x := by
  unfold spatialNormalizedScore
  split_ifs with h
  · exact absurd h one_ne_zero
  · exact div_one _

omit [IsStrictOrderedRing K] in
/-- Spatial normalisation at a zero-extent host returns 0: a host with no spatial extent
exhibits no disturbance. -/
@[simp]
theorem spatialNormalizedScore_zero (weights : List K) (measures : List (α → K))
    (spatial : α → K) (x : α) (h : spatial x = 0) :
    spatialNormalizedScore weights measures spatial x = 0 := by
  simp [spatialNormalizedScore, h]

/-- A weighted score bounded by the host's spatial extent normalises to at most 1:
[tham-2025]'s boundedness from spatial extent. -/
theorem spatialNormalizedScore_le_one
    (weights : List K) (measures : List (α → K))
    (spatial : α → K) (x : α)
    (hsum : weightedScore weights measures x ≤ spatial x)
    (hpos : 0 < spatial x) :
    spatialNormalizedScore weights measures spatial x ≤ 1 := by
  unfold spatialNormalizedScore
  rw [if_neg hpos.ne']
  exact div_le_one_of_le₀ hsum hpos.le

/-- A nonnegative weighted score over a nonnegative extent normalises to a nonnegative score;
with `spatialNormalizedScore_le_one` it lies in `[0, 1]`, the fraction of the totality of
[tham-2025] and [solt-2018-proportional]. -/
theorem spatialNormalizedScore_nonneg
    (weights : List K) (measures : List (α → K))
    (spatial : α → K) (x : α)
    (hnum : 0 ≤ weightedScore weights measures x)
    (hspatial : 0 ≤ spatial x) :
    0 ≤ spatialNormalizedScore weights measures spatial x := by
  unfold spatialNormalizedScore
  by_cases h : spatial x = 0
  · rw [if_pos h]
  · rw [if_neg h]; exact div_nonneg hnum hspatial

/-- Multiplicative (Cobb-Douglas) score: Πᵢ fᵢ(x).
    [sassoon-fadlon-2017] argue natural kind nouns compose
    multiplicatively: failure on ANY single dimension kills membership.
    Contrast with additive `weightedScore` for artifact nouns. -/
def multiplicativeScore (measures : List (α → K)) (x : α) : K :=
  measures.foldl (λ acc f => acc * f x) 1

end Scores

end Degree.Aggregation
