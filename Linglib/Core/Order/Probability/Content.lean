import Linglib.Core.Order.Probability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Additive contents and the orders they induce

Finitely additive (`FinAddMeasure`) and qualitatively additive
(`QualAddMeasure`) probability contents on `Set W`, valued in an ordered field,
and the qualitative probability orders they induce.

## Main definitions

* `FinAddMeasure`, `QualAddMeasure` — with `FunLike` application `m A`,
  `ofFintype` (discrete contents), `map` (pushforward).
* `QualAddMeasure.toQualitativeProbability`, `FinAddMeasure.toQualAdd`,
  `FinAddMeasure.toQualitativeProbability`.

## Implementation notes

The contents are generic over an ordered field `K`: `ℝ` gives classical
`[0,1]`-valued measures, `ℚ` the computable theory. On a finite state space the
two agree (rational and real linear feasibility coincide), and only `ℚ` supports
the constructive Farkas (`Core/Order/FourierMotzkin.lean`) and `decide`-checked
models (`Representability.lean`) behind the representation theorems.
`FinAddMeasure` mirrors mathlib's `MeasureTheory.AddContent` interface (`FunLike`,
primed axiom fields with unprimed lemmas); re-founding on `AddContent` itself
would trade the ordered-field axioms for monoid-valued contents over a set
system with `sUnion` side conditions, so the structure stays local.
`FinAddMeasure.inducedGe` is `Order.Preimage ⇑m (· ≥ ·)`.
-/

namespace ComparativeProbability

/-- A finitely additive probability measure on subsets of `W`, valued in an
    ordered field `K`. The value type is left generic: instantiate at `ℚ` for the
    constructive, `decide`-able representation theory and at `ℝ` for classical
    `[0,1]`-valued measures (see the module docstring).

    The measure applies as a function: `m A`, via `FunLike`. -/
structure FinAddMeasure (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (W : Type*) where
  /-- The measure function. Apply the measure itself: `m A`. -/
  toFun : Set W → K
  /-- Non-negativity. Use the lemma `nonneg`. -/
  nonneg' : ∀ A, 0 ≤ toFun A
  /-- Finite additivity on disjoint sets. Use the lemma `additive`. -/
  additive' : ∀ A B, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B
  /-- Normalization. Use the lemma `total`. -/
  total' : toFun Set.univ = 1

namespace FinAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

instance : FunLike (FinAddMeasure K W) (Set W) K where
  coe := toFun
  coe_injective m m' _ := by cases m; cases m'; congr

@[simp] theorem coe_mk (f : Set W → K) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : FinAddMeasure K W) = f := rfl

@[simp] theorem toFun_eq_coe (m : FinAddMeasure K W) : m.toFun = ⇑m := rfl

@[ext] theorem ext {m m' : FinAddMeasure K W} (h : ∀ A, m A = m' A) : m = m' :=
  DFunLike.ext m m' h

theorem nonneg (m : FinAddMeasure K W) (A : Set W) : 0 ≤ m A := m.nonneg' A

theorem additive (m : FinAddMeasure K W) {A B : Set W} (h : Disjoint A B) :
    m (A ∪ B) = m A + m B := m.additive' A B h

@[simp] theorem total (m : FinAddMeasure K W) : m Set.univ = 1 := m.total'

/-- Measure-induced comparative likelihood `A ≿ B ↔ μ(A) ≥ μ(B)` — the
    `≿`-reading (`QualitativeProbability.ge`) consumed by the logic layer; the
    order itself is `toQualitativeProbability`. -/
def inducedGe (m : FinAddMeasure K W) (A B : Set W) : Prop := m A ≥ m B

/-- μ(∅) = 0 for any finitely additive measure.
    Follows from additivity: μ(∅ ∪ ∅) = μ(∅) + μ(∅), but ∅ ∪ ∅ = ∅. -/
@[simp] theorem mu_empty (m : FinAddMeasure K W) : m ∅ = 0 := by
  have h := m.additive (A := ∅) (B := ∅) disjoint_bot_left
  rw [Set.empty_union] at h; linarith

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. -/
theorem mu_mono (m : FinAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m A ≤ m B := by
  have hunion := m.additive (A := A) (B := B \ A) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel h] at hunion; linarith [m.nonneg (B \ A)]

/-- Complement measure: `μ(A) + μ(Aᶜ) = 1`. -/
theorem mu_compl (m : FinAddMeasure K W) (A : Set W) :
    m A + m Aᶜ = 1 := by
  have hunion := m.additive (A := A) (B := Aᶜ) disjoint_compl_right
  rw [Set.union_compl_self] at hunion; linarith [m.total]

/-- Qualitative additivity for a finitely additive measure: splitting `A` and `B`
    into the shared part `A ∩ B` and the private parts cancels the shared part. -/
theorem mu_qadd (m : FinAddMeasure K W) (A B : Set W) :
    m A ≤ m B ↔ m (A \ B) ≤ m (B \ A) := by
  have key : ∀ X Y : Set W, m X = m (X \ Y) + m (X ∩ Y) := fun X Y => by
    conv_lhs => rw [(Set.sdiff_union_inter X Y).symm]
    exact m.additive (Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.2)
  rw [key A B, key B A, Set.inter_comm B A]; exact add_le_add_iff_right (m (A ∩ B))

/-- The measure of a finite set is the sum of its singleton measures. -/
@[simp] theorem sum_mu_singleton (m : FinAddMeasure K W) (S : Finset W) :
    ∑ i ∈ S, m {i} = m ↑S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hdisj : Disjoint ({a} : Set W) ↑S :=
      Set.disjoint_singleton_left.mpr fun h => ha (Finset.mem_coe.mp h)
    rw [Finset.sum_insert ha, ih, Finset.coe_insert, Set.insert_eq, m.additive hdisj]

/-- Pushforward of a finitely additive measure along a map. -/
def map {α : Type*} (f : W → α) (m : FinAddMeasure K W) : FinAddMeasure K α where
  toFun A := m (f ⁻¹' A)
  nonneg' _ := m.nonneg _
  additive' A B h := by rw [Set.preimage_union]; exact m.additive (h.preimage f)
  total' := by rw [Set.preimage_univ]; exact m.total

@[simp] theorem map_apply {α : Type*} (f : W → α) (m : FinAddMeasure K W)
    (A : Set α) : m.map f A = m (f ⁻¹' A) := rfl

open scoped Classical in
/-- The discrete measure with weight `w i` on the atom `i` (the `PMF.ofFintype`
    pattern). -/
noncomputable def ofFintype [Fintype W] (w : W → K) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : FinAddMeasure K W where
  toFun A := ∑ i, if i ∈ A then w i else 0
  nonneg' A := Finset.sum_nonneg fun i _ => by split <;> simp [hw i]
  additive' A B h := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hA : i ∈ A
    · simp [Set.mem_union, hA, Set.disjoint_left.mp h hA]
    · by_cases hB : i ∈ B <;> simp [Set.mem_union, hA, hB]
  total' := by simpa using hw1

@[simp] theorem ofFintype_singleton [Fintype W] (w : W → K)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (i : W) :
    ofFintype w hw hw1 {i} = w i := by
  classical
  simp [ofFintype, Set.mem_singleton_iff, Finset.sum_ite_eq' Finset.univ i w]

end FinAddMeasure

/-! ### Qualitatively additive measures -/

/-- A qualitatively additive measure on subsets of W.
    Unlike `FinAddMeasure`, this does NOT require μ(A ∪ B) = μ(A) + μ(B)
    for disjoint A, B. Instead it requires the weaker **qualitative additivity**
    condition: μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A).

    Every qualitative probability order on a finite carrier is represented by
    one (`exists_qualAddMeasure_repr`), by an affine renormalisation of the
    dominated-set count. -/
structure QualAddMeasure (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (W : Type*) where
  /-- The measure function. Apply the measure itself: `m A`. -/
  toFun : Set W → K
  /-- Non-negativity. Use the lemma `nonneg`. -/
  nonneg' : ∀ A, 0 ≤ toFun A
  /-- The impossible proposition has measure zero. Use the lemma `mu_empty`. -/
  empty' : toFun ∅ = 0
  /-- Normalization. Use the lemma `total`. -/
  total' : toFun Set.univ = 1
  /-- Qualitative additivity. Use the lemma `qualAdd`. -/
  qualAdd' : ∀ A B, toFun A ≤ toFun B ↔ toFun (A \ B) ≤ toFun (B \ A)

namespace QualAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

instance : FunLike (QualAddMeasure K W) (Set W) K where
  coe := toFun
  coe_injective m m' _ := by cases m; cases m'; congr

@[ext] theorem ext {m m' : QualAddMeasure K W} (h : ∀ A, m A = m' A) : m = m' :=
  DFunLike.ext m m' h

theorem nonneg (m : QualAddMeasure K W) (A : Set W) : 0 ≤ m A := m.nonneg' A

@[simp] theorem mu_empty (m : QualAddMeasure K W) : m ∅ = 0 := m.empty'

@[simp] theorem total (m : QualAddMeasure K W) : m Set.univ = 1 := m.total'

/-- Qualitative additivity: `μ(A) ≤ μ(B) ↔ μ(A ∖ B) ≤ μ(B ∖ A)`. -/
theorem qualAdd (m : QualAddMeasure K W) (A B : Set W) :
    m A ≤ m B ↔ m (A \ B) ≤ m (B \ A) := m.qualAdd' A B

/-- Measure-induced comparative likelihood `A ≿ B ↔ μ(A) ≥ μ(B)` (the
    `≿`-reading; see `FinAddMeasure.inducedGe`). -/
def inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop := m A ≥ m B

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. From qualAdd + μ(∅) = 0 + nonneg. -/
theorem mu_mono (m : QualAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m A ≤ m B := by
  rw [m.qualAdd A B, Set.sdiff_eq_empty.mpr h, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces a qualitative probability order. -/
def toQualitativeProbability (m : QualAddMeasure K W) :
    QualitativeProbability (Set W) where
  le A B := m A ≤ m B
  mono' := fun _ _ h => m.mu_mono h
  nonTrivial := by simp
  total := fun A B => le_total (m A) (m B)
  trans' := fun _ _ _ hab hbc => le_trans hab hbc
  additive := m.qualAdd

end QualAddMeasure

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

/-- Every finitely additive measure is qualitatively additive.
    Proof: μ(A) = μ(A \ B) + μ(A ∩ B) and μ(B) = μ(B \ A) + μ(A ∩ B),
    so μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A). -/
def FinAddMeasure.toQualAdd (m : FinAddMeasure K W) : QualAddMeasure K W where
  toFun := m.toFun
  nonneg' := m.nonneg'
  empty' := m.mu_empty
  total' := m.total'
  qualAdd' := m.mu_qadd

/-- Every finitely additive measure induces a qualitative probability order,
    through `toQualAdd`. -/
def FinAddMeasure.toQualitativeProbability (m : FinAddMeasure K W) :
    QualitativeProbability (Set W) :=
  m.toQualAdd.toQualitativeProbability

end

end ComparativeProbability
