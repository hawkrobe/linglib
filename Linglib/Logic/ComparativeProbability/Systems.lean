import Linglib.Logic.ComparativeProbability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Comparative probability

Comparative-likelihood orders `≿` on propositions (`Set W`) — "`A` is at least as
likely as `B`" — after [holliday-icard-2013]: an axiom hierarchy, finitely- and
qualitatively-additive measure semantics, and the two world-ordering lifts.

## Main definitions

* `RightUnion`, `DeterminedBySingletons` — the two likelihood axioms with no
  mathlib/`Defs` analog (the rest are the `Defs.lean` mixins).
* `QualitativeProbability` — the bundled qualitative probability order,
  [holliday-icard-2013]'s logic FA.
* `FinAddMeasure`/`QualAddMeasure` — finitely- and qualitatively-additive
  probability measures over an ordered field, with their induced orders.
* `dominationLift`/`matchingLift` — the l- and m-liftings of a world preorder.

## Main statements

* `QualAddMeasure.toQualitativeProbability` — a qualitatively additive measure satisfies FA;
  `FinAddMeasure.toQualitativeProbability` derives the finitely additive case through
  `FinAddMeasure.toQualAdd`.
* `dominationLift_rightUnion`, `dominationLift_determinedBySingletons` — the
  soundness half of the l-lifting representation (`Completeness.lean`).

## Implementation notes

Reflexivity and `Ω ≿ ∅` are consequences of monotonicity, not fields
(`QualitativeProbability.refl`/`univ_ge_empty`). Sub-FA hypotheses (the
completeness theorems for weaker logics) are stated on a bare relation with
explicit monotonicity/transitivity hypotheses, not on a weaker bundle.

The measures are generic over an ordered field `K`: `ℝ` gives the paper's literal
`[0,1]`-valued measures, `ℚ` the computable theory. On a finite state space the
two agree (rational and real linear feasibility coincide), and only `ℚ` supports
the constructive Farkas (`FourierMotzkin.lean`) and `decide`-checked models
(`Representability.lean`) behind the representation theorems. `FinAddMeasure`
mirrors mathlib's `MeasureTheory.AddContent` interface (`FunLike` application
`m A`, primed axiom fields with unprimed lemmas); re-founding on `AddContent`
itself would trade the ordered-field axioms for monoid-valued contents over a
set system with `sUnion` side conditions, so the structure stays local.
`FinAddMeasure.inducedGe` is `Order.Preimage ⇑m (· ≥ ·)`.

`[UPSTREAM]` candidate: `QualitativeProbability`, the measures, and the
KPS/Scott representation theory (`Representability.lean`, `Cancellation.lean`,
`CancellationFin4.lean`, `Completeness.lean`) are measurement-theoretic
mathematics with no mathlib counterpart; the world-ordering lifts and the
pattern layer are program content and stay here.

## References

[holliday-icard-2013], [van-der-hoek-1996], [kraft-pratt-seidenberg-1959]
-/

namespace ComparativeProbability

/-! ### Axioms

Two likelihood-relation axioms of [holliday-icard-2013] with no mathlib or
`Defs.lean` analog. The remaining axioms are mathlib's `Reflexive` and the
`Defs.lean` mixin classes `IsLikelihoodMono` (monotonicity, the paper's `Mon`),
`IsQualitativeAdditive`, and `IsNontrivial`; the systems below carry those as
plain propositional fields. -/

section Axioms
variable {W : Type*} (ge : Set W → Set W → Prop)

/-- Right-union (axiom `J` of [holliday-icard-2013], Figure 4):
`A ≿ B → A ≿ C → A ≿ B ∪ C`. -/
def RightUnion : Prop := ∀ A B C, ge A B → ge A C → ge A (B ∪ C)

/-- Determination by singletons: `A ≿ {b} → ∃ a ∈ A, {a} ≿ {b}`. -/
def DeterminedBySingletons : Prop := ∀ (A : Set W) (b : W), ge A {b} → ∃ a ∈ A, ge {a} {b}

end Axioms

/-! ### Qualitative probability orders

Fields hold the bare propositions; the matching `Defs.lean` mixin instances
are below. -/

/-- A **qualitative probability** order on `Set W`: total, transitive, monotone,
non-trivial, and qualitatively additive — the standard base system for
comparative probability since de Finetti, and [holliday-icard-2013]'s logic FA.
Sound and complete for qualitatively additive measure semantics (Theorem 6;
[van-der-hoek-1996]), and strictly weaker than finite additivity for `|W| ≥ 5`
(Theorem 8, after [kraft-pratt-seidenberg-1959]). Reflexivity and `Ω ≿ ∅` are
consequences of monotonicity (`refl`, `univ_ge_empty`), not fields. -/
structure QualitativeProbability (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Monotonicity: supersets are at least as likely. Use the lemma `mono`. -/
  mono' : ∀ A B : Set W, A ⊆ B → ge B A
  /-- Non-triviality: excludes the degenerate all-equivalent order. -/
  nonTrivial : ¬ ge ∅ Set.univ
  /-- Totality: any two propositions are comparable. -/
  total : ∀ A B : Set W, ge A B ∨ ge B A
  /-- Transitivity. Use the lemma `trans`. -/
  trans' : ∀ A B C : Set W, ge A B → ge B C → ge A C
  /-- Qualitative additivity: `A ≿ B ↔ (A \ B) ≿ (B \ A)`. -/
  additive : ∀ A B : Set W, ge A B ↔ ge (A \ B) (B \ A)

namespace QualitativeProbability

variable {W : Type*} (sys : QualitativeProbability W)

/-- Monotonicity: supersets are at least as likely. -/
theorem mono {A B : Set W} (h : A ⊆ B) : sys.ge B A := sys.mono' A B h

/-- Transitivity. -/
theorem trans {A B C : Set W} (hab : sys.ge A B) (hbc : sys.ge B C) : sys.ge A C :=
  sys.trans' A B C hab hbc

/-- Reflexivity, from monotonicity. -/
theorem refl (A : Set W) : sys.ge A A := sys.mono subset_rfl

/-- The tautology is at least as likely as the contradiction. -/
theorem univ_ge_empty : sys.ge Set.univ ∅ := sys.mono (Set.empty_subset _)

end QualitativeProbability

/-! ### FA systems carry the comparative-probability mixins

An FA system's fields are defeq the `Defs.lean` mixin classes (`a ≤ b` is `a ⊆ b`
on `Set W`), so the instances below register its relation as a comparative-
probability order, and the validity patterns V1–V13 transfer from
`ComparativeProbability.Patterns` by instance resolution. -/

section

variable {W : Type*} (sys : QualitativeProbability W)

instance : ComparativeProbability.IsLikelihoodMono sys.ge := ⟨sys.mono'⟩

instance : IsTrans (Set W) sys.ge := ⟨sys.trans'⟩

instance : ComparativeProbability.IsQualitativeAdditive sys.ge := ⟨sys.additive⟩

instance : ComparativeProbability.IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

end

/-! ### Consequences of the FA axioms -/

section
variable {W : Type*} (sys : QualitativeProbability W)

/-- **Add common context**: for `C` disjoint from both `X` and `Y`,
    `X ≿ Y ↔ (X ∪ C) ≿ (Y ∪ C)`. -/
lemma ge_union_context (X Y C : Set W)
    (hCX : Disjoint C X := by grind) (hCY : Disjoint C Y := by grind) :
    sys.ge X Y ↔ sys.ge (X ∪ C) (Y ∪ C) := by
  rw [sys.additive X Y, sys.additive (X ∪ C) (Y ∪ C)]
  congr! 1 <;> grind

/-- Forward form of `ge_union_context`: context `C` disjoint from both sides
    preserves `≿`. -/
lemma ge_add_context {X Y C : Set W} (h : sys.ge X Y)
    (hCX : Disjoint C X := by grind) (hCY : Disjoint C Y := by grind) :
    sys.ge (X ∪ C) (Y ∪ C) :=
  (ge_union_context sys X Y C hCX hCY).mp h

/-- **Generalized merge**: two valid comparisons with disjoint left parts and
    disjoint right parts merge into their union, even with pivot overlaps.
    Derivation: add context to each side, transit through `X₂ ∪ Y₁`, then
    restore the pivot `X₂ ∩ Y₁` via Axiom A. -/
lemma ge_generalized_merge {X₁ Y₁ X₂ Y₂ : Set W}
    (h1 : sys.ge X₁ Y₁) (h2 : sys.ge X₂ Y₂)
    (hX : Disjoint X₁ X₂) (hY : Disjoint Y₁ Y₂) :
    sys.ge (X₁ ∪ X₂) (Y₁ ∪ Y₂) := by
  -- split each side around the pivot `X₂ ∩ Y₁`
  rw [show X₁ ∪ X₂ = (X₁ ∪ (X₂ \ Y₁)) ∪ (X₂ ∩ Y₁) by grind,
    show Y₁ ∪ Y₂ = (Y₂ ∪ (Y₁ \ X₂)) ∪ (X₂ ∩ Y₁) by grind]
  -- the pivot is common context; strip it, then transit through `X₂ ∪ Y₁`
  refine ge_add_context sys ?_
  refine sys.trans (B := X₂ ∪ Y₁) ?_ ?_
  · rw [show X₂ ∪ Y₁ = Y₁ ∪ (X₂ \ Y₁) by grind]
    exact ge_add_context sys h1
  · rw [show X₂ ∪ Y₁ = X₂ ∪ (Y₁ \ X₂) by grind]
    exact ge_add_context sys h2

/-- **Mono-domination**: a valid comparison `X ≿ Y` with `X ⊆ P` and `Q ⊆ Y`
    proves `P ≿ Q`. -/
lemma ge_mono_dominated {X Y P Q : Set W} (h : sys.ge X Y) (hXP : X ⊆ P) (hQY : Q ⊆ Y) :
    sys.ge P Q :=
  sys.trans (sys.mono hXP) (sys.trans h (sys.mono hQY))

/-- `P ≿ ∅` always (monotonicity). -/
lemma ge_empty_target (P : Set W) : sys.ge P ∅ :=
  sys.mono (Set.empty_subset P)

end

/-! ### Measure semantics -/

/-- A finitely additive probability measure on subsets of `W`, valued in an
    ordered field `K`. The value type is left generic: instantiate at `ℚ` for the
    constructive, `decide`-able representation theory and at `ℝ` for the paper's
    literal `[0,1]`-valued measures (see the module docstring).

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

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
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
    m A ≥ m B ↔ m (A \ B) ≥ m (B \ A) := by
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

    [holliday-icard-2013] Theorem 6: System FA is sound and complete
    with respect to qualitatively additive measure models. The completeness
    construction (`exists_qualAddMeasure_repr`) realises μ(∅) = 0 by an
    affine renormalisation of the dominated-set count. -/
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
  qualAdd' : ∀ A B, toFun A ≥ toFun B ↔ toFun (A \ B) ≥ toFun (B \ A)

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

/-- Qualitative additivity: `μ(A) ≥ μ(B) ↔ μ(A ∖ B) ≥ μ(B ∖ A)`. -/
theorem qualAdd (m : QualAddMeasure K W) (A B : Set W) :
    m A ≥ m B ↔ m (A \ B) ≥ m (B \ A) := m.qualAdd' A B

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop := m A ≥ m B

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. From qualAdd + μ(∅) = 0 + nonneg. -/
theorem mu_mono (m : QualAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m A ≤ m B := by
  show m B ≥ m A
  rw [m.qualAdd B A, Set.sdiff_eq_empty.mpr h, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces System FA.
    Soundness direction of [holliday-icard-2013] Theorem 6:
    every qualitatively additive measure model satisfies the FA axioms. -/
def toQualitativeProbability (m : QualAddMeasure K W) :
    QualitativeProbability W where
  ge := m.inducedGe
  mono' := fun _ _ h => m.mu_mono h
  nonTrivial := by simp only [inducedGe, m.mu_empty, m.total, not_le]; exact one_pos
  total := fun A B => le_total (m B) (m A)
  trans' := fun _ _ _ hab hbc => le_trans hbc hab
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

/-- Every finitely additive measure satisfies the FA axioms, through
    `toQualAdd`. A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def FinAddMeasure.toQualitativeProbability (m : FinAddMeasure K W) : QualitativeProbability W :=
  m.toQualAdd.toQualitativeProbability

end

/-! ### World-ordering lifts

The l-lifting (Lewis's lifting; [holliday-icard-2013], §5) and its injection
refinement, the m-lifting (§9). The l-lifting is the **Smyth (upper powerdomain)
order**; the m-lifting requires *distinct* dominators (an injection), which avoids
the disjunction problem (invalidates I1–I3) while validating V1–V13 (Fact 5). -/

section Lift

variable {W : Type*} {ge_w : W → W → Prop}

/-- The l-lifting: `A ≿ B` iff every `b ∈ B` is dominated by some `a ∈ A`. -/
def dominationLift (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b

/-- The m-lifting: `A ≿ B` iff some injection `f : B ↪ A` dominates pointwise. -/
def matchingLift (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∃ (f : W → W),
    (∀ b, b ∈ B → f b ∈ A ∧ ge_w (f b) b) ∧
    (∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → f b₁ = f b₂ → b₁ = b₂)

/-- The l-lifting satisfies right-union (axiom `J`). -/
theorem dominationLift_rightUnion : RightUnion (dominationLift ge_w) :=
  fun _ _ _ hAB hAC b hb => hb.elim (hAB b) (hAC b)

/-- Over a **total** relation, the strict l-lifting collapses to Lewis's
∃∀ comparative possibility: some A-point strictly dominates every B-point. -/
theorem strict_dominationLift_iff (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (A B : Set W) :
    ComparativeProbability.Strict (dominationLift ge_w) A B ↔
    ∃ a ∈ A, ∀ b ∈ B, ge_w a b ∧ ¬ ge_w b a := by
  constructor
  · rintro ⟨-, hn⟩
    unfold dominationLift at hn
    push Not at hn
    obtain ⟨a, haA, ha⟩ := hn
    exact ⟨a, haA, fun b hbB =>
      ⟨(hTotal a b).resolve_right (ha b hbB), ha b hbB⟩⟩
  · rintro ⟨a, haA, ha⟩
    refine ⟨fun b hbB => ⟨a, haA, (ha b hbB).1⟩, fun h => ?_⟩
    obtain ⟨b, hbB, hba⟩ := h a haA
    exact (ha b hbB).2 hba

/-- The l-lifting satisfies determination by singletons. -/
theorem dominationLift_determinedBySingletons : DeterminedBySingletons (dominationLift ge_w) :=
  fun _ b hAb =>
    let ⟨a, ha, hab⟩ := hAb b rfl
    ⟨a, ha, fun _b' hb' => ⟨a, rfl, hb' ▸ hab⟩⟩

end Lift

/-! ### Connection to the `ComparativeProbability` theory

Every finitely-additive measure's induced order is a comparative-probability
order (monotone, transitive, qualitatively additive, non-trivial), so the
validity patterns V1–V13 transfer for free from `ComparativeProbability.Patterns`
by instance resolution — no per-measure arithmetic. -/

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}
  (m : FinAddMeasure K W)

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe :=
  ⟨m.toQualitativeProbability.mono'⟩

instance : IsTrans (Set W) m.inducedGe := ⟨m.toQualitativeProbability.trans'⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe :=
  ⟨m.toQualitativeProbability.additive⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe :=
  ⟨m.toQualitativeProbability.nonTrivial⟩

end

end ComparativeProbability
