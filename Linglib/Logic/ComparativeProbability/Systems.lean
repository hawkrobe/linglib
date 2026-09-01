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
* `QualitativeProbability` — the bundled qualitative probability order on a
  Boolean algebra (`le`-primitive; `ge` is the paper-facing `≿`), on `Set W`
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

The order is stored as `le` and stated in `≤`-vocabulary, mathlib's
convention; the literature's `≿` is the derived `ge`, and it is `ge` that
carries the pattern-layer mixin instances (the `Defs.lean` classes are
`≿`-calibrated, as are the papers). Reflexivity and `⊥ ≼ a` are consequences
of monotonicity, not fields. Sub-FA hypotheses (the completeness theorems for
weaker logics) are stated on a bare relation with explicit
monotonicity/transitivity hypotheses, not on a weaker bundle.

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

The relation is stored as `le` (`a ≼ b`: `a` is at most as likely as `b`),
mathlib's convention; the paper-facing converse `≿` is `ge`, mathlib's `GE.ge`
pattern, and it is `ge` that carries the `Defs.lean` mixin instances. -/

/-- A **qualitative probability** order on a Boolean algebra `α`: total,
transitive, monotone, non-trivial, and qualitatively additive — the standard
base system for comparative probability since de Finetti, and, on `Set W`,
[holliday-icard-2013]'s logic FA. Sound and complete for qualitatively additive
measure semantics (Theorem 6; [van-der-hoek-1996]), and strictly weaker than
finite additivity for `|W| ≥ 5` (Theorem 8, after [kraft-pratt-seidenberg-1959]).
Reflexivity and `⊥ ≼ a` are consequences of monotonicity (`refl`, `bot_le`), not
fields. -/
structure QualitativeProbability (α : Type*) [BooleanAlgebra α] where
  /-- The "at most as likely as" relation. -/
  le : α → α → Prop
  /-- Monotonicity: `a ≤ b → a ≼ b`. Use the lemma `mono`. -/
  mono' : ∀ a b : α, a ≤ b → le a b
  /-- Non-triviality: `⊤` is not at most as likely as `⊥`. -/
  nonTrivial : ¬ le ⊤ ⊥
  /-- Totality: any two elements are comparable. -/
  total : ∀ a b : α, le a b ∨ le b a
  /-- Transitivity. Use the lemma `trans`. -/
  trans' : ∀ a b c : α, le a b → le b c → le a c
  /-- Qualitative additivity: `a ≼ b ↔ a \ b ≼ b \ a`. -/
  additive : ∀ a b : α, le a b ↔ le (a \ b) (b \ a)

namespace QualitativeProbability

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

/-- `sys.ge a b` (`a ≿ b`): `a` is at least as likely as `b` — the converse of
`le`, mathlib's `GE.ge` pattern. This is the relation the `Defs.lean` mixins,
the pattern layer, and the paper-facing studies consume. -/
def ge (a b : α) : Prop := sys.le b a

@[inherit_doc le] scoped notation:50 a:51 " ≼[" sys "] " b:51 => QualitativeProbability.le sys a b
@[inherit_doc ge] scoped notation:50 a:51 " ≿[" sys "] " b:51 => QualitativeProbability.ge sys a b

@[simp] theorem ge_iff_le {a b : α} : sys.ge a b ↔ sys.le b a := Iff.rfl

/-- Monotonicity. -/
theorem mono {a b : α} (h : a ≤ b) : sys.le a b := sys.mono' a b h

/-- Transitivity. -/
theorem trans {a b c : α} (hab : sys.le a b) (hbc : sys.le b c) : sys.le a c :=
  sys.trans' a b c hab hbc

/-- Reflexivity, from monotonicity. -/
theorem refl (a : α) : sys.le a a := sys.mono le_rfl

protected theorem bot_le (a : α) : sys.le ⊥ a := sys.mono bot_le

protected theorem le_top (a : α) : sys.le a ⊤ := sys.mono le_top

/-! #### Consequences of the axioms -/

/-- Disjoint common context cancels: `a ⊔ c ≼ b ⊔ c ↔ a ≼ b` for `c` disjoint
    from both. -/
theorem sup_le_sup_iff_right {a b c : α} (hca : Disjoint c a) (hcb : Disjoint c b) :
    sys.le (a ⊔ c) (b ⊔ c) ↔ sys.le a b := by
  rw [sys.additive a b, sys.additive (a ⊔ c) (b ⊔ c), sup_comm b c, ← sdiff_sdiff_left,
    sup_sdiff_right_self, sdiff_eq_left.mpr hca.symm, sup_comm a c, ← sdiff_sdiff_left,
    sup_sdiff_left_self, sdiff_eq_left.mpr hcb.symm]

theorem sup_le_sup_right {a b c : α} (h : sys.le a b) (hca : Disjoint c a)
    (hcb : Disjoint c b) : sys.le (a ⊔ c) (b ⊔ c) :=
  (sys.sup_le_sup_iff_right hca hcb).mpr h

/-- Two comparisons with disjoint left parts and disjoint right parts merge
    into their joins, even with cross overlaps: add context to each side,
    transit through `b₁ ⊔ a₂`, then restore the pivot `a₂ ⊓ b₁` by additivity. -/
theorem sup_le_sup {a₁ b₁ a₂ b₂ : α} (h₁ : sys.le a₁ b₁) (h₂ : sys.le a₂ b₂)
    (ha : Disjoint a₁ a₂) (hb : Disjoint b₁ b₂) : sys.le (a₁ ⊔ a₂) (b₁ ⊔ b₂) := by
  have e₁ : (a₂ ⊔ a₁ \ b₂) ⊔ a₁ ⊓ b₂ = a₁ ⊔ a₂ := by
    rw [sup_assoc, sup_comm (a₁ \ b₂), sup_inf_sdiff, sup_comm]
  have e₂ : (b₁ ⊔ b₂ \ a₁) ⊔ a₁ ⊓ b₂ = b₁ ⊔ b₂ := by
    rw [sup_assoc, inf_comm a₁, sup_comm (b₂ \ a₁), sup_inf_sdiff]
  rw [← e₁, ← e₂]
  refine sys.sup_le_sup_right (sys.trans (b := b₂ ⊔ a₁) ?_ ?_)
    ((ha.mono_left inf_le_left).sup_right (disjoint_sdiff_self_right.mono_left inf_le_right))
    ((hb.symm.mono_left inf_le_right).sup_right (disjoint_sdiff_self_right.mono_left inf_le_left))
  · have h := sys.sup_le_sup_right h₂ (ha.mono_left sdiff_le) disjoint_sdiff_self_left
    rwa [sup_sdiff_self_right] at h
  · have h := sys.sup_le_sup_right h₁ disjoint_sdiff_self_left (hb.symm.mono_left sdiff_le)
    rwa [sup_sdiff_self_right, sup_comm a₁ b₂] at h

end QualitativeProbability

/-! ### The mixin instances

`ge` is defeq the `Defs.lean` mixin classes' relation, so the instances below
register it as a comparative-probability order, and the validity patterns
V1–V13 transfer from `ComparativeProbability.Patterns` by instance resolution. -/

section

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

instance : IsLikelihoodMono sys.ge := ⟨sys.mono'⟩

instance : IsTrans α sys.ge := ⟨fun _ _ _ hab hbc => sys.trans hbc hab⟩

instance : IsQualitativeAdditive sys.ge := ⟨fun a b => sys.additive b a⟩

instance : IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

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

/-- Measure-induced comparative likelihood `A ≿ B ↔ μ(A) ≥ μ(B)` — the
    paper-facing converse relation (`QualitativeProbability.ge`) that the pattern
    layer consumes; the order itself is `toQualitativeProbability`. -/
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
    paper-facing converse; see `FinAddMeasure.inducedGe`). -/
def inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop := m A ≥ m B

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. From qualAdd + μ(∅) = 0 + nonneg. -/
theorem mu_mono (m : QualAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m A ≤ m B := by
  rw [m.qualAdd A B, Set.sdiff_eq_empty.mpr h, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces a qualitative probability order —
    the soundness direction of [holliday-icard-2013] Theorem 6. -/
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

/-- Every finitely additive measure satisfies the FA axioms, through
    `toQualAdd`. A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def FinAddMeasure.toQualitativeProbability (m : FinAddMeasure K W) :
    QualitativeProbability (Set W) :=
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

instance : IsTrans (Set W) m.inducedGe :=
  ⟨fun _ _ _ hab hbc => m.toQualitativeProbability.trans hbc hab⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe :=
  ⟨fun A B => m.toQualitativeProbability.additive B A⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe :=
  ⟨m.toQualitativeProbability.nonTrivial⟩

end

end ComparativeProbability
