import Linglib.Core.Order.ComparativeProbability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Comparative probability

Comparative-likelihood orders `≿` on propositions (`Set W`) — "`A` is at least as
likely as `B`" — after [holliday-icard-2013]: an axiom hierarchy, finitely- and
qualitatively-additive measure semantics, and the two world-ordering lifts.

## Main definitions

* `RightUnion`, `DeterminedBySingletons` — the two likelihood axioms with no
  mathlib/`Defs` analog (the rest are the `Defs.lean` mixins).
* `EpistemicSystemW`/`FA` — bundled axiom systems; `EpistemicSystemFA` is
  [holliday-icard-2013]'s logic FA.
* `FinAddMeasure`/`QualAddMeasure` — finitely- and qualitatively-additive
  probability measures over an ordered field, with their induced orders.
* `dominationLift`/`matchingLift` — the l- and m-liftings of a world preorder.

## Main statements

* `QualAddMeasure.toSystemFA` — a qualitatively additive measure satisfies FA;
  `FinAddMeasure.toSystemFA` derives the finitely additive case through
  `FinAddMeasure.toQualAdd`.
* `dominationLift_rightUnion`, `dominationLift_determinedBySingletons` — the
  soundness half of the l-lifting representation (`Completeness.lean`).

## Implementation notes

`EpistemicSystemW` is coarse staging toward `EpistemicSystemFA`, not
[holliday-icard-2013]'s logic `W`. Reflexivity and `Ω ≿ ∅` are consequences of
monotonicity, not fields (`EpistemicSystemW.refl`/`univ_ge_empty`).

The measures are generic over an ordered field `K`: `ℝ` gives the paper's literal
`[0,1]`-valued measures, `ℚ` the computable theory. On a finite state space the
two agree (rational and real linear feasibility coincide), and only `ℚ` supports
the constructive Farkas (`FourierMotzkin.lean`) and `decide`-checked models
(`Representability.lean`) behind the representation theorems. `FinAddMeasure`
overlaps mathlib's `MeasureTheory.AddContent` and could be re-founded on it;
`FinAddMeasure.inducedGe` is `Order.Preimage m.mu (· ≥ ·)`.

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

/-! ### Axiom systems

`EpistemicSystemW` is coarse staging toward `EpistemicSystemFA`. Fields hold
the bare propositions; the matching `Defs.lean` mixin instances are below. -/

/-- A monotone likelihood relation (weaker than [holliday-icard-2013]'s
logic `W`; see the module docstring). Reflexivity and `Ω ≿ ∅` are derived
(`refl`, `univ_ge_empty`), not fields. -/
structure EpistemicSystemW (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Monotonicity: supersets are at least as likely. -/
  mono : ∀ A B : Set W, A ⊆ B → ge B A

namespace EpistemicSystemW

variable {W : Type*} (sys : EpistemicSystemW W)

/-- Reflexivity, from monotonicity. -/
theorem refl (A : Set W) : sys.ge A A := sys.mono A A subset_rfl

/-- The tautology is at least as likely as the contradiction. -/
theorem univ_ge_empty : sys.ge Set.univ ∅ := sys.mono ∅ Set.univ (Set.empty_subset _)

end EpistemicSystemW

/-- [holliday-icard-2013]'s logic FA: a total, transitive, qualitatively additive
likelihood order. Sound and complete for qualitatively additive measure semantics
(Theorem 6; [van-der-hoek-1996]), and strictly weaker than finite additivity for
`|W| ≥ 5` (Theorem 8, after [kraft-pratt-seidenberg-1959]). -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemW W where
  /-- Non-triviality: excludes the degenerate all-equivalent order. -/
  nonTrivial : ¬ ge ∅ Set.univ
  /-- Totality: any two propositions are comparable. -/
  total : ∀ A B : Set W, ge A B ∨ ge B A
  /-- Transitivity. -/
  trans : ∀ A B C : Set W, ge A B → ge B C → ge A C
  /-- Qualitative additivity: `A ≿ B ↔ (A \ B) ≿ (B \ A)`. -/
  additive : ∀ A B : Set W, ge A B ↔ ge (A \ B) (B \ A)

/-! ### FA systems carry the comparative-probability mixins

An FA system's fields are defeq the `Defs.lean` mixin classes (`a ≤ b` is `a ⊆ b`
on `Set W`), so the instances below register its relation as a comparative-
probability order, and the validity patterns V1–V13 transfer from
`ComparativeProbability.Patterns` by instance resolution. -/

section

variable {W : Type*} (sys : EpistemicSystemFA W)

instance : ComparativeProbability.IsLikelihoodMono sys.ge := ⟨sys.mono⟩

instance : IsTrans (Set W) sys.ge := ⟨sys.trans⟩

instance : ComparativeProbability.IsQualitativeAdditive sys.ge := ⟨sys.additive⟩

instance : ComparativeProbability.IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

end

/-! ### Consequences of the FA axioms -/

section
variable {W : Type*} (sys : EpistemicSystemFA W)

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
  refine sys.trans _ (X₂ ∪ Y₁) _ ?_ ?_
  · rw [show X₂ ∪ Y₁ = Y₁ ∪ (X₂ \ Y₁) by grind]
    exact ge_add_context sys h1
  · rw [show X₂ ∪ Y₁ = X₂ ∪ (Y₁ \ X₂) by grind]
    exact ge_add_context sys h2

/-- **Mono-domination**: a valid comparison `X ≿ Y` with `X ⊆ P` and `Q ⊆ Y`
    proves `P ≿ Q`. -/
lemma ge_mono_dominated {X Y P Q : Set W} (h : sys.ge X Y) (hXP : X ⊆ P) (hQY : Q ⊆ Y) :
    sys.ge P Q :=
  sys.trans _ _ _ (sys.mono X P hXP) (sys.trans _ _ _ h (sys.mono Q Y hQY))

/-- `P ≿ ∅` always (monotonicity). -/
lemma ge_empty_target (P : Set W) : sys.ge P ∅ :=
  sys.mono ∅ P (Set.empty_subset P)

end

/-! ### Measure semantics -/

/-- A finitely additive probability measure on subsets of `W`, valued in an
    ordered field `K`. The value type is left generic: instantiate at `ℚ` for the
    constructive, `decide`-able representation theory and at `ℝ` for the paper's
    literal `[0,1]`-valued measures (see the module docstring). -/
structure FinAddMeasure (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (W : Type*) where
  /-- The measure function -/
  mu : Set W → K
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- Finite additivity: μ(A ∪ B) = μ(A) + μ(B) for disjoint A, B -/
  additive : ∀ A B, Disjoint A B → mu (A ∪ B) = mu A + mu B
  /-- Normalization -/
  total : mu Set.univ = 1

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def FinAddMeasure.inducedGe (m : FinAddMeasure K W) (A B : Set W) : Prop := m.mu A ≥ m.mu B

/-- μ(∅) = 0 for any finitely additive measure.
    Follows from additivity: μ(∅ ∪ ∅) = μ(∅) + μ(∅), but ∅ ∪ ∅ = ∅. -/
@[simp] theorem FinAddMeasure.mu_empty (m : FinAddMeasure K W) : m.mu ∅ = 0 := by
  have h := m.additive ∅ ∅ disjoint_bot_left; rw [Set.empty_union] at h; linarith

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. -/
theorem FinAddMeasure.mu_mono (m : FinAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  have hunion := m.additive A (B \ A) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel h] at hunion; linarith [m.nonneg (B \ A)]

/-- Complement measure: `μ(A) + μ(Aᶜ) = 1`. -/
theorem FinAddMeasure.mu_compl (m : FinAddMeasure K W) (A : Set W) :
    m.mu A + m.mu Aᶜ = 1 := by
  have hunion := m.additive A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self] at hunion; linarith [m.total]

/-- Qualitative additivity for a finitely additive measure: splitting `A` and `B`
    into the shared part `A ∩ B` and the private parts cancels the shared part. -/
theorem FinAddMeasure.mu_qadd (m : FinAddMeasure K W) (A B : Set W) :
    m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A) := by
  have key : ∀ X Y : Set W, m.mu X = m.mu (X \ Y) + m.mu (X ∩ Y) := fun X Y => by
    conv_lhs => rw [(Set.sdiff_union_inter X Y).symm]
    exact m.additive _ _ (Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.2)
  rw [key A B, key B A, Set.inter_comm B A]; exact add_le_add_iff_right (m.mu (A ∩ B))

/-- The measure of a finite set is the sum of its singleton measures. -/
@[simp] theorem FinAddMeasure.sum_mu_singleton (m : FinAddMeasure K W) (S : Finset W) :
    ∑ i ∈ S, m.mu {i} = m.mu ↑S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hdisj : Disjoint ({a} : Set W) ↑S :=
      Set.disjoint_singleton_left.mpr fun h => ha (Finset.mem_coe.mp h)
    rw [Finset.sum_insert ha, ih, Finset.coe_insert, Set.insert_eq, m.additive _ _ hdisj]

end

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
  /-- The measure function -/
  mu : Set W → K
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- The impossible proposition has measure zero -/
  mu_empty : mu ∅ = 0
  /-- Normalization -/
  total : mu Set.univ = 1
  /-- Qualitative additivity: μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A) -/
  qualAdd : ∀ A B, mu A ≥ mu B ↔ mu (A \ B) ≥ mu (B \ A)

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def QualAddMeasure.inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop := m.mu A ≥ m.mu B

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. From qualAdd + μ(∅) = 0 + nonneg. -/
theorem QualAddMeasure.mu_mono (m : QualAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  show m.mu B ≥ m.mu A
  rw [m.qualAdd B A, Set.sdiff_eq_empty.mpr h, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces System FA.
    Soundness direction of [holliday-icard-2013] Theorem 6:
    every qualitatively additive measure model satisfies the FA axioms. -/
def QualAddMeasure.toSystemFA (m : QualAddMeasure K W) : EpistemicSystemFA W where
  ge := m.inducedGe
  mono := fun _ _ h => m.mu_mono h
  nonTrivial := by simp only [inducedGe, m.mu_empty, m.total, not_le]; exact one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := m.qualAdd

/-- Every finitely additive measure is qualitatively additive.
    Proof: μ(A) = μ(A \ B) + μ(A ∩ B) and μ(B) = μ(B \ A) + μ(A ∩ B),
    so μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A). -/
def FinAddMeasure.toQualAdd (m : FinAddMeasure K W) : QualAddMeasure K W where
  mu := m.mu
  nonneg := m.nonneg
  mu_empty := m.mu_empty
  total := m.total
  qualAdd := m.mu_qadd

/-- Every finitely additive measure satisfies the FA axioms, through
    `toQualAdd`. A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def FinAddMeasure.toSystemFA (m : FinAddMeasure K W) : EpistemicSystemFA W :=
  m.toQualAdd.toSystemFA

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

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe := ⟨m.toSystemFA.mono⟩

instance : IsTrans (Set W) m.inducedGe := ⟨m.toSystemFA.trans⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe := ⟨m.toSystemFA.additive⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe := ⟨m.toSystemFA.nonTrivial⟩

end

end ComparativeProbability
