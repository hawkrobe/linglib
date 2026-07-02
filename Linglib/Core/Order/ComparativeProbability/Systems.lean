import Linglib.Core.Order.ComparativeProbability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Comparative probability

Comparative-likelihood orders `≿` on propositions (`Set W`) — "`A` is at least as
likely as `B`" — after [holliday-icard-2013]: an axiom hierarchy, finitely- and
qualitatively-additive measure semantics, the two world-ordering lifts, and the
generalized finite cancellation theory of imprecise (multi-prior) comparative
probability.

## Main definitions

* `RightUnion`, `DeterminedBySingletons` — the two likelihood axioms with no
  mathlib/`Defs` analog (the rest are `Reflexive` and the `Defs.lean` mixins).
* `EpistemicSystemW`/`F`/`FA` — bundled axiom systems; `EpistemicSystemFA` is
  [holliday-icard-2013]'s logic FA.
* `FinAddMeasure`/`QualAddMeasure` — finitely- and qualitatively-additive
  probability measures over an ordered field, with their induced orders.
* `dominationLift`/`matchingLift` — the l- and m-liftings of a world preorder.
* `GeneralizedFiniteCancellation` and `GFCOrder` — the cancellation axiom and the
  GFC order of [harrison-trainor-holliday-icard-2016].

## Main statements

* `FinAddMeasure.toSystemFA`, `QualAddMeasure.toSystemFA` — measures satisfy FA.
* `FinAddMeasure.toGFCOrder` — a measure induces a GFC order.
* `GFCOrder.trans`/`mono`/`complRev` — derived from cancellation, not stipulated.

## Implementation notes

`EpistemicSystemW`/`F` are coarse staging toward `EpistemicSystemFA`, not
[holliday-icard-2013]'s logics `W`/`F` (whose `W`-to-`F` step is totality);
labels `R`/`T` are mnemonic for the paper's `Mon` and reflexivity.

The measures are generic over an ordered field `K`: `ℝ` gives the paper's literal
`[0,1]`-valued measures, `ℚ` the computable theory. On a finite state space the
two agree (rational and real linear feasibility coincide), and only `ℚ` supports
the constructive Farkas (`FourierMotzkin.lean`) and `decide`-checked models
(`Representability.lean`) behind the representation theorems. `FinAddMeasure`
overlaps mathlib's `MeasureTheory.AddContent` and could be re-founded on it;
`FinAddMeasure.inducedGe` is `Order.Preimage m.mu (· ≥ ·)`.

## References

[holliday-icard-2013], [halpern-2003], [van-der-hoek-1996],
[kraft-pratt-seidenberg-1959], [harrison-trainor-holliday-icard-2016],
[harrison-trainor-holliday-icard-2018]
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

`EpistemicSystemW`/`F` are coarse staging toward `EpistemicSystemFA`. Fields hold
the bare propositions; the matching `Defs.lean` mixin instances are below. -/

/-- A reflexive, monotone likelihood relation (weaker than [holliday-icard-2013]'s
logic `W`; see the module docstring). -/
structure EpistemicSystemW (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Reflexivity. -/
  refl : Reflexive ge
  /-- Monotonicity: supersets are at least as likely. -/
  mono : ∀ A B : Set W, A ⊆ B → ge B A

/-- Adds `Ω ≿ ∅` and non-triviality. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  /-- The tautology is at least as likely as the contradiction. -/
  bottom : ge Set.univ ∅
  /-- Non-triviality: excludes the degenerate all-equivalent order. -/
  nonTrivial : ¬ ge ∅ Set.univ

/-- [holliday-icard-2013]'s logic FA: a total, transitive, qualitatively additive
likelihood order. Sound and complete for qualitatively additive measure semantics
(Theorem 6; [van-der-hoek-1996]), and strictly weaker than finite additivity for
`|W| ≥ 5` (Theorem 8, after [kraft-pratt-seidenberg-1959]). -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemF W where
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

/-- Every finitely additive measure satisfies the FA axioms.
    A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def FinAddMeasure.toSystemFA (m : FinAddMeasure K W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  mono := fun _ _ h => m.mu_mono h
  bottom := by show m.mu Set.univ ≥ m.mu ∅; rw [m.mu_empty]; exact m.nonneg Set.univ
  nonTrivial := by simp only [inducedGe, m.mu_empty, m.total, not_le]; exact one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := m.mu_qadd

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
  refl := fun _ => le_refl _
  mono := fun _ _ h => m.mu_mono h
  bottom := by show m.mu Set.univ ≥ m.mu ∅; rw [m.mu_empty]; exact m.nonneg Set.univ
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

/-- The l-lifting of a reflexive relation is reflexive. -/
theorem dominationLift_axiomR (hRefl : ∀ w, ge_w w w) : Reflexive (dominationLift ge_w) :=
  fun _ b hb => ⟨b, hb, hRefl b⟩

/-- The l-lifting of a reflexive relation is monotone. -/
theorem dominationLift_axiomT (hRefl : ∀ w, ge_w w w) :
    ∀ A B : Set W, A ⊆ B → dominationLift ge_w B A := fun _ _ hAB b hbA => ⟨b, hAB hbA, hRefl b⟩

/-- The l-lifting satisfies right-union. -/
theorem dominationLift_axiomJ : RightUnion (dominationLift ge_w) :=
  fun _ _ _ hAB hAC b hb => hb.elim (hAB b) (hAC b)

/-- Over a **total** relation, the strict l-lifting collapses to Lewis's
∃∀ comparative possibility: some A-point strictly dominates every B-point.
This is the form the metalinguistic comparative takes in
[rudolph-kocurek-2024] (there bounded to the cone below an evaluation index,
with worlds read as semantic interpretations). -/
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

/-- `strict_dominationLift_iff` with the strict pair packaged as a dominance
relation: whenever `below` is the strict form of the total `ge_w`, strict
l-lifting is an ∃∀ clause in `below`. -/
theorem strict_dominationLift_iff_below {below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b) (A B : Set W) :
    ComparativeProbability.Strict (dominationLift ge_w) A B ↔
    ∃ a ∈ A, ∀ b ∈ B, below b a := by
  rw [strict_dominationLift_iff hTotal]
  exact exists_congr fun a => and_congr_right fun _ =>
    forall₂_congr fun b _ => (hBelow b a).symm

/-- Lewis's ∃∀ comparative-possibility clause, localized to the `le`-cone at
an index and comparing difference sets (`P∖Q` against `Q∖P`, the shape of
[kratzer-2012]'s revised lifting), with the dominance relation a parameter —
the single clause behind [rudolph-kocurek-2024]'s ≻ (`below` the strict
ordering) and ≫ (`below` = far-below). -/
def coneStrictLift (le below : W → W → Prop) (P Q : W → Prop) (i : W) : Prop :=
  ∃ a, le a i ∧ P a ∧ ¬ Q a ∧ ∀ b, le b i → Q b → ¬ P b → below b a

instance (le below : W → W → Prop) (P Q : W → Prop) (i : W) [Fintype W]
    [DecidableRel le] [DecidableRel below] [DecidablePred P] [DecidablePred Q] :
    Decidable (coneStrictLift le below P Q i) := by
  unfold coneStrictLift; infer_instance

/-- Whenever `below` is the strict form of the total `ge_w`, the
cone-localized clause is the strict l-lifting on the cone difference sets. -/
theorem coneStrictLift_iff_strict_dominationLift {le below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b)
    (P Q : W → Prop) (i : W) :
    coneStrictLift le below P Q i ↔
    ComparativeProbability.Strict (dominationLift ge_w)
      {x | le x i ∧ P x ∧ ¬ Q x} {x | le x i ∧ Q x ∧ ¬ P x} := by
  rw [strict_dominationLift_iff_below hTotal hBelow]
  unfold coneStrictLift
  simp only [Set.mem_setOf_eq, and_imp, and_assoc]

/-- The l-lifting satisfies determination by singletons. -/
theorem dominationLift_axiomDS : DeterminedBySingletons (dominationLift ge_w) :=
  fun _ b hAb =>
    let ⟨a, ha, hab⟩ := hAb b rfl
    ⟨a, ha, fun _b' hb' => ⟨a, rfl, hb' ▸ hab⟩⟩

/-- The m-lifting of a reflexive relation is reflexive. -/
theorem matchingLift_axiomR (hRefl : ∀ w, ge_w w w) : Reflexive (matchingLift ge_w) :=
  fun _ => ⟨id, fun b hb => ⟨hb, hRefl b⟩, fun _ _ _ _ h => h⟩

/-- The m-lifting of a reflexive relation is monotone. -/
theorem matchingLift_axiomT (hRefl : ∀ w, ge_w w w) :
    ∀ A B : Set W, A ⊆ B → matchingLift ge_w B A :=
  fun _ _ hAB => ⟨id, fun b hbA => ⟨hAB hbA, hRefl b⟩, fun _ _ _ _ h => h⟩

/-- The l-lifting of a reflexive preorder yields a System W (soundness). -/
def dominationLiftSystemW (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) : EpistemicSystemW W where
  ge := dominationLift ge_w
  refl := dominationLift_axiomR hRefl
  mono := dominationLift_axiomT hRefl

/-- The m-lifting of a reflexive preorder yields a System W. -/
def matchingLiftSystemW (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) : EpistemicSystemW W where
  ge := matchingLift ge_w
  refl := matchingLift_axiomR hRefl
  mono := matchingLift_axiomT hRefl

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

/-! ### Generalized finite cancellation and GFC orders

The cancellation theory of imprecise (multi-prior) comparative probability,
following [harrison-trainor-holliday-icard-2016] (after Ríos Insua 1992 and
Alon–Lehrer 2014) and used by [harrison-trainor-holliday-icard-2018]. A pair of
event-sequences is *balanced* when every state lies in equally many events on
each side; **Finite Cancellation** (Scott) and its **Generalized** strengthening
are the cancellation axioms whose `Refl + Positivity + Non-triviality` companions
characterize representability by a single, resp. a *set* of, additive measures. -/

open scoped Classical in
/-- Indicator count of a state across an event sequence. -/
noncomputable def seqCount {W : Type*} (s : W) (Es : List (Set W)) : ℕ :=
  (Es.map (fun E => if s ∈ E then (1 : ℕ) else 0)).sum

/-- A **balanced** pair of event-sequences ([harrison-trainor-holliday-icard-2016]):
    every state lies in equally many events on the left as on the right. -/
def Balanced {W : Type*} (Es Fs : List (Set W)) : Prop := ∀ s : W, seqCount s Es = seqCount s Fs

/-- **Finite Cancellation** (Scott's axiom; [harrison-trainor-holliday-icard-2016]):
    for every balanced pair `⟨…, X⟩` / `⟨…, Y⟩` whose premise comparisons all hold,
    `Y ≿ X`. (`prem` carries the paired premise events; `X`/`Y` are the heads.) -/
def FiniteCancellation {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W),
    Balanced (X :: prem.map Prod.fst) (Y :: prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- **Generalized Finite Cancellation** (Ríos Insua; Alon–Lehrer; the form of
    [harrison-trainor-holliday-icard-2016]): like `FiniteCancellation`, but the
    distinguished pair may be repeated `r ≥ 1` times. Strictly stronger than
    `FiniteCancellation` for incomplete relations; equivalent under totality. -/
def GeneralizedFiniteCancellation {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W) (r : ℕ), 1 ≤ r →
    Balanced (List.replicate r X ++ prem.map Prod.fst)
             (List.replicate r Y ++ prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-- GFC implies FC (the `r = 1` instance). -/
theorem FiniteCancellation.of_gfc {W : Type*} {ge : Set W → Set W → Prop}
    (h : GeneralizedFiniteCancellation ge) : FiniteCancellation ge :=
  fun prem X Y hbal hprem => h prem X Y 1 le_rfl (by simpa [List.replicate_one] using hbal) hprem

/-- A **GFC order** ([harrison-trainor-holliday-icard-2018], after
    [harrison-trainor-holliday-icard-2016]): reflexivity, positivity,
    non-triviality, and generalized finite cancellation. These four axioms
    characterize representability by a nonempty set of additive measures
    (`E ≿ F ↔ ∀ μ ∈ P, μ E ≥ μ F`). Transitivity, monotonicity, and complement
    reversal are *derived* from cancellation (`GFCOrder.trans`/`mono`/`complRev`),
    not stipulated. -/
structure GFCOrder (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Reflexivity. -/
  refl : ∀ A, ge A A
  /-- Positivity: every proposition is at least as likely as the contradiction. -/
  positivity : ∀ A, ge A ∅
  /-- Non-triviality: the contradiction is not at least as likely as the tautology. -/
  nonTriviality : ¬ ge ∅ Set.univ
  /-- Generalized finite cancellation. -/
  gfc : GeneralizedFiniteCancellation ge

section

variable {W : Type*} (G : GFCOrder W)

/-- A GFC order satisfies finite cancellation. -/
theorem GFCOrder.fc : FiniteCancellation G.ge := FiniteCancellation.of_gfc G.gfc

/-- Transitivity is derived from cancellation (balanced sequence `⟨A,B,C⟩`/`⟨B,C,A⟩`). -/
theorem GFCOrder.trans {A B C : Set W} (hAB : G.ge A B) (hBC : G.ge B C) : G.ge A C := by
  refine G.fc [(A, B), (B, C)] C A (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hAB
    · exact hBC

/-- Monotonicity is derived from positivity + cancellation
    (balanced sequence `⟨B∖A, A⟩`/`⟨∅, B⟩`). -/
theorem GFCOrder.mono {A B : Set W} (hAB : A ⊆ B) : G.ge B A := by
  refine G.fc [(B \ A, ∅)] A B (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_empty_iff_false, if_false, Set.mem_sdiff]
    by_cases hsA : s ∈ A
    · simp [hsA, hAB hsA]
    · by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact G.positivity _

/-- Complement reversal is derived from cancellation
    (balanced sequence `⟨A, Aᶜ⟩`/`⟨B, Bᶜ⟩`). -/
theorem GFCOrder.complRev {A B : Set W} (hAB : G.ge A B) : G.ge Bᶜ Aᶜ := by
  refine G.fc [(A, B)] Aᶜ Bᶜ (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_compl_iff]
    by_cases hsA : s ∈ A <;> by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hAB

end

/-! #### Measures induce GFC orders -/

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {W : Type*} [Fintype W] (m : FinAddMeasure K W)

omit [Fintype W] in
/-- The measure of a finite set is the sum of its singleton measures. -/
lemma FinAddMeasure.muFinsetSum (S : Finset W) :
    m.mu (↑S : Set W) = ∑ i ∈ S, m.mu {i} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hdisj : Disjoint ({a} : Set W) ↑S :=
      Set.disjoint_singleton_left.mpr (fun h => ha (Finset.mem_coe.mp h))
    rw [Finset.coe_insert, Set.insert_eq, m.additive _ _ hdisj, ih, Finset.sum_insert ha]

open scoped Classical in
private lemma FinAddMeasure.muEqSumIte (E : Set W) :
    m.mu E = ∑ s, if s ∈ E then m.mu {s} else 0 := by
  classical
  have h : m.mu E = ∑ i ∈ E.toFinset, m.mu {i} := by
    conv_lhs => rw [← Set.coe_toFinset E]
    exact muFinsetSum m E.toFinset
  rw [h, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext s; simp [Set.mem_toFinset]

private lemma FinAddMeasure.muListSum (L : List (Set W)) :
    (L.map m.mu).sum = ∑ s, m.mu {s} * (seqCount s L : K) := by
  classical
  induction L with
  | nil => simp [seqCount]
  | cons E L ih =>
    rw [List.map_cons, List.sum_cons, ih, muEqSumIte m E, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hsc : seqCount s (E :: L) = (if s ∈ E then 1 else 0) + seqCount s L := by
      simp [seqCount]
    rw [hsc]; push_cast
    by_cases hs : s ∈ E
    · simp only [hs, if_true]; rw [mul_add, mul_one]
    · simp [hs]

private lemma FinAddMeasure.muListSum_eq_of_balanced {L₁ L₂ : List (Set W)} (h : Balanced L₁ L₂) :
    (L₁.map m.mu).sum = (L₂.map m.mu).sum := by
  rw [muListSum m L₁, muListSum m L₂]
  exact Finset.sum_congr rfl (fun s _ => by rw [h s])

omit [Fintype W] in
private lemma FinAddMeasure.sum_mono {prem : List (Set W × Set W)}
    (hprem : ∀ p ∈ prem, m.inducedGe p.1 p.2) :
    ((prem.map Prod.snd).map m.mu).sum ≤ ((prem.map Prod.fst).map m.mu).sum := by
  induction prem with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hprem p (List.mem_cons_self ..))
      (ih (fun q hq => hprem q (List.mem_cons_of_mem _ hq)))

/-- Every finitely additive measure's induced order is a GFC order: the
    Scott / Alon–Lehrer soundness direction (a single measure `μ` is the
    nonempty set `{μ}`). -/
def FinAddMeasure.toGFCOrder : GFCOrder W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  positivity := fun A => by simpa [inducedGe, m.mu_empty] using m.nonneg A
  nonTriviality := by simp only [inducedGe, m.mu_empty, m.total, not_le]; exact one_pos
  gfc := by
    intro prem X Y r hr hbal hprem
    have hsum := muListSum_eq_of_balanced m hbal
    simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul] at hsum
    have hr0 : (0 : K) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    show m.mu X ≤ m.mu Y
    have hkey : (r : K) * m.mu X ≤ (r : K) * m.mu Y := by nlinarith [sum_mono m hprem]
    exact le_of_mul_le_mul_left hkey hr0

end

end ComparativeProbability
