import Linglib.Core.Order.ComparativeProbability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Epistemic Comparative Likelihood

[holliday-icard-2013] [halpern-2003] [van-der-hoek-1996]
[harrison-trainor-holliday-icard-2016] [harrison-trainor-holliday-icard-2018]

Comparative-likelihood orders on propositions (`Set W`): an axiom hierarchy,
finitely- and qualitatively-additive measure semantics, the two world-ordering
lifts, and the generalized cancellation theory of imprecise (multi-prior)
comparative probability.

[holliday-icard-2013] study the logic of "at least as likely as" (≿) on
propositions, whose qualitative-additivity axiom is the qualitative counterpart
of finite additivity.

**Axiom systems.** The bundled `EpistemicSystemW ⊂ F ⊂ FA` are a *coarse staging*
toward [holliday-icard-2013]'s logic **FA** (their Figure 6: `Ex, Bot, BT, Tot,
Tran, A` over the base modal logic `K`); only `EpistemicSystemFA` reproduces a
named logic of the paper (`Ex` and `K` are automatic for the `Set W` relation
rendering). The intermediate `EpistemicSystemW`/`F` are *not* the paper's logics
`W`/`F`: the paper's `W` already carries `Mon`, `Tran`, `BT`, and the `W`-to-`F`
step there is totality `Tot`; its full landscape (Figure 3, the "Logical
landscape") is developed in the companion *On the logic of comparative
likelihood*. The local labels `R`/`T` are mnemonic — the paper writes `Mon` for
monotonicity, and its `R` is the regularity axiom `◇φ ↔ ¬(⊥ ≿ φ)`.

**Generalized Finite Cancellation.** `GFCOrder` is the genuine GFC order of
[harrison-trainor-holliday-icard-2018], after [harrison-trainor-holliday-icard-2016]
(Ríos Insua 1992; Alon–Lehrer 2014): reflexivity, positivity, non-triviality, and
the `GeneralizedFiniteCancellation` balanced-sequence axiom characterizing
representability by a *set* of measures. Its `trans`/`mono`/`complRev` are
*derived* from the cancellation axiom, and every `FinAddMeasure` induces one
(`FinAddMeasure.toGFCOrder`, the Scott/Alon–Lehrer soundness direction).

**Bridge**: Axiom A (qualitative additivity) is equivalent to disjoint-augmentation
invariance — the law-shape `AdditiveScale.fa` (`Core/Order/ComparativeScale.lean`)
imposes on degree carriers (`axiomA_iff_fa`, `Completeness.lean`).

**Upstreaming (`Core/Order` candidate).** The `Set W` axioms specialise the
`BooleanAlgebra`-general mixin classes of `Defs.lean` (mathlib's `IsTrans`-style
relation classes); `dominationLift`/`matchingLift` are the Smyth (upper
powerdomain) order and its injection refinement — order constructions mathlib
lacks; `FinAddMeasure.inducedGe` is `Order.Preimage m.mu (· ≥ ·)`. `FinAddMeasure`
overlaps mathlib's `MeasureTheory.AddContent` (an `AddCommMonoid`-valued
finitely-additive content — here morally `AddContent (univ : Set (Set W)) K` plus
non-negativity and normalization) and could be re-founded on it.

`FinAddMeasure`/`QualAddMeasure` are **generic over an ordered field `K`**
(`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`): instantiate at **ℝ** for
the paper's literal `[0,1]`-valued measures ([holliday-icard-2013], §4;
[kraft-pratt-seidenberg-1959]), or at **ℚ** for the constructive representation
theory. On a *finite* state space the two agree — a feasible system of rational
linear inequalities has a rational solution, so an order is representable by a
real measure iff by a rational one — and only ℚ is computable: the Scott/KPS
direction rides a computable rational Farkas/Fourier-Motzkin
(`Core/Order/FourierMotzkin.lean`, deliberately avoiding mathlib's noncomputable
real hyperplane-separation Farkas) and `decide`-checked finite models
(`Representability.lean`), both of which a real value type would block.
-/

namespace ComparativeProbability

-- ── Axioms (Figures 4–6) ────────────────────────

namespace EpistemicAxiom

/-- Axiom R (mnemonic): reflexivity — A ≿ A. (In [holliday-icard-2013], `R` names
    the regularity axiom `◇φ ↔ ¬(⊥ ≿ φ)`; reflexivity is unnamed there.) -/
def R {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A, ge A A

/-- Axiom T (mnemonic): monotonicity — A ⊆ B → B ≿ A. ([holliday-icard-2013]
    write this `Mon`.) -/
def T {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, A ⊆ B → ge B A

/-- Axiom Bot ([holliday-icard-2013]): Ω ≿ ∅ — tautology is at least as likely as
    contradiction. -/
def Bot {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ge Set.univ ∅

/-- Axiom BT: ¬(∅ ≿ Ω) — contradiction is NOT at least as likely as tautology.
    The non-triviality condition from [holliday-icard-2013].
    Without this, the degenerate ordering (all sets equivalent) would satisfy
    FA but admit no finitely additive measure representation (since μ(∅) = 0
    but μ(Ω) = 1). -/
def BT {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ¬ge ∅ Set.univ

/-- Axiom A: qualitative additivity — A ≿ B ↔ (A \ B) ≿ (B \ A).
    The comparative likelihood factors through disjoint parts. -/
def A {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, ge A B ↔ ge (A \ B) (B \ A)

/-- Axiom J ([holliday-icard-2013], Figure 4): right-union —
    φ ≿ ψ ∧ φ ≿ χ → φ ≿ (ψ ∨ χ). -/
def J {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B C, ge A B → ge A C → ge A (B ∪ C)

/-- Axiom DS: determination by singletons — A ≿ {b} → ∃ a ∈ A, {a} ≿ {b}. The
    comparison can be witnessed by a single element of the dominating set; this
    is a structural property of the l-lifting (see `dominationLift_axiomDS`),
    used by the completeness construction for the l-lifting logic
    ([halpern-2003]; [holliday-icard-2013]). -/
def DS {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ (A : Set W) (b : W), ge A {b} → ∃ a ∈ A, ge {a} {b}

end EpistemicAxiom

-- ── Logic Hierarchy ─────────────────────────────

/-- Staging system W: reflexivity + monotonicity (weaker than
    [holliday-icard-2013]'s logic `W`; see the module docstring). -/
structure EpistemicSystemW (W : Type*) where
  /-- The "at least as likely as" relation on propositions. -/
  ge : Set W → Set W → Prop
  /-- Reflexivity. -/
  refl : EpistemicAxiom.R ge
  /-- Monotonicity: supersets are at least as likely. -/
  mono : EpistemicAxiom.T ge

/-- Staging system F: adds `Bot` (Ω ≿ ∅, redundant with monotonicity) and `BT`,
    the non-triviality condition that excludes degenerate orderings. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  /-- Bottom: the tautology is at least as likely as the contradiction. -/
  bottom : EpistemicAxiom.Bot ge
  /-- Non-triviality: the contradiction is not at least as likely as the tautology. -/
  nonTrivial : EpistemicAxiom.BT ge

/-- System FA: staging system F + totality + transitivity + qualitative additivity.
    Sound and complete for **qualitatively additive** measure semantics
    ([holliday-icard-2013], Theorem 6; [van-der-hoek-1996]). Strictly weaker than
    FP∞ (finitely additive measures) for |W| ≥ 5 ([holliday-icard-2013], Theorem 8,
    after [kraft-pratt-seidenberg-1959]). This reproduces the paper's logic FA
    (Figure 6: `Ex, Bot, BT, Tot, Tran, A`; `Ex` is automatic for `Set W`). -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemF W where
  /-- Totality: any two propositions are comparable. -/
  total : ∀ A B : Set W, ge A B ∨ ge B A
  /-- Transitivity. -/
  trans : ∀ A B C : Set W, ge A B → ge B C → ge A C
  /-- Qualitative additivity (Axiom A). -/
  additive : EpistemicAxiom.A ge

/-! ### FA systems carry the comparative-probability mixins

The `EpistemicAxiom.*` predicates are the `Set W` spellings of the
Boolean-algebra-general `ComparativeProbability` mixin classes (`a ≤ b` is
defeq `a ⊆ b` on `Set W`), so the instances below register every FA system's
relation as a comparative-probability order by definitional unfolding, and the
validity patterns V1–V13 transfer from `ComparativeProbability.Patterns` by
instance resolution. -/

namespace EpistemicSystemFA

variable {W : Type*} (sys : EpistemicSystemFA W)

instance : ComparativeProbability.IsLikelihoodMono sys.ge := ⟨sys.mono⟩

instance : IsTrans (Set W) sys.ge := ⟨sys.trans⟩

instance : ComparativeProbability.IsQualitativeAdditive sys.ge := ⟨sys.additive⟩

instance : ComparativeProbability.IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

end EpistemicSystemFA

/-! ### Consequences of the FA axioms -/

/-- **Add common context**: for `C` disjoint from both `X` and `Y`,
    `X ≿ Y ↔ (X ∪ C) ≿ (Y ∪ C)`. -/
lemma ge_union_context {W : Type*} (sys : EpistemicSystemFA W) (X Y C : Set W)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) :
    sys.ge X Y ↔ sys.ge (X ∪ C) (Y ∪ C) := by
  rw [sys.additive X Y, sys.additive (X ∪ C) (Y ∪ C)]
  have hCXl := Set.disjoint_left.mp hCX
  have hCYl := Set.disjoint_left.mp hCY
  have e1 : (X ∪ C) \ (Y ∪ C) = X \ Y := by
    ext x; simp only [Set.mem_sdiff, Set.mem_union]; have := @hCXl x; tauto
  have e2 : (Y ∪ C) \ (X ∪ C) = Y \ X := by
    ext x; simp only [Set.mem_sdiff, Set.mem_union]; have := @hCYl x; tauto
  rw [e1, e2]

/-- **Generalized merge**: two valid comparisons with disjoint left parts and
    disjoint right parts merge into their union, even with pivot overlaps.
    Derivation: add context to each side, transit through `X₂ ∪ Y₁`, then
    restore the pivot `X₂ ∩ Y₁` via Axiom A. -/
lemma ge_generalized_merge {W : Type*} (sys : EpistemicSystemFA W)
    {X₁ Y₁ X₂ Y₂ : Set W}
    (h1 : sys.ge X₁ Y₁) (h2 : sys.ge X₂ Y₂)
    (hX : Disjoint X₁ X₂) (hY : Disjoint Y₁ Y₂) :
    sys.ge (X₁ ∪ X₂) (Y₁ ∪ Y₂) := by
  have hXl : ∀ x, x ∈ X₁ → x ∉ X₂ := fun x hx => Set.disjoint_left.mp hX hx
  have hYl : ∀ x, x ∈ Y₂ → x ∉ Y₁ := fun x hy2 hy1 => Set.disjoint_left.mp hY hy1 hy2
  -- context C₁ = X₂ \ Y₁ added to (X₁ ≿ Y₁); C₂ = Y₁ \ X₂ added to (X₂ ≿ Y₂)
  have step1 : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₁ ∪ (X₂ \ Y₁)) :=
    (ge_union_context sys X₁ Y₁ (X₂ \ Y₁) (Set.disjoint_left.mpr fun x hx hx1 => hXl x hx1 hx.1)
      (Set.disjoint_left.mpr fun x hx hxY1 => hx.2 hxY1)).mp h1
  have step2 : sys.ge (X₂ ∪ (Y₁ \ X₂)) (Y₂ ∪ (Y₁ \ X₂)) :=
    (ge_union_context sys X₂ Y₂ (Y₁ \ X₂) (Set.disjoint_left.mpr fun x hx hx2 => hx.2 hx2)
      (Set.disjoint_left.mpr fun x hx hxY2 => hYl x hxY2 hx.1)).mp h2
  rw [show Y₁ ∪ (X₂ \ Y₁) = X₂ ∪ (Y₁ \ X₂) by ext x; simp only [Set.mem_union, Set.mem_sdiff]; tauto]
    at step1
  have htrans : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₂ ∪ (Y₁ \ X₂)) := sys.trans _ _ _ step1 step2
  set P : Set W := X₂ ∩ Y₁ with hP
  have hLHS : X₁ ∪ (X₂ \ Y₁) = (X₁ ∪ X₂) \ P := by
    ext x; have := hXl x; simp only [Set.mem_union, Set.mem_sdiff, hP, Set.mem_inter_iff, not_and]; tauto
  have hRHS : Y₂ ∪ (Y₁ \ X₂) = (Y₁ ∪ Y₂) \ P := by
    ext x; have := hYl x; simp only [Set.mem_union, Set.mem_sdiff, hP, Set.mem_inter_iff, not_and]; tauto
  rw [hLHS, hRHS] at htrans
  have key := (ge_union_context sys ((X₁ ∪ X₂) \ P) ((Y₁ ∪ Y₂) \ P) P
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)).mp htrans
  rwa [Set.sdiff_union_of_subset (Set.inter_subset_left.trans Set.subset_union_right),
    Set.sdiff_union_of_subset (Set.inter_subset_right.trans Set.subset_union_left)] at key

/-- **Mono-domination**: a valid comparison `X ≿ Y` with `X ⊆ P` and `Q ⊆ Y`
    proves `P ≿ Q`. -/
lemma ge_mono_dominated {W : Type*} (sys : EpistemicSystemFA W)
    {X Y P Q : Set W} (h : sys.ge X Y) (hXP : X ⊆ P) (hQY : Q ⊆ Y) :
    sys.ge P Q :=
  sys.trans _ _ _ (sys.mono X P hXP) (sys.trans _ _ _ h (sys.mono Q Y hQY))

/-- `P ≿ ∅` always (monotonicity). -/
lemma ge_empty_target {W : Type*} (sys : EpistemicSystemFA W) (P : Set W) :
    sys.ge P ∅ :=
  sys.mono ∅ P (Set.empty_subset P)

-- ── Measure Semantics ───────────────────────────

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

namespace FinAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : FinAddMeasure K W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Measure-induced ≿ is reflexive. -/
theorem inducedGe_axiomR (m : FinAddMeasure K W) :
    EpistemicAxiom.R m.inducedGe :=
  fun _ => le_refl _

/-- Measure-induced ≿ satisfies monotonicity.
    A ⊆ B → B = A ∪ (B \ A) → μ(B) = μ(A) + μ(B \ A) ≥ μ(A). -/
theorem inducedGe_axiomT (m : FinAddMeasure K W) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  rw [(Set.union_sdiff_cancel hAB).symm, m.additive A (B \ A) disjoint_sdiff_self_right]
  exact le_add_of_nonneg_right (m.nonneg (B \ A))

/-- μ(∅) = 0 for any finitely additive measure.
    Follows from additivity: μ(∅ ∪ ∅) = μ(∅) + μ(∅), but ∅ ∪ ∅ = ∅. -/
@[simp] theorem mu_empty (m : FinAddMeasure K W) : m.mu ∅ = 0 := by
  have hempty := m.additive ∅ ∅ disjoint_bot_left
  rw [Set.empty_union] at hempty; linarith

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. -/
theorem mu_mono (m : FinAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  have hunion := m.additive A (B \ A) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel h] at hunion; linarith [m.nonneg (B \ A)]

/-- Complement measure: `μ(A) + μ(Aᶜ) = 1`. -/
theorem mu_compl (m : FinAddMeasure K W) (A : Set W) :
    m.mu A + m.mu Aᶜ = 1 := by
  have hunion := m.additive A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self] at hunion; linarith [m.total]

/-- Qualitative additivity for a finitely additive measure: splitting `A` and `B`
    into the shared part `A ∩ B` and the private parts cancels the shared part. -/
theorem mu_qadd (m : FinAddMeasure K W) (A B : Set W) :
    m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A) := by
  have key : ∀ X Y : Set W, m.mu X = m.mu (X \ Y) + m.mu (X ∩ Y) := fun X Y => by
    conv_lhs => rw [(Set.sdiff_union_inter X Y).symm]
    exact m.additive _ _ (Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.2)
  rw [key A B, key B A, Set.inter_comm B A]; exact add_le_add_iff_right (m.mu (A ∩ B))

/-- Every finitely additive measure satisfies the FA axioms.
    A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def toSystemFA (m : FinAddMeasure K W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := m.inducedGe_axiomR
  mono := m.inducedGe_axiomT
  bottom := by show m.mu Set.univ ≥ m.mu ∅; rw [m.mu_empty]; exact m.nonneg Set.univ
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ); rw [m.mu_empty, m.total]; exact not_le.mpr one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := m.mu_qadd

end FinAddMeasure

-- ── Qualitatively Additive Measures ──────────────

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

namespace QualAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Monotonicity for qualitatively additive measures:
    A ⊆ B → μ(B) ≥ μ(A). Follows from qualAdd + μ(∅) = 0 + nonneg. -/
theorem inducedGe_axiomT (m : QualAddMeasure K W) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  rw [m.qualAdd B A, Set.sdiff_eq_empty.mpr hAB, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces System FA.
    Soundness direction of [holliday-icard-2013] Theorem 6:
    every qualitatively additive measure model satisfies the FA axioms. -/
def toSystemFA (m : QualAddMeasure K W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  mono := m.inducedGe_axiomT
  bottom := by show m.mu Set.univ ≥ m.mu ∅; rw [m.mu_empty]; exact m.nonneg Set.univ
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ); rw [m.mu_empty, m.total]; exact not_le.mpr one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := m.qualAdd

end QualAddMeasure

/-- Every finitely additive measure is qualitatively additive.
    Proof: μ(A) = μ(A \ B) + μ(A ∩ B) and μ(B) = μ(B \ A) + μ(A ∩ B),
    so μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A). -/
def FinAddMeasure.toQualAdd {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W : Type*} (m : FinAddMeasure K W) : QualAddMeasure K W where
  mu := m.mu
  nonneg := m.nonneg
  mu_empty := m.mu_empty
  total := m.total
  qualAdd := m.mu_qadd

-- ── World-Ordering Semantics ────────────────────

/-- The *l*-lifting (Lewis's lifting; [holliday-icard-2013], §5): a preorder on
    worlds induces a comparison on propositions. A ≿ B iff for every b ∈ B,
    ∃ a ∈ A with a ≥_w b. See also their injection-based *m*-lifting (`matchingLift`,
    §9), which yields a complete logic for world-ordering models.

    This is the **Smyth (upper powerdomain) order** lifted from `ge_w`. -/
def dominationLift {W : Type*} (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b

/-- l-lifting from a reflexive relation satisfies Axiom R. -/
theorem dominationLift_axiomR {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.R (dominationLift ge_w) :=
  fun _ b hb => ⟨b, hb, hRefl b⟩

/-- l-lifting from a reflexive relation satisfies Axiom T.
    If A ⊆ B and b ∈ A, then b ∈ B, so take a = b. -/
theorem dominationLift_axiomT {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.T (dominationLift ge_w) :=
  fun _ _ hAB b hbA => ⟨b, hAB hbA, hRefl b⟩

/-- The *l*-lifting from a reflexive preorder yields System W.
    Soundness direction: world-ordering models with the l-lifting
    validate System W ([halpern-2003]; [holliday-icard-2013]). -/
def dominationLiftSystemW {W : Type*} (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    EpistemicSystemW W where
  ge := dominationLift ge_w
  refl := dominationLift_axiomR hRefl
  mono := dominationLift_axiomT hRefl

/-- l-lifting satisfies Axiom J (right-union).
    If every b ∈ B is dominated and every c ∈ C is dominated, then
    every element of B ∪ C is dominated. -/
theorem dominationLift_axiomJ {W : Type*} {ge_w : W → W → Prop} :
    EpistemicAxiom.J (dominationLift ge_w) :=
  fun _ _ _ hAB hAC b hb => hb.elim (hAB b) (hAC b)

/-- l-lifting satisfies Axiom DS (determination by singletons).
    If A ≿ {b} via the lift, some a ∈ A has ge_w a b, so {a} ≿ {b}. -/
theorem dominationLift_axiomDS {W : Type*} {ge_w : W → W → Prop} :
    EpistemicAxiom.DS (dominationLift ge_w) :=
  fun _ b hAb =>
    let ⟨a, ha, hab⟩ := hAb b rfl
    ⟨a, ha, fun _b' hb' => ⟨a, rfl, hb' ▸ hab⟩⟩

-- ── m-Lifting ([holliday-icard-2013], §9) ──

/-- The *m*-lifting ([holliday-icard-2013], §9): an injection-based
    alternative to `dominationLift`. A ≿ B iff there exists an injection
    f : B ↪ A such that f(b) ≥_w b for all b ∈ B.

    The key difference from `dominationLift` (l-lifting) is that dominators
    must be **distinct**: each element of B is matched to a unique element
    of A. This avoids the "disjunction problem" (I1–I3 become invalid),
    while validating all 13 validity patterns V1–V13 (Fact 5). -/
def matchingLift {W : Type*} (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∃ (f : W → W),
    (∀ b, b ∈ B → f b ∈ A ∧ ge_w (f b) b) ∧
    (∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → f b₁ = f b₂ → b₁ = b₂)

/-- m-lift from a reflexive relation satisfies Axiom R. -/
theorem matchingLift_axiomR {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.R (matchingLift ge_w) :=
  fun _ => ⟨id, fun b hb => ⟨hb, hRefl b⟩, fun _ _ _ _ h => h⟩

/-- m-lift from a reflexive relation satisfies Axiom T.
    If A ⊆ B and b ∈ A, then b ∈ B, so take f = id. -/
theorem matchingLift_axiomT {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.T (matchingLift ge_w) :=
  fun _ _ hAB => ⟨id, fun b hbA => ⟨hAB hbA, hRefl b⟩, fun _ _ _ _ h => h⟩

/-- m-lifting from a reflexive preorder yields System W. -/
def matchingLiftSystemW {W : Type*} (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    EpistemicSystemW W where
  ge := matchingLift ge_w
  refl := matchingLift_axiomR hRefl
  mono := matchingLift_axiomT hRefl

/-! ### Connection to the `ComparativeProbability` theory

Every finitely-additive measure's induced order is a comparative-probability
order (monotone, transitive, qualitatively additive, non-trivial), so the
validity patterns V1–V13 transfer for free from `ComparativeProbability.Patterns`
by instance resolution — no per-measure arithmetic. -/

namespace FinAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}
  (m : FinAddMeasure K W)

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe := ⟨m.inducedGe_axiomT⟩

instance : IsTrans (Set W) m.inducedGe := ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe := ⟨m.toSystemFA.additive⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe := ⟨m.toSystemFA.nonTrivial⟩

end FinAddMeasure

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
def Balanced {W : Type*} (Es Fs : List (Set W)) : Prop :=
  ∀ s : W, seqCount s Es = seqCount s Fs

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
    (h : GeneralizedFiniteCancellation ge) : FiniteCancellation ge := by
  intro prem X Y hbal hprem
  refine h prem X Y 1 le_rfl ?_ hprem
  simpa [List.replicate_one] using hbal

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

namespace GFCOrder

variable {W : Type*} (G : GFCOrder W)

/-- A GFC order satisfies finite cancellation. -/
theorem fc : FiniteCancellation G.ge := FiniteCancellation.of_gfc G.gfc

/-- Transitivity is derived from cancellation (balanced sequence `⟨A,B,C⟩`/`⟨B,C,A⟩`). -/
theorem trans {A B C : Set W} (hAB : G.ge A B) (hBC : G.ge B C) : G.ge A C := by
  refine G.fc [(A, B), (B, C)] C A (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hAB
    · exact hBC

/-- Monotonicity is derived from positivity + cancellation
    (balanced sequence `⟨B∖A, A⟩`/`⟨∅, B⟩`). -/
theorem mono {A B : Set W} (hAB : A ⊆ B) : G.ge B A := by
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
theorem complRev {A B : Set W} (hAB : G.ge A B) : G.ge Bᶜ Aᶜ := by
  refine G.fc [(A, B)] Aᶜ Bᶜ (fun s => ?_) (fun p hp => ?_)
  · simp only [seqCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Set.mem_compl_iff]
    by_cases hsA : s ∈ A <;> by_cases hsB : s ∈ B <;> simp [hsA, hsB]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hAB

end GFCOrder

/-! #### Measures induce GFC orders -/

namespace FinAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {W : Type*} [Fintype W] (m : FinAddMeasure K W)

omit [Fintype W] in
/-- The measure of a finite set is the sum of its singleton measures. -/
lemma muFinsetSum (S : Finset W) :
    m.mu (↑S : Set W) = ∑ i ∈ S, m.mu {i} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hdisj : Disjoint ({a} : Set W) ↑S :=
      Set.disjoint_singleton_left.mpr (fun h => ha (Finset.mem_coe.mp h))
    rw [Finset.coe_insert, Set.insert_eq, m.additive _ _ hdisj, ih, Finset.sum_insert ha]

open scoped Classical in
private lemma muEqSumIte (E : Set W) :
    m.mu E = ∑ s, if s ∈ E then m.mu {s} else 0 := by
  classical
  have h : m.mu E = ∑ i ∈ E.toFinset, m.mu {i} := by
    conv_lhs => rw [← Set.coe_toFinset E]
    exact muFinsetSum m E.toFinset
  rw [h, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext s; simp [Set.mem_toFinset]

private lemma muListSum (L : List (Set W)) :
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

private lemma muListSum_eq_of_balanced {L₁ L₂ : List (Set W)} (h : Balanced L₁ L₂) :
    (L₁.map m.mu).sum = (L₂.map m.mu).sum := by
  rw [muListSum m L₁, muListSum m L₂]
  exact Finset.sum_congr rfl (fun s _ => by rw [h s])

omit [Fintype W] in
private lemma sum_mono {prem : List (Set W × Set W)}
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
def toGFCOrder : GFCOrder W where
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

end FinAddMeasure

end ComparativeProbability
