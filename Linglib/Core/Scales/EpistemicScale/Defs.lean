import Linglib.Core.Scales.Scale
import Linglib.Core.Order.ComparativeProbability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-!
# Epistemic Comparative Likelihood

[holliday-icard-2013] [halpern-2003] [van-der-hoek-1996]

Epistemic likelihood scales: comparative-likelihood orders on propositions
(`Set W`), their axiom hierarchy, and their measure semantics.

[holliday-icard-2013] study the logic of "at least as likely as" (≿) on
propositions, defining a hierarchy of axiom systems (W ⊂ F ⊂ FA) whose
qualitative additivity axiom is the epistemic counterpart of finite additivity.

**Axiom hierarchy** ([holliday-icard-2013], Figure 3; axioms in Figures 4–6):

| System | Axioms                  | Semantics                          |
|--------|-------------------------|------------------------------------|
| W      | R, T                   | World-ordering + l-lifting         |
| F      | W + Bot, BT            | + bottom, non-triviality           |
| FA     | F + Tot, Tran, A       | Qualitatively additive measures    |
| FP∞    | FA + Scott cancellation | Finitely additive measures         |

**Bridge**: Axiom A (epistemic qualitative additivity) is equivalent to
disjoint-augmentation invariance — the same law-shape that `AdditiveScale.fa`
(`Core/Scales/Comparative.lean`) imposes on degree carriers. The equivalence
is `axiomA_iff_fa` in `Completeness.lean`.

References:
- Holliday, W. & Icard, T. (2013). Measure Semantics and Qualitative
  Semantics for Epistemic Modals. SALT 23: 514–534.
- Halpern, J. (2003). Reasoning about Uncertainty. MIT Press.
- van der Hoek, W. (1996). Qualitative modalities. IJUFKS 4(1).
-/

namespace Core.Scale

-- ── Axioms (Figures 4–6) ────────────────────────

namespace EpistemicAxiom

/-- Axiom R: reflexivity — A ≿ A. -/
def R {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A, ge A A

/-- Axiom T: monotonicity — A ⊆ B → B ≿ A. -/
def T {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, A ⊆ B → ge B A

/-- Axiom F: Ω ≿ ∅ — tautology is at least as likely as contradiction. -/
def F {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
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

/-- Axiom DS: determination by singletons ([halpern-2003], Thm. 7.5.1a) —
    A ≿ {b} → ∃ a ∈ A, {a} ≿ {b}. The comparison can be witnessed
    by a single element of the dominating set. -/
def DS {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ (A : Set W) (b : W), ge A {b} → ∃ a ∈ A, ge {a} {b}

end EpistemicAxiom

-- ── Logic Hierarchy ─────────────────────────────

/-- System W: the weakest epistemic likelihood logic.
    Reflexivity + monotonicity. -/
structure EpistemicSystemW (W : Type*) where
  ge : Set W → Set W → Prop
  refl : EpistemicAxiom.R ge
  mono : EpistemicAxiom.T ge

/-- System F: System W + Bot + BT.
    Bot (Ω ≿ ∅) is redundant with monotonicity. BT (¬(∅ ≿ Ω)) is the
    non-triviality condition that excludes degenerate orderings. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  bottom : EpistemicAxiom.F ge
  nonTrivial : EpistemicAxiom.BT ge

/-- System FA: System F + totality + transitivity + qualitative additivity.
    Sound and complete for **qualitatively additive** measure semantics
    ([holliday-icard-2013], Theorem 6; [van-der-hoek-1996]).
    Strictly weaker than FP∞ (finitely additive measures) for |W| ≥ 5
    (Kraft, [kraft-pratt-seidenberg-1959], Theorem 8).

    Totality and transitivity are part of the FA logic in [holliday-icard-2013]: FA = Bot + BT + Tot + Tran + A. -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemF W where
  total : ∀ A B : Set W, ge A B ∨ ge B A
  trans : ∀ A B C : Set W, ge A B → ge B C → ge A C
  additive : EpistemicAxiom.A ge

/-! ### FA systems carry the comparative-probability mixins

The `EpistemicAxiom.*` predicates are the `Set W` spellings of the
Boolean-algebra-general `ComparativeProbability` mixin classes; the
instances below make every FA system's relation a comparative-probability
order, so the validity patterns V1–V13 transfer from
`ComparativeProbability.Patterns` by instance resolution. -/

theorem isLikelihoodMono_iff_axiomT {W : Type*} {ge : Set W → Set W → Prop} :
    ComparativeProbability.IsLikelihoodMono ge ↔ EpistemicAxiom.T ge :=
  ⟨fun h A B hAB => h.mono A B hAB, fun h => ⟨h⟩⟩

theorem isQualitativeAdditive_iff_axiomA {W : Type*} {ge : Set W → Set W → Prop} :
    ComparativeProbability.IsQualitativeAdditive ge ↔ EpistemicAxiom.A ge :=
  ⟨fun h => h.qadd, fun h => ⟨h⟩⟩

theorem isNontrivial_iff_axiomBT {W : Type*} {ge : Set W → Set W → Prop} :
    ComparativeProbability.IsNontrivial ge ↔ EpistemicAxiom.BT ge :=
  ⟨fun h => h.bot_not_ge_top, fun h => ⟨h⟩⟩

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
  have hCXl : ∀ x, x ∈ C → x ∉ X := fun x hx => Set.disjoint_left.mp hCX hx
  have hCYl : ∀ x, x ∈ C → x ∉ Y := fun x hx => Set.disjoint_left.mp hCY hx
  have e1 : (X ∪ C) \ (Y ∪ C) = X \ Y := by
    ext x
    have := hCXl x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  have e2 : (Y ∪ C) \ (X ∪ C) = Y \ X := by
    ext x
    have := hCYl x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
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
  -- context C₁ = X₂ \ Y₁ added to (X₁ ≿ Y₁)
  have step1 : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₁ ∪ (X₂ \ Y₁)) :=
    (ge_union_context sys X₁ Y₁ (X₂ \ Y₁)
      (Set.disjoint_left.mpr fun x hx hx1 => hXl x hx1 hx.1)
      (Set.disjoint_left.mpr fun x hx hxY1 => hx.2 hxY1)).mp h1
  -- context C₂ = Y₁ \ X₂ added to (X₂ ≿ Y₂)
  have step2 : sys.ge (X₂ ∪ (Y₁ \ X₂)) (Y₂ ∪ (Y₁ \ X₂)) :=
    (ge_union_context sys X₂ Y₂ (Y₁ \ X₂)
      (Set.disjoint_left.mpr fun x hx hx2 => hx.2 hx2)
      (Set.disjoint_left.mpr fun x hx hxY2 => hYl x hxY2 hx.1)).mp h2
  have hmid : Y₁ ∪ (X₂ \ Y₁) = X₂ ∪ (Y₁ \ X₂) := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; tauto
  rw [hmid] at step1
  have htrans : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₂ ∪ (Y₁ \ X₂)) := sys.trans _ _ _ step1 step2
  set P : Set W := X₂ ∩ Y₁ with hP
  have hLHS : X₁ ∪ (X₂ \ Y₁) = (X₁ ∪ X₂) \ P := by
    ext x
    have := hXl x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    tauto
  have hRHS : Y₂ ∪ (Y₁ \ X₂) = (Y₁ ∪ Y₂) \ P := by
    ext x
    have := hYl x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    tauto
  rw [hLHS, hRHS] at htrans
  have hPsubX : P ⊆ X₁ ∪ X₂ := Set.inter_subset_left.trans Set.subset_union_right
  have hPsubY : P ⊆ Y₁ ∪ Y₂ := Set.inter_subset_right.trans Set.subset_union_left
  have key := (ge_union_context sys ((X₁ ∪ X₂) \ P) ((Y₁ ∪ Y₂) \ P) P
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)).mp htrans
  rwa [Set.diff_union_of_subset hPsubX, Set.diff_union_of_subset hPsubY] at key

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

-- ── GFC Order ([harrison-trainor-holliday-icard-2018] Definition 2.7) ──

/-- A **GFC preorder** on propositions: a preorder on `Set W` that is
    monotone (supersets are at least as likely) and complement-reversing
    (A ≿ B → Bᶜ ≿ Aᶜ).

    [harrison-trainor-holliday-icard-2018] Definition 2.7. The acronym
    "GFC" reflects the three axiom groups: (G) preorder, (F) faithfulness
    (monotonicity), (C) complement reversal.

    The m-lifting (≿ⁱ) of any reflexive, transitive world ordering is a
    GFC preorder (Theorem 3.2). Note that GFC preorders are NOT necessarily
    total — `matchingLift_not_total` gives a counterexample. -/
structure GFCPreorder (W : Type*) where
  ge : Set W → Set W → Prop
  refl : EpistemicAxiom.R ge
  trans : ∀ A B C : Set W, ge A B → ge B C → ge A C
  mono : EpistemicAxiom.T ge
  complRev : ∀ A B : Set W, ge A B → ge Bᶜ Aᶜ

/-- Every GFC preorder yields System W (the weakest epistemic logic). -/
def GFCPreorder.toSystemW {W : Type*} (g : GFCPreorder W) : EpistemicSystemW W where
  ge := g.ge
  refl := g.refl
  mono := g.mono

/-- Every System FA model is a GFC preorder: complement reversal comes from
    qualitative additivity via the comparative-probability layer
    (`instComplementReversingOfQualitativeAdditive`). -/
def EpistemicSystemFA.toGFCPreorder {W : Type*} (sys : EpistemicSystemFA W) :
    GFCPreorder W where
  ge := sys.ge
  refl := sys.refl
  trans := sys.trans
  mono := sys.mono
  complRev := ComparativeProbability.complRev

-- ── Measure Semantics ───────────────────────────

/-- A finitely additive probability measure on subsets of W. -/
structure FinAddMeasure (W : Type*) where
  /-- The measure function -/
  mu : Set W → ℚ
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- Finite additivity: μ(A ∪ B) = μ(A) + μ(B) for disjoint A, B -/
  additive : ∀ A B, Disjoint A B → mu (A ∪ B) = mu A + mu B
  /-- Normalization -/
  total : mu Set.univ = 1

namespace FinAddMeasure

variable {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : FinAddMeasure W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Measure-induced ≿ is reflexive. -/
theorem inducedGe_axiomR (m : FinAddMeasure W) :
    EpistemicAxiom.R m.inducedGe :=
  fun _ => le_refl _

/-- Measure-induced ≿ satisfies monotonicity.
    A ⊆ B → B = A ∪ (B \ A) → μ(B) = μ(A) + μ(B \ A) ≥ μ(A). -/
theorem inducedGe_axiomT (m : FinAddMeasure W) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  rw [(Set.union_diff_cancel hAB).symm, m.additive A (B \ A) disjoint_sdiff_self_right]
  exact le_add_of_nonneg_right (m.nonneg (B \ A))

/-- μ(∅) = 0 for any finitely additive measure.
    Follows from additivity: μ(∅ ∪ ∅) = μ(∅) + μ(∅), but ∅ ∪ ∅ = ∅. -/
theorem mu_empty (m : FinAddMeasure W) : m.mu ∅ = 0 := by
  have hempty := m.additive ∅ ∅ disjoint_bot_left
  rw [Set.empty_union] at hempty
  linarith

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. -/
theorem mu_mono (m : FinAddMeasure W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  have hunion := m.additive A (B \ A) disjoint_sdiff_self_right
  rw [Set.union_diff_cancel h] at hunion
  linarith [m.nonneg (B \ A)]

/-- Complement measure: `μ(A) + μ(Aᶜ) = 1`. -/
theorem mu_compl (m : FinAddMeasure W) (A : Set W) :
    m.mu A + m.mu Aᶜ = 1 := by
  have hunion := m.additive A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self] at hunion
  linarith [m.total]

/-- Qualitative additivity for a finitely additive measure: splitting `A` and `B`
    into the shared part `A ∩ B` and the private parts cancels the shared part. -/
theorem mu_qadd (m : FinAddMeasure W) (A B : Set W) :
    m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A) := by
  have hmuA : m.mu A = m.mu (A \ B) + m.mu (A ∩ B) := by
    conv_lhs => rw [(Set.diff_union_inter A B).symm]
    exact m.additive _ _ (Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.2)
  have hmuB : m.mu B = m.mu (B \ A) + m.mu (A ∩ B) := by
    conv_lhs => rw [show B = (B \ A) ∪ (A ∩ B) from by
      rw [Set.inter_comm]; exact (Set.diff_union_inter B A).symm]
    exact m.additive _ _ (Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.1)
  rw [hmuA, hmuB]
  exact add_le_add_iff_right (m.mu (A ∩ B))

/-- Every finitely additive measure satisfies the FA axioms.
    A fortiori from [holliday-icard-2013] Theorem 6 soundness,
    since every finitely additive measure is qualitatively additive. -/
def toSystemFA (m : FinAddMeasure W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := m.inducedGe_axiomR
  mono := m.inducedGe_axiomT
  bottom := by
    show m.mu Set.univ ≥ m.mu ∅
    rw [m.mu_empty]; exact m.nonneg Set.univ
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ)
    rw [m.mu_empty, m.total]; exact not_le.mpr one_pos
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
structure QualAddMeasure (W : Type*) where
  /-- The measure function -/
  mu : Set W → ℚ
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- The impossible proposition has measure zero -/
  mu_empty : mu ∅ = 0
  /-- Normalization -/
  total : mu Set.univ = 1
  /-- Qualitative additivity: μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A) -/
  qualAdd : ∀ A B, mu A ≥ mu B ↔ mu (A \ B) ≥ mu (B \ A)

namespace QualAddMeasure

variable {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : QualAddMeasure W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Monotonicity for qualitatively additive measures:
    A ⊆ B → μ(B) ≥ μ(A). Follows from qualAdd + μ(∅) = 0 + nonneg. -/
theorem inducedGe_axiomT (m : QualAddMeasure W) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  rw [m.qualAdd B A, Set.diff_eq_empty.mpr hAB, m.mu_empty]
  exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces System FA.
    Soundness direction of [holliday-icard-2013] Theorem 6:
    every qualitatively additive measure model satisfies the FA axioms. -/
def toSystemFA (m : QualAddMeasure W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  mono := m.inducedGe_axiomT
  bottom := by
    show m.mu Set.univ ≥ m.mu ∅
    rw [m.mu_empty]; exact m.nonneg Set.univ
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ)
    rw [m.mu_empty, m.total]; exact not_le.mpr one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := m.qualAdd

end QualAddMeasure

/-- Every finitely additive measure is qualitatively additive.
    Proof: μ(A) = μ(A \ B) + μ(A ∩ B) and μ(B) = μ(B \ A) + μ(A ∩ B),
    so μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A). -/
def FinAddMeasure.toQualAdd {W : Type*} (m : FinAddMeasure W) : QualAddMeasure W where
  mu := m.mu
  nonneg := m.nonneg
  mu_empty := m.mu_empty
  total := m.total
  qualAdd := m.mu_qadd

-- ── World-Ordering Semantics ────────────────────

/-- The *l*-lifting: a preorder on worlds induces a comparison on
    propositions. A ≿ B iff for every b ∈ B, ∃ a ∈ A with a ≥_w b.
    [holliday-icard-2013] Definition 6; see also their injection-based
    *m*-lifting (Definition 7), which yields a complete logic for
    world-ordering models. -/
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

-- ── m-Lifting ([holliday-icard-2013] Definition 7) ──

/-- The *m*-lifting ([holliday-icard-2013], Definition 7): an injection-based
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

variable {W : Type*} (m : FinAddMeasure W)

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe := ⟨m.inducedGe_axiomT⟩

instance : IsTrans (Set W) m.inducedGe := ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe := ⟨m.toSystemFA.additive⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe := ⟨m.toSystemFA.nonTrivial⟩

end FinAddMeasure

end Core.Scale
