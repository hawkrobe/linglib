import Linglib.Core.Scales.Scale
import Linglib.Core.Order.ComparativeProbability.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Epistemic Comparative Likelihood

[holliday-icard-2013] [halpern-2003] [van-der-hoek-1996]

Epistemic likelihood scales: the `EpistemicScale` arm of the categorical
diagram in `Core/Scales/Scale.lean`.

[holliday-icard-2013] study the logic of "at least as likely as" (≿) on
propositions, defining a hierarchy of axiom systems (W ⊂ F ⊂ FA) whose
qualitative additivity axiom is the epistemic counterpart of `AdditiveScale.fa`.

**Axiom hierarchy** ([holliday-icard-2013], Figure 3; axioms in Figures 4–6):

| System | Axioms                  | Semantics                          |
|--------|-------------------------|------------------------------------|
| W      | R, T                   | World-ordering + l-lifting         |
| F      | W + Bot, BT            | + bottom, non-triviality           |
| FA     | F + Tot, Tran, A       | Qualitatively additive measures    |
| FP∞    | FA + Scott cancellation | Finitely additive measures         |

**Bridge**: Axiom A (epistemic qualitative additivity) and `AdditiveScale.fa`
(mereological finite additivity) are algebraically equivalent — both express
that a comparison factors through disjoint parts.

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

instance : ComparativeProbability.IsLikelihoodMono sys.ge where
  mono A B h := sys.mono A B h

instance : IsTrans (Set W) sys.ge where
  trans A B C := sys.trans A B C

instance : ComparativeProbability.IsQualitativeAdditive sys.ge where
  qadd A B := sys.additive A B

instance : ComparativeProbability.IsNontrivial sys.ge where
  bot_not_ge_top := sys.nonTrivial

end EpistemicSystemFA

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
  complRev := fun A B hAB => ComparativeProbability.complRev A B hAB

-- ── Measure Semantics ───────────────────────────

/-- A finitely additive probability measure on subsets of W. -/
structure FinAddMeasure (W : Type*) where
  /-- The measure function -/
  mu : Set W → ℚ
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- Finite additivity: μ(A ∪ B) = μ(A) + μ(B) when A ∩ B = ∅ -/
  additive : ∀ A B, (∀ x, x ∈ A → x ∉ B) → mu (A ∪ B) = mu A + mu B
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
  have hdecomp : B = A ∪ (B \ A) := (Set.union_diff_cancel hAB).symm
  have hdisj : ∀ x, x ∈ A → x ∉ B \ A := fun x hx ⟨_, hna⟩ => hna hx
  rw [hdecomp, m.additive A (B \ A) hdisj]
  exact le_add_of_nonneg_right (m.nonneg (B \ A))

/-- μ(∅) = 0 for any finitely additive measure.
    Follows from additivity: μ(∅ ∪ ∅) = μ(∅) + μ(∅), but ∅ ∪ ∅ = ∅. -/
theorem mu_empty (m : FinAddMeasure W) : m.mu ∅ = 0 := by
  have hempty : m.mu (∅ ∪ ∅) = m.mu ∅ + m.mu ∅ :=
    m.additive ∅ ∅ (fun x hx => hx.elim)
  simp only [Set.empty_union] at hempty
  have h : m.mu ∅ + m.mu ∅ = m.mu ∅ + 0 := by rw [add_zero]; exact hempty.symm
  exact add_left_cancel h

/-- Subset monotonicity: `A ⊆ B → μ(A) ≤ μ(B)`. -/
theorem mu_mono (m : FinAddMeasure W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  have hdisj : ∀ x, x ∈ A → x ∉ B \ A := fun x hx ⟨_, hna⟩ => hna hx
  have hunion := m.additive A (B \ A) hdisj
  rw [Set.union_diff_cancel h] at hunion
  linarith [m.nonneg (B \ A)]

/-- Complement measure: `μ(A) + μ(Aᶜ) = 1`. -/
theorem mu_compl (m : FinAddMeasure W) (A : Set W) :
    m.mu A + m.mu Aᶜ = 1 := by
  have hdisj : ∀ x, x ∈ A → x ∉ Aᶜ := fun x hx hxc => hxc hx
  have hunion := m.additive A Aᶜ hdisj
  rw [Set.union_compl_self] at hunion
  linarith [m.total]

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
  additive := by
    intro A B
    show m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A)
    have hdA : ∀ x, x ∈ A \ B → x ∉ A ∩ B := fun x ⟨_, hxnb⟩ ⟨_, hxb⟩ => hxnb hxb
    have hdB : ∀ x, x ∈ B \ A → x ∉ A ∩ B := fun x ⟨_, hxna⟩ ⟨hxa, _⟩ => hxna hxa
    have hmuA : m.mu A = m.mu (A \ B) + m.mu (A ∩ B) := by
      conv_lhs => rw [(Set.diff_union_inter A B).symm]
      exact m.additive _ _ hdA
    have hmuB : m.mu B = m.mu (B \ A) + m.mu (A ∩ B) := by
      conv_lhs => rw [show B = (B \ A) ∪ (A ∩ B) from by
        rw [Set.inter_comm]; exact (Set.diff_union_inter B A).symm]
      exact m.additive _ _ hdB
    rw [hmuA, hmuB]
    exact add_le_add_iff_right (m.mu (A ∩ B))

/-- Extract a world prior from a finitely additive measure by
    evaluating μ on singletons: prior(w) = μ({w}).

    This bridges the epistemic likelihood representation theorem
    to RSA's `worldPrior` field. The resulting function maps each
    world to a non-negative rational, suitable for use as an
    unnormalized prior. -/
noncomputable def toWorldPrior (m : FinAddMeasure W) : W → ℚ :=
  fun w => m.mu {w}

/-- Singleton measures are non-negative. -/
theorem toWorldPrior_nonneg (m : FinAddMeasure W) (w : W) :
    0 ≤ m.toWorldPrior w :=
  m.nonneg {w}

end FinAddMeasure

-- ── Qualitatively Additive Measures ──────────────

/-- A qualitatively additive measure on subsets of W.
    Unlike `FinAddMeasure`, this does NOT require μ(A ∪ B) = μ(A) + μ(B)
    for disjoint A, B. Instead it requires the weaker **qualitative additivity**
    condition: μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A).

    [holliday-icard-2013] Theorem 6: System FA is sound and complete
    with respect to qualitatively additive measure models.

    Note: the paper's definition of qualitatively additive measures includes μ(∅) = 0, but we omit it here
    because the completeness proof (Theorem 6) constructs a measure with
    μ(∅) > 0 (belowCount counts ∅ itself via reflexivity). The soundness
    direction (`toSystemFA`) takes `mu_empty` as an explicit hypothesis. -/
structure QualAddMeasure (W : Type*) where
  /-- The measure function -/
  mu : Set W → ℚ
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- Normalization -/
  total : mu Set.univ = 1
  /-- Qualitative additivity: μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A) -/
  qualAdd : ∀ A B, mu A ≥ mu B ↔ mu (A \ B) ≥ mu (B \ A)

namespace QualAddMeasure

variable {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : QualAddMeasure W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Monotonicity for qualitatively additive measures with μ(∅) = 0:
    A ⊆ B → μ(B) ≥ μ(A). Follows from qualAdd + μ(∅) = 0 + nonneg. -/
theorem inducedGe_axiomT (m : QualAddMeasure W) (h_empty : m.mu ∅ = 0) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  have hAB_diff : A \ B = ∅ := Set.diff_eq_empty.mpr hAB
  rw [m.qualAdd B A]
  rw [hAB_diff, h_empty]
  exact m.nonneg (B \ A)

/-- A qualitatively additive measure with μ(∅) = 0 induces System FA.
    Soundness direction of [holliday-icard-2013] Theorem 6:
    every qualitatively additive measure model (with μ(∅) = 0) satisfies
    the FA axioms.

    The `h_empty` hypothesis is needed for monotonicity and non-triviality;
    it is NOT a field on `QualAddMeasure` because the completeness proof
    constructs a measure where μ(∅) > 0. -/
def toSystemFA (m : QualAddMeasure W) (h_empty : m.mu ∅ = 0) :
    EpistemicSystemFA W where
  ge := m.inducedGe
  refl := fun _ => le_refl _
  mono := m.inducedGe_axiomT h_empty
  bottom := by
    show m.mu Set.univ ≥ m.mu ∅
    rw [h_empty]; exact m.nonneg Set.univ
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ)
    rw [h_empty, m.total]; exact not_le.mpr one_pos
  total := fun A B => le_total (m.mu B) (m.mu A)
  trans := fun _ _ _ hab hbc => le_trans hbc hab
  additive := by
    intro A B; show m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A)
    exact m.qualAdd A B

end QualAddMeasure

/-- Every finitely additive measure is qualitatively additive.
    Proof: μ(A) = μ(A \ B) + μ(A ∩ B) and μ(B) = μ(B \ A) + μ(A ∩ B),
    so μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A). -/
noncomputable def FinAddMeasure.toQualAdd {W : Type*} (m : FinAddMeasure W) : QualAddMeasure W where
  mu := m.mu
  nonneg := m.nonneg
  total := m.total
  qualAdd := fun A B => by
    have hdA : ∀ x, x ∈ A \ B → x ∉ A ∩ B :=
      fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ => hxnB hxB
    have hdB : ∀ x, x ∈ B \ A → x ∉ A ∩ B :=
      fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ => hxnA hxA
    have hmuA : m.mu A = m.mu (A \ B) + m.mu (A ∩ B) := by
      conv_lhs => rw [show A = (A \ B) ∪ (A ∩ B) from (Set.diff_union_inter A B).symm]
      exact m.additive _ _ hdA
    have hmuB : m.mu B = m.mu (B \ A) + m.mu (A ∩ B) := by
      conv_lhs => rw [show B = (B \ A) ∪ (A ∩ B) from by
        rw [Set.inter_comm]; exact (Set.diff_union_inter B A).symm]
      exact m.additive _ _ hdB
    rw [hmuA, hmuB]
    exact add_le_add_iff_right (m.mu (A ∩ B))

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

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe where
  mono a b h := m.inducedGe_axiomT a b h

instance : IsTrans (Set W) m.inducedGe where
  trans _ _ _ hab hbc := le_trans hbc hab

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe where
  qadd a b := m.toSystemFA.additive a b

instance : ComparativeProbability.IsNontrivial m.inducedGe where
  bot_not_ge_top := m.toSystemFA.nonTrivial

end FinAddMeasure

end Core.Scale
