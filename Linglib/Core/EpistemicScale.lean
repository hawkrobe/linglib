import Linglib.Core.Scale

/-!
# Epistemic Comparative Likelihood (Holliday & Icard 2013)

@cite{holliday-icard-2013}

Epistemic likelihood scales: the `EpistemicScale` arm of the categorical
diagram in `Core/Scale.lean`. Extracted here because this domain-specific
theory has a single downstream consumer (`Comparisons/KratzerEpistemicRSA.lean`).

Holliday & Icard (2013) study the logic of "at least as likely as" (≿) on
propositions, defining a hierarchy of axiom systems (W ⊂ F ⊂ FA) whose
qualitative additivity axiom is the epistemic counterpart of `AdditiveScale.fa`.

**Axiom hierarchy** (Table 1):

| System | Axioms         | Semantics                          |
|--------|----------------|------------------------------------|
| W      | R, T           | World-ordering + Halpern lift      |
| F      | R, T, F        | + bottom element                   |
| FA     | R, T, F, A     | Qualitatively additive measures    |
| FP∞    | R, T, F, A, Sc | Finitely additive measures         |

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

-- ── Axioms (Table 1) ────────────────────────────

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

/-- Axiom S: supplementation — A ≿ B → Bᶜ ≿ Aᶜ. -/
def S {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, ge A B → ge Bᶜ Aᶜ

/-- Axiom A: qualitative additivity — A ≿ B ↔ (A \ B) ≿ (B \ A).
    The comparative likelihood factors through disjoint parts. -/
def A {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, ge A B ↔ ge (A \ B) (B \ A)

/-- Axiom J: join — A ≿ C ∧ B ≿ C ∧ A ∩ B = ∅ → A ∪ B ≿ C. -/
def J {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B C, ge A C → ge B C → (∀ x, x ∈ A → x ∉ B) → ge (A ∪ B) C

end EpistemicAxiom

-- ── Logic Hierarchy ─────────────────────────────

/-- System W: the weakest epistemic likelihood logic.
    Reflexivity + monotonicity (Holliday & Icard 2013, Table 1). -/
structure EpistemicSystemW (W : Type*) where
  ge : Set W → Set W → Prop
  refl : EpistemicAxiom.R ge
  mono : EpistemicAxiom.T ge

/-- System F: System W + Ω ≿ ∅. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  bottom : EpistemicAxiom.F ge

/-- System FA: System F + totality + transitivity + qualitative additivity.
    Sound and complete for **qualitatively additive** measure semantics
    (Holliday & Icard 2013, Theorem 6; van der Hoek 1996).
    Strictly weaker than FP∞ (finitely additive measures) for |W| ≥ 5
    (Kraft, Pratt & Seidenberg 1959, Theorem 8).

    Totality and transitivity are part of the FA logic in Holliday & Icard
    (2013, Figure 6): FA = Bot + BT + Tot + Tran + A. -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemF W where
  total : ∀ A B : Set W, ge A B ∨ ge B A
  trans : ∀ A B C : Set W, ge A B → ge B C → ge A C
  additive : EpistemicAxiom.A ge

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

/-- A finitely additive measure induces System FA.
    This is the soundness direction of **Theorem 6** (Holliday & Icard
    2013; van der Hoek 1996). -/
def toSystemFA (m : FinAddMeasure W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := m.inducedGe_axiomR
  mono := m.inducedGe_axiomT
  bottom := by
    show m.mu Set.univ ≥ m.mu ∅
    have hempty : m.mu (∅ ∪ ∅) = m.mu ∅ + m.mu ∅ :=
      m.additive ∅ ∅ (fun x hx => hx.elim)
    simp only [Set.empty_union] at hempty
    have hzero : m.mu ∅ = 0 := by
      have h : m.mu ∅ + m.mu ∅ = m.mu ∅ + 0 := by rw [add_zero]; exact hempty.symm
      exact add_left_cancel h
    rw [hzero]; exact m.nonneg Set.univ
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

    Holliday & Icard (2013) Theorem 6: System FA is sound and complete
    with respect to qualitatively additive measure models. -/
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

/-- Lewis's *l*-lifting: a preorder on worlds induces a comparison on
    propositions. A ≿ B iff for every b ∈ B, ∃ a ∈ A with a ≥_w b.
    Holliday & Icard (2013) §3; see also their injection-based *m*-lifting
    (Theorem 7), which yields a complete logic for world-ordering models. -/
def halpernLift {W : Type*} (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b

/-- Halpern lift from a reflexive relation satisfies Axiom R. -/
theorem halpernLift_axiomR {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.R (halpernLift ge_w) :=
  fun _ b hb => ⟨b, hb, hRefl b⟩

/-- Halpern lift from a reflexive relation satisfies Axiom T.
    If A ⊆ B and b ∈ A, then b ∈ B, so take a = b. -/
theorem halpernLift_axiomT {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.T (halpernLift ge_w) :=
  fun _ _ hAB b hbA => ⟨b, hAB hbA, hRefl b⟩

/-- Lewis's *l*-lifting from a reflexive preorder yields System W.
    Soundness direction: world-ordering models with the l-lifting
    validate System W (Halpern 2003; Holliday & Icard 2013 §3). -/
def halpernSystemW {W : Type*} (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    EpistemicSystemW W where
  ge := halpernLift ge_w
  refl := halpernLift_axiomR hRefl
  mono := halpernLift_axiomT hRefl

-- ── Theorem 8 (Kraft, Pratt & Seidenberg 1959) ───

/-- **Theorem 8a** (Kraft, Pratt & Seidenberg 1959): for |W| < 5,
    every FA model is representable by a finitely additive probability
    measure. Below 5 worlds, the logics FA and FP∞ coincide. -/
theorem theorem8a {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (hcard : Fintype.card W < 5) :
    ∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  sorry -- Kraft, Pratt & Seidenberg (1959); finite linear programming

/-- **Theorem 8b** (Kraft, Pratt & Seidenberg 1959): for |W| ≥ 5,
    FA is strictly weaker than FP∞ — there exists a 5-element type
    with an FA ordering admitting no finitely additive measure
    representation. The FP∞ axioms (Scott schemata) are strictly
    stronger than qualitative additivity alone. -/
theorem theorem8b :
    ∃ (W : Type) (_ : Fintype W) (sys : EpistemicSystemFA W),
      Fintype.card W = 5 ∧
      ¬∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  sorry -- Kraft, Pratt & Seidenberg (1959); 5-world counterexample

-- ── Completeness (Theorems 6–7) ──────────────────

/-- **Theorem 6 completeness** (Holliday & Icard 2013, Theorem 6; van der Hoek 1996):
    every EpistemicSystemFA is representable by a **qualitatively additive** measure.
    Combined with `toSystemFA` (soundness), this gives FA ↔ QualAddMeasure.

    Note: this is NOT about finitely additive measures (`FinAddMeasure`).
    FA is strictly weaker than FP∞ for |W| ≥ 5 (Theorem 8, KPS 1959):
    there exist FA orderings with no finitely additive measure representation.
    See `theorem8b`. -/
theorem theorem6_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    ∃ (m : QualAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  sorry -- van der Hoek (1996); linear extension of qualitative probability

/-- **Theorem 2 completeness** (Halpern 2003; Holliday & Icard 2013 §3):
    every system satisfying R, T, BT, Tran, J, Mon (System WJR) is
    representable by Lewis's l-lifting from a reflexive preorder on worlds.

    Note: the current hypothesis asks only for `EpistemicSystemW` (R + T),
    which is weaker than WJR. The full completeness result requires
    additional axioms (join, transitivity, monotonicity). This is left
    as `sorry` pending the formalization of System WJR.

    (The paper's Theorem 7 is about the *m*-lifting, not the l-lifting.) -/
theorem theorem7_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemW W) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w),
      ∀ A B, sys.ge A B ↔ halpernLift ge_w A B :=
  sorry -- Halpern (2003); requires WJR axioms for completeness

-- ── Bridge: Axiom A ↔ FA ────────────────────────

/-- **Algebraic bridge**: Axiom A and the finite additivity property
    of `AdditiveScale` are equivalent for any comparison on sets.
    - FA: ge A B ↔ ge (A ∪ C) (B ∪ C) when C disjoint from A and B
    - Axiom A: ge A B ↔ ge (A \ B) (B \ A)
    Proof sketch:
    - A → FA: (A∪C)\(B∪C) = A\B when A∩C = ∅; apply A twice.
    - FA → A: take C = A ∩ B; (A\B)∪(A∩B) = A; apply FA. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    EpistemicAxiom.A ge ↔
    (∀ A B C : Set W, (∀ x, x ∈ A → x ∉ C) → (∀ x, x ∈ B → x ∉ C) →
      (ge A B ↔ ge (A ∪ C) (B ∪ C))) := by
  constructor
  · -- A → FA
    intro hA A B C hAC hBC
    -- Axiom A on both sides reduces to the same diffs
    have h1 := hA A B
    have h2 := hA (A ∪ C) (B ∪ C)
    -- (A ∪ C) \ (B ∪ C) = A \ B when A ∩ C = ∅
    have hd1 : (A ∪ C) \ (B ∪ C) = A \ B := by
      ext x; simp only [Set.mem_diff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hnx⟩
        · exact ⟨hx, fun hb => hnx (Or.inl hb)⟩
        · exact absurd (Or.inr hx) hnx
      · rintro ⟨hxA, hxnB⟩
        exact ⟨Or.inl hxA, fun h => h.elim hxnB (hAC x hxA)⟩
    -- (B ∪ C) \ (A ∪ C) = B \ A when B ∩ C = ∅
    have hd2 : (B ∪ C) \ (A ∪ C) = B \ A := by
      ext x; simp only [Set.mem_diff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hnx⟩
        · exact ⟨hx, fun ha => hnx (Or.inl ha)⟩
        · exact absurd (Or.inr hx) hnx
      · rintro ⟨hxB, hxnA⟩
        exact ⟨Or.inl hxB, fun h => h.elim hxnA (hBC x hxB)⟩
    rw [hd1, hd2] at h2
    exact h1.trans h2.symm
  · -- FA → A: take C = A ∩ B
    intro hFA A B
    have hdA : ∀ x, x ∈ A \ B → x ∉ A ∩ B :=
      fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ => hxnB hxB
    have hdB : ∀ x, x ∈ B \ A → x ∉ A ∩ B :=
      fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ => hxnA hxA
    have hA_eq : (A \ B) ∪ (A ∩ B) = A := Set.diff_union_inter A B
    have hB_eq : (B \ A) ∪ (A ∩ B) = B := by
      rw [Set.inter_comm]; exact Set.diff_union_inter B A
    have h := hFA (A \ B) (B \ A) (A ∩ B) hdA hdB
    rw [hA_eq, hB_eq] at h
    exact h.symm

-- ── EpistemicTag + Five Frameworks ──────────────

/-- Binary epistemic classification, parallel to `MereoTag`.
    - `finitelyAdditive`: probability-representable (System FA), closed
    - `qualitative`: general comparative (System W only), open -/
inductive EpistemicTag where
  | finitelyAdditive  -- FA: closed, probability-representable
  | qualitative       -- W: no guaranteed bounds, open
  deriving DecidableEq, BEq, Repr

instance : LicensingPipeline EpistemicTag where
  toBoundedness
    | .finitelyAdditive => .closed
    | .qualitative => .open_

/-- FA epistemic scales are licensed (closed → admits optimum). -/
theorem epistemicFA_licensed :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive = true := rfl

/-- Qualitative epistemic scales are blocked (open → no optimum). -/
theorem epistemicQualitative_blocked :
    LicensingPipeline.isLicensed EpistemicTag.qualitative = false := rfl

/-- **Five frameworks agree on licensing**: Kennedy (adjective degree
    boundedness), Rouillard (temporal MIP), Krifka (mereological QUA/CUM),
    Zwarts (path shape), and Holliday–Icard (epistemic likelihood) all
    route through `Boundedness.isLicensed` via `LicensingPipeline`.

    This extends `four_frameworks_agree` with the epistemic arm:
    epistemic FA ↔ mereological QUA ↔ closed → licensed;
    epistemic qualitative ↔ mereological CUM ↔ open → blocked. -/
theorem five_frameworks_agree
    (m : MereoTag) (e : EpistemicTag)
    (h : LicensingPipeline.toBoundedness m = LicensingPipeline.toBoundedness e) :
    LicensingPipeline.isLicensed m = LicensingPipeline.isLicensed e :=
  LicensingPipeline.universal m e h

/-- Epistemic FA agrees with mereological QUA. -/
theorem epistemicFA_eq_qua :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive =
    LicensingPipeline.isLicensed MereoTag.qua := rfl

/-- Epistemic qualitative agrees with mereological CUM. -/
theorem epistemicQualitative_eq_cum :
    LicensingPipeline.isLicensed EpistemicTag.qualitative =
    LicensingPipeline.isLicensed MereoTag.cum := rfl

end Core.Scale
