import Linglib.Core.Scales.Scale
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

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

/-- Axiom BT: ¬(∅ ≿ Ω) — contradiction is NOT at least as likely as tautology.
    The non-triviality condition from Holliday & Icard (2013, Figure 6).
    Without this, the degenerate ordering (all sets equivalent) would satisfy
    FA but admit no finitely additive measure representation (since μ(∅) = 0
    but μ(Ω) = 1). -/
def BT {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ¬ge ∅ Set.univ

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

/-- System F: System W + Bot + BT.
    Bot (Ω ≿ ∅) is redundant with monotonicity. BT (¬(∅ ≿ Ω)) is the
    non-triviality condition that excludes degenerate orderings. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  bottom : EpistemicAxiom.F ge
  nonTrivial : EpistemicAxiom.BT ge

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
  nonTrivial := by
    show ¬(m.mu ∅ ≥ m.mu Set.univ)
    have hempty : m.mu (∅ ∪ ∅) = m.mu ∅ + m.mu ∅ :=
      m.additive ∅ ∅ (fun x hx => hx.elim)
    simp only [Set.empty_union] at hempty
    have hzero : m.mu ∅ = 0 := by
      have h : m.mu ∅ + m.mu ∅ = m.mu ∅ + 0 := by rw [add_zero]; exact hempty.symm
      exact add_left_cancel h
    rw [hzero, m.total]; exact not_le.mpr one_pos
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

-- ── KPS Counterexample Infrastructure ──────────────

/-- Convert a Finset (Fin 5) to a bitmask index. -/
private def finsetIdx (s : Finset (Fin 5)) : ℕ :=
  s.sum (λ i => 2 ^ i.val)

/-- The KPS rank table: maps bitmask index to rank (0–31).
    Ordering from Kraft, Pratt & Seidenberg (1959), Section 4.
    Elements: p=0, q=1, r=2, s=3, t=4.
    ∅ < q < r < s < qr < qs < p < pq < rs < t < qrs < rp < ps < tq < qrp < rt
    and complements in reverse (by supplementation, from axiom A). -/
private def kpsRankNat (idx : ℕ) : ℕ :=
  match idx with
  |  0 =>  0 |  1 =>  6 |  2 =>  1 |  3 =>  7
  |  4 =>  2 |  5 => 11 |  6 =>  4 |  7 => 14
  |  8 =>  3 |  9 => 12 | 10 =>  5 | 11 => 16
  | 12 =>  8 | 13 => 18 | 14 => 10 | 15 => 22
  | 16 =>  9 | 17 => 21 | 18 => 13 | 19 => 23
  | 20 => 15 | 21 => 26 | 22 => 19 | 23 => 28
  | 24 => 17 | 25 => 27 | 26 => 20 | 27 => 29
  | 28 => 24 | 29 => 30 | 30 => 25 | 31 => 31
  |  _ =>  0

/-- KPS rank of a finset. -/
private def kpsRank (s : Finset (Fin 5)) : ℕ :=
  kpsRankNat (finsetIdx s)

private theorem kps_mono_finset :
    ∀ (a b : Finset (Fin 5)), a ⊆ b → kpsRank b ≥ kpsRank a := by
  native_decide

private theorem kps_additive_finset :
    ∀ (a b : Finset (Fin 5)),
      (kpsRank a ≥ kpsRank b) ↔ (kpsRank (a \ b) ≥ kpsRank (b \ a)) := by
  native_decide

private theorem kps_bottom_finset :
    kpsRank Finset.univ ≥ kpsRank ∅ := by native_decide

section KPSSystem

attribute [local instance] Classical.propDecidable

private noncomputable def toFS (A : Set (Fin 5)) : Finset (Fin 5) :=
  Finset.univ.filter (λ x => x ∈ A)

private theorem toFS_mem (A : Set (Fin 5)) (x : Fin 5) :
    x ∈ toFS A ↔ x ∈ A := by
  simp only [toFS, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem toFS_univ : toFS (Set.univ : Set (Fin 5)) = Finset.univ := by
  ext x; simp only [toFS_mem, Set.mem_univ, Finset.mem_univ]

private theorem toFS_empty : toFS (∅ : Set (Fin 5)) = ∅ := by
  ext x; simp [toFS_mem]

private theorem toFS_diff (A B : Set (Fin 5)) :
    toFS (A \ B) = toFS A \ toFS B := by
  ext x; simp only [toFS_mem, Set.mem_diff, Finset.mem_sdiff]

private theorem toFS_subset (A B : Set (Fin 5)) :
    A ⊆ B ↔ toFS A ⊆ toFS B := by
  constructor
  · intro h x hx; rw [toFS_mem] at hx ⊢; exact h hx
  · intro h x hx; exact (toFS_mem B x).mp (h ((toFS_mem A x).mpr hx))

private noncomputable def kpsRankSet (A : Set (Fin 5)) : ℕ := kpsRank (toFS A)
private noncomputable def kpsGe (A B : Set (Fin 5)) : Prop := kpsRankSet A ≥ kpsRankSet B

private noncomputable def kpsSystemFA : EpistemicSystemFA (Fin 5) where
  ge := kpsGe
  refl := λ A => le_refl (kpsRankSet A)
  mono := λ {A B} hAB => kps_mono_finset _ _ ((toFS_subset A B).mp hAB)
  bottom := by
    simp only [EpistemicAxiom.F, kpsGe, kpsRankSet, toFS_univ, toFS_empty]
    exact kps_bottom_finset
  nonTrivial := by
    simp only [EpistemicAxiom.BT, kpsGe, kpsRankSet, toFS_univ, toFS_empty]
    native_decide
  total := λ A B => le_total (kpsRankSet B) (kpsRankSet A)
  trans := λ {_ _ _} hab hbc => le_trans hbc hab
  additive := by
    intro A B
    show kpsRank (toFS A) ≥ kpsRank (toFS B) ↔
         kpsRank (toFS (A \ B)) ≥ kpsRank (toFS (B \ A))
    rw [toFS_diff, toFS_diff]
    exact kps_additive_finset (toFS A) (toFS B)

private theorem mu_pair (m : FinAddMeasure (Fin 5)) (a b : Fin 5) (hab : a ≠ b) :
    m.mu ({a, b} : Set (Fin 5)) = m.mu {a} + m.mu {b} := by
  have hunion : ({a, b} : Set (Fin 5)) = {a} ∪ {b} := Set.insert_eq a {b}
  rw [hunion, m.additive {a} {b} (λ x hx hxb => by
    rw [Set.mem_singleton_iff] at hx hxb; exact hab (hx ▸ hxb))]

private theorem mu_triple (m : FinAddMeasure (Fin 5)) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    m.mu ({a, b, c} : Set (Fin 5)) = m.mu {a} + m.mu {b} + m.mu {c} := by
  have hunion : ({a, b, c} : Set (Fin 5)) = {a} ∪ ({b, c} : Set (Fin 5)) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [hunion, m.additive {a} {b, c} (λ x hx hxbc => by
    rw [Set.mem_singleton_iff] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxbc
    subst hx; rcases hxbc with rfl | rfl
    · exact absurd rfl hab
    · exact absurd rfl hac)]
  rw [mu_pair m b c hbc, add_assoc]

private theorem kps_not_representable :
    ¬∃ (m : FinAddMeasure (Fin 5)), ∀ A B, kpsSystemFA.ge A B ↔ m.inducedGe A B := by
  intro ⟨m, hm⟩
  set P := m.mu ({(0 : Fin 5)} : Set (Fin 5))
  set Q := m.mu ({(1 : Fin 5)} : Set (Fin 5))
  set R := m.mu ({(2 : Fin 5)} : Set (Fin 5))
  set S := m.mu ({(3 : Fin 5)} : Set (Fin 5))
  set T := m.mu ({(4 : Fin 5)} : Set (Fin 5))
  -- Ordering facts: three strict (rank <), one weak (rank ≥)
  have hord1 : ¬ kpsGe ({1, 3} : Set (Fin 5)) {0} := by
    unfold kpsGe kpsRankSet
    have h1 : toFS ({1, 3} : Set (Fin 5)) = {1, 3} := by ext x; simp [toFS_mem]
    have h2 : toFS ({(0 : Fin 5)} : Set (Fin 5)) = {0} := by ext x; simp [toFS_mem]
    rw [h1, h2]; native_decide
  have hord2 : ¬ kpsGe ({0, 1} : Set (Fin 5)) {2, 3} := by
    unfold kpsGe kpsRankSet
    have h1 : toFS ({0, 1} : Set (Fin 5)) = {0, 1} := by ext x; simp [toFS_mem]
    have h2 : toFS ({2, 3} : Set (Fin 5)) = {2, 3} := by ext x; simp [toFS_mem]
    rw [h1, h2]; native_decide
  have hord3 : ¬ kpsGe ({0, 3} : Set (Fin 5)) {1, 4} := by
    unfold kpsGe kpsRankSet
    have h1 : toFS ({0, 3} : Set (Fin 5)) = {0, 3} := by ext x; simp [toFS_mem]
    have h2 : toFS ({1, 4} : Set (Fin 5)) = {1, 4} := by ext x; simp [toFS_mem]
    rw [h1, h2]; native_decide
  have hord4 : kpsGe ({0, 1, 3} : Set (Fin 5)) {2, 4} := by
    unfold kpsGe kpsRankSet
    have h1 : toFS ({0, 1, 3} : Set (Fin 5)) = {0, 1, 3} := by ext x; simp [toFS_mem]
    have h2 : toFS ({2, 4} : Set (Fin 5)) = {2, 4} := by ext x; simp [toFS_mem]
    rw [h1, h2]; native_decide
  -- Convert to measure inequalities via the representation isomorphism
  have hmeas1 : m.mu ({1, 3} : Set _) < m.mu ({(0 : Fin 5)} : Set _) :=
    not_le.mp (λ h => hord1 ((hm _ _).mpr h))
  have hmeas2 : m.mu ({0, 1} : Set _) < m.mu ({2, 3} : Set _) :=
    not_le.mp (λ h => hord2 ((hm _ _).mpr h))
  have hmeas3 : m.mu ({0, 3} : Set _) < m.mu ({1, 4} : Set _) :=
    not_le.mp (λ h => hord3 ((hm _ _).mpr h))
  have hmeas4 : m.mu ({0, 1, 3} : Set _) ≥ m.mu ({2, 4} : Set _) :=
    (hm _ _).mp hord4
  -- Decompose pairs/triples using finite additivity
  rw [mu_pair m 1 3 (by decide)] at hmeas1
  rw [mu_pair m 0 1 (by decide), mu_pair m 2 3 (by decide)] at hmeas2
  rw [mu_pair m 0 3 (by decide), mu_pair m 1 4 (by decide)] at hmeas3
  rw [mu_triple m 0 1 3 (by decide) (by decide) (by decide),
      mu_pair m 2 4 (by decide)] at hmeas4
  -- hmeas1: Q + S < P      hmeas2: P + Q < R + S
  -- hmeas3: P + S < Q + T   hmeas4: P + Q + S ≥ R + T
  -- Summing the three strict inequalities (Scott cancellation):
  --   (Q+S) + (P+Q) + (P+S) < P + (R+S) + (Q+T)
  --   P + Q + S < R + T
  -- contradicts hmeas4.
  linarith

end KPSSystem


-- ── Theorem 8a: Per-cardinality proofs ──────────

attribute [local instance] Classical.propDecidable

-- ── Reduction Lemma ────────────────────────────────

private theorem measure_axiomA {W : Type*} (m : FinAddMeasure W) (A B : Set W) :
    m.inducedGe A B ↔ m.inducedGe (A \ B) (B \ A) := by
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

private theorem reduce_to_disjoint {W : Type*} (sys : EpistemicSystemFA W)
    (m : FinAddMeasure W)
    (h : ∀ C D : Set W, (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ m.inducedGe C D)) :
    ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  intro A B
  rw [sys.additive A B, measure_axiomA m A B]
  exact h _ _ (fun x ⟨_, hxnB⟩ ⟨_, hxnA⟩ => hxnA (by assumption))

-- ── Card 0: impossible ─────────────────────────────

private theorem no_fa_empty (sys : EpistemicSystemFA (Fin 0)) : False := by
  have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
  exact sys.nonTrivial (this ▸ sys.refl ∅)

-- ── Card 1 ─────────────────────────────────────────

private theorem set_fin1_eq (A : Set (Fin 1)) : A = ∅ ∨ A = Set.univ := by
  by_cases h : (0 : Fin 1) ∈ A
  · right; ext x; simp [Fin.eq_zero x, h]
  · left; ext x; constructor
    · intro hx; rw [Fin.eq_zero x] at hx; exact absurd hx h
    · intro hx; exact hx.elim

private noncomputable def measure_fin1 : FinAddMeasure (Fin 1) where
  mu := fun A => if (0 : Fin 1) ∈ A then 1 else 0
  nonneg := fun A => by split <;> norm_num
  additive := fun A B hdisj => by
    by_cases h0A : (0 : Fin 1) ∈ A <;> by_cases h0B : (0 : Fin 1) ∈ B
    · exact absurd h0B (hdisj 0 h0A)
    · simp [Set.mem_union, h0A, h0B]
    · simp [Set.mem_union, h0A, h0B]
    · have : (0 : Fin 1) ∉ A ∪ B := fun h => h.elim h0A h0B
      simp [h0A, h0B, this]
  total := by simp [Set.mem_univ]

private theorem theorem8a_fin1 (sys : EpistemicSystemFA (Fin 1)) :
    ∃ (m : FinAddMeasure (Fin 1)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  refine ⟨measure_fin1, fun A B => ?_⟩
  rcases set_fin1_eq A with rfl | rfl <;> rcases set_fin1_eq B with rfl | rfl
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  · exact ⟨fun h => absurd h sys.nonTrivial,
          fun h => by simp [FinAddMeasure.inducedGe, measure_fin1, Set.mem_univ] at h; linarith⟩
  · exact ⟨fun _ => by simp [FinAddMeasure.inducedGe, measure_fin1, Set.mem_univ],
          fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩

-- ── Card 2: Infrastructure ──────────────────────────

private noncomputable def measure_fin2 (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    FinAddMeasure (Fin 2) where
  mu := fun A =>
    (if (0 : Fin 2) ∈ A then a else 0) + (if (1 : Fin 2) ∈ A then 1 - a else 0)
  nonneg := fun A => add_nonneg (by split <;> [exact ha; exact le_refl _])
    (by split <;> [linarith; exact le_refl _])
  additive := fun A B hdisj => by
    simp only [Set.mem_union]
    by_cases h0A : (0 : Fin 2) ∈ A <;> by_cases h0B : (0 : Fin 2) ∈ B <;>
    by_cases h1A : (1 : Fin 2) ∈ A <;> by_cases h1B : (1 : Fin 2) ∈ B <;>
    simp_all <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; linarith

private theorem measure_fin2_mu (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (A : Set (Fin 2)) :
    (measure_fin2 a ha ha1).mu A =
    (if (0 : Fin 2) ∈ A then a else 0) + (if (1 : Fin 2) ∈ A then 1 - a else 0) := rfl

private theorem mf2_empty (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu ∅ = 0 := by
  rw [measure_fin2_mu]; simp

private theorem mf2_zero (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu {(0 : Fin 2)} = a := by
  rw [measure_fin2_mu]
  have h0 : (0 : Fin 2) ∈ ({(0 : Fin 2)} : Set _) := rfl
  have h1 : (1 : Fin 2) ∉ ({(0 : Fin 2)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_pos h0, if_neg h1]; linarith

private theorem mf2_one (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu {(1 : Fin 2)} = 1 - a := by
  rw [measure_fin2_mu]
  have h0 : (0 : Fin 2) ∉ ({(1 : Fin 2)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 2) ∈ ({(1 : Fin 2)} : Set _) := rfl
  rw [if_neg h0, if_pos h1]; linarith

private theorem mf2_univ (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (measure_fin2 a ha ha1).mu (Set.univ : Set (Fin 2)) = 1 := by
  rw [measure_fin2_mu]; simp only [Set.mem_univ, ite_true]; linarith

private theorem set_fin2_eq (A : Set (Fin 2)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := by
  by_cases h0 : (0 : Fin 2) ∈ A <;> by_cases h1 : (1 : Fin 2) ∈ A
  · right; right; right; ext x; fin_cases x <;> simp_all
  · right; left; ext x; fin_cases x <;> simp_all
  · right; right; left; ext x; fin_cases x <;> simp_all
  · left; ext x; fin_cases x <;> simp_all

private theorem not_both_null_fin2 (sys : EpistemicSystemFA (Fin 2)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1}) := by
  intro ⟨h0, h1⟩
  have hd1 : ({(0 : Fin 2)} : Set _) \ Set.univ = ∅ := by ext x; simp
  have hd2 : Set.univ \ ({(0 : Fin 2)} : Set _) = {(1 : Fin 2)} := by
    ext x; simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, Fin.ext_iff]
    omega
  exact sys.nonTrivial (sys.trans _ _ _ h0
    ((sys.additive {0} Set.univ).mpr (hd1 ▸ hd2 ▸ h1)))

-- ── Card 2: Helper for disjoint-pair dispatch ────────

/-- Given measure values and ordering facts, close all 16 disjoint-pair cases on Fin 2.
    The 7 non-disjoint pairs close by exfalso.
    The 5 uniform pairs (∅/∅, X/∅, ∅/univ) are independent of the ordering.
    The 4 critical pairs (∅/{0}, ∅/{1}, {0}/{1}, {1}/{0}) use the hypotheses. -/
private theorem fin2_dispatch (sys : EpistemicSystemFA (Fin 2))
    (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hme : (measure_fin2 a ha ha1).mu ∅ = 0)
    (hm0 : (measure_fin2 a ha ha1).mu {(0 : Fin 2)} = a)
    (hm1 : (measure_fin2 a ha ha1).mu {(1 : Fin 2)} = 1 - a)
    (hmu : (measure_fin2 a ha ha1).mu (Set.univ : Set (Fin 2)) = 1)
    -- Ordering hypotheses matching measure values
    (he0 : sys.ge ∅ {(0 : Fin 2)} ↔ a ≤ 0)
    (he1 : sys.ge ∅ {(1 : Fin 2)} ↔ 1 - a ≤ 0)
    (h01 : sys.ge {(0 : Fin 2)} {1} ↔ a ≥ 1 - a)
    (h10 : sys.ge {(1 : Fin 2)} {0} ↔ 1 - a ≥ a)
    :
    ∀ C D : Set (Fin 2), (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ (measure_fin2 a ha ha1).inducedGe C D) := by
  intro C D hdisj
  rcases set_fin2_eq C with rfl | rfl | rfl | rfl <;>
  rcases set_fin2_eq D with rfl | rfl | rfl | rfl
  -- ∅ vs ∅
  · exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
  -- ∅ vs {0}
  · show sys.ge ∅ {0} ↔ _ ≥ _; rw [hme, hm0]; exact ⟨fun h => he0.mp h, fun h => he0.mpr h⟩
  -- ∅ vs {1}
  · show sys.ge ∅ {1} ↔ _ ≥ _; rw [hme, hm1]
    exact ⟨fun h => by linarith [he1.mp h], fun h => he1.mpr (by linarith)⟩
  -- ∅ vs univ
  · show sys.ge ∅ Set.univ ↔ _ ≥ _; rw [hme, hmu]
    exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
  -- {0} vs ∅
  · show sys.ge {0} ∅ ↔ _ ≥ _; rw [hm0, hme]
    exact ⟨fun _ => ha, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- {0} vs {0}: not disjoint
  · exfalso; exact hdisj 0 rfl rfl
  -- {0} vs {1}
  · show sys.ge {0} {1} ↔ _ ≥ _; rw [hm0, hm1]
    exact ⟨fun h => h01.mp h, fun h => h01.mpr h⟩
  -- {0} vs univ: not disjoint
  · exfalso; exact hdisj 0 rfl (Set.mem_univ _)
  -- {1} vs ∅
  · show sys.ge {1} ∅ ↔ _ ≥ _; rw [hm1, hme]
    exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- {1} vs {0}
  · show sys.ge {1} {0} ↔ _ ≥ _; rw [hm1, hm0]
    exact ⟨fun h => h10.mp h, fun h => h10.mpr h⟩
  -- {1} vs {1}: not disjoint
  · exfalso; exact hdisj 1 rfl rfl
  -- {1} vs univ: not disjoint
  · exfalso; exact hdisj 1 rfl (Set.mem_univ _)
  -- univ vs ∅
  · show sys.ge Set.univ ∅ ↔ _ ≥ _; rw [hmu, hme]
    exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
  -- univ vs {0}: not disjoint
  · exfalso; exact hdisj 0 (Set.mem_univ _) rfl
  -- univ vs {1}: not disjoint
  · exfalso; exact hdisj 1 (Set.mem_univ _) rfl
  -- univ vs univ: not disjoint
  · exfalso; exact hdisj 0 (Set.mem_univ _) (Set.mem_univ _)

-- ── Card 2: Main theorem ───────────────────────────

private theorem theorem8a_fin2 (sys : EpistemicSystemFA (Fin 2)) :
    ∃ (m : FinAddMeasure (Fin 2)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  by_cases h_null0 : sys.ge ∅ {(0 : Fin 2)}
  · -- Case 1: ge ∅ {0} → a = 0
    have h_nnull1 : ¬sys.ge ∅ {(1 : Fin 2)} := fun h => not_both_null_fin2 sys ⟨h_null0, h⟩
    have h_nge01 : ¬sys.ge {(0 : Fin 2)} {1} :=
      fun h => not_both_null_fin2 sys ⟨h_null0, sys.trans _ _ _ h_null0 h⟩
    have h_ge10 : sys.ge {(1 : Fin 2)} {0} :=
      (sys.total {(1 : Fin 2)} {0}).resolve_right h_nge01
    refine ⟨measure_fin2 0 le_rfl zero_le_one,
      reduce_to_disjoint sys _ (fin2_dispatch sys 0 le_rfl zero_le_one
        (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
        ⟨fun _ => le_refl _, fun _ => h_null0⟩
        ⟨fun h => absurd h h_nnull1, fun h => by linarith⟩
        ⟨fun h => absurd h h_nge01, fun h => by linarith⟩
        ⟨fun _ => by linarith, fun _ => h_ge10⟩)⟩
  · by_cases h_null1 : sys.ge ∅ {(1 : Fin 2)}
    · -- Case 2: ge ∅ {1} → a = 1
      have h_nge10 : ¬sys.ge {(1 : Fin 2)} {0} :=
        fun h => not_both_null_fin2 sys ⟨sys.trans _ _ _ h_null1 h, h_null1⟩
      have h_ge01 : sys.ge {(0 : Fin 2)} {1} :=
        (sys.total {(0 : Fin 2)} {1}).resolve_right h_nge10
      refine ⟨measure_fin2 1 zero_le_one le_rfl,
        reduce_to_disjoint sys _ (fin2_dispatch sys 1 zero_le_one le_rfl
          (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
          ⟨fun h => absurd h h_null0, fun h => by linarith⟩
          ⟨fun _ => by linarith, fun _ => h_null1⟩
          ⟨fun _ => by linarith, fun _ => h_ge01⟩
          ⟨fun h => absurd h h_nge10, fun h => by linarith⟩)⟩
    · -- Neither null: both singletons are "positive"
      by_cases h01 : sys.ge {(0 : Fin 2)} {1}
      · by_cases h10 : sys.ge {(1 : Fin 2)} {0}
        · -- Case 3c: ge {0} {1} ∧ ge {1} {0} → a = 1/2
          refine ⟨measure_fin2 (1/2) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (1/2) (by linarith) (by linarith)
              (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun _ => by linarith, fun _ => h10⟩)⟩
        · -- Case 3a: ge {0} {1} ∧ ¬ge {1} {0} → a = 2/3
          refine ⟨measure_fin2 (2/3) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin2_dispatch sys (2/3) (by linarith) (by linarith)
              (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
              ⟨fun h => absurd h h_null0, fun h => by linarith⟩
              ⟨fun h => absurd h h_null1, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h01⟩
              ⟨fun h => absurd h h10, fun h => by linarith⟩)⟩
      · -- Case 3b: ¬ge {0} {1} → ge {1} {0} (totality), a = 1/3
        have h10 : sys.ge {(1 : Fin 2)} {0} :=
          (sys.total {(1 : Fin 2)} {0}).resolve_right h01
        refine ⟨measure_fin2 (1/3) (by linarith) (by linarith),
          reduce_to_disjoint sys _ (fin2_dispatch sys (1/3) (by linarith) (by linarith)
            (mf2_empty ..) (mf2_zero ..) (mf2_one ..) (mf2_univ ..)
            ⟨fun h => absurd h h_null0, fun h => by linarith⟩
            ⟨fun h => absurd h h_null1, fun h => by linarith⟩
            ⟨fun h => absurd h h01, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => h10⟩)⟩

-- ── Card 3: Infrastructure ──────────────────────────

private noncomputable def measure_fin3 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : FinAddMeasure (Fin 3) where
  mu := fun A =>
    (if (0 : Fin 3) ∈ A then a else 0) +
    (if (1 : Fin 3) ∈ A then b else 0) +
    (if (2 : Fin 3) ∈ A then 1 - a - b else 0)
  nonneg := fun A => by
    apply add_nonneg; apply add_nonneg
    · split <;> [exact ha; exact le_refl _]
    · split <;> [exact hb; exact le_refl _]
    · split <;> [linarith; exact le_refl _]
  additive := fun A B hdisj => by
    simp only [Set.mem_union]
    by_cases h0A : (0 : Fin 3) ∈ A <;> by_cases h0B : (0 : Fin 3) ∈ B <;>
    by_cases h1A : (1 : Fin 3) ∈ A <;> by_cases h1B : (1 : Fin 3) ∈ B <;>
    by_cases h2A : (2 : Fin 3) ∈ A <;> by_cases h2B : (2 : Fin 3) ∈ B <;>
    simp_all <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; linarith

private theorem measure_fin3_mu (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (A : Set (Fin 3)) :
    (measure_fin3 a b ha hb hab).mu A =
    (if (0 : Fin 3) ∈ A then a else 0) +
    (if (1 : Fin 3) ∈ A then b else 0) +
    (if (2 : Fin 3) ∈ A then 1 - a - b else 0) := rfl

private theorem set_fin3_eq (A : Set (Fin 3)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = {2} ∨ A = {0,1} ∨ A = {0,2} ∨ A = {1,2} ∨
    A = Set.univ := by
  by_cases h0 : (0 : Fin 3) ∈ A <;> by_cases h1 : (1 : Fin 3) ∈ A <;>
  by_cases h2 : (2 : Fin 3) ∈ A
  · right; right; right; right; right; right; right; ext x; fin_cases x <;> simp_all
  · right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; left; ext x; fin_cases x <;> simp_all
  · left; ext x; fin_cases x <;> simp_all

-- Measure value lemmas for Fin 3
private theorem mf3_empty (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu ∅ = 0 := by
  rw [measure_fin3_mu]; simp

private theorem mf3_s0 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu {(0 : Fin 3)} = a := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∈ ({(0 : Fin 3)} : Set _) := rfl
  have h1 : (1 : Fin 3) ∉ ({(0 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h2 : (2 : Fin 3) ∉ ({(0 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_pos h0, if_neg h1, if_neg h2]; linarith

private theorem mf3_s1 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu {(1 : Fin 3)} = b := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∉ ({(1 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 3) ∈ ({(1 : Fin 3)} : Set _) := rfl
  have h2 : (2 : Fin 3) ∉ ({(1 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  rw [if_neg h0, if_pos h1, if_neg h2]; linarith

private theorem mf3_s2 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu {(2 : Fin 3)} = 1 - a - b := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∉ ({(2 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h1 : (1 : Fin 3) ∉ ({(2 : Fin 3)} : Set _) := by
    simp only [Set.mem_singleton_iff]; exact fun h => absurd (Fin.ext_iff.mp h) (by omega)
  have h2 : (2 : Fin 3) ∈ ({(2 : Fin 3)} : Set _) := rfl
  rw [if_neg h0, if_neg h1, if_pos h2]; linarith

private theorem mf3_p01 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu ({0, 1} : Set (Fin 3)) = a + b := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
  have h1 : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
  have h2 : (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  rw [if_pos h0, if_pos h1, if_neg h2]; linarith

private theorem mf3_p02 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu ({0, 2} : Set (Fin 3)) = 1 - b := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by simp
  have h1 : (1 : Fin 3) ∉ ({0, 2} : Set (Fin 3)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h2 : (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by simp
  rw [if_pos h0, if_neg h1, if_pos h2]; linarith

private theorem mf3_p12 (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu ({1, 2} : Set (Fin 3)) = 1 - a := by
  rw [measure_fin3_mu]
  have h0 : (0 : Fin 3) ∉ ({1, 2} : Set (Fin 3)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
                          (fun h' => absurd (Fin.ext_iff.mp h') (by omega))
  have h1 : (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  have h2 : (2 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  rw [if_neg h0, if_pos h1, if_pos h2]; linarith

private theorem mf3_univ (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (measure_fin3 a b ha hb hab).mu (Set.univ : Set (Fin 3)) = 1 := by
  rw [measure_fin3_mu]; simp only [Set.mem_univ, ite_true]; linarith

-- All three singletons null → contradiction
private theorem not_all_null_fin3 (sys : EpistemicSystemFA (Fin 3)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1} ∧ sys.ge ∅ {2}) := by
  intro ⟨h0, h1, h2⟩
  -- ge ∅ {0}, FA add C={1}: ge {1} {0,1}. trans with ge ∅ {1}: ge ∅ {0,1}
  have h01 : sys.ge ∅ ({0, 1} : Set (Fin 3)) := by
    have : sys.ge {1} ({0, 1} : Set (Fin 3)) := by
      rw [sys.additive {1} {0, 1}]
      rw [show ({1} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1} : Set (Fin 3)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
      exact h0
    exact sys.trans _ _ _ h1 this
  -- ge ∅ {0,1}, FA add C={2}: ge {2} univ. trans with ge ∅ {2}: ge ∅ univ
  have huniv : sys.ge ∅ Set.univ := by
    have : sys.ge {2} (Set.univ : Set (Fin 3)) := by
      rw [sys.additive {2} Set.univ]
      rw [show ({2} : Set (Fin 3)) \ Set.univ = ∅ from by ext x; simp]
      rw [show (Set.univ : Set (Fin 3)) \ {2} = {0, 1} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h2 this
  exact sys.nonTrivial huniv

-- ── Card 3: Dispatch helper ─────────────────────────

private theorem fin3_dispatch (sys : EpistemicSystemFA (Fin 3))
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hme : (measure_fin3 a b ha hb hab).mu ∅ = 0)
    (hm0 : (measure_fin3 a b ha hb hab).mu {(0 : Fin 3)} = a)
    (hm1 : (measure_fin3 a b ha hb hab).mu {(1 : Fin 3)} = b)
    (hm2 : (measure_fin3 a b ha hb hab).mu {(2 : Fin 3)} = 1 - a - b)
    (hm01 : (measure_fin3 a b ha hb hab).mu ({0, 1} : Set (Fin 3)) = a + b)
    (hm02 : (measure_fin3 a b ha hb hab).mu ({0, 2} : Set (Fin 3)) = 1 - b)
    (hm12 : (measure_fin3 a b ha hb hab).mu ({1, 2} : Set (Fin 3)) = 1 - a)
    (hmu : (measure_fin3 a b ha hb hab).mu (Set.univ : Set (Fin 3)) = 1)
    -- 9 ordering ↔ measure facts
    (he0 : sys.ge ∅ {(0 : Fin 3)} ↔ a ≤ 0)
    (he1 : sys.ge ∅ {(1 : Fin 3)} ↔ b ≤ 0)
    (he2 : sys.ge ∅ {(2 : Fin 3)} ↔ 1 - a - b ≤ 0)
    (he01 : sys.ge ∅ ({0, 1} : Set (Fin 3)) ↔ a + b ≤ 0)
    (he02 : sys.ge ∅ ({0, 2} : Set (Fin 3)) ↔ 1 - b ≤ 0)
    (he12 : sys.ge ∅ ({1, 2} : Set (Fin 3)) ↔ 1 - a ≤ 0)
    (h01 : sys.ge {(0 : Fin 3)} {1} ↔ a ≥ b)
    (h10 : sys.ge {(1 : Fin 3)} {0} ↔ b ≥ a)
    (h02 : sys.ge {(0 : Fin 3)} {2} ↔ a ≥ 1 - a - b)
    (h20 : sys.ge {(2 : Fin 3)} {0} ↔ 1 - a - b ≥ a)
    (h12 : sys.ge {(1 : Fin 3)} {2} ↔ b ≥ 1 - a - b)
    (h21 : sys.ge {(2 : Fin 3)} {1} ↔ 1 - a - b ≥ b)
    (h0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) ↔ a ≥ 1 - a)
    (h1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) ↔ b ≥ 1 - b)
    (h2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) ↔ 1 - a - b ≥ a + b)
    (h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} ↔ a + b ≥ 1 - a - b)
    (h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} ↔ 1 - b ≥ b)
    (h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} ↔ 1 - a ≥ a) :
    ∀ C D : Set (Fin 3), (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ (measure_fin3 a b ha hb hab).inducedGe C D) := by
  intro C D hdisj
  simp only [FinAddMeasure.inducedGe]
  rcases set_fin3_eq C with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases set_fin3_eq D with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- Phase 1: Close non-disjoint cases via term-level membership proofs
  all_goals try (exfalso; first
    | exact hdisj 0 rfl rfl | exact hdisj 1 rfl rfl | exact hdisj 2 rfl rfl
    | exact hdisj 0 rfl (Set.mem_univ _) | exact hdisj 1 rfl (Set.mem_univ _)
    | exact hdisj 2 rfl (Set.mem_univ _)
    | exact hdisj 0 (Set.mem_univ _) rfl | exact hdisj 1 (Set.mem_univ _) rfl
    | exact hdisj 2 (Set.mem_univ _) rfl
    | exact hdisj 0 (Set.mem_univ _) (Set.mem_univ _)
    | exact hdisj 0 rfl (Set.mem_insert _ _) | exact hdisj 1 rfl (Set.mem_insert _ _)
    | exact hdisj 2 rfl (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 0 rfl (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 1 rfl (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 2 rfl (Set.mem_insert _ _)
    | exact hdisj 0 (Set.mem_insert _ _) rfl | exact hdisj 1 (Set.mem_insert_of_mem _ rfl) rfl
    | exact hdisj 0 (Set.mem_insert _ _) (Set.mem_univ _)
    | exact hdisj 1 (Set.mem_insert_of_mem _ rfl) (Set.mem_univ _)
    | exact hdisj 0 (Set.mem_insert _ _) (Set.mem_insert _ _)
    | exact hdisj 2 (Set.mem_insert_of_mem _ rfl) rfl
    | exact hdisj 1 (Set.mem_insert _ _) rfl
    | exact hdisj 2 (Set.mem_insert_of_mem _ rfl) (Set.mem_univ _)
    | exact hdisj 1 (Set.mem_insert _ _) (Set.mem_univ _)
    | exact hdisj 0 (Set.mem_univ _) (Set.mem_insert _ _)
    | exact hdisj 1 (Set.mem_univ _) (Set.mem_insert _ _)
    | exact hdisj 1 (Set.mem_univ _) (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 0 (Set.mem_univ _) (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 2 (Set.mem_univ _) (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 1 (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _)
    | exact hdisj 0 (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 2 (Set.mem_insert_of_mem _ rfl) (Set.mem_insert_of_mem _ rfl)
    | exact hdisj 2 (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _)
    | exact hdisj 1 (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
  -- Phase 2: Rewrite measure values on remaining goals
  all_goals simp only [hme, hm0, hm1, hm2, hm01, hm02, hm12, hmu]
  -- Phase 3: Close remaining goals
  all_goals first
    | exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
    | exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
    | exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
    | exact he0 | exact he1 | exact he2 | exact he01 | exact he02 | exact he12
    | exact h01 | exact h10 | exact h02 | exact h20 | exact h12 | exact h21
    | exact h0_12 | exact h1_02 | exact h2_01
    | exact h01_2 | exact h02_1 | exact h12_0

-- ── Card 3: Derive ↔ helper ──────────────────────

/-- Given null/ordering facts about the system and a choice of a, b,
    derive all 21 ↔ hypotheses needed by fin3_dispatch.
    Uses FA axioms to derive ∅-vs-pair and pair-vs-singleton from simpler facts. -/
private theorem derive_null_pair (sys : EpistemicSystemFA (Fin 3))
    (he0 : sys.ge ∅ {0}) (he1 : sys.ge ∅ {1}) :
    sys.ge ∅ ({0, 1} : Set (Fin 3)) := by
  have h01 : sys.ge {0} ({0, 1} : Set (Fin 3)) := by
    rw [sys.additive {0} {0, 1}]
    rw [show ({0} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
    rw [show ({0, 1} : Set (Fin 3)) \ {0} = {1} from by ext x; fin_cases x <;> simp_all]
    exact he1
  exact sys.trans _ _ _ he0 h01

-- Helper: derive ¬ge {i} {j,k} from ge {j} {i} and ¬ge ∅ {k}
-- Route: ge {i} {j,k} → trans ge {j,k} {i,k} (add ↔ ge {j} {i}) → ge {i} {i,k} → add → ge ∅ {k} → hn_k
-- We need 6 variants for the 6 choices of (i,j,k) ∈ permutations of {0,1,2}.
-- Pattern: nge_via i j k means ¬ge {i} {j,k} using ge {j} {i} and ¬ge ∅ {k}.

private theorem nge_0_12 (sys : EpistemicSystemFA (Fin 3))
    (h10 : sys.ge {1} {0}) (hn2 : ¬sys.ge ∅ {2}) :
    ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) := fun h => by
  have hge_12_02 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 2} : Set _) := by
    rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}]
    rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
    rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
    exact h10
  have h1 := sys.trans _ _ _ h hge_12_02
  rw [sys.additive {0} {0, 2}] at h1
  rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn2 h1

-- ¬ge {0} {1,2} via route through {0,1}: uses ge {2} {0} and ¬ge ∅ {1}
private theorem nge_0_12' (sys : EpistemicSystemFA (Fin 3))
    (h20 : sys.ge {2} {0}) (hn1 : ¬sys.ge ∅ {1}) :
    ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) := fun h => by
  have hge_12_01 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
    rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 1}]
    rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
    rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
    exact h20
  have h1 := sys.trans _ _ _ h hge_12_01
  rw [sys.additive {0} {0, 1}] at h1
  rw [show ({0} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({0, 1} : Set (Fin 3)) \ {0} = {1} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn1 h1

private theorem nge_1_02 (sys : EpistemicSystemFA (Fin 3))
    (h01 : sys.ge {0} {1}) (hn2 : ¬sys.ge ∅ {2}) :
    ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := fun h => by
  have hge_02_12 : sys.ge ({0, 2} : Set (Fin 3)) ({1, 2} : Set _) := by
    rw [sys.additive ({0, 2} : Set (Fin 3)) {1, 2}]
    rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
    rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
    exact h01
  have h1 := sys.trans _ _ _ h hge_02_12
  rw [sys.additive {1} {1, 2}] at h1
  rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn2 h1

-- ¬ge {1} {0,2} via route through {0,1}: uses ge {2} {1} and ¬ge ∅ {0}
private theorem nge_1_02' (sys : EpistemicSystemFA (Fin 3))
    (h21 : sys.ge {2} {1}) (hn0 : ¬sys.ge ∅ {0}) :
    ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := fun h => by
  have hge_02_01 : sys.ge ({0, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
    rw [sys.additive ({0, 2} : Set (Fin 3)) {0, 1}]
    rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
    rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
    exact h21
  have h1 := sys.trans _ _ _ h hge_02_01
  rw [sys.additive {1} {0, 1}] at h1
  rw [show ({1} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({0, 1} : Set (Fin 3)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn0 h1

private theorem nge_2_01 (sys : EpistemicSystemFA (Fin 3))
    (h12 : sys.ge {1} {2}) (hn0 : ¬sys.ge ∅ {0}) :
    ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) := fun h => by
  have hge_01_02 : sys.ge ({0, 1} : Set (Fin 3)) ({0, 2} : Set _) := by
    rw [sys.additive ({0, 1} : Set (Fin 3)) {0, 2}]
    rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
    rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
    exact h12
  have h1 := sys.trans _ _ _ h hge_01_02
  rw [sys.additive {2} {0, 2}] at h1
  rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn0 h1

-- ¬ge {2} {0,1} via route through {1,2}: uses ge {0} {2} and ¬ge ∅ {1}
private theorem nge_2_01' (sys : EpistemicSystemFA (Fin 3))
    (h02 : sys.ge {0} {2}) (hn1 : ¬sys.ge ∅ {1}) :
    ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) := fun h => by
  have hge_01_12 : sys.ge ({0, 1} : Set (Fin 3)) ({1, 2} : Set _) := by
    rw [sys.additive ({0, 1} : Set (Fin 3)) {1, 2}]
    rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
    rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
    exact h02
  have h1 := sys.trans _ _ _ h hge_01_12
  rw [sys.additive {2} {1, 2}] at h1
  rw [show ({2} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
  rw [show ({1, 2} : Set (Fin 3)) \ {2} = {1} from by ext x; fin_cases x <;> simp_all] at h1
  exact hn1 h1

-- ── Card 3: Main theorem ─────────────────────────

set_option maxHeartbeats 3200000 in
private theorem theorem8a_fin3 (sys : EpistemicSystemFA (Fin 3)) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  -- Determine null status
  by_cases hn0 : sys.ge ∅ {(0 : Fin 3)}
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 3)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · exact absurd ⟨hn0, hn1, hn2⟩ (not_all_null_fin3 sys)
      · -- 2 null: {0},{1} null, {2} non-null → a=0, b=0
        -- Key intermediate facts
        have hge01 := derive_null_pair sys hn0 hn1
        have mono0 := sys.mono _ _ (Set.empty_subset ({0} : Set (Fin 3)))
        have mono1 := sys.mono _ _ (Set.empty_subset ({1} : Set (Fin 3)))
        -- ge {i} {j} for null singletons
        have hge_0_1 : sys.ge {0} {1} := sys.trans _ _ _ mono0 hn1
        have hge_1_0 : sys.ge {1} {0} := sys.trans _ _ _ mono1 hn0
        -- ¬ge {null} {2}: would give ge ∅ {2} by trans with null hyp
        have hng_0_2 : ¬sys.ge {(0 : Fin 3)} {2} :=
          fun h => hn2 (sys.trans _ _ _ hn0 h)
        have hng_1_2 : ¬sys.ge {(1 : Fin 3)} {2} :=
          fun h => hn2 (sys.trans _ _ _ hn1 h)
        have hge_2_0 : sys.ge {(2 : Fin 3)} {0} :=
          (sys.total _ _).resolve_right hng_0_2
        have hge_2_1 : sys.ge {(2 : Fin 3)} {1} :=
          (sys.total _ _).resolve_right hng_1_2
        -- ¬ge {0,1} {2}: would give ge ∅ {2} by trans with hge01
        have hng_01_2 : ¬sys.ge ({0, 1} : Set (Fin 3)) {2} :=
          fun h => hn2 (sys.trans _ _ _ hge01 h)
        have hge_2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
          (sys.total _ _).resolve_right hng_01_2
        -- ¬ge {null} {pair_with_2}: mono + trans gives ge ∅ {2}
        have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
          fun h => hn2 (sys.trans _ _ _ hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2}))))
        have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
          fun h => hn2 (sys.trans _ _ _ hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2}))))
        -- ¬ge ∅ {pair_with_2}: mono + trans gives ge ∅ {2}
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})))
        -- ge {0,2} {1} and ge {1,2} {0}: by totality
        have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
          (sys.total _ _).resolve_right hng_1_02
        have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
          (sys.total _ _).resolve_right hng_0_12
        refine ⟨measure_fin3 0 0 le_rfl le_rfl (by linarith),
          reduce_to_disjoint sys _ (fin3_dispatch sys 0 0 le_rfl le_rfl (by linarith)
            (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
            (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
            ⟨fun _ => le_refl _, fun _ => hn0⟩
            ⟨fun _ => le_refl _, fun _ => hn1⟩
            ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge01⟩
            ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_0_1⟩
            ⟨fun _ => by linarith, fun _ => hge_1_0⟩
            ⟨fun h => (hng_0_2 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_2_0⟩
            ⟨fun h => (hng_1_2 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_2_1⟩
            ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_2_01⟩
            ⟨fun h => (hng_01_2 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_02_1⟩
            ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 2 null: {0},{2} null, {1} non-null → a=0, b=1, c=0
        have hge02 : sys.ge ∅ ({0, 2} : Set (Fin 3)) := by
          have : sys.ge {0} ({0, 2} : Set (Fin 3)) := by
            rw [sys.additive {0} {0, 2}]
            rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all]
            exact hn2
          exact sys.trans _ _ _ hn0 this
        have mono0 := sys.mono _ _ (Set.empty_subset ({0} : Set (Fin 3)))
        have mono2 := sys.mono _ _ (Set.empty_subset ({2} : Set (Fin 3)))
        have hge_0_2 : sys.ge {0} {2} := sys.trans _ _ _ mono0 hn2
        have hge_2_0 : sys.ge {2} {0} := sys.trans _ _ _ mono2 hn0
        have hng_0_1 : ¬sys.ge {(0 : Fin 3)} {1} :=
          fun h => hn1 (sys.trans _ _ _ hn0 h)
        have hng_2_1 : ¬sys.ge {(2 : Fin 3)} {1} :=
          fun h => hn1 (sys.trans _ _ _ hn2 h)
        have hge_1_0 : sys.ge {(1 : Fin 3)} {0} := (sys.total _ _).resolve_right hng_0_1
        have hge_1_2 : sys.ge {(1 : Fin 3)} {2} := (sys.total _ _).resolve_right hng_2_1
        have hng_02_1 : ¬sys.ge ({0, 2} : Set (Fin 3)) {1} :=
          fun h => hn1 (sys.trans _ _ _ hge02 h)
        have hge_1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := (sys.total _ _).resolve_right hng_02_1
        have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
          fun h => hn1 (sys.trans _ _ _ hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _))))))
        have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
          fun h => hn1 (sys.trans _ _ _ hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1}))))
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))))
        have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right hng_2_01
        have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right hng_0_12
        refine ⟨measure_fin3 0 1 le_rfl zero_le_one (by linarith),
          reduce_to_disjoint sys _ (fin3_dispatch sys 0 1 le_rfl zero_le_one (by linarith)
            (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
            (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
            ⟨fun _ => le_refl _, fun _ => hn0⟩
            ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hn2⟩
            ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge02⟩
            ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_0_1 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_1_0⟩
            ⟨fun _ => by linarith, fun _ => hge_0_2⟩
            ⟨fun _ => by linarith, fun _ => hge_2_0⟩
            ⟨fun _ => by linarith, fun _ => hge_1_2⟩
            ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_1_02⟩
            ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_01_2⟩
            ⟨fun h => (hng_02_1 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
      · -- 1 null: {0} null, {1},{2} non-null → a=0
        have mono0 := sys.mono _ _ (Set.empty_subset ({0} : Set (Fin 3)))
        -- {0} is null, so ge {0} {i} iff ge ∅ {i}
        have hng_0_1 : ¬sys.ge {(0 : Fin 3)} {1} :=
          fun h => hn1 (sys.trans _ _ _ hn0 h)
        have hng_0_2 : ¬sys.ge {(0 : Fin 3)} {2} :=
          fun h => hn2 (sys.trans _ _ _ hn0 h)
        have hge_1_0 : sys.ge {(1 : Fin 3)} {0} := (sys.total _ _).resolve_right hng_0_1
        have hge_2_0 : sys.ge {(2 : Fin 3)} {0} := (sys.total _ _).resolve_right hng_0_2
        -- ¬ge ∅ {pair}: mono gives ge {pair} {singleton_in_pair}
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})))
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))))
        -- ¬ge {0} {pair_without_0}: trans with null gives ge ∅ {pair}
        have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
          fun h => hn1 (sys.trans _ _ _ hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _))))))
        have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right hng_0_12
        -- Wait, hn1 is ¬sys.ge ∅ {1}, so we can't derive_null_pair with it.
        -- Instead: {0,1}\{2} reduces via additivity.
        -- Actually for {0,1} vs {2}: by additivity, ge {0,1} {2} ↔ ge ({0,1}\{2}) ({2}\{0,1})
        -- = ge {0,1} {2} (already disjoint). So we need direct reasoning.
        -- ge {0,1} {2} → ge {0} {2} by... no, that's wrong direction.
        -- Actually we need to sub-case on ge {1} {2}.
        by_cases h12 : sys.ge {(1 : Fin 3)} {2}
        · by_cases h21 : sys.ge {(2 : Fin 3)} {1}
          · -- Tie: b = 1/2
            -- ge {0,1} {2}: by additivity {0,1}\{2}={0,1}, {2}\{0,1}={2}
            -- so ge {0,1} {2} ↔ ge {0,1} {2}. Need: ge {0,1} {2}?
            -- {1} ≥ {2} and {0,1} ⊇ {1}, so ge {0,1} {1} by mono, then trans
            have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
            have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
            -- ge {1} {0,2}? totality: ge {1} {0,2} or ge {0,2} {1}
            -- ge {0,2} {1} is true (above). ge {1} {0,2}?
            -- If ge {1} {0,2}, then ge {1} {2} (mono) — already true. Not helpful.
            -- Need: does ge {1} {0,2} hold? mu({1})=1/2, mu({0,2})=1/2, so ↔ should be true
            -- ge {1} {0,2} iff b ≥ 1-b iff 1/2 ≥ 1/2, true.
            -- Derive: {0,2} ⊇ {2}, ge {1} {2} (h12), ge {0,2} {2} (mono).
            -- But we need ge {1} {0,2}, not ge {0,2} {1}.
            -- Hmm, can't directly derive ge {1} {0,2} from ge {1} {2}.
            -- By additivity: ge {1} {0,2} ↔ ge ({1}\{0,2}) ({0,2}\{1}) = ge {1} {0,2}
            -- (already disjoint). So this is the original question.
            -- Actually: ge {2} {0} (hge_2_0). By additivity on {1,2} vs {0,2}:
            -- Nah, let's just use totality and check both directions.
            -- If ¬ge {1} {0,2}, then ge {0,2} {1} (true above). That's consistent.
            -- The ↔ for h1_02 needs: sys.ge {1} {0,2} ↔ b ≥ 1-b = 1/2 ≥ 1/2, i.e. true.
            -- So we need ge {1} {0,2} to be true for the ↔ to work.
            -- Derive via additivity: ge {1} {0,2} ↔ ge ({1}\{0,2}) ({0,2}\{1})
            -- {1}\{0,2} = {1} (disjoint), {0,2}\{1} = {0,2}. So ge {1} {0,2} directly.
            -- Can we derive it? ge {1} {2} and ge {2} {0} → ge {1} {0} by trans.
            -- Then ge {1} {0} and ge {1} {2}... hmm we need ge {1} {0,2}.
            -- By FA: ge {1} {0,2} ↔ ge {1} ({0,2}\{1}) = ge {1} {0,2} (disjoint, same).
            -- Not helpful. Let's try: ge {1,2} {0,2} by additivity:
            -- ge {1,2} {0,2} ↔ ge ({1,2}\{0,2}) ({0,2}\{1,2}) = ge {1} {0}.
            -- ge {1} {0} = hge_1_0. So ge {1,2} {0,2}.
            -- Then ge {1} {0,2}... still can't get there directly.
            -- Let me think differently. ge {0} ∅ (mono). ge {1} {0} (hge_1_0).
            -- By additivity: ge {0,1} {0} ↔ ge ({0,1}\{0}) ({0}\{0,1}) = ge {1} ∅. True by mono.
            -- So ge {0,1} {0}. Not helpful.
            -- OK let me just try: sys.ge {1} {0} (hge_1_0), sys.ge {1} {2} (h12).
            -- I want sys.ge {1} {0,2}.
            -- By additivity: ge {1} {0,2} ↔ ge ({1}\{0,2}) ({0,2}\{1}) = ge {1} {0,2} (already disjoint).
            -- Hmm, {1} and {0,2} are disjoint, so additivity is trivial here.
            -- Actually wait, additivity says ge A B ↔ ge (A\B) (B\A). If A and B are already disjoint, then A\B=A and B\A=B. So it's just ge A B ↔ ge A B. Tautological.
            -- So I can't use additivity to derive ge {1} {0,2} from simpler facts.
            -- Can I derive it from FA axioms at all?
            -- Actually I think for the tie case we might need to use a different approach.
            -- Let me think about what the FA axioms give us.
            --
            -- Actually, I realize the issue. In the 1-null case with a tie between {1} and {2},
            -- we might NOT always have ge {1} {0,2}. Consider:
            -- ge {1} {2} and ge {2} {1} (tie). {0} is null.
            -- ge {1} {0,2}: since {0} has "zero weight" and {2} has same weight as {1},
            -- {0,2} should have same weight as {2} = same as {1}. So ge {1} {0,2} should hold (tie).
            -- But can we prove this from the axioms?
            --
            -- By additivity on {1} vs {0,2}: already disjoint, no help.
            -- By additivity on {1,0} vs {0,2}: ge {0,1} {0,2} ↔ ge ({0,1}\{0,2}) ({0,2}\{0,1})
            --   = ge {1} {2}. So ge {0,1} {0,2} ↔ ge {1} {2}. Since h12, ge {0,1} {0,2}.
            -- By additivity on {0,1} vs {1}: ge {0,1} {1} ↔ ge {0} ∅. True by mono.
            -- So ge {0,1} {1}.
            -- Now: ge {0,1} {0,2} and ge {1} {0,1} (by mono, {0,1} ⊇ {1}).
            -- Wait, mono gives ge {0,1} {1}, not ge {1} {0,1}.
            -- Do we have ge {1} {0,1}? By additivity: ge {1} {0,1} ↔ ge ({1}\{0,1}) ({0,1}\{1})
            --   = ge ∅ {0} = hn0. So ge {1} {0,1} ↔ hn0. Since hn0 is true, ge {1} {0,1}.
            --
            -- OK so: ge {1} {0,1} (from hn0 via additivity).
            -- ge {0,1} {0,2} (from h12 via additivity).
            -- By trans: ge {1} {0,2}.
            --
            -- Similarly: ge {2} {0,2} (from hn0 via additivity on {2} vs {0,2}).
            -- Actually: ge {2} {0,2} ↔ ge ({2}\{0,2}) ({0,2}\{2}) = ge ∅ {0} = hn0.
            -- So ge {2} {0,2} iff hn0. True.
            -- And ge {0,2} {0,1} ↔ ge ({0,2}\{0,1}) ({0,1}\{0,2}) = ge {2} {1} = h21. True.
            -- By trans: ge {2} {0,1}. Good.
            --
            -- OK this is getting complex. Let me just write the code and see what happens.
            -- I'll derive the needed facts step by step.

            -- ge {1} {0,1}: additivity gives ↔ ge ∅ {0} = hn0
            have hge_1_01 : sys.ge {(1 : Fin 3)} ({0, 1} : Set _) := by
              rw [sys.additive {1} {0, 1}]
              rw [show ({1} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
              exact hn0
            -- ge {0,1} {0,2}: additivity gives ↔ ge {1} {2} = h12
            have hge_01_02 : sys.ge ({0, 1} : Set (Fin 3)) ({0, 2} : Set _) := by
              rw [sys.additive ({0, 1} : Set (Fin 3)) {0, 2}]
              rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
              exact h12
            have hge_1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
              sys.trans _ _ _ hge_1_01 hge_01_02
            -- Similarly: ge {2} {0,2} via additivity ↔ ge ∅ {0} = hn0
            have hge_2_02 : sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
              rw [sys.additive {2} {0, 2}]
              rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all]
              exact hn0
            -- ge {0,2} {0,1} via additivity ↔ ge {2} {1} = h21
            have hge_02_01 : sys.ge ({0, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
              rw [sys.additive ({0, 2} : Set (Fin 3)) {0, 1}]
              rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
              exact h21
            have hge_2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
              sys.trans _ _ _ hge_2_02 hge_02_01
            refine ⟨measure_fin3 0 (1/2) le_rfl (by linarith) (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys 0 (1/2) le_rfl (by linarith) (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun _ => le_refl _, fun _ => hn0⟩
                ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_0_1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_0⟩
                ⟨fun h => (hng_0_2 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_2_0⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun _ => by linarith, fun _ => h21⟩
                ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_02⟩
                ⟨fun _ => by linarith, fun _ => hge_2_01⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
          · -- Strict {1} > {2}: b = 2/3
            have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
            -- ¬ge {0,2} {1}: by additivity ↔ ge ({0,2}\{1}) ({1}\{0,2}) = ge {0,2} {1}
            -- Actually {0,2} and {1} are disjoint so additivity is trivial.
            -- Instead: ¬ge {2} {1} (h21). ge {0,2} {1} → ge {2} {1} by...
            -- No, ge {0,2} {1} does NOT imply ge {2} {1}. {0,2} is bigger.
            -- By additivity: ge {0,2} {1} ↔ ge ({0,2}\{1}) ({1}\{0,2}) = ge {0,2} {1} (disjoint).
            -- Hmm. ge {0,2} {0,1} ↔ ge {2} {1} (by additivity, as above). ¬h21 means ¬ge {0,2} {0,1}.
            -- ge {0,1} {0,2} (by additivity ↔ ge {1} {2} = h12). True.
            -- But does ge {0,2} {1} hold? mu({0,2})=1/3, mu({1})=2/3. So ¬ge {0,2} {1}.
            -- Derive: ¬ge {0,2} {1} from ¬ge {2} {1}?
            -- If ge {0,2} {1}, then by additivity on {0,2} vs {0,1}:
            --   ge {0,2} {0,1} ↔ ge {2} {1}. If ¬ge {2} {1}, then ¬ge {0,2} {0,1}.
            -- But ge {0,2} {1} doesn't directly give ge {0,2} {0,1}.
            -- Hmm. Let's try: if ge {0,2} {1}, and ge ∅ {0} (hn0), then by additivity on {0,2} vs {0,1}:
            -- Actually I need a cleaner approach.
            --
            -- ge {0,2} {1}: additivity on {0,2} vs {1} is trivial (disjoint).
            -- Need to determine: does sys.ge ({0,2}) {1} hold?
            -- By totality: either ge {0,2} {1} or ge {1} {0,2}.
            -- If ge {0,2} {1}, then by additivity {0,2} vs {0,1}:
            --   ge {0,2} {0,1} ↔ ge {2} {1}. Since ¬h21, ¬ge {0,2} {0,1}.
            --   But ge {0,2} {1} doesn't give ge {0,2} {0,1} directly.
            --   Actually it does via mono: {0,1} ⊇ {1}, so ge {0,1} {1}, hence if ge {0,2} {1}
            --   we can't get ge {0,2} {0,1} without more.
            --
            -- OK I think the issue is that ge {0,2} {1} CAN be true even when ¬ge {2} {1},
            -- because {0,2} has more "weight" than {2} alone (even though {0} is null,
            -- null means ge ∅ {0}, not that {0} contributes nothing to pairs).
            --
            -- Wait, actually: {0} IS null (ge ∅ {0}). By FA:
            -- ge {0,2} {2} ↔ ge ({0,2}\{2}) ({2}\{0,2}) = ge {0} ∅. True by mono.
            -- So ge {0,2} {2}. And ge {2} {0,2} (derived above via additivity ↔ hn0).
            -- So {0,2} ~ {2} in the ordering. And ¬ge {2} {1} → ¬ge {0,2} {1}?
            -- ge {0,2} {1}: suppose true. ge {2} {0,2} (true). By trans: ge {2} {1}. Contradiction with ¬h21.
            -- YES! So ¬ge {0,2} {1}.

            have hge_2_02 : sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
              rw [sys.additive {2} {0, 2}]
              rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all]
              exact hn0
            have hng_02_1 : ¬sys.ge ({0, 2} : Set (Fin 3)) {1} :=
              fun h => h21 (sys.trans _ _ _ hge_2_02 h)
            have hge_1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := (sys.total _ _).resolve_right hng_02_1
            -- ge {2} {0,1}? ge {2} {0,2} and ge {0,2} {0,1} ↔ ge {2} {1} (¬h21). So ¬ge {0,2} {0,1}.
            -- But {2} vs {0,1}: by additivity, disjoint, so no simplification.
            -- Totality: ge {2} {0,1} or ge {0,1} {2}. ge {0,1} {2} is true (hge_01_2).
            -- Does ge {2} {0,1} hold? mu({2})=1/3, mu({0,1})=2/3. No.
            -- Derive ¬ge {2} {0,1}: if ge {2} {0,1}, then ge {2} {1} by mono on {0,1}⊇{1}...
            -- No, mono gives ge {0,1} {1}, not ge {1} {0,1}. We need:
            -- ge {2} {0,1} → ? Can we get ge {2} {1}?
            -- ge {2} {0,1} and mono {0,1} ⊇ {1} gives ge {0,1} {1}. Not helpful.
            -- By additivity: ge {2} {0,1} ↔ ge ({2}\{0,1}) ({0,1}\{2}) = ge {2} {0,1} (disjoint). Trivial.
            -- Hmm. What about: ge {2} {0,1}. By additivity on {0,2} vs {0,1}:
            --   ge {0,2} {0,1} ↔ ge {2} {1}. ¬h21 gives ¬ge {0,2} {0,1}.
            -- But ge {2} {0,1} doesn't give ge {0,2} {0,1}.
            --
            -- Actually: if ge {2} {0,1}, and ge ∅ {0} (hn0), then:
            --   By additivity on {2} vs {0}: ge {2} {0} ↔ ge ({2}\{0}) ({0}\{2}) = ge {2} {0} (disjoint). Trivial.
            --   By additivity on {0,2} vs {0,1}: ge {0,2} {0,1} ↔ ge {2} {1}. ¬h21.
            --   So ¬ge {0,2} {0,1}. But we want to show ¬ge {2} {0,1}.
            --
            -- Alternative: if ge {2} {0,1}, by additivity on {1,2} vs {0,1}:
            --   ge {1,2} {0,1} ↔ ge ({1,2}\{0,1}) ({0,1}\{1,2}) = ge {2} {0}.
            --   ge {2} {0} is true (hge_2_0). So ge {1,2} {0,1}.
            --   Hmm, that's just consistent, doesn't give a contradiction.
            --
            -- What if ge {2} {0,1}? Then ge {2} {0} (mono on {0,1}⊇{0}... no).
            -- Actually ge {2} {0,1}: this means {2} is at least as likely as {0,1}.
            -- {0} is null, so {0,1} ~ {1}. So ge {2} {0,1} ↔ ge {2} {1}.
            -- Can we formalize "{0,1} ~ {1}"?
            -- ge {0,1} {1} (mono). ge {1} {0,1} (by additivity ↔ ge ∅ {0} = hn0).
            -- So ge {2} {0,1} + ge {0,1} {1} (mono) → ... that gives ge {0,1} {1}, not ge {2} {1}.
            -- ge {2} {0,1} + trans with ge {0,1} → need ge {0,1} {something}.
            --
            -- Try: ge {1} {0,1} (proved above from hn0 via additivity).
            -- ge {0,1} {1} (mono). So {0,1} ~ {1}.
            -- If ge {2} {0,1}, then ge {2} {0,1} + ge {0,1} = ge {0,1} {1}... NO.
            -- Trans: ge {2} {0,1} and ge {0,1} {1} → ge {2} {1}. But ¬h21. Contradiction!
            -- YES!

            have hge_01_1 : sys.ge ({0, 1} : Set (Fin 3)) {1} :=
              sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})
            have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
              fun h => h21 (sys.trans _ _ _ h hge_01_1)
            have hge_01_2' : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right hng_2_01
            -- Now we still need hge_12_0 and hng_0_12
            have hge_1_01 : sys.ge {(1 : Fin 3)} ({0, 1} : Set _) := by
              rw [sys.additive {1} {0, 1}]
              rw [show ({1} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
              exact hn0
            refine ⟨measure_fin3 0 (2/3) le_rfl (by linarith) (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys 0 (2/3) le_rfl (by linarith) (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun _ => le_refl _, fun _ => hn0⟩
                ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_0_1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_0⟩
                ⟨fun h => (hng_0_2 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_2_0⟩
                ⟨fun _ => by linarith, fun _ => h12⟩
                ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_02⟩
                ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun h => (hng_02_1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
        · -- ¬ge {1} {2} → ge {2} {1} by totality: b = 1/3
          have h21 : sys.ge {(2 : Fin 3)} {1} := (sys.total _ _).resolve_right h12
          have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
            sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
          -- ge {1} {0,2}? mu=1/3 vs 2/3. No.
          -- Derive ¬ge {1} {0,2}: ge {0,2} {0,1} ↔ ge {2} {1} (h21). So ge {0,2} {0,1}.
          -- ge {1} {0,1} (from hn0 via additivity).
          -- If ge {1} {0,2}, trans with ge {0,2} {0,1}: ge {1} {0,1}.
          -- That's already true, no contradiction.
          -- Better: ge {0,2} {2} (mono). ge {2} {0,2} (from hn0 via additivity).
          -- If ge {1} {0,2}, trans with ge {0,2} {2}: ge {1} {2}... wait, that gives ge {0,2} {2},
          -- and if ge {1} {0,2} then ge {1} {0,2} trans ge {0,2} {2}... no that's wrong direction.
          -- ge {1} {0,2} and ge {0,2} {2} = mono, gives ge {0,2} {2}. Trans: ge {1} {0,2} + ...
          -- Hmm, I need ge {something} {something} where {1} ends up ≥ {2}.
          -- OK simpler: ge {0,2} {2} (mono: {0,2} ⊇ {2}).
          -- If ge {1} {0,2}, then ge {1} {0,2} and {0,2} ⊇ {2} doesn't give ge {1} {2} directly.
          -- But wait, mono gives ge {0,2} {2}, not ge {2} {0,2}.
          -- Actually if I want ge {1} {2}, I'd need ge {1} {0,2} and then... I can't decompose {0,2}.
          --
          -- Alternative approach: ge {0,2} {0,2} (refl). By additivity {0,2} vs {0,1}:
          --   ge {0,2} {0,1} ↔ ge {2} {1} = h21. True.
          -- ge {0,1} {1} (mono). Trans: ge {0,2} {0,1} and ge {0,1} {1} → ge {0,2} {1}.
          -- Already have that. Not helpful for ¬ge {1} {0,2}.
          --
          -- Try: if ge {1} {0,2}, then ge {1} {0,2} and ge {0,2} {0,1} (from h21 via additivity):
          --   trans: ge {1} {0,1}. Already true. No contradiction.
          --
          -- Hmm, what about: if ge {1} {0,2}, then by additivity on {1,2} vs {0,2}:
          --   ge {1,2} {0,2} ↔ ge ({1,2}\{0,2}) ({0,2}\{1,2}) = ge {1} {0}.
          --   ge {1} {0} = hge_1_0. True. So ge {1,2} {0,2}. Already consistent.
          --
          -- What about ge {1} {0}? That's hge_1_0 (true).
          -- And ge {1} {2}? That's h12 (false).
          -- Can we derive ¬ge {1} {0,2} from ¬ge {1} {2}?
          -- If ge {1} {0,2}: By additivity on {1} vs {0,2}: disjoint, trivial.
          -- Hmm.
          --
          -- Wait, let me reconsider. With {0} null:
          -- ge {2} {0,2} (from hn0 via additivity: ge {2} {0,2} ↔ ge ∅ {0} = hn0).
          -- So {2} ~ {0,2}. Then ge {1} {0,2} ↔ ge {1} {2} by transitivity through the equivalence.
          -- Specifically: if ge {1} {0,2}, then ge {1} {0,2} and ge {0,2} {2} (mono: {0,2} ⊇ {2}).
          -- Wait, ge {0,2} {2} is mono (supset), but I need ge {2} {0,2} for the other direction.
          -- I have ge {2} {0,2} (from hn0). If ge {1} {0,2}, then I can't directly get ge {1} {2}.
          -- But: if ge {1} {0,2}, then... hmm let me think about this differently.
          --
          -- Actually: ge {2} {0,2} means {0,2} ≤ {2}. ge {0,2} {2} (mono) means {2} ≤ {0,2}.
          -- So {2} ~ {0,2}. ge {1} {0,2} with {0,2} ~ {2} should give ge {1} {2}.
          -- Formally: ge {1} {0,2} and ge {0,2} {2} (mono) → ge {1} {2} by trans? No!
          -- Trans takes ge A B and ge B C → ge A C. So ge {1} {0,2} and ge {0,2} {2} → ge {1} {2}.
          -- Wait, but mono gives ge (superset) (subset), so ge {0,2} {2}.
          -- Hmm, is that right? mono : A ⊆ B → ge B A. So {2} ⊆ {0,2} → ge {0,2} {2}. Yes.
          -- So ge {1} {0,2} (hypothesis) and ge {0,2} {2} (mono) → by trans, ge {1} {2}.
          -- But ¬ge {1} {2} (h12). Contradiction!
          --
          -- Great! So ¬ge {1} {0,2}.

          have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
            fun h => h12 (sys.trans _ _ _ h (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})))
          -- ge {2} {0,1}: same as tie case. ge {0,1} {1} (mono).
          -- If ge {2} {0,1}, trans with ge {0,1} {1}: ge {2} {1}. True (h21). Consistent.
          -- ¬ge {2} {0,1}: if ge {2} {0,1}, trans ge {0,1} {0} (mono)... no, mono gives ge {0,1} {0}, trans: ge {2} {0}. True. Consistent.
          -- Hmm, mu({2})=2/3 > mu({0,1})=1/3, so ge {2} {0,1} should be true.
          -- Derive: ge {2} {1} (h21) and ge {1} {0} (hge_1_0), so ge {2} {0} (trans).
          -- ge {2} {0} and ge {2} {1}. Can we get ge {2} {0,1}?
          -- By additivity on {0,2} vs {0,1}: ge {0,2} {0,1} ↔ ge {2} {1} = h21. True.
          -- ge {2} {0,2} (from hn0 via additivity). Trans: ge {2} {0,2} and ge {0,2} {0,1}: ge {2} {0,1}.

          have hge_2_02 : sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
            rw [sys.additive {2} {0, 2}]
            rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all]
            exact hn0
          have hge_02_01 : sys.ge ({0, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
            rw [sys.additive ({0, 2} : Set (Fin 3)) {0, 1}]
            rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
            exact h21
          have hge_2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
            sys.trans _ _ _ hge_2_02 hge_02_01
          -- ge {0,1} {2}: totality. ¬ge {2} {0,1} → ... no, we proved ge {2} {0,1}.
          -- Does ge {0,1} {2} hold? mu=1/3 vs 1/3. Tie. So yes.
          -- Derive: ge {0,1} {2} ← mono {0,1} ⊇ {1}? No, that gives ge {0,1} {1}, not ge {0,1} {2}.
          -- ge {0,1} {0,2} ↔ ge {1} {2}. ¬h12. So ¬ge {0,1} {0,2}.
          -- But ge {0,1} {2}? Additivity: disjoint, trivial. Need direct.
          -- ge {0,1} {0} (mono, {0,1}⊇{0}). ge {0} {2}? ¬hng_0_2. So ¬ge {0} {2}.
          -- ge {1} {2}? ¬h12.
          -- Totality: ge {0,1} {2} or ge {2} {0,1}. We proved ge {2} {0,1}.
          -- Does ge {0,1} {2} also hold? By FA, consistent with ge {2} {0,1} only if tie.
          -- Can we derive ge {0,1} {2}?
          -- ge {0,1} {0} (mono). ge {0} {0}... not helpful.
          -- ge {0,1} {2}: by additivity on {0,1,2}=univ vs {2}:
          --   ge univ {2} ↔ ge (univ\{2}) ({2}\univ) = ge {0,1} ∅. True by mono.
          --   But that gives ge univ {2}, not ge {0,1} {2}.
          -- Hmm. Let me try: ge {1,2} {0,1} ↔ ge ({1,2}\{0,1}) ({0,1}\{1,2}) = ge {2} {0}.
          --   ge {2} {0} = hge_2_0. So ge {1,2} {0,1}.
          -- ge {0,1} {1,2}? ↔ ge {0} {2}. ¬hng_0_2. So ¬ge {0,1} {1,2}.
          -- Hmm.
          -- Actually, maybe ge {0,1} {2} DOESN'T hold in general. We just need it for the ↔.
          -- The ↔ says: ge {0,1} {2} ↔ a+b ≥ 1-a-b = 0+1/3 ≥ 2/3. That's 1/3 ≥ 2/3 = false!
          -- So we need ¬ge {0,1} {2} and the measure inequality to also be false.
          -- mu({0,1})=0+1/3=1/3, mu({2})=2/3. 1/3 ≥ 2/3 is false. Good.
          -- So we need ¬ge {0,1} {2}.
          -- If ge {0,1} {2}, trans with ge {2} {1} (h21): ge {0,1} {1}. True by mono. Consistent. No contradiction.
          -- If ge {0,1} {2}, trans with ge {2} {0} (hge_2_0): ge {0,1} {0}. True by mono. Consistent.
          -- Hmm, hard to get ¬ge {0,1} {2} directly.
          --
          -- Wait, by additivity on {0,1} vs {2}: disjoint, trivial.
          -- By additivity on {0,1} vs {0,2}: ge {0,1} {0,2} ↔ ge {1} {2}. ¬h12. So ¬ge {0,1} {0,2}.
          -- If ge {0,1} {2}, and ge {2} {0,2} (proved above), then trans: ge {0,1} {0,2}. But ¬ge {0,1} {0,2}. Contradiction!

          have hng_01_02 : ¬sys.ge ({0, 1} : Set (Fin 3)) ({0, 2} : Set _) := by
            rw [sys.additive ({0, 1} : Set (Fin 3)) {0, 2}]
            rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
            exact h12
          have hng_01_2 : ¬sys.ge ({0, 1} : Set (Fin 3)) {2} :=
            fun h => hng_01_02 (sys.trans _ _ _ h hge_2_02)
          refine ⟨measure_fin3 0 (1/3) le_rfl (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin3_dispatch sys 0 (1/3) le_rfl (by linarith) (by linarith)
              (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
              (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
              ⟨fun _ => le_refl _, fun _ => hn0⟩
              ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
              ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_0_1 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_1_0⟩
              ⟨fun h => (hng_0_2 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_2_0⟩
              ⟨fun h => (h12 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h21⟩
              ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_2_01⟩
              ⟨fun h => (hng_01_2 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_02_1⟩
              ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 3)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 2 null: {1},{2} null, {0} non-null → a=1, b=0, c=0
        have hge12 : sys.ge ∅ ({1, 2} : Set (Fin 3)) := by
          have : sys.ge {1} ({1, 2} : Set (Fin 3)) := by
            rw [sys.additive {1} {1, 2}]
            rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all]
            exact hn2
          exact sys.trans _ _ _ hn1 this
        have mono1 := sys.mono _ _ (Set.empty_subset ({1} : Set (Fin 3)))
        have mono2 := sys.mono _ _ (Set.empty_subset ({2} : Set (Fin 3)))
        have hge_1_2 : sys.ge {1} {2} := sys.trans _ _ _ mono1 hn2
        have hge_2_1 : sys.ge {2} {1} := sys.trans _ _ _ mono2 hn1
        have hng_1_0 : ¬sys.ge {(1 : Fin 3)} {0} :=
          fun h => hn0 (sys.trans _ _ _ hn1 h)
        have hng_2_0 : ¬sys.ge {(2 : Fin 3)} {0} :=
          fun h => hn0 (sys.trans _ _ _ hn2 h)
        have hge_0_1 : sys.ge {(0 : Fin 3)} {1} := (sys.total _ _).resolve_right hng_1_0
        have hge_0_2 : sys.ge {(0 : Fin 3)} {2} := (sys.total _ _).resolve_right hng_2_0
        have hng_12_0 : ¬sys.ge ({1, 2} : Set (Fin 3)) {0} :=
          fun h => hn0 (sys.trans _ _ _ hge12 h)
        have hge_0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) := (sys.total _ _).resolve_right hng_12_0
        have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
          fun h => hn0 (sys.trans _ _ _ hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _))))))
        have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
          fun h => hn0 (sys.trans _ _ _ hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _))))))
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))))
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))))
        have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right hng_1_02
        have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right hng_2_01
        refine ⟨measure_fin3 1 0 zero_le_one le_rfl (by linarith),
          reduce_to_disjoint sys _ (fin3_dispatch sys 1 0 zero_le_one le_rfl (by linarith)
            (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
            (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
            ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hn1⟩
            ⟨fun _ => by linarith, fun _ => hn2⟩
            ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge12⟩
            ⟨fun _ => by linarith, fun _ => hge_0_1⟩
            ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_0_2⟩
            ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_1_2⟩
            ⟨fun _ => by linarith, fun _ => hge_2_1⟩
            ⟨fun _ => by linarith, fun _ => hge_0_12⟩
            ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
            ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
            ⟨fun _ => by linarith, fun _ => hge_01_2⟩
            ⟨fun _ => by linarith, fun _ => hge_02_1⟩
            ⟨fun h => (hng_12_0 h).elim, fun h => by linarith⟩)⟩
      · -- 1 null: {1} null, {0},{2} non-null → b=0
        have mono1 := sys.mono _ _ (Set.empty_subset ({1} : Set (Fin 3)))
        have hng_1_0 : ¬sys.ge {(1 : Fin 3)} {0} :=
          fun h => hn0 (sys.trans _ _ _ hn1 h)
        have hng_1_2 : ¬sys.ge {(1 : Fin 3)} {2} :=
          fun h => hn2 (sys.trans _ _ _ hn1 h)
        have hge_0_1 : sys.ge {(0 : Fin 3)} {1} := (sys.total _ _).resolve_right hng_1_0
        have hge_2_1 : sys.ge {(2 : Fin 3)} {1} := (sys.total _ _).resolve_right hng_1_2
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})))
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))))
        have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
          fun h => hn0 (sys.trans _ _ _ hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _))))))
        have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right hng_1_02
        -- ge/¬ge {1} {0,1} and {1} {1,2} via additivity
        have hng_1_01 : ¬sys.ge {(1 : Fin 3)} ({0, 1} : Set _) := by
          rw [sys.additive {1} {0, 1}]
          rw [show ({1} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
          rw [show ({0, 1} : Set (Fin 3)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
          exact hn0
        have hng_1_12 : ¬sys.ge {(1 : Fin 3)} ({1, 2} : Set _) := by
          rw [sys.additive {1} {1, 2}]
          rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
          rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all]
          exact hn2
        by_cases h02 : sys.ge {(0 : Fin 3)} {2}
        · by_cases h20 : sys.ge {(2 : Fin 3)} {0}
          · -- Tie: a = 1/2, b = 0, c = 1/2
            have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
            have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
            -- ge {0} {0,1} via additivity ↔ ge ∅ {1} = hn1
            have hge_0_01 : sys.ge {(0 : Fin 3)} ({0, 1} : Set _) := by
              rw [sys.additive {0} {0, 1}]
              rw [show ({0} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {0} = {1} from by ext x; fin_cases x <;> simp_all]
              exact hn1
            -- ge {0,1} {1,2} via additivity ↔ ge {0} {2} = h02
            have hge_01_12 : sys.ge ({0, 1} : Set (Fin 3)) ({1, 2} : Set _) := by
              rw [sys.additive ({0, 1} : Set (Fin 3)) {1, 2}]
              rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
              exact h02
            have hge_0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
              sys.trans _ _ _ hge_0_01 hge_01_12
            -- ge {2} {1,2} via additivity ↔ ge ∅ {1} = hn1
            have hge_2_12 : sys.ge {(2 : Fin 3)} ({1, 2} : Set _) := by
              rw [sys.additive {2} {1, 2}]
              rw [show ({2} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {2} = {1} from by ext x; fin_cases x <;> simp_all]
              exact hn1
            -- ge {1,2} {0,1} via additivity ↔ ge {2} {0} = h20
            have hge_12_01 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
              rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 1}]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              exact h20
            have hge_2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
              sys.trans _ _ _ hge_2_12 hge_12_01
            refine ⟨measure_fin3 (1/2) 0 (by linarith) le_rfl (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys (1/2) 0 (by linarith) le_rfl (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hn1⟩
                ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_0_1⟩
                ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun _ => by linarith, fun _ => h20⟩
                ⟨fun h => (hng_1_2 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_2_1⟩
                ⟨fun _ => by linarith, fun _ => hge_0_12⟩
                ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_2_01⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
          · -- Strict {0} > {2}: a = 2/3, b = 0, c = 1/3
            -- ge {0} {0,1} via additivity ↔ ge ∅ {1} = hn1
            have hge_0_01 : sys.ge {(0 : Fin 3)} ({0, 1} : Set _) := by
              rw [sys.additive {0} {0, 1}]
              rw [show ({0} : Set (Fin 3)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 1} : Set (Fin 3)) \ {0} = {1} from by ext x; fin_cases x <;> simp_all]
              exact hn1
            -- ge {0,1} {1,2} via additivity ↔ ge {0} {2} = h02
            have hge_01_12 : sys.ge ({0, 1} : Set (Fin 3)) ({1, 2} : Set _) := by
              rw [sys.additive ({0, 1} : Set (Fin 3)) {1, 2}]
              rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
              exact h02
            have hge_0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
              sys.trans _ _ _ hge_0_01 hge_01_12
            have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
            -- ¬ge {2} {0,1}: if ge {2} {0,1}, trans ge {0,1} {0} (mono): ge {2} {0}. ¬h20.
            -- Actually: ge {2} {0,1} + mono ge {0,1} {1}: ge {0,1} {1} by mono. Trans doesn't help.
            -- Better: ge {0} {0,1} (hge_0_01). If ge {2} {0,1}, trans ge {0,1} {0,2}?
            -- ge {0,1} {0,2} ↔ ge {1} {2}. hng_1_2. ¬ge {0,1} {0,2}.
            -- If ge {2} {0,1}: trans with hge_0_01 = ge {0} {0,1}: nope, wrong direction.
            -- ge {2} {1,2} via additivity ↔ ge ∅ {1} = hn1. True.
            have hge_2_12 : sys.ge {(2 : Fin 3)} ({1, 2} : Set _) := by
              rw [sys.additive {2} {1, 2}]
              rw [show ({2} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {2} = {1} from by ext x; fin_cases x <;> simp_all]
              exact hn1
            -- ¬ge {2} {0,1}: if yes, trans with ge {0,1} {0,2} ↔ ge {1} {2} (¬hng_1_2, false). Hmm.
            -- Try: if ge {2} {0,1}, and ge {0} {0,1} (hge_0_01), then:
            -- ge {0,2} {0,1} ↔ ge {2} {0} (additivity). If ¬h20 then ¬ge {2} {0}, so ¬ge {0,2} {0,1}.
            -- But ge {2} {0,1} doesn't give ge {0,2} {0,1}.
            -- Try: ge {2} {0,1}, ge {1,2} {0,2} ↔ ge {1} {0} (¬hng_1_0, false). So ¬ge {1,2} {0,2}.
            -- ge {2} {0,1}: trans with ge {0,1} {0} (mono {0} ⊆ {0,1} → ge {0,1} {0}).
            -- ge {2} {0,1} + ge {0,1} {0} → ge {2} {0}. ¬h20! Contradiction!
            have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
              fun h => h20 (sys.trans _ _ _ h
                (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))))
            -- ¬ge {1,2} {0}: if yes, trans with ge {0} {0,1} (hge_0_01): ge {1,2} {0,1}.
            -- ge {1,2} {0,1} ↔ ge {2} {0}. ¬h20. Contradiction.
            have hng_12_0 : ¬sys.ge ({1, 2} : Set (Fin 3)) {0} := by
              intro h
              have h1 := sys.trans _ _ _ h hge_0_01
              rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 1}] at h1
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all] at h1
              rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
              exact h20 h1
            refine ⟨measure_fin3 (2/3) 0 (by linarith) le_rfl (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys (2/3) 0 (by linarith) le_rfl (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hn1⟩
                ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_0_1⟩
                ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h02⟩
                ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_1_2 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_2_1⟩
                ⟨fun _ => by linarith, fun _ => hge_0_12⟩
                ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                ⟨fun h => (hng_12_0 h).elim, fun h => by linarith⟩)⟩
        · -- ¬ge {0} {2} → ge {2} {0}: a = 1/3, b = 0, c = 2/3
          have h20 : sys.ge {(2 : Fin 3)} {0} := (sys.total _ _).resolve_right h02
          have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
            sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
          -- ge {2} {1,2} via additivity ↔ ge ∅ {1} = hn1
          have hge_2_12 : sys.ge {(2 : Fin 3)} ({1, 2} : Set _) := by
            rw [sys.additive {2} {1, 2}]
            rw [show ({2} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({1, 2} : Set (Fin 3)) \ {2} = {1} from by ext x; fin_cases x <;> simp_all]
            exact hn1
          -- ge {1,2} {0,2} ↔ ge {1} {0}. hng_1_0. ¬ge {1,2} {0,2}.
          -- ge {0,2} {0,1} ↔ ge {2} {1}. hge_2_1. ge {0,2} {0,1}.
          have hge_02_01 : sys.ge ({0, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
            rw [sys.additive ({0, 2} : Set (Fin 3)) {0, 1}]
            rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
            exact hge_2_1
          -- ge {2} {0,1}: trans ge {2} {1,2} + ge {1,2} {0,1} ↔ ge {2} {0} = h20.
          have hge_12_01 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 1} : Set _) := by
            rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 1}]
            rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
            exact h20
          have hge_2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
            sys.trans _ _ _ hge_2_12 hge_12_01
          -- ¬ge {0} {1,2}: ge {1,2} {1} (mono). If ge {0} {1,2}, trans: ge {0} {2} (via mono {1,2}⊇{2}).
          -- Actually ge {1,2} {2} (mono). If ge {0} {1,2}: trans ge {1,2} {2}: hmm wrong direction.
          -- Better: ge {0,1} {0} (mono). ge {0} {0,1} via additivity ↔ ge ∅ {1} = hn1. True.
          -- Wait hn1 is ¬ge ∅ {1}. So ¬ge {0} {0,1}. Hmm.
          -- Actually: ge {0} {0,2} via additivity ↔ ge ∅ {2}. hn2 (¬). So ¬ge {0} {0,2}.
          -- ge {0,2} {0} (mono). If ge {0} {1,2}: trans ge {1,2} {0,2} ↔ ge {1} {0} (¬hng_1_0). So ¬ge {1,2} {0,2}.
          -- Hmm. If ge {0} {1,2}: ge {0,2} {1,2} ↔ ge {0} {1} = hge_0_1 (true). ge {0,2} {1,2}.
          -- ge {0} {0,2} ↔ ge ∅ {2} = hn2 (¬). So ¬ge {0} {0,2}.
          -- Can't get ¬ge {0} {1,2} easily. Let me check: mu({0})=1/3, mu({1,2})=2/3. ¬ge {0} {1,2}. True.
          -- Derive: ge {0} {1,2}. mono ge {1,2} {2}: ge {1,2} {2}. Trans: ge {0} {1,2} + ge {1,2} {2} → ge {0} {2}. h02 (¬). Contradiction!
          have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
            fun h => h02 (sys.trans _ _ _ h (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})))
          -- ge {0,1} {2}: mono ge {0,1} {0}: ge {0,1} {0}. Trans ge {0} {2}? h02 (¬). Can't.
          -- mono ge {0,1} {1}: ge {0,1} {1}. Trans ge {1} {2}? hng_1_2 (¬). Can't.
          -- So ¬ge {0,1} {2}? mu({0,1})=1/3, mu({2})=2/3. Yes, ¬ge.
          -- Derive: ge {0} {0,1} ↔ ge ∅ {1} = hn1 (¬). So ¬ge {0} {0,1}.
          -- ge {0,1} {2}: additivity (disjoint). Can't simplify.
          -- If ge {0,1} {2}: ge {0,1} {0,2} ↔ ge {1} {2} (hng_1_2, ¬). So ¬ge {0,1} {0,2}.
          -- But ge {0,1} {2} and ge {2} {0,2} ↔ ge ∅ {0} (hn0, ¬). So ¬ge {2} {0,2}.
          -- Hmm, ge {2} {1,2} (hge_2_12, true). If ge {0,1} {2}: trans ge {2} {1,2}: ge {0,1} {1,2}.
          -- ge {0,1} {1,2} ↔ ge {0} {2}. h02 (¬). Contradiction!
          have hng_01_2 : ¬sys.ge ({0, 1} : Set (Fin 3)) {2} :=
            fun h => h02 (by
              have h1 := sys.trans _ _ _ h hge_2_12
              rw [sys.additive ({0, 1} : Set (Fin 3)) {1, 2}] at h1
              rw [show ({0, 1} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all] at h1
              exact h1)
          -- ¬ge {0,2} {1}: mu({0,2})=1, mu({1})=0. ge {0,2} {1} should be true!
          -- Wait, b=0 means mu({1})=0, mu({0,2})=1. So ge {0,2} {1} is true.
          -- We already have hge_02_1 from totality with hng_1_02. Good.
          refine ⟨measure_fin3 (1/3) 0 (by linarith) le_rfl (by linarith),
            reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) 0 (by linarith) le_rfl (by linarith)
              (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
              (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
              ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hn1⟩
              ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_0_1⟩
              ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
              ⟨fun h => (h02 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h20⟩
              ⟨fun h => (hng_1_2 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_2_1⟩
              ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_2_01⟩
              ⟨fun h => (hng_01_2 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_02_1⟩
              ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 1 null: {2} null, {0},{1} non-null → c=0
        have mono2 := sys.mono _ _ (Set.empty_subset ({2} : Set (Fin 3)))
        have hng_2_0 : ¬sys.ge {(2 : Fin 3)} {0} :=
          fun h => hn0 (sys.trans _ _ _ hn2 h)
        have hng_2_1 : ¬sys.ge {(2 : Fin 3)} {1} :=
          fun h => hn1 (sys.trans _ _ _ hn2 h)
        have hge_0_2 : sys.ge {(0 : Fin 3)} {2} := (sys.total _ _).resolve_right hng_2_0
        have hge_1_2 : sys.ge {(1 : Fin 3)} {2} := (sys.total _ _).resolve_right hng_2_1
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))))
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))))
        have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) :=
          fun h => hn0 (sys.trans _ _ _ hn2 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _))))))
        have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right hng_2_01
        have hng_2_02 : ¬sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
          rw [sys.additive {2} {0, 2}]
          rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
          rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all]
          exact hn0
        have hng_2_12 : ¬sys.ge {(2 : Fin 3)} ({1, 2} : Set _) := by
          rw [sys.additive {2} {1, 2}]
          rw [show ({2} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
          rw [show ({1, 2} : Set (Fin 3)) \ {2} = {1} from by ext x; fin_cases x <;> simp_all]
          exact hn1
        by_cases h01 : sys.ge {(0 : Fin 3)} {1}
        · by_cases h10 : sys.ge {(1 : Fin 3)} {0}
          · -- Tie: a = 1/2, b = 1/2
            have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
            have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
              sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
            have hge_0_02 : sys.ge {(0 : Fin 3)} ({0, 2} : Set _) := by
              rw [sys.additive {0} {0, 2}]
              rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all]
              exact hn2
            have hge_02_12 : sys.ge ({0, 2} : Set (Fin 3)) ({1, 2} : Set _) := by
              rw [sys.additive ({0, 2} : Set (Fin 3)) {1, 2}]
              rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
              exact h01
            have hge_0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
              sys.trans _ _ _ hge_0_02 hge_02_12
            have hge_1_12 : sys.ge {(1 : Fin 3)} ({1, 2} : Set _) := by
              rw [sys.additive {1} {1, 2}]
              rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all]
              exact hn2
            have hge_12_02 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 2} : Set _) := by
              rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              exact h10
            have hge_1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
              sys.trans _ _ _ hge_1_12 hge_12_02
            refine ⟨measure_fin3 (1/2) (1/2) (by linarith) (by linarith) (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys (1/2) (1/2) (by linarith) (by linarith) (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hn2⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun _ => by linarith, fun _ => h10⟩
                ⟨fun _ => by linarith, fun _ => hge_0_2⟩
                ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_2⟩
                ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_0_12⟩
                ⟨fun _ => by linarith, fun _ => hge_1_02⟩
                ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
          · -- Strict {0} > {1}: a = 2/3, b = 1/3
            have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
              fun h => h10 (sys.trans _ _ _ h (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))))
            have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right hng_1_02
            have hge_0_02 : sys.ge {(0 : Fin 3)} ({0, 2} : Set _) := by
              rw [sys.additive {0} {0, 2}]
              rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
              rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all]
              exact hn2
            have hge_02_12 : sys.ge ({0, 2} : Set (Fin 3)) ({1, 2} : Set _) := by
              rw [sys.additive ({0, 2} : Set (Fin 3)) {1, 2}]
              rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
              exact h01
            have hge_0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
              sys.trans _ _ _ hge_0_02 hge_02_12
            -- ¬ge {1,2} {0}: If ge {1,2} {0}, trans ge {0} {0,1} (mono): ge {1,2} {0,1}.
            -- ge {1,2} {0,1} ↔ ge {2} {0} (additivity). hng_2_0. Contradiction.
            have hng_12_0 : ¬sys.ge ({1, 2} : Set (Fin 3)) {0} := by
              intro h
              -- Trans: ge {1,2} {0} + ge {0} {0,2} → ge {1,2} {0,2}
              have h1 := sys.trans _ _ _ h hge_0_02
              -- ge {1,2} {0,2} ↔ ge {1} {0} (additivity). ¬h10. Contradiction.
              rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}] at h1
              rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all] at h1
              rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
              exact h10 h1
            refine ⟨measure_fin3 (2/3) (1/3) (by linarith) (by linarith) (by linarith),
              reduce_to_disjoint sys _ (fin3_dispatch sys (2/3) (1/3) (by linarith) (by linarith) (by linarith)
                (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hn2⟩
                ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => h01⟩
                ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_0_2⟩
                ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_1_2⟩
                ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_0_12⟩
                ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                ⟨fun h => (hng_12_0 h).elim, fun h => by linarith⟩)⟩
        · -- ¬ge {0} {1} → ge {1} {0}: a = 1/3, b = 2/3
          have h10 : sys.ge {(1 : Fin 3)} {0} := (sys.total _ _).resolve_right h01
          have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) :=
            fun h => h01 (sys.trans _ _ _ h (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))))
          have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right hng_0_12
          have hge_1_12 : sys.ge {(1 : Fin 3)} ({1, 2} : Set _) := by
            rw [sys.additive {1} {1, 2}]
            rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all]
            exact hn2
          have hge_12_02 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 2} : Set _) := by
            rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}]
            rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
            exact h10
          have hge_1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _) :=
            sys.trans _ _ _ hge_1_12 hge_12_02
          have hge_0_02 : sys.ge {(0 : Fin 3)} ({0, 2} : Set _) := by
            rw [sys.additive {0} {0, 2}]
            rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
            rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all]
            exact hn2
          have hng_02_1 : ¬sys.ge ({0, 2} : Set (Fin 3)) {1} :=
            fun h => h01 (sys.trans _ _ _ hge_0_02 h)
          have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
            sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) hge_1_2
          refine ⟨measure_fin3 (1/3) (2/3) (by linarith) (by linarith) (by linarith),
            reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (2/3) (by linarith) (by linarith) (by linarith)
              (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
              (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
              ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
              ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hn2⟩
              ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
              ⟨fun h => (h01 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => h10⟩
              ⟨fun _ => by linarith, fun _ => hge_0_2⟩
              ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_1_2⟩
              ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
              ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_1_02⟩
              ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_01_2⟩
              ⟨fun h => (hng_02_1 h).elim, fun h => by linarith⟩
              ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
      · -- 0 null: all non-null
        -- ¬ge ∅ {i,j} for all pairs (from ¬ge ∅ {i} + mono)
        have hng_e_01 : ¬sys.ge ∅ ({0, 1} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))))
        have hng_e_02 : ¬sys.ge ∅ ({0, 2} : Set (Fin 3)) :=
          fun h => hn0 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))))
        have hng_e_12 : ¬sys.ge ∅ ({1, 2} : Set (Fin 3)) :=
          fun h => hn1 (sys.trans _ _ _ h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))))
        -- Case split on pairwise orderings
        by_cases h01 : sys.ge {(0 : Fin 3)} {1}
        · by_cases h12 : sys.ge {(1 : Fin 3)} {2}
          · -- ge {0} {1}, ge {1} {2} → ge {0} {2} by trans
            have h02 : sys.ge {(0 : Fin 3)} {2} := sys.trans _ _ _ h01 h12
            -- Sub-case on h10
            by_cases h10 : sys.ge {(1 : Fin 3)} {0}
            · -- {0} ~ {1} ≥ {2}. Sub-case on h21
              by_cases h21 : sys.ge {(2 : Fin 3)} {1}
              · -- {0} ~ {1} ~ {2}: a=1/3, b=1/3
                have h20 : sys.ge {(2 : Fin 3)} {0} := sys.trans _ _ _ h21 h10
                -- Pair-vs-singleton: all ge (pair ≥ singleton)
                -- ge {0,1} {2}: mono from {0} ⊆ {0,1}, then h02
                have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                -- Singleton-vs-pair: ¬ge (1/3 < 2/3)
                -- ¬ge {0} {1,2}: if yes, trans with mono {1,2}⊇{2}: ge {0} {2}. OK that's fine, not a contradiction.
                -- Better: ge {0} {1,2} + ge {1,2} {0,2} ↔ ge {1} {0} (h10 true). So ge {0} {0,2}.
                -- ge {0} {0,2} ↔ ge ∅ {2} (additivity). hn2 (¬). Contradiction!
                have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) := fun h => by
                  have h1 : sys.ge {(0 : Fin 3)} ({0, 2} : Set _) := by
                    have hge_12_02 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 2} : Set _) := by
                      rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}]
                      rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
                      exact h10
                    exact sys.trans _ _ _ h hge_12_02
                  rw [sys.additive {0} {0, 2}] at h1
                  rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn2 h1
                have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := fun h => by
                  have h1 : sys.ge {(1 : Fin 3)} ({1, 2} : Set _) := by
                    have hge_02_12 : sys.ge ({0, 2} : Set (Fin 3)) ({1, 2} : Set _) := by
                      rw [sys.additive ({0, 2} : Set (Fin 3)) {1, 2}]
                      rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      exact h01
                    exact sys.trans _ _ _ h hge_02_12
                  rw [sys.additive {1} {1, 2}] at h1
                  rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn2 h1
                have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) := fun h => by
                  have h1 : sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
                    have hge_01_02 : sys.ge ({0, 1} : Set (Fin 3)) ({0, 2} : Set _) := by
                      rw [sys.additive ({0, 1} : Set (Fin 3)) {0, 2}]
                      rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
                      exact h12
                    exact sys.trans _ _ _ h hge_01_02
                  rw [sys.additive {2} {0, 2}] at h1
                  rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn0 h1
                refine ⟨measure_fin3 (1/3) (1/3) (by linarith) (by linarith) (by linarith),
                  reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (1/3) (by linarith) (by linarith) (by linarith)
                    (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                    (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                    ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h01⟩
                    ⟨fun _ => by linarith, fun _ => h10⟩
                    ⟨fun _ => by linarith, fun _ => h02⟩
                    ⟨fun _ => by linarith, fun _ => h20⟩
                    ⟨fun _ => by linarith, fun _ => h12⟩
                    ⟨fun _ => by linarith, fun _ => h21⟩
                    ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                    ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                    ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- {0} ~ {1} > {2}: a=2/5, b=2/5
                -- Have: h01, h10, h12, h02 (trans), ¬h21
                -- Derive h20: totality with ¬h02? No, h02 is true. By_cases h20.
                -- ge {2} {0}: if yes, trans ge {2} {0} + ge {0} {1} → ge {2} {1}. ¬h21. Contradiction.
                have hng_2_0 : ¬sys.ge {(2 : Fin 3)} {0} :=
                  fun h => h21 (sys.trans _ _ _ h h01)
                -- Pair-vs-singleton
                have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                -- Singleton-vs-pair: same derivation as all-tied
                have hng_0_12 : ¬sys.ge {(0 : Fin 3)} ({1, 2} : Set _) := fun h => by
                  have h1 : sys.ge {(0 : Fin 3)} ({0, 2} : Set _) := by
                    have hge_12_02 : sys.ge ({1, 2} : Set (Fin 3)) ({0, 2} : Set _) := by
                      rw [sys.additive ({1, 2} : Set (Fin 3)) {0, 2}]
                      rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
                      exact h10
                    exact sys.trans _ _ _ h hge_12_02
                  rw [sys.additive {0} {0, 2}] at h1
                  rw [show ({0} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({0, 2} : Set (Fin 3)) \ {0} = {2} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn2 h1
                have hng_1_02 : ¬sys.ge {(1 : Fin 3)} ({0, 2} : Set _) := fun h => by
                  have h1 : sys.ge {(1 : Fin 3)} ({1, 2} : Set _) := by
                    have hge_02_12 : sys.ge ({0, 2} : Set (Fin 3)) ({1, 2} : Set _) := by
                      rw [sys.additive ({0, 2} : Set (Fin 3)) {1, 2}]
                      rw [show ({0, 2} : Set (Fin 3)) \ {1, 2} = {0} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({1, 2} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      exact h01
                    exact sys.trans _ _ _ h hge_02_12
                  rw [sys.additive {1} {1, 2}] at h1
                  rw [show ({1} : Set (Fin 3)) \ {1, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({1, 2} : Set (Fin 3)) \ {1} = {2} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn2 h1
                have hng_2_01 : ¬sys.ge {(2 : Fin 3)} ({0, 1} : Set _) := fun h => by
                  have h1 : sys.ge {(2 : Fin 3)} ({0, 2} : Set _) := by
                    have hge_01_02 : sys.ge ({0, 1} : Set (Fin 3)) ({0, 2} : Set _) := by
                      rw [sys.additive ({0, 1} : Set (Fin 3)) {0, 2}]
                      rw [show ({0, 1} : Set (Fin 3)) \ {0, 2} = {1} from by ext x; fin_cases x <;> simp_all]
                      rw [show ({0, 2} : Set (Fin 3)) \ {0, 1} = {2} from by ext x; fin_cases x <;> simp_all]
                      exact h12
                    exact sys.trans _ _ _ h hge_01_02
                  rw [sys.additive {2} {0, 2}] at h1
                  rw [show ({2} : Set (Fin 3)) \ {0, 2} = ∅ from by ext x; fin_cases x <;> simp_all] at h1
                  rw [show ({0, 2} : Set (Fin 3)) \ {2} = {0} from by ext x; fin_cases x <;> simp_all] at h1
                  exact hn0 h1
                refine ⟨measure_fin3 (2/5) (2/5) (by linarith) (by linarith) (by linarith),
                  reduce_to_disjoint sys _ (fin3_dispatch sys (2/5) (2/5) (by linarith) (by linarith) (by linarith)
                    (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                    (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                    ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h01⟩
                    ⟨fun _ => by linarith, fun _ => h10⟩
                    ⟨fun _ => by linarith, fun _ => h02⟩
                    ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h12⟩
                    ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                    ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                    ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
            · -- {0} > {1} ≥ {2}. Sub-case on h21
              by_cases h21 : sys.ge {(2 : Fin 3)} {1}
              · -- {0} > {1} ~ {2}: a=3/5, b=1/5. h01, ¬h10, h12, h21, h02(trans)
                -- ¬h20: trans h12 h → ge {1}{0}. ¬h10.
                have hng_2_0 : ¬sys.ge {(2 : Fin 3)} {0} :=
                  fun h => h10 (sys.trans _ _ _ h12 h)
                -- hge_0_12: ge {0} {1,2}. Derive: ge {0} {0,1} (add ↔ ge ∅ {1} reversed)
                -- Actually: h0_12 ↔ a ≥ 1-a = 3/5 ≥ 2/5. True.
                -- Route: ge {0,1} {1,2} (add ↔ ge {0} {2} = h02). ge {0} {0,1} (add ↔ ge ∅ {1}... ¬hn1).
                -- Better: ge {0} {1} (h01) + ge {1} {1,2} (add ↔ ge ∅ {2}... ¬hn2). Hmm.
                -- Use: ge {0} {2} (h02) + ge {2} {1,2} (add ↔ ge ∅ {1}... ¬hn1). Hmm.
                -- ge {i} {i,k} ↔ ge ∅ {k}. Since ¬hn_k, this is FALSE not true.
                -- So ge {0} {0,2} is FALSE (add ↔ ge ∅ {2}, ¬hn2). And ge {1} {1,2} is FALSE.
                -- Need a different route. ge {0} {1,2} directly:
                -- mono ge {0} ⊆ {0,1}: ge {0,1} {0}. Then ge {0} {1,2} + ge {1,2} {0,1}?
                -- ge {1,2} {0,1} ↔ ge {2} {0} (add). ¬hng_2_0. FALSE.
                -- ge {0} {1,2} + ge {0,1} {1,2} (add ↔ ge {0} {2} = h02): ge {0,1} {1,2}. True.
                -- Hmm, I need ge {0} {1,2}, not ge {0,1} {1,2}.
                -- Try: ge {0} {1} (h01). ge {0} {2} (h02). ge {0} {1,2}?
                -- Need: for any C D, ge {0} C and ge {0} D implies ge {0} (C ∪ D)?
                -- Not directly from axioms. Let's use additivity on {0} vs {1,2}:
                -- ge {0} {1,2} ↔ ge ({0}\{1,2}) ({1,2}\{0}) = ge {0} {1,2}. That's circular.
                -- Actually additivity says ge A B ↔ ge (A\B) (B\A). For disjoint A,B: A\B=A, B\A=B.
                -- So ge {0} {1,2} ↔ ge {0} {1,2}. Circular.
                -- So {0} vs {1,2} IS already disjoint. I need to prove it from the ordering facts.
                -- ge {0} {1} (h01) means a ≥ b. ge {0} {2} (h02) means a ≥ c.
                -- ge {0} {1,2} ↔ a ≥ b+c = 1-a ↔ 2a ≥ 1 ↔ a ≥ 1/2. With a=3/5, yes.
                -- But I need to DERIVE this from the system axioms, not just check arithmetic.
                -- The system has: ge {0} {1}, ge {0} {2}, ¬ge {1} {0}, ¬ge {2} {0}.
                -- ge {0} {1,2}: additivity on {0,2} vs {1,2}: ge {0,2} {1,2} ↔ ge {0} {1} (h01). True.
                -- ge {0} {0,2}: add ↔ ge ∅ {2}. FALSE (hn2).
                -- ge {0,2} {1,2} (true from above). ge {0} {0,2}... false.
                -- Hmm, that gives ge {0,2} {1,2} but not ge {0} {1,2}.
                -- Try: ge {0,1} {1,2} (add ↔ ge {0} {2} = h02). True.
                -- ge {0} {0,1} (add ↔ ge ∅ {1}). FALSE (hn1).
                -- Need monotonicity-like property for unions? Not available.
                -- Actually: BT gives ge Univ ∅. ge Univ {0,1,2}. mono from {0,1,2} = Univ.
                -- We have ge ∅ Univ and ge Univ ∅ (reflexivity on Univ and bottom).
                -- Hmm, this is getting complicated. Let me try a DIFFERENT measure value.
                -- For a=3/5, we need ge {0} {1,2} which requires proving 2a ≥ 1 from the axioms.
                -- What if I use a=1/2, b=1/4, c=1/4 instead? Then:
                -- h0_12: 1/2 ≥ 1/2. TRUE (tie). h1_02: 1/4 ≥ 3/4. FALSE. h2_01: 1/4 ≥ 3/4. FALSE.
                -- h01_2: 3/4 ≥ 1/4. TRUE. h02_1: 3/4 ≥ 1/4. TRUE. h12_0: 1/2 ≥ 1/2. TRUE (tie).
                -- So with a=1/2, b=1/4: ge {0} {1,2} ↔ 1/2 ≥ 1/2 TRUE, ge {1,2} {0} ↔ 1/2 ≥ 1/2 TRUE.
                -- That means I need BOTH hge_0_12 and hge_12_0. Those are easier to derive.
                -- hge_12_0: mono {1} ⊆ {1,2}, trans with h10... wait ¬h10.
                -- hge_12_0: if ¬ge {1,2} {0}: ge {0} {1,2} (totality). Then ge {0} {0,1} (add ↔ ge ∅ {1} = hn1, FALSE). Hmm.
                -- Actually let me directly derive ge {1,2} {0}:
                -- ge {1,2} {0,2} (add ↔ ge {1} {0}). ¬h10. FALSE.
                -- ge {1,2} {0,1} (add ↔ ge {2} {0}). hng_2_0. FALSE.
                -- So ¬ge {1,2} {0,2} and ¬ge {1,2} {0,1}. But I need ge {1,2} {0}.
                -- ge {2} {0,2} (add ↔ ge ∅ {0}). FALSE (hn0). So ¬ge {2} {0,2}.
                -- mono {2} ⊆ {1,2}: ge {1,2} {2}. trans with h12 gives ge {1,2} {2} (trivially).
                -- I can get ge {1,2} {0} from ge {1,2} {2} + ge {2} {0}? No, hng_2_0.
                -- I'm stuck. ge {1,2} {0} seems unprovable from h01, h12, h21, ¬h10, ¬h20.
                -- With a=1/2, b=1/4: h12_0 ↔ 1/2 ≥ 1/2 is a tie. So ge {1,2} {0} should hold.
                -- But derivationally, without some chain that produces this...
                -- Use a value where h12_0 is strictly true or strictly false.
                -- a=2/5, b=1/5: c=2/5. h01: 2/5≥1/5 T. h10: 1/5≥2/5 F ✓. h12: 1/5≥2/5 F!
                -- No good, we need h12 TRUE.
                -- a=1/2, b=1/3: c=1/6. h01: 1/2≥1/3 T. h10: 1/3≥1/2 F ✓. h12: 1/3≥1/6 T ✓. h21: 1/6≥1/3 F ✓.
                -- Wait but this case is {0}>{1}~{2} which requires h12 AND h21.
                -- h12 true h21 true means b=c. So b=1-a-b means 2b=1-a. Also ¬h10: b<a. ¬h20: c<a, same as b<a.
                -- a=1/2, b=1/4, c=1/4. h12: 1/4≥1/4 T. h21: 1/4≥1/4 T. ¬h10: 1/4<1/2 ✓. ¬h20: 1/4<1/2 ✓.
                -- h0_12: 1/2 ≥ 1/2 T. h12_0: 1/2 ≥ 1/2 T. BOTH are ties!
                -- So I need both hge_0_12 AND hge_12_0.
                -- Derive hge_0_12: need ge {0} {1,2}. ???
                -- This is hard. Let me try to see if the 0-null case with {0}>{1}~{2} can avoid
                -- singleton vs pair issues by noting it reduces to fewer cases.
                -- INSIGHT: For {0}>{1}~{2}, we have {1}~{2}. So {1,2} has measure 2b = 1-a.
                -- ge {0} {1,2} ↔ a ≥ 1-a. With 2b=1-a and a>b: a > (1-a)/2, so 2a > 1-a, 3a > 1, a > 1/3.
                -- But a > 1/3 doesn't mean a ≥ 1-a (i.e., a ≥ 1/2).
                -- If a < 1/2: ¬ge {0} {1,2} and ge {1,2} {0}.
                -- If a = 1/2: tie.
                -- If a > 1/2: ge {0} {1,2} and ¬ge {1,2} {0}.
                -- So the truth value of h0_12 depends on whether a ≥ 1/2 or not.
                -- But from the axioms alone (h01, ¬h10, h12, h21), we can't determine this!
                -- This means I need to FURTHER SPLIT on ge {0} {1,2}.
                -- Sigh. Let me add a by_cases.
                by_cases h0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _)
                · -- ge {0} {1,2}: h12_0 also true (by totality? no, both can hold).
                  -- a ≥ 1-a. Use a=3/5, b=1/5. Then 1-a=2/5 ≤ 3/5. h12_0: 2/5 ≥ 3/5? FALSE.
                  -- So ¬ge {1,2} {0}.
                  -- ¬h12_0: if ge {1,2} {0}: trans with h0_12: ge {1,2} {1,2}. Reflexivity, always true. No contradiction.
                  -- Need different route. ge {1,2} {0,1} (add ↔ ge {2} {0}). hng_2_0. FALSE.
                  -- ge {1,2} {0} + ge {0} {0,1} (add ↔ ge ∅ {1}, hn1, FALSE). Can't chain.
                  -- ge {1,2} {0}: mono {1} ⊆ {1,2} gives ge {1,2} {1}. ¬useful directly.
                  -- ge {0} {1,2} (h0_12). If also ge {1,2} {0}: ge {0} {0} (trans). Always true, no contradiction.
                  -- ¬ge {1,2} {0}: need to derive from axioms + h0_12 + ...
                  -- Hmm. Can I derive ¬ge {1,2} {0} from ge {0} {1,2}?
                  -- ge {0} {1,2} and ge {1,2} {0} means {0} ~ {1,2}. Then mu({0}) = mu({1,2}) = 1-mu({0}), so mu({0}) = 1/2.
                  -- From ¬h10 (a > b) and h12, h21 (b = c): a > b, b = c, a + 2b = 1, a = 1/2 means b = 1/4.
                  -- ge {0} {1,2} and ge {1,2} {0} is CONSISTENT with the axioms. So I can't prove ¬ge {1,2} {0} from h0_12 alone.
                  -- I need ANOTHER by_cases on h12_0.
                  -- This is getting very nested. Let me step back and think about a better approach.
                  -- ACTUALLY: the measure values just need to be CONSISTENT. If both h0_12 and h12_0 hold:
                  -- a = 1/2, b = 1/4. All good.
                  -- If h0_12 and ¬h12_0: a > 1/2. Use a = 3/5, b = 1/5.
                  -- In both cases the remaining facts are the same except h12_0/¬h12_0.
                  by_cases h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0}
                  · -- ge {0} {1,2} AND ge {1,2} {0}: tie. a=1/2, b=1/4
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hng_2_01 := nge_2_01 sys h12 hn0
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (1/2) (1/4) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/2) (1/4) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
                  · -- ge {0} {1,2} but ¬ge {1,2} {0}: a=3/5, b=1/5
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hng_2_01 := nge_2_01 sys h12 hn0
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (3/5) (1/5) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (3/5) (1/5) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun h => (h12_0 h).elim, fun h => by linarith⟩)⟩
                · -- ¬ge {0} {1,2}: ge {1,2} {0} by totality. a=2/5, b=3/10... hmm
                  -- a < 1-a means a < 1/2. b = (1-a)/2. a > b iff a > (1-a)/2 iff 2a > 1-a iff 3a > 1 iff a > 1/3.
                  -- Use a=2/5, b=3/10, c=3/10. h01: 2/5≥3/10 T. h12: 3/10≥3/10 T. h0_12: 2/5≥3/5 F ✓.
                  -- h12_0: 3/5≥2/5 T. h1_02: 3/10≥7/10 F. h2_01: 3/10≥7/10 F.
                  have h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right h0_12
                  have hng_1_02 := nge_1_02 sys h01 hn2
                  have hng_2_01 := nge_2_01 sys h12 hn0
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                  refine ⟨measure_fin3 (2/5) (3/10) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (2/5) (3/10) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01⟩
                      ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h02⟩
                      ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h12⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (h0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
              · -- {0} > {1} > {2}: a=1/2, b=1/3. h01, ¬h10, h12, ¬h21, h02(trans)
                -- ¬h20: trans h12 h → ge {1}{0}, ¬h10.
                have hng_2_0 : ¬sys.ge {(2 : Fin 3)} {0} :=
                  fun h => h10 (sys.trans _ _ _ h12 h)
                -- Need by_cases on ge {0} {1,2} again: a≥1-a iff a≥1/2.
                -- Use a=1/2, b=1/3: h0_12: 1/2≥1/2 T (tie). h12_0: 1/2≥1/2 T (tie).
                -- But deriving ge {0} {1,2} from axioms is the same problem.
                -- Use a=1/3, b=1/4: c=5/12. h01: 1/3≥1/4 T. h12: 1/4≥5/12 F! No good.
                -- In this case h12 is TRUE and h21 is FALSE. So b > c strictly.
                -- a > b > c > 0. I need specific values. a=1/2, b=1/3, c=1/6 works.
                -- h0_12: 1/2 ≥ 1/2 T (tie). Both true.
                -- Or a=3/6=1/2, b=2/6=1/3, c=1/6.
                -- With these, h0_12 and h12_0 are both ties.
                -- Since I can't easily derive ge {0} {1,2}, let me by_cases.
                by_cases h0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _)
                · by_cases h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0}
                  · -- Both tie: a=1/2, b=1/3
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (1/2) (1/3) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/2) (1/3) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
                  · -- ge {0} {1,2} but ¬ge {1,2} {0}: a=3/5, b=4/15 (a>1/2)
                    -- Use a=3/5, b=4/15, c=1/5? Check: b>c: 4/15>1/5=3/15 ✓. a>b: 3/5=9/15>4/15 ✓.
                    -- h0_12: 3/5≥2/5 T. h12_0: 2/5≥3/5 F ✓.
                    -- h1_02: 4/15≥11/15 F. h2_01: 1/5≥4/5 F.
                    -- h01_2: 13/15≥1/5 T. h02_1: 11/15≥4/15 T.
                    -- Hmm awkward fractions. Use a=2/3, b=1/4, c=1/12.
                    -- h01: 2/3≥1/4 T. h12: 1/4≥1/12 T. h0_12: 2/3≥1/3 T. h12_0: 1/3≥2/3 F ✓.
                    -- Actually any a,b with a > b > 1-a-b > 0 and a > 1/2 works.
                    -- Simplest: a=3/5, b=1/4, c=3/20. But ugly fractions.
                    -- Use a=5/9, b=3/9=1/3, c=1/9. h01: 5/9≥1/3 T. h12: 1/3≥1/9 T. h0_12: 5/9≥4/9 T. h12_0: 4/9≥5/9 F ✓.
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (5/9) (1/3) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (5/9) (1/3) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun h => (h12_0 h).elim, fun h => by linarith⟩)⟩
                · -- ¬ge {0} {1,2}: ge {1,2} {0} by totality. a=2/5, b=1/3, c=4/15
                  -- a < 1/2. a > b > c > 0. Use a=5/12, b=1/3, c=1/4.
                  -- h01: 5/12≥1/3=4/12 T. h12: 1/3=4/12≥1/4=3/12 T. h0_12: 5/12≥7/12 F ✓.
                  -- h12_0: 7/12≥5/12 T.
                  have h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right h0_12
                  have hng_1_02 := nge_1_02 sys h01 hn2
                  have hng_2_01 := nge_2_01' sys h02 hn1
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                  refine ⟨measure_fin3 (5/12) (1/3) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (5/12) (1/3) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01⟩
                      ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h02⟩
                      ⟨fun h => (hng_2_0 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h12⟩
                      ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
          · -- ge {0} {1}, ¬ge {1} {2} → ge {2} {1}
            have h21 : sys.ge {(2 : Fin 3)} {1} := (sys.total _ _).resolve_right h12
            -- Sub-case on h02
            by_cases h02 : sys.ge {(0 : Fin 3)} {2}
            · -- {0} ≥ {2} > {1}. h01, h02, h21, ¬h12
              -- ¬h10: if h10, trans h10 h21 → h01... that's true. No contradiction from h10 directly.
              -- ¬h10: not necessarily! h10 could be true ({0}~{1}). But then h12 would... no.
              -- Actually h01 (ge{0}{1}) is given. ¬h12 is given. h21 is derived.
              -- Sub-case on h20
              by_cases h20 : sys.ge {(2 : Fin 3)} {0}
              · -- {0} ~ {2} > {1}: h01, h02, h20, h21, ¬h12
                -- ¬h10: if h10, trans h10 h01... no, h10 is ge{1}{0}, trans with what?
                -- h10 and h01: {0}~{1}. h21: ge{2}{1}. ¬h12: ¬ge{1}{2}. OK {0}~{1} and {2}>{1}.
                -- trans h02 h21: ge{0}{1} (h01, already known). No new info.
                -- ¬h10: can I prove? If h10: ge{1}{0}. trans h21 h10: ge{2}{0} (h20, true). No contradiction.
                -- So h10 is undetermined. Need by_cases on h10.
                -- a=c, a ≥ b, c > b (since h21 and ¬h12). So a=c > b.
                -- h10 ↔ b ≥ a. Since a > b, h10 is FALSE.
                -- Derive: if h10 (ge{1}{0}): and h01 (ge{0}{1}): tie {0}~{1}.
                --   h02 (ge{0}{2}), h20 (ge{2}{0}): tie {0}~{2}. So {0}~{1}~{2}.
                --   Then h12 should hold (ge{1}{2}). But ¬h12. Contradiction!
                have hng_1_0 : ¬sys.ge {(1 : Fin 3)} {0} :=
                  fun hh => h12 (sys.trans _ _ _ hh h02)
                -- All singleton-vs-pair: ¬ge. All pair-vs-singleton: ge.
                -- by_cases on h0_12 (like {0}>{1}~{2}).
                -- Actually: with a=c > b, h0_12 ↔ a ≥ 1-a = a ≥ c+b = a ≥ a+b. FALSE (b>0).
                -- Wait, 1-a = b+c = b+a (since a=c). So 1-a = a+b → 1 = 2a+b. And a ≥ 1-a iff a ≥ a+b iff b ≤ 0. FALSE.
                -- Hmm that means ¬h0_12 always! Wait: 1-a-b = c = 2/5 when a=2/5,b=1/5.
                -- 1-a = 3/5 = b+c. h0_12: a≥1-a = 2/5≥3/5 F. h2_01: c≥a+b = 2/5≥3/5 F.
                -- h1_02: b≥1-b = 1/5≥4/5 F. All singleton-vs-pair FALSE.
                -- h01_2: a+b≥c = 3/5≥2/5 T. h02_1: 1-b≥b = 4/5≥1/5 T. h12_0: 1-a≥a = 3/5≥2/5 T.
                have hng_0_12 := nge_0_12' sys h20 hn1
                have hng_1_02 := nge_1_02 sys h01 hn2
                have hng_2_01 := nge_2_01' sys h02 hn1
                have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                refine ⟨measure_fin3 (2/5) (1/5) (by linarith) (by linarith) (by linarith),
                  reduce_to_disjoint sys _ (fin3_dispatch sys (2/5) (1/5) (by linarith) (by linarith) (by linarith)
                    (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                    (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                    ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h01⟩
                    ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h02⟩
                    ⟨fun _ => by linarith, fun _ => h20⟩
                    ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h21⟩
                    ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                    ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                    ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- {0} > {2} > {1}: h01, h02, ¬h20, h21, ¬h12. a > c > b.
                -- ¬h10: if h10, trans h10 h02 → ge{1}{2}. ¬h12! Contradiction.
                have hng_1_0 : ¬sys.ge {(1 : Fin 3)} {0} :=
                  fun hh => h12 (sys.trans _ _ _ hh h02)
                -- By symmetry with {0}>{1}>{2} case but with 1↔2 swap.
                -- Need by_cases on h0_12: ge {0} {1,2} ↔ a ≥ 1-a.
                by_cases h0_12 : sys.ge {(0 : Fin 3)} ({1, 2} : Set _)
                · by_cases h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0}
                  · -- Tie: a=1/2, b=1/6, c=1/3
                    have hng_1_02 := nge_1_02' sys h21 hn0
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (1/2) (1/6) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/2) (1/6) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
                  · -- a=5/9, b=1/9, c=1/3
                    have hng_1_02 := nge_1_02' sys h21 hn0
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    refine ⟨measure_fin3 (5/9) (1/9) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (5/9) (1/9) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun _ => by linarith, fun _ => h0_12⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun h => (h12_0 h).elim, fun h => by linarith⟩)⟩
                · -- ¬ge {0} {1,2}: a=5/12, b=1/4, c=1/3
                  have h12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} := (sys.total _ _).resolve_right h0_12
                  have hng_1_02 := nge_1_02' sys h21 hn0
                  have hng_2_01 := nge_2_01' sys h02 hn1
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                  refine ⟨measure_fin3 (5/12) (1/4) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (5/12) (1/4) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01⟩
                      ⟨fun h => (hng_1_0 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h02⟩
                      ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (h0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => h12_0⟩)⟩
            · -- ¬ge {0} {2} → ge {2} {0}
              have h20 : sys.ge {(2 : Fin 3)} {0} := (sys.total _ _).resolve_right h02
              -- {2} > {0} ≥ {1}: h01, ¬h02, h20, h21, ¬h12. c > a ≥ b.
              -- Need by_cases on h10 (whether a = b or a > b).
              by_cases h10 : sys.ge {(1 : Fin 3)} {0}
              · -- {2} > {0} ~ {1}: c > a = b. Like {0}~{2}>{1} case above but rotated.
                -- a=1/5, b=1/5, c=3/5? h2_01: 3/5≥2/5 T. h0_12: 1/5≥4/5 F. h12_0: 4/5≥1/5 T.
                -- But need by_cases on h2_01: ge {2} {0,1} ↔ c ≥ a+b.
                -- c = 1-a-b. c ≥ a+b iff 1-a-b ≥ a+b iff 1 ≥ 2(a+b). With a=b: 1 ≥ 4a iff a ≤ 1/4.
                -- Can't determine from axioms. by_cases.
                by_cases h2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _)
                · by_cases h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2}
                  · -- Tie: a=1/4, b=1/4, c=1/2
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_1_02 := nge_1_02' sys h21 hn0
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                    refine ⟨measure_fin3 (1/4) (1/4) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/4) (1/4) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h2_01⟩
                        ⟨fun _ => by linarith, fun _ => h01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                  · -- a=1/5, b=1/5, c=3/5
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_1_02 := nge_1_02' sys h21 hn0
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                    refine ⟨measure_fin3 (1/5) (1/5) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/5) (1/5) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h2_01⟩
                        ⟨fun h => (h01_2 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- ¬ge {2} {0,1}: a=3/10, b=3/10, c=2/5
                  have h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right h2_01
                  have hng_0_12 := nge_0_12' sys h20 hn1
                  have hng_1_02 := nge_1_02' sys h21 hn0
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                  refine ⟨measure_fin3 (3/10) (3/10) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (3/10) (3/10) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- {2} > {0} > {1}: c > a > b. h01, ¬h10, ¬h02, h20, h21, ¬h12.
                -- by_cases on h2_01: ge {2} {0,1} ↔ c ≥ a+b.
                by_cases h2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _)
                · by_cases h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2}
                  · -- Tie: a=1/3, b=1/6, c=1/2
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                    refine ⟨measure_fin3 (1/3) (1/6) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (1/6) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h2_01⟩
                        ⟨fun _ => by linarith, fun _ => h01_2⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                  · -- a=1/4, b=1/6, c=7/12
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_1_02 := nge_1_02 sys h01 hn2
                    have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                    refine ⟨measure_fin3 (1/4) (1/6) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/4) (1/6) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h01⟩
                        ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h21⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h2_01⟩
                        ⟨fun h => (h01_2 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- a=1/3, b=1/4, c=5/12
                  have h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right h2_01
                  have hng_0_12 := nge_0_12' sys h20 hn1
                  have hng_1_02 := nge_1_02 sys h01 hn2
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({2} : Set _)))) h01
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (1 : Fin 3) {2})) h20
                  refine ⟨measure_fin3 (1/3) (1/4) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (1/4) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01⟩
                      ⟨fun h => (h10 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
        · -- ¬ge {0} {1} → ge {1} {0}
          have h10 : sys.ge {(1 : Fin 3)} {0} := (sys.total _ _).resolve_right h01
          by_cases h12 : sys.ge {(1 : Fin 3)} {2}
          · -- ge {1} {0}, ge {1} {2}: {1} biggest. h10, h12, ¬h01
            -- Symmetric to the {0} biggest branch but with 0↔1 swapped.
            -- h02: unknown. Sub-case.
            by_cases h02 : sys.ge {(0 : Fin 3)} {2}
            · -- {1} > {0} ≥ {2}. Sub-case on h20
              by_cases h20 : sys.ge {(2 : Fin 3)} {0}
              · -- {1} > {0} ~ {2}: b > a = c. Like {0}>{1}~{2} with 0↔1 swap.
                -- ¬h01: fun hh => h01 ... wait h01 is already ¬ge{0}{1}. Good.
                -- ¬h21: if h21 (ge{2}{1}), trans h21 h10 → ge{2}{0} (h20, true). No contradiction.
                -- trans h02 h20 → ge{0}{0}. No.
                -- If h21: ge{2}{1}. And h10: ge{1}{0}. trans: ge{2}{0} = h20 (true). No contradiction.
                -- h21 and h12: both could be true (tie). Need by_cases.
                -- b > a = c. h12: b ≥ c true. h21: c ≥ b false (since c = a < b).
                -- Derive ¬h21: if h21 (ge{2}{1}), trans h20 h10 → ge{2}{0} (true). No help.
                -- if h21, trans h02 (swap? no): ge{0}{2} (h02 true), ge{2}{1} (h21): trans ge{0}{1}. ¬h01! Contradiction!
                have hng_2_1 : ¬sys.ge {(2 : Fin 3)} {1} :=
                  fun hh => h01 (sys.trans _ _ _ h02 hh)
                -- {1} > {0} ~ {2}: b > a = c. h10, h12, h02, h20, ¬h01, ¬h21.
                -- Same structure as {0}~{2}>{1} case but swapping 0↔1.
                -- Need ¬h0_12 (same as nge_0_12 route), etc.
                -- nge_0_12': needs h20 (✓) and hn1 (✓)? Wait hn1 is ¬ge ∅ {1}. Yes.
                -- But wait: a = c, b > a. h0_12: a ≥ 1-a? a ≥ b+c = b+a. So 0 ≥ b. FALSE (b>0).
                -- So ¬hge_0_12, ¬hge_2_01. h1_02: b ≥ 1-b. Need b ≥ 1/2.
                -- b > a = c. a+b+c=1. b+2a=1. b=1-2a. b ≥ 1/2 iff 1-2a ≥ 1/2 iff a ≤ 1/4.
                -- Undetermined. Need by_cases on h1_02.
                by_cases h1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _)
                · by_cases h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1}
                  · -- Tie: a=1/4, b=1/2
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/4) (1/2) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/4) (1/2) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => h02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                  · -- a=1/5, b=3/5
                    have hng_0_12 := nge_0_12' sys h20 hn1
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/5) (3/5) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/5) (3/5) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun h => (h02_1 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- a=3/10, b=2/5
                  have h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right h1_02
                  have hng_0_12 := nge_0_12' sys h20 hn1
                  have hng_2_01 := nge_2_01' sys h02 hn1
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                  refine ⟨measure_fin3 (3/10) (2/5) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (3/10) (2/5) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun _ => by linarith, fun _ => h02⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun _ => by linarith, fun _ => h12⟩
                      ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => h02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- {1} > {0} > {2}: b > a > c. h10, h12, h02, ¬h01, ¬h20, ¬h21.
                have hng_2_1 : ¬sys.ge {(2 : Fin 3)} {1} :=
                  fun hh => h01 (sys.trans _ _ _ h02 hh)
                -- by_cases on h1_02: ge {1} {0,2} ↔ b ≥ 1-b.
                by_cases h1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _)
                · by_cases h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1}
                  · -- Tie: a=1/3, b=1/2, c=1/6
                    have hng_0_12 := nge_0_12 sys h10 hn2
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/3) (1/2) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (1/2) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => h02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                  · -- a=1/3, b=5/9
                    have hng_0_12 := nge_0_12 sys h10 hn2
                    have hng_2_01 := nge_2_01' sys h02 hn1
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/3) (5/9) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (5/9) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun _ => by linarith, fun _ => h02⟩
                        ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun h => (h02_1 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- a=1/3, b=5/12
                  have h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right h1_02
                  have hng_0_12 := nge_0_12 sys h10 hn2
                  have hng_2_01 := nge_2_01' sys h02 hn1
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (0 : Fin 3) ({1} : Set _)))) h02
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                  refine ⟨measure_fin3 (1/3) (5/12) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (1/3) (5/12) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun _ => by linarith, fun _ => h02⟩
                      ⟨fun h => (h20 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h12⟩
                      ⟨fun h => (hng_2_1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => h02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
            · -- ¬ge {0} {2} → ge {2} {0}
              have h20 : sys.ge {(2 : Fin 3)} {0} := (sys.total _ _).resolve_right h02
              -- Sub-case on h21
              by_cases h21 : sys.ge {(2 : Fin 3)} {1}
              · -- {1} ~ {2} > {0}: b = c > a. h10, h12, h20, h21, ¬h01, ¬h02.
                -- ¬h0_12 (nge_0_12 via h10): hn2? Or nge_0_12' via h20: hn1.
                -- Since ¬h01: ge{0}{1} false. ¬h02: ge{0}{2} false. ¬h0_12 trivially via mono:
                -- if ge{0}{1,2}, mono {1} ⊆ {1,2}: ge{1,2}{1}. trans ge{0}{1}. ¬h01. Contradiction.
                -- Wait, that's ge{0}{1,2} + ge{1,2}{1}? No. mono gives ge{1,2}{1}, not the direction I need.
                -- Actually mono {0} ⊆ {0,1}: ge{0,1}{0}. That doesn't help.
                -- Use nge_0_12 sys h10 hn2 or nge_0_12' sys h20 hn1. Both work.
                -- b = c > a. h1_02: b ≥ 1-b. Need by_cases.
                -- h2_01: c ≥ a+b = a+c → a ≤ 0. FALSE (hn0). So ¬h2_01.
                -- Wait: ¬ge ∅ {0} means a > 0 in the measure. h2_01 ↔ c ≥ a+b. c = b. a+b+c = 1. a+2b=1. c ≥ a+b = a+b. c=b. So b ≥ a+b → 0 ≥ a. But a > 0. Contradiction.
                -- So ¬h2_01 derivable! Proof: if h2_01 (ge{2}{0,1}), trans with ge{0,1}{0} (mono) → ge{2}{0}. Already known (h20). No contradiction.
                -- Hmm, that doesn't work. Let me use nge_2_01: needs h12 (ge{1}{2}) and hn0.
                -- h12 is given (positive). hn0 is given. So nge_2_01 sys h12 hn0 works!
                -- nge_2_01' uses h02 and hn1. h02 is ¬ge{0}{2} here. Doesn't work.
                have hng_0_12 := nge_0_12 sys h10 hn2
                have hng_1_02 := nge_1_02' sys h21 hn0
                have hng_2_01 := nge_2_01 sys h12 hn0
                have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
                have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
                -- mono {2} ⊆ {0,2}: ge{0,2}{2}. trans ge{2}{1} = h21. ge{0,2}{1}.
                have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                refine ⟨measure_fin3 (1/5) (2/5) (by linarith) (by linarith) (by linarith),
                  reduce_to_disjoint sys _ (fin3_dispatch sys (1/5) (2/5) (by linarith) (by linarith) (by linarith)
                    (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                    (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                    ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h10⟩
                    ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h20⟩
                    ⟨fun _ => by linarith, fun _ => h12⟩
                    ⟨fun _ => by linarith, fun _ => h21⟩
                    ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                    ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                    ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- {1} > {2} > {0}: b > c > a. h10, h12, h20, ¬h01, ¬h02, ¬h21.
                -- by_cases on h1_02: ge {1} {0,2} ↔ b ≥ 1-b.
                by_cases h1_02 : sys.ge {(1 : Fin 3)} ({0, 2} : Set _)
                · by_cases h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1}
                  · -- Tie: a=1/6, b=1/2, c=1/3
                    have hng_0_12 := nge_0_12 sys h10 hn2
                    have hng_2_01 := nge_2_01 sys h12 hn0
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/6) (1/2) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/6) (1/2) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun _ => by linarith, fun _ => h02_1⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                  · -- a=1/9, b=5/9
                    have hng_0_12 := nge_0_12 sys h10 hn2
                    have hng_2_01 := nge_2_01 sys h12 hn0
                    have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
                    have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                      sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                    refine ⟨measure_fin3 (1/9) (5/9) (by linarith) (by linarith) (by linarith),
                      reduce_to_disjoint sys _ (fin3_dispatch sys (1/9) (5/9) (by linarith) (by linarith) (by linarith)
                        (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                        (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                        ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                        ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h10⟩
                        ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h20⟩
                        ⟨fun _ => by linarith, fun _ => h12⟩
                        ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                        ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => h1_02⟩
                        ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                        ⟨fun h => (h02_1 h).elim, fun h => by linarith⟩
                        ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- a=1/4, b=5/12
                  have h02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} := (sys.total _ _).resolve_right h1_02
                  have hng_0_12 := nge_0_12 sys h10 hn2
                  have hng_2_01 := nge_2_01 sys h12 hn0
                  have hge_01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {1})) h12
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                  refine ⟨measure_fin3 (1/4) (5/12) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (1/4) (5/12) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun _ => by linarith, fun _ => h12⟩
                      ⟨fun h => (h21 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h1_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_2_01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_01_2⟩
                      ⟨fun _ => by linarith, fun _ => h02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
          · -- ¬ge {1} {2} → ge {2} {1}
            have h21 : sys.ge {(2 : Fin 3)} {1} := (sys.total _ _).resolve_right h12
            -- ge {2} {1}, ge {1} {0} → ge {2} {0}
            have h20 : sys.ge {(2 : Fin 3)} {0} := sys.trans _ _ _ h21 h10
            -- {2} ≥ {1} ≥ {0}, {2} biggest
            -- Sub-case on h02
            by_cases h02 : sys.ge {(0 : Fin 3)} {2}
            · -- impossible: ¬h01 and h02 and h21: trans h02 h21: ge{0}{1}. ¬h01. Contradiction.
              exfalso; exact h01 (sys.trans _ _ _ h02 h21)
            · -- {2} > {1} > {0}: c > b > a. h10, h20, h21, ¬h01, ¬h02, ¬h12. a=1/6, b=1/3.
              -- by_cases on h2_01: ge {2} {0,1} ↔ c ≥ a+b.
              by_cases h2_01 : sys.ge {(2 : Fin 3)} ({0, 1} : Set _)
              · by_cases h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2}
                · -- Tie: a=1/6, b=1/3, c=1/2
                  have hng_0_12 := nge_0_12 sys h10 hn2
                  have hng_1_02 := nge_1_02' sys h21 hn0
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                  refine ⟨measure_fin3 (1/6) (1/3) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (1/6) (1/3) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h2_01⟩
                      ⟨fun _ => by linarith, fun _ => h01_2⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
                · -- a=1/6, b=1/4, c=7/12
                  have hng_0_12 := nge_0_12 sys h10 hn2
                  have hng_1_02 := nge_1_02' sys h21 hn0
                  have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
                  have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                    sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                  refine ⟨measure_fin3 (1/6) (1/4) (by linarith) (by linarith) (by linarith),
                    reduce_to_disjoint sys _ (fin3_dispatch sys (1/6) (1/4) (by linarith) (by linarith) (by linarith)
                      (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                      (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                      ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h10⟩
                      ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h20⟩
                      ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h21⟩
                      ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                      ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => h2_01⟩
                      ⟨fun h => (h01_2 h).elim, fun h => by linarith⟩
                      ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                      ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩
              · -- a=1/4, b=1/3, c=5/12
                have h01_2 : sys.ge ({0, 1} : Set (Fin 3)) {2} := (sys.total _ _).resolve_right h2_01
                have hng_0_12 := nge_0_12 sys h10 hn2
                have hng_1_02 := nge_1_02' sys h21 hn0
                have hge_02_1 : sys.ge ({0, 2} : Set (Fin 3)) {1} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.subset_insert (0 : Fin 3) {2})) h21
                have hge_12_0 : sys.ge ({1, 2} : Set (Fin 3)) {0} :=
                  sys.trans _ _ _ (sys.mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert (1 : Fin 3) ({2} : Set _)))) h10
                refine ⟨measure_fin3 (1/4) (1/3) (by linarith) (by linarith) (by linarith),
                  reduce_to_disjoint sys _ (fin3_dispatch sys (1/4) (1/3) (by linarith) (by linarith) (by linarith)
                    (mf3_empty ..) (mf3_s0 ..) (mf3_s1 ..) (mf3_s2 ..)
                    (mf3_p01 ..) (mf3_p02 ..) (mf3_p12 ..) (mf3_univ ..)
                    ⟨fun h => (hn0 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn1 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hn2 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_01 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_e_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (h01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h10⟩
                    ⟨fun h => (h02 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h20⟩
                    ⟨fun h => (h12 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h21⟩
                    ⟨fun h => (hng_0_12 h).elim, fun h => by linarith⟩
                    ⟨fun h => (hng_1_02 h).elim, fun h => by linarith⟩
                    ⟨fun h => (h2_01 h).elim, fun h => by linarith⟩
                    ⟨fun _ => by linarith, fun _ => h01_2⟩
                    ⟨fun _ => by linarith, fun _ => hge_02_1⟩
                    ⟨fun _ => by linarith, fun _ => hge_12_0⟩)⟩

-- ── Card 4: Infrastructure ──────────────────────────

private noncomputable def measure_fin4 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) : FinAddMeasure (Fin 4) where
  mu := fun A =>
    (if (0 : Fin 4) ∈ A then a else 0) +
    (if (1 : Fin 4) ∈ A then b else 0) +
    (if (2 : Fin 4) ∈ A then c else 0) +
    (if (3 : Fin 4) ∈ A then 1 - a - b - c else 0)
  nonneg := fun A => by
    apply add_nonneg; apply add_nonneg; apply add_nonneg
    · split <;> [exact ha; exact le_refl _]
    · split <;> [exact hb; exact le_refl _]
    · split <;> [exact hc; exact le_refl _]
    · split <;> [linarith; exact le_refl _]
  additive := fun A B hdisj => by
    by_cases h0A : (0 : Fin 4) ∈ A <;> by_cases h0B : (0 : Fin 4) ∈ B <;>
    by_cases h1A : (1 : Fin 4) ∈ A <;> by_cases h1B : (1 : Fin 4) ∈ B <;>
    by_cases h2A : (2 : Fin 4) ∈ A <;> by_cases h2B : (2 : Fin 4) ∈ B <;>
    by_cases h3A : (3 : Fin 4) ∈ A <;> by_cases h3B : (3 : Fin 4) ∈ B <;>
    simp_all [Set.mem_union] <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; linarith

private theorem measure_fin4_mu (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) (A : Set (Fin 4)) :
    (measure_fin4 a b c ha hb hc habc).mu A =
    (if (0 : Fin 4) ∈ A then a else 0) +
    (if (1 : Fin 4) ∈ A then b else 0) +
    (if (2 : Fin 4) ∈ A then c else 0) +
    (if (3 : Fin 4) ∈ A then 1 - a - b - c else 0) := rfl

private theorem set_fin4_eq (A : Set (Fin 4)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = {2} ∨ A = {3} ∨
    A = {0,1} ∨ A = {0,2} ∨ A = {0,3} ∨ A = {1,2} ∨ A = {1,3} ∨ A = {2,3} ∨
    A = {0,1,2} ∨ A = {0,1,3} ∨ A = {0,2,3} ∨ A = {1,2,3} ∨
    A = Set.univ := by
  by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
  by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; right; right; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; right
    right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; right
    right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; right
    right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  · right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; right; right; right; right; right; right; left
    ext x; fin_cases x <;> simp_all
  · right; right; right; left; ext x; fin_cases x <;> simp_all
  · right; right; right; right; left; ext x; fin_cases x <;> simp_all
  · left; ext x; fin_cases x <;> simp_all

private theorem mf4_val (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) (S : Set (Fin 4)) (v : ℚ)
    (hv : (if (0 : Fin 4) ∈ S then a else 0) +
          (if (1 : Fin 4) ∈ S then b else 0) +
          (if (2 : Fin 4) ∈ S then c else 0) +
          (if (3 : Fin 4) ∈ S then 1 - a - b - c else 0) = v) :
    (measure_fin4 a b c ha hb hc habc).mu S = v := hv

private theorem mf4_empty (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ∅ = 0 := by
  rw [measure_fin4_mu]; simp

private theorem mf4_univ (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu (Set.univ : Set (Fin 4)) = 1 := by
  rw [measure_fin4_mu]; simp only [Set.mem_univ, ite_true]; linarith

set_option maxHeartbeats 800000 in
private theorem mf4_s0 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(0 : Fin 4)} = a := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_s1 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(1 : Fin 4)} = b := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_s2 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(2 : Fin 4)} = c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_s3 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu {(3 : Fin 4)} = 1 - a - b - c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p01 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1} : Set (Fin 4)) = a + b := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p02 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 2} : Set (Fin 4)) = a + c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p03 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 3} : Set (Fin 4)) = 1 - b - c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p12 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 2} : Set (Fin 4)) = b + c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p13 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 3} : Set (Fin 4)) = 1 - a - c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 800000 in
private theorem mf4_p23 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({2, 3} : Set (Fin 4)) = 1 - a - b := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 1600000 in
private theorem mf4_t012 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 2} : Set (Fin 4)) = a + b + c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 1600000 in
private theorem mf4_t013 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 3} : Set (Fin 4)) = 1 - c := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 1600000 in
private theorem mf4_t023 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({0, 2, 3} : Set (Fin 4)) = 1 - b := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

set_option maxHeartbeats 1600000 in
private theorem mf4_t123 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c ≤ 1) :
    (measure_fin4 a b c ha hb hc habc).mu ({1, 2, 3} : Set (Fin 4)) = 1 - a := by
  rw [measure_fin4_mu]; split_ifs <;>
  simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff] <;> linarith

private theorem not_all_null_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1} ∧ sys.ge ∅ {2} ∧ sys.ge ∅ {3}) := by
  intro ⟨h0, h1, h2, h3⟩
  have h01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) := by
    have : sys.ge {1} ({0, 1} : Set (Fin 4)) := by
      rw [sys.additive {1} {0, 1}]
      rw [show ({1} : Set (Fin 4)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1} : Set (Fin 4)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
      exact h0
    exact sys.trans _ _ _ h1 this
  have h012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) := by
    have : sys.ge {2} ({0, 1, 2} : Set (Fin 4)) := by
      rw [sys.additive {2} {0, 1, 2}]
      rw [show ({2} : Set (Fin 4)) \ {0, 1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1, 2} : Set (Fin 4)) \ {2} = {0, 1} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h2 this
  have huniv : sys.ge ∅ Set.univ := by
    have : sys.ge {3} (Set.univ : Set (Fin 4)) := by
      rw [sys.additive {3} Set.univ]
      rw [show ({3} : Set (Fin 4)) \ Set.univ = ∅ from by ext x; simp]
      rw [show (Set.univ : Set (Fin 4)) \ {3} = {0, 1, 2} from by
        ext x; fin_cases x <;> simp_all]
      exact h012
    exact sys.trans _ _ _ h3 this
  exact sys.nonTrivial huniv

set_option maxHeartbeats 6400000 in
private theorem fin4_dispatch (sys : EpistemicSystemFA (Fin 4))
    (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c ≤ 1)
    (hme : (measure_fin4 a b c ha hb hc habc).mu ∅ = 0)
    (hm0 : (measure_fin4 a b c ha hb hc habc).mu {(0 : Fin 4)} = a)
    (hm1 : (measure_fin4 a b c ha hb hc habc).mu {(1 : Fin 4)} = b)
    (hm2 : (measure_fin4 a b c ha hb hc habc).mu {(2 : Fin 4)} = c)
    (hm3 : (measure_fin4 a b c ha hb hc habc).mu {(3 : Fin 4)} = 1 - a - b - c)
    (hm01 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1} : Set (Fin 4)) = a + b)
    (hm02 : (measure_fin4 a b c ha hb hc habc).mu ({0, 2} : Set (Fin 4)) = a + c)
    (hm03 : (measure_fin4 a b c ha hb hc habc).mu ({0, 3} : Set (Fin 4)) = 1 - b - c)
    (hm12 : (measure_fin4 a b c ha hb hc habc).mu ({1, 2} : Set (Fin 4)) = b + c)
    (hm13 : (measure_fin4 a b c ha hb hc habc).mu ({1, 3} : Set (Fin 4)) = 1 - a - c)
    (hm23 : (measure_fin4 a b c ha hb hc habc).mu ({2, 3} : Set (Fin 4)) = 1 - a - b)
    (hm012 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 2} : Set (Fin 4)) = a + b + c)
    (hm013 : (measure_fin4 a b c ha hb hc habc).mu ({0, 1, 3} : Set (Fin 4)) = 1 - c)
    (hm023 : (measure_fin4 a b c ha hb hc habc).mu ({0, 2, 3} : Set (Fin 4)) = 1 - b)
    (hm123 : (measure_fin4 a b c ha hb hc habc).mu ({1, 2, 3} : Set (Fin 4)) = 1 - a)
    (hmu : (measure_fin4 a b c ha hb hc habc).mu (Set.univ : Set (Fin 4)) = 1)
    (he0 : sys.ge ∅ {(0 : Fin 4)} ↔ a ≤ 0)
    (he1 : sys.ge ∅ {(1 : Fin 4)} ↔ b ≤ 0)
    (he2 : sys.ge ∅ {(2 : Fin 4)} ↔ c ≤ 0)
    (he3 : sys.ge ∅ {(3 : Fin 4)} ↔ 1 - a - b - c ≤ 0)
    (he01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) ↔ a + b ≤ 0)
    (he02 : sys.ge ∅ ({0, 2} : Set (Fin 4)) ↔ a + c ≤ 0)
    (he03 : sys.ge ∅ ({0, 3} : Set (Fin 4)) ↔ 1 - b - c ≤ 0)
    (he12 : sys.ge ∅ ({1, 2} : Set (Fin 4)) ↔ b + c ≤ 0)
    (he13 : sys.ge ∅ ({1, 3} : Set (Fin 4)) ↔ 1 - a - c ≤ 0)
    (he23 : sys.ge ∅ ({2, 3} : Set (Fin 4)) ↔ 1 - a - b ≤ 0)
    (he012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) ↔ a + b + c ≤ 0)
    (he013 : sys.ge ∅ ({0, 1, 3} : Set (Fin 4)) ↔ 1 - c ≤ 0)
    (he023 : sys.ge ∅ ({0, 2, 3} : Set (Fin 4)) ↔ 1 - b ≤ 0)
    (he123 : sys.ge ∅ ({1, 2, 3} : Set (Fin 4)) ↔ 1 - a ≤ 0)
    (h01 : sys.ge {(0 : Fin 4)} {1} ↔ a ≥ b)
    (h10 : sys.ge {(1 : Fin 4)} {0} ↔ b ≥ a)
    (h02 : sys.ge {(0 : Fin 4)} {2} ↔ a ≥ c)
    (h20 : sys.ge {(2 : Fin 4)} {0} ↔ c ≥ a)
    (h03 : sys.ge {(0 : Fin 4)} {3} ↔ a ≥ 1 - a - b - c)
    (h30 : sys.ge {(3 : Fin 4)} {0} ↔ 1 - a - b - c ≥ a)
    (h12 : sys.ge {(1 : Fin 4)} {2} ↔ b ≥ c)
    (h21 : sys.ge {(2 : Fin 4)} {1} ↔ c ≥ b)
    (h13 : sys.ge {(1 : Fin 4)} {3} ↔ b ≥ 1 - a - b - c)
    (h31 : sys.ge {(3 : Fin 4)} {1} ↔ 1 - a - b - c ≥ b)
    (h23 : sys.ge {(2 : Fin 4)} {3} ↔ c ≥ 1 - a - b - c)
    (h32 : sys.ge {(3 : Fin 4)} {2} ↔ 1 - a - b - c ≥ c)
    (h0_12 : sys.ge {(0 : Fin 4)} ({1, 2} : Set _) ↔ a ≥ b + c)
    (h12_0 : sys.ge ({1, 2} : Set (Fin 4)) {0} ↔ b + c ≥ a)
    (h0_13 : sys.ge {(0 : Fin 4)} ({1, 3} : Set _) ↔ a ≥ 1 - a - c)
    (h13_0 : sys.ge ({1, 3} : Set (Fin 4)) {0} ↔ 1 - a - c ≥ a)
    (h0_23 : sys.ge {(0 : Fin 4)} ({2, 3} : Set _) ↔ a ≥ 1 - a - b)
    (h23_0 : sys.ge ({2, 3} : Set (Fin 4)) {0} ↔ 1 - a - b ≥ a)
    (h1_02 : sys.ge {(1 : Fin 4)} ({0, 2} : Set _) ↔ b ≥ a + c)
    (h02_1 : sys.ge ({0, 2} : Set (Fin 4)) {1} ↔ a + c ≥ b)
    (h1_03 : sys.ge {(1 : Fin 4)} ({0, 3} : Set _) ↔ b ≥ 1 - b - c)
    (h03_1 : sys.ge ({0, 3} : Set (Fin 4)) {1} ↔ 1 - b - c ≥ b)
    (h1_23 : sys.ge {(1 : Fin 4)} ({2, 3} : Set _) ↔ b ≥ 1 - a - b)
    (h23_1 : sys.ge ({2, 3} : Set (Fin 4)) {1} ↔ 1 - a - b ≥ b)
    (h2_01 : sys.ge {(2 : Fin 4)} ({0, 1} : Set _) ↔ c ≥ a + b)
    (h01_2 : sys.ge ({0, 1} : Set (Fin 4)) {2} ↔ a + b ≥ c)
    (h2_03 : sys.ge {(2 : Fin 4)} ({0, 3} : Set _) ↔ c ≥ 1 - b - c)
    (h03_2 : sys.ge ({0, 3} : Set (Fin 4)) {2} ↔ 1 - b - c ≥ c)
    (h2_13 : sys.ge {(2 : Fin 4)} ({1, 3} : Set _) ↔ c ≥ 1 - a - c)
    (h13_2 : sys.ge ({1, 3} : Set (Fin 4)) {2} ↔ 1 - a - c ≥ c)
    (h3_01 : sys.ge {(3 : Fin 4)} ({0, 1} : Set _) ↔ 1 - a - b - c ≥ a + b)
    (h01_3 : sys.ge ({0, 1} : Set (Fin 4)) {3} ↔ a + b ≥ 1 - a - b - c)
    (h3_02 : sys.ge {(3 : Fin 4)} ({0, 2} : Set _) ↔ 1 - a - b - c ≥ a + c)
    (h02_3 : sys.ge ({0, 2} : Set (Fin 4)) {3} ↔ a + c ≥ 1 - a - b - c)
    (h3_12 : sys.ge {(3 : Fin 4)} ({1, 2} : Set _) ↔ 1 - a - b - c ≥ b + c)
    (h12_3 : sys.ge ({1, 2} : Set (Fin 4)) {3} ↔ b + c ≥ 1 - a - b - c)
    (h0_123 : sys.ge {(0 : Fin 4)} ({1, 2, 3} : Set _) ↔ a ≥ 1 - a)
    (h123_0 : sys.ge ({1, 2, 3} : Set (Fin 4)) {0} ↔ 1 - a ≥ a)
    (h1_023 : sys.ge {(1 : Fin 4)} ({0, 2, 3} : Set _) ↔ b ≥ 1 - b)
    (h023_1 : sys.ge ({0, 2, 3} : Set (Fin 4)) {1} ↔ 1 - b ≥ b)
    (h2_013 : sys.ge {(2 : Fin 4)} ({0, 1, 3} : Set _) ↔ c ≥ 1 - c)
    (h013_2 : sys.ge ({0, 1, 3} : Set (Fin 4)) {2} ↔ 1 - c ≥ c)
    (h3_012 : sys.ge {(3 : Fin 4)} ({0, 1, 2} : Set _) ↔ 1 - a - b - c ≥ a + b + c)
    (h012_3 : sys.ge ({0, 1, 2} : Set (Fin 4)) {3} ↔ a + b + c ≥ 1 - a - b - c)
    (h01_23 : sys.ge ({0, 1} : Set (Fin 4)) ({2, 3} : Set _) ↔ a + b ≥ 1 - a - b)
    (h23_01 : sys.ge ({2, 3} : Set (Fin 4)) ({0, 1} : Set _) ↔ 1 - a - b ≥ a + b)
    (h02_13 : sys.ge ({0, 2} : Set (Fin 4)) ({1, 3} : Set _) ↔ a + c ≥ 1 - a - c)
    (h13_02 : sys.ge ({1, 3} : Set (Fin 4)) ({0, 2} : Set _) ↔ 1 - a - c ≥ a + c)
    (h03_12 : sys.ge ({0, 3} : Set (Fin 4)) ({1, 2} : Set _) ↔ 1 - b - c ≥ b + c)
    (h12_03 : sys.ge ({1, 2} : Set (Fin 4)) ({0, 3} : Set _) ↔ b + c ≥ 1 - b - c) :
    ∀ C D : Set (Fin 4), (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ (measure_fin4 a b c ha hb hc habc).inducedGe C D) := by
  intro C D hdisj
  simp only [FinAddMeasure.inducedGe]
  rcases set_fin4_eq C with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases set_fin4_eq D with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try (exfalso; first
    | (apply hdisj 0; all_goals (simp; done))
    | (apply hdisj 1; all_goals (simp; done))
    | (apply hdisj 2; all_goals (simp; done))
    | (apply hdisj 3; all_goals (simp; done)))
  all_goals simp only [hme, hm0, hm1, hm2, hm3, hm01, hm02, hm03, hm12, hm13, hm23,
    hm012, hm013, hm023, hm123, hmu]
  all_goals first
    | exact ⟨fun _ => le_refl _, fun _ => sys.refl _⟩
    | exact ⟨fun h => absurd h sys.nonTrivial, fun h => by linarith⟩
    | exact ⟨fun _ => by linarith, fun _ => sys.mono _ _ (Set.empty_subset _)⟩
    | exact he0 | exact he1 | exact he2 | exact he3
    | exact he01 | exact he02 | exact he03 | exact he12 | exact he13 | exact he23
    | exact he012 | exact he013 | exact he023 | exact he123
    | exact h01 | exact h10 | exact h02 | exact h20 | exact h03 | exact h30
    | exact h12 | exact h21 | exact h13 | exact h31 | exact h23 | exact h32
    | exact h0_12 | exact h12_0 | exact h0_13 | exact h13_0
    | exact h0_23 | exact h23_0
    | exact h1_02 | exact h02_1 | exact h1_03 | exact h03_1
    | exact h1_23 | exact h23_1
    | exact h2_01 | exact h01_2 | exact h2_03 | exact h03_2
    | exact h2_13 | exact h13_2
    | exact h3_01 | exact h01_3 | exact h3_02 | exact h02_3
    | exact h3_12 | exact h12_3
    | exact h0_123 | exact h123_0 | exact h1_023 | exact h023_1
    | exact h2_013 | exact h013_2 | exact h3_012 | exact h012_3
    | exact h01_23 | exact h23_01 | exact h02_13 | exact h13_02
    | exact h03_12 | exact h12_03

-- ── Card 4: Dirac helper (3-null cases) ──────────────

set_option maxHeartbeats 800000 in
private theorem fin4_dirac_repr (sys : EpistemicSystemFA (Fin 4))
    (j : Fin 4)
    (ge_null : ∀ D : Set (Fin 4), j ∉ D → sys.ge ∅ D)
    (hn_j : ¬sys.ge ∅ {j}) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  -- Construct Dirac measure at j
  have ⟨m, hmu⟩ : ∃ m : FinAddMeasure (Fin 4), ∀ C, m.mu C = if j ∈ C then 1 else 0 := by
    fin_cases j
    · exact ⟨measure_fin4 1 0 0 (by linarith) le_rfl le_rfl (by linarith),
        fun C => by rw [measure_fin4_mu]; simp⟩
    · exact ⟨measure_fin4 0 1 0 le_rfl (by linarith) le_rfl (by linarith),
        fun C => by rw [measure_fin4_mu]; simp⟩
    · exact ⟨measure_fin4 0 0 1 le_rfl le_rfl (by linarith) (by linarith),
        fun C => by rw [measure_fin4_mu]; simp⟩
    · exact ⟨measure_fin4 0 0 0 le_rfl le_rfl le_rfl (by linarith),
        fun C => by rw [measure_fin4_mu]; simp⟩
  exact ⟨m, reduce_to_disjoint sys m (fun C D hdisj => by
    simp only [FinAddMeasure.inducedGe, hmu]
    by_cases hjC : j ∈ C <;> by_cases hjD : j ∈ D
    · exact absurd hjD (hdisj j hjC)
    · rw [if_pos hjC, if_neg hjD]; constructor
      · intro _; linarith
      · intro _; exact sys.trans C {j} D
          (sys.mono _ _ (Set.singleton_subset_iff.mpr hjC))
          (sys.trans {j} ∅ D (sys.mono _ _ (Set.empty_subset {j})) (ge_null D hjD))
    · rw [if_neg hjC, if_pos hjD]; constructor
      · intro h; exfalso; exact hn_j (sys.trans ∅ C {j}
          (ge_null C hjC) (sys.trans C D {j} h
            (sys.mono _ _ (Set.singleton_subset_iff.mpr hjD))))
      · intro h; linarith
    · rw [if_neg hjC, if_neg hjD]; constructor
      · intro _; linarith
      · intro _; exact sys.trans C ∅ D
          (sys.mono _ _ (Set.empty_subset C)) (ge_null D hjD))⟩

-- ── Card 4: Main theorem ────────────────────────────
set_option maxHeartbeats 3200000 in
private theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  by_cases hn0 : sys.ge ∅ {(0 : Fin 4)}
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 4)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- All null: impossible
          exact absurd ⟨hn0, hn1, hn2, hn3⟩ (not_all_null_fin4 sys)
        · -- 3 null ({0},{1},{2}), {3} non-null
          have hd1 : ({0} : Set (Fin 4)) \ {0, 1} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd2 : ({0, 1} : Set (Fin 4)) \ {0} = {1} := by ext x; fin_cases x <;> simp_all
          have hd3 : ({2} : Set (Fin 4)) \ {0, 1, 2} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd4 : ({0, 1, 2} : Set (Fin 4)) \ {2} = {0, 1} := by ext x; fin_cases x <;> simp_all
          have ge_01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) :=
            sys.trans _ _ _ hn0 (by rw [sys.additive {0} {0, 1}, hd1, hd2]; exact hn1)
          have ge_012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) :=
            sys.trans _ _ _ hn2 (by rw [sys.additive {2} {0, 1, 2}, hd3, hd4]; exact ge_01)
          exact fin4_dirac_repr sys 3
            (fun D hD => sys.trans _ _ _ ge_012
              (sys.mono _ _ (fun x hx => by fin_cases x <;> simp_all)))
            hn3
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 3 null ({0},{1},{3}), {2} non-null
          have hd1 : ({0} : Set (Fin 4)) \ {0, 1} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd2 : ({0, 1} : Set (Fin 4)) \ {0} = {1} := by ext x; fin_cases x <;> simp_all
          have hd3 : ({3} : Set (Fin 4)) \ {0, 1, 3} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd4 : ({0, 1, 3} : Set (Fin 4)) \ {3} = {0, 1} := by ext x; fin_cases x <;> simp_all
          have ge_01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) :=
            sys.trans _ _ _ hn0 (by rw [sys.additive {0} {0, 1}, hd1, hd2]; exact hn1)
          have ge_013 : sys.ge ∅ ({0, 1, 3} : Set (Fin 4)) :=
            sys.trans _ _ _ hn3 (by rw [sys.additive {3} {0, 1, 3}, hd3, hd4]; exact ge_01)
          exact fin4_dirac_repr sys 2
            (fun D hD => sys.trans _ _ _ ge_013
              (sys.mono _ _ (fun x hx => by fin_cases x <;> simp_all)))
            hn2
        · -- 2 null ({0},{1}), {2},{3} non-null
          sorry
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 3 null ({0},{2},{3}), {1} non-null
          have hd1 : ({0} : Set (Fin 4)) \ {0, 2} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd2 : ({0, 2} : Set (Fin 4)) \ {0} = {2} := by ext x; fin_cases x <;> simp_all
          have hd3 : ({3} : Set (Fin 4)) \ {0, 2, 3} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd4 : ({0, 2, 3} : Set (Fin 4)) \ {3} = {0, 2} := by ext x; fin_cases x <;> simp_all
          have ge_02 : sys.ge ∅ ({0, 2} : Set (Fin 4)) :=
            sys.trans _ _ _ hn0 (by rw [sys.additive {0} {0, 2}, hd1, hd2]; exact hn2)
          have ge_023 : sys.ge ∅ ({0, 2, 3} : Set (Fin 4)) :=
            sys.trans _ _ _ hn3 (by rw [sys.additive {3} {0, 2, 3}, hd3, hd4]; exact ge_02)
          exact fin4_dirac_repr sys 1
            (fun D hD => sys.trans _ _ _ ge_023
              (sys.mono _ _ (fun x hx => by fin_cases x <;> simp_all)))
            hn1
        · -- 2 null ({0},{2}), {1},{3} non-null
          sorry
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 2 null ({0},{3}), {1},{2} non-null
          sorry
        · -- 1 null ({0}), {1},{2},{3} non-null
          sorry
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 4)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 3 null ({1},{2},{3}), {0} non-null
          have hd1 : ({1} : Set (Fin 4)) \ {1, 2} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd2 : ({1, 2} : Set (Fin 4)) \ {1} = {2} := by ext x; fin_cases x <;> simp_all
          have hd3 : ({3} : Set (Fin 4)) \ {1, 2, 3} = ∅ := by ext x; fin_cases x <;> simp_all
          have hd4 : ({1, 2, 3} : Set (Fin 4)) \ {3} = {1, 2} := by ext x; fin_cases x <;> simp_all
          have ge_12 : sys.ge ∅ ({1, 2} : Set (Fin 4)) :=
            sys.trans _ _ _ hn1 (by rw [sys.additive {1} {1, 2}, hd1, hd2]; exact hn2)
          have ge_123 : sys.ge ∅ ({1, 2, 3} : Set (Fin 4)) :=
            sys.trans _ _ _ hn3 (by rw [sys.additive {3} {1, 2, 3}, hd3, hd4]; exact ge_12)
          exact fin4_dirac_repr sys 0
            (fun D hD => sys.trans _ _ _ ge_123
              (sys.mono _ _ (fun x hx => by fin_cases x <;> simp_all)))
            hn0
        · -- 2 null ({1},{2}), {0},{3} non-null
          sorry
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 2 null ({1},{3}), {0},{2} non-null
          sorry
        · -- 1 null ({1}), {0},{2},{3} non-null
          sorry
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 4)}
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 2 null ({2},{3}), {0},{1} non-null
          sorry
        · -- 1 null ({2}), {0},{1},{3} non-null
          sorry
      · by_cases hn3 : sys.ge ∅ {(3 : Fin 4)}
        · -- 1 null ({3}), {0},{1},{2} non-null
          sorry
        · -- 0 null: all non-null
          sorry

-- ── Transfer infrastructure ────────────────────────

private noncomputable def transportFA {W α : Type*} (e : W ≃ α)
    (sys : EpistemicSystemFA W) : EpistemicSystemFA α where
  ge := fun A B => sys.ge (e.symm '' A) (e.symm '' B)
  refl := fun A => sys.refl _
  mono := fun A B hAB => sys.mono _ _ (Set.image_mono hAB)
  bottom := by
    show sys.ge (e.symm '' Set.univ) (e.symm '' ∅)
    rw [Set.image_univ_of_surjective e.symm.surjective, Set.image_empty]
    exact sys.bottom
  nonTrivial := by
    show ¬sys.ge (e.symm '' ∅) (e.symm '' Set.univ)
    rw [Set.image_empty, Set.image_univ_of_surjective e.symm.surjective]
    exact sys.nonTrivial
  total := fun A B => sys.total _ _
  trans := fun A B C h1 h2 => sys.trans _ _ _ h1 h2
  additive := fun A B => by
    show sys.ge (e.symm '' A) (e.symm '' B) ↔
         sys.ge (e.symm '' (A \ B)) (e.symm '' (B \ A))
    rw [Set.image_diff e.symm.injective, Set.image_diff e.symm.injective]
    exact sys.additive _ _

private noncomputable def transportMeasure {W α : Type*}
    (e : W ≃ α) (m : FinAddMeasure α) : FinAddMeasure W where
  mu := fun A => m.mu (e '' A)
  nonneg := fun A => m.nonneg _
  additive := fun A B hdisj => by
    rw [Set.image_union]
    exact m.additive _ _ (fun x ⟨a, ha, hea⟩ ⟨b, hb, heb⟩ =>
      hdisj a ha (e.injective (hea ▸ heb) ▸ hb))
  total := by
    rw [Set.image_univ_of_surjective e.surjective]
    exact m.total

private theorem transfer_repr {W α : Type*}
    (e : W ≃ α) (sys : EpistemicSystemFA W) (m : FinAddMeasure α)
    (hm : ∀ A B : Set α, (transportFA e sys).ge A B ↔ m.inducedGe A B) :
    ∀ A B : Set W, sys.ge A B ↔ (transportMeasure e m).inducedGe A B := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simp only [transportFA, Equiv.symm_image_image] at h
  exact h

-- ── Theorem 8 (Kraft, Pratt & Seidenberg 1959) ───

set_option maxHeartbeats 1600000 in
/-- **Theorem 8a** (Kraft, Pratt & Seidenberg 1959): for |W| < 5,
    every FA model is representable by a finitely additive probability
    measure. Below 5 worlds, the logics FA and FP∞ coincide.

    The proof transfers an arbitrary `Fintype W` to `Fin n` via
    `Fintype.equivFin`, applies the per-cardinality proof for n ∈ {0,1,2,3,4},
    and transports the resulting measure back.

    TODO: the `Fin 4` case (`theorem8a_fin4`) is sorry — the dispatch
    infrastructure is in place but the case analysis is pending. -/
theorem theorem8a {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (hcard : Fintype.card W < 5) :
    ∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  haveI : DecidableEq W := Classical.typeDecidableEq W
  let e := Fintype.equivFin W
  set n := Fintype.card W with hn_def
  interval_cases n
  · -- n = 0: impossible
    exfalso
    have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
    exact (transportFA e sys).nonTrivial (this ▸ (transportFA e sys).refl ∅)
  · -- n = 1
    obtain ⟨m', hm'⟩ := theorem8a_fin1 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 2
    obtain ⟨m', hm'⟩ := theorem8a_fin2 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 3
    obtain ⟨m', hm'⟩ := theorem8a_fin3 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 4
    obtain ⟨m', hm'⟩ := theorem8a_fin4 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩

/-- **Theorem 8b** (Kraft, Pratt & Seidenberg 1959): for |W| ≥ 5,
    FA is strictly weaker than FP∞ — there exists a 5-element type
    with an FA ordering admitting no finitely additive measure
    representation. The FP∞ axioms (Scott schemata) are strictly
    stronger than qualitative additivity alone.

    Proof: the KPS 5-world counterexample. We construct an explicit
    total ordering on subsets of Fin 5 satisfying FA axioms (verified
    by `native_decide` over all 1024 pairs), then prove no finitely
    additive measure can represent it via Scott cancellation:
    three strict ordering facts {q,s} < {p}, {p,q} < {r,s}, {p,s} < {t,q}
    plus one weak {p,q,s} ≥ {r,t} yield balanced element counts but
    contradictory measure sums. -/
theorem theorem8b :
    ∃ (W : Type) (_ : Fintype W) (sys : EpistemicSystemFA W),
      Fintype.card W = 5 ∧
      ¬∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  ⟨Fin 5, inferInstance, kpsSystemFA, Fintype.card_fin 5, kps_not_representable⟩

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
