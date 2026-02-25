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

noncomputable def kpsSystemFA : EpistemicSystemFA (Fin 5) where
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

theorem kps_not_representable :
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

theorem measure_axiomA {W : Type*} (m : FinAddMeasure W) (A B : Set W) :
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

theorem reduce_to_disjoint {W : Type*} (sys : EpistemicSystemFA W)
    (m : FinAddMeasure W)
    (h : ∀ C D : Set W, (∀ x, x ∈ C → x ∉ D) →
      (sys.ge C D ↔ m.inducedGe C D)) :
    ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  intro A B
  rw [sys.additive A B, measure_axiomA m A B]
  exact h _ _ (fun x ⟨_, hxnB⟩ ⟨_, hxnA⟩ => hxnA (by assumption))

-- ── Null element reduction ────────────────────────────

/-- Removing a null element from both sides of a disjoint comparison preserves `ge`.
    When `sys.ge ∅ {j}` (j is null) and C, D are disjoint, `sys.ge C D ↔ sys.ge (C\{j}) (D\{j})`. -/
theorem null_removal_disjoint {W : Type*} (sys : EpistemicSystemFA W)
    (j : W) (hj : sys.ge ∅ {j})
    (C D : Set W) (hdisj : ∀ x, x ∈ C → x ∉ D) :
    sys.ge C D ↔ sys.ge (C \ {j}) (D \ {j}) := by
  have null_sub : ∀ S : Set W, sys.ge (S \ {j}) S := by
    intro S
    by_cases hj_in : j ∈ S
    · rw [sys.additive (S \ {j}) S]
      have h1 : (S \ {j}) \ S = ∅ := by
        ext x; constructor
        · intro ⟨⟨_, _⟩, hns⟩; exact absurd (by assumption) hns
        · intro h; exact h.elim
      have h2 : S \ (S \ {j}) = {j} := by
        ext x; simp only [Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · intro ⟨hx, hn⟩; by_contra hne; exact hn ⟨hx, hne⟩
        · intro hx; subst hx; exact ⟨hj_in, fun ⟨_, h⟩ => h rfl⟩
      rw [h1, h2]; exact hj
    · rw [Set.diff_singleton_eq_self hj_in]; exact sys.refl S
  by_cases hjC : j ∈ C
  · have hjnD : j ∉ D := fun h => hdisj j hjC h
    rw [Set.diff_singleton_eq_self hjnD]
    exact ⟨fun h => sys.trans _ _ _ (null_sub C) h,
           fun h => sys.trans _ _ _ (sys.mono _ _ Set.diff_subset) h⟩
  · rw [Set.diff_singleton_eq_self hjC]
    by_cases hjD : j ∈ D
    · exact ⟨fun h => sys.trans _ _ _ h (sys.mono _ _ Set.diff_subset),
             fun h => sys.trans _ _ _ h (null_sub D)⟩
    · rw [Set.diff_singleton_eq_self hjD]

/-- `Fin.succ '' (Fin.succ ⁻¹' S) = S \ {0}` for `S : Set (Fin (n+1))`.
    The image of `Fin.succ` covers exactly the non-zero elements. -/
private theorem succ_image_preimage {n : ℕ} (S : Set (Fin (n + 1))) :
    Fin.succ '' (Fin.succ ⁻¹' S) = S \ {(0 : Fin (n + 1))} := by
  rw [Set.image_preimage_eq_range_inter, Fin.range_succ]
  ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_diff]; exact And.comm

set_option maxHeartbeats 3200000 in
/-- Null element reduction: if element 0 is null in an FA system on Fin (n+2), reduce
    to Fin (n+1) via Fin.succ and delegate to a sub-theorem. -/
theorem null_elem_reduce {n : ℕ} (sys : EpistemicSystemFA (Fin (n + 2)))
    (hn0 : sys.ge ∅ {(0 : Fin (n + 2))})
    (hnn : ∃ i : Fin (n + 1), ¬sys.ge ∅ {Fin.succ i})
    (sub_repr : ∀ sys' : EpistemicSystemFA (Fin (n + 1)),
      ∃ m : FinAddMeasure (Fin (n + 1)), ∀ A B, sys'.ge A B ↔ m.inducedGe A B) :
    ∃ m : FinAddMeasure (Fin (n + 2)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  -- Step 1: Build restricted system on Fin (n+1)
  let sys_r : EpistemicSystemFA (Fin (n + 1)) := {
    ge := fun A B => sys.ge (Fin.succ '' A) (Fin.succ '' B)
    refl := fun A => sys.refl _
    mono := fun A B hAB => sys.mono _ _ (Set.image_mono hAB)
    bottom := by
      show sys.ge (Fin.succ '' Set.univ) (Fin.succ '' ∅)
      simp only [Set.image_empty]
      exact sys.mono _ _ (Set.empty_subset _)
    nonTrivial := by
      show ¬sys.ge (Fin.succ '' ∅) (Fin.succ '' Set.univ)
      simp only [Set.image_empty]
      obtain ⟨i, hi⟩ := hnn
      intro h
      exact hi (sys.trans _ _ _ h (sys.mono _ _
        (Set.singleton_subset_iff.mpr ⟨i, Set.mem_univ _, rfl⟩)))
    total := fun A B => sys.total _ _
    trans := fun A B C h1 h2 => sys.trans _ _ _ h1 h2
    additive := fun A B => by
      show sys.ge (Fin.succ '' A) (Fin.succ '' B) ↔
           sys.ge (Fin.succ '' (A \ B)) (Fin.succ '' (B \ A))
      rw [Set.image_diff (Fin.succ_injective (n + 1)),
          Set.image_diff (Fin.succ_injective (n + 1))]
      exact sys.additive _ _
  }
  -- Step 2: Get sub-measure
  obtain ⟨m_r, hm_r⟩ := sub_repr sys_r
  -- Step 3: Lift measure (null element gets weight 0)
  refine ⟨{
    mu := fun A => m_r.mu (Fin.succ ⁻¹' A)
    nonneg := fun A => m_r.nonneg _
    additive := fun A B hdisj => by
      rw [Set.preimage_union]
      exact m_r.additive _ _ (fun x hxA hxB => hdisj (Fin.succ x) hxA hxB)
    total := by
      show m_r.mu (Fin.succ ⁻¹' Set.univ) = 1
      rw [Set.preimage_univ]; exact m_r.total
  }, reduce_to_disjoint sys _ (fun C D hdisj => ?_)⟩
  -- Step 4: Prove representation for disjoint C, D
  rw [null_removal_disjoint sys 0 hn0 C D hdisj]
  rw [← succ_image_preimage C, ← succ_image_preimage D]
  exact hm_r (Fin.succ ⁻¹' C) (Fin.succ ⁻¹' D)

-- ── Card 0: impossible ─────────────────────────────

theorem no_fa_empty (sys : EpistemicSystemFA (Fin 0)) : False := by
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

theorem theorem8a_fin1 (sys : EpistemicSystemFA (Fin 1)) :
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

theorem theorem8a_fin2 (sys : EpistemicSystemFA (Fin 2)) :
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

-- ── Transport + Permutation infrastructure ────────────

noncomputable def transportFA {W α : Type*} (e : W ≃ α)
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

noncomputable def transportMeasure {W α : Type*}
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

theorem transfer_repr {W α : Type*}
    (e : W ≃ α) (sys : EpistemicSystemFA W) (m : FinAddMeasure α)
    (hm : ∀ A B : Set α, (transportFA e sys).ge A B ↔ m.inducedGe A B) :
    ∀ A B : Set W, sys.ge A B ↔ (transportMeasure e m).inducedGe A B := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simp only [transportFA, Equiv.symm_image_image] at h
  exact h

/-- Null pattern transport: j is null in `transportFA σ sys` iff `σ.symm j` is null in `sys`. -/
theorem perm_null_iff {n : ℕ} (σ : Fin n ≃ Fin n)
    (sys : EpistemicSystemFA (Fin n)) (j : Fin n) :
    (transportFA σ sys).ge ∅ {j} ↔ sys.ge ∅ {σ.symm j} := by
  show sys.ge (σ.symm '' ∅) (σ.symm '' {j}) ↔ sys.ge ∅ {σ.symm j}
  simp only [Set.image_empty, Set.image_singleton]

/-- Concrete null pattern conversion: if `σ.symm j = k` then null-at-j in transported
    system iff null-at-k in original. -/
theorem perm_null_convert {n : ℕ} (σ : Fin n ≃ Fin n)
    (sys : EpistemicSystemFA (Fin n)) (j k : Fin n)
    (hk : σ.symm j = k) :
    (transportFA σ sys).ge ∅ {j} ↔ sys.ge ∅ {k} := by
  rw [perm_null_iff, hk]

/-- Permutation transport for representability: if `transportFA σ sys` is representable,
    then so is `sys`. -/
theorem perm_repr {n : ℕ} (σ : Fin n ≃ Fin n) (sys : EpistemicSystemFA (Fin n))
    (h : ∃ m : FinAddMeasure (Fin n),
         ∀ A B, (transportFA σ sys).ge A B ↔ m.inducedGe A B) :
    ∃ m : FinAddMeasure (Fin n), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  obtain ⟨m, hm⟩ := h
  exact ⟨transportMeasure σ m, transfer_repr σ sys m hm⟩

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

private theorem theorem8a_fin3_2null_01 (sys : EpistemicSystemFA (Fin 3))
    (hn0 : sys.ge ∅ {(0 : Fin 3)}) (_hn1 : sys.ge ∅ {(1 : Fin 3)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 3)}) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  -- Fin.succ (1 : Fin 2) = (2 : Fin 3), non-null by hn2
  null_elem_reduce sys hn0 ⟨1, hn2⟩ theorem8a_fin2

private theorem theorem8a_fin3_1null_0 (sys : EpistemicSystemFA (Fin 3))
    (hn0 : sys.ge ∅ {(0 : Fin 3)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 3)})
    (_hn2 : ¬sys.ge ∅ {(2 : Fin 3)}) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  -- Fin.succ (0 : Fin 2) = (1 : Fin 3), non-null by hn1
  null_elem_reduce sys hn0 ⟨0, hn1⟩ theorem8a_fin2

set_option maxHeartbeats 3200000 in
private theorem theorem8a_fin3_0null (sys : EpistemicSystemFA (Fin 3))
    (hn0 : ¬sys.ge ∅ {(0 : Fin 3)}) (hn1 : ¬sys.ge ∅ {(1 : Fin 3)})
    (hn2 : ¬sys.ge ∅ {(2 : Fin 3)}) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
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


-- ── Card 3: Main theorem ─────────────────────────

set_option maxHeartbeats 800000 in
theorem theorem8a_fin3 (sys : EpistemicSystemFA (Fin 3)) :
    ∃ (m : FinAddMeasure (Fin 3)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  by_cases hn0 : sys.ge ∅ {(0 : Fin 3)}
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 3)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · exact absurd ⟨hn0, hn1, hn2⟩ (not_all_null_fin3 sys)
      · exact theorem8a_fin3_2null_01 sys hn0 hn1 hn2
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 2 null {0,2}: permute to {0,1} via swap(1,2)
        exact perm_repr (Equiv.swap 1 2) sys (theorem8a_fin3_2null_01 _
          ((perm_null_convert _ _ 0 0 (by decide)).mpr hn0)
          ((perm_null_convert _ _ 1 2 (by decide)).mpr hn2)
          (fun h => hn1 ((perm_null_convert _ _ 2 1 (by decide)).mp h)))
      · exact theorem8a_fin3_1null_0 sys hn0 hn1 hn2
  · by_cases hn1 : sys.ge ∅ {(1 : Fin 3)}
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 2 null {1,2}: permute to {0,1} via swap(0,2)
        exact perm_repr (Equiv.swap 0 2) sys (theorem8a_fin3_2null_01 _
          ((perm_null_convert _ _ 0 2 (by decide)).mpr hn2)
          ((perm_null_convert _ _ 1 1 (by decide)).mpr hn1)
          (fun h => hn0 ((perm_null_convert _ _ 2 0 (by decide)).mp h)))
      · -- 1 null {1}: permute to {0} via swap(0,1)
        exact perm_repr (Equiv.swap 0 1) sys (theorem8a_fin3_1null_0 _
          ((perm_null_convert _ _ 0 1 (by decide)).mpr hn1)
          (fun h => hn0 ((perm_null_convert _ _ 1 0 (by decide)).mp h))
          (fun h => hn2 ((perm_null_convert _ _ 2 2 (by decide)).mp h)))
    · by_cases hn2 : sys.ge ∅ {(2 : Fin 3)}
      · -- 1 null {2}: permute to {0} via swap(0,2)
        exact perm_repr (Equiv.swap 0 2) sys (theorem8a_fin3_1null_0 _
          ((perm_null_convert _ _ 0 2 (by decide)).mpr hn2)
          (fun h => hn1 ((perm_null_convert _ _ 1 1 (by decide)).mp h))
          (fun h => hn0 ((perm_null_convert _ _ 2 0 (by decide)).mp h)))
      · exact theorem8a_fin3_0null sys hn0 hn1 hn2


end Core.Scale
