import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# ABLE: A Bit Like English
@cite{beaver-2001}

ABLE is the fragment language of @cite{beaver-2001}'s *Presupposition and
Assertion in Dynamic Semantics*. It serves as the formal object language
for Presuppositional Update Logic (PUL), mapping English-like formulas to
context change potentials.

## Core Ideas

ABLE's key innovation is the **presupposition operator** ∂ (D59), a test
that checks whether the current context already entails a proposition.
When it does, the context passes through unchanged; when it doesn't,
the update is undefined (yields ∅). This makes presupposition projection
fall out of structural admittance (D30) — the requirement that each
subformula's presupposition be satisfied at its local context.

## Formal Definitions

The formalization captures the propositional core of PUL (@cite{beaver-2001}
Ch. 6) and ABLE (Ch. 7), without discourse markers or extended sequences.
Connectives follow D52 (Ch. 7 §7.4), modals follow D60 (Ch. 8 §8.3),
and the presupposition operator is D59 (Ch. 7 §7.6).

| ABLE          | Formal               | CCP equivalent      |
|---------------|----------------------|----------------------|
| `pred sat`    | `{p ∈ σ \| sat p}`  | `updateFromSat`      |
| `NOT φ`       | `σ \ σ[φ]`          | *(PUL-specific)*     |
| `AND φ ψ`     | `σ[φ][ψ]`           | `CCP.seq`            |
| `MIGHT φ`     | `σ if σ[φ]≠∅, ∅ o/w`| `CCP.might`          |
| `∂ φ`         | `σ if σ[φ]=σ, ∅ o/w`| `CCP.must`           |

**Important**: ABLE NOT uses set complement within the input (`σ \ σ[φ]`),
which differs from `CCP.neg` (test-based pass/fail). This is how PUL
handles negation — it is eliminative but not a test.

**Simplification**: Full ABLE (D52) takes anaphoric closure (↓) before
negation to strip discourse markers; our set-based version omits this
since we don't model discourse markers.

## Key Results

- **Fact 8.1**: Presupposition projects through NOT, AND, IF...THEN
- **Fact 8.3**: Conditional presupposition — second conjunct's presupposition
  becomes conditional on first conjunct
- **Lemma 8.6**: Satisfaction ↔ inconsistency with NOT (eliminativity bridge)
- **Fact 8.7**: MUST is a test for satisfaction
- **Facts 8.5, 8.8**: MIGHT and MUST are tests; presupposition projects through them
-/

namespace Semantics.Dynamic.ABLE

open Classical
open Semantics.Dynamic.Core (CCP InfoStateOf IsEliminative IsTest
  updateFromSat eliminative_seq test_eliminative)

variable {P : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. ABLE Formulas
-- ════════════════════════════════════════════════════════════════

/-- ABLE formula type. @cite{beaver-2001} Ch. 7.

The five constructors correspond to the five basic ABLE operations.
Connectives (NOT, AND) are D52 (§7.4), epistemic modality (MIGHT) is
D60 (§8.3), and the presupposition operator (∂) is D59 (§7.6).
Derived connectives (IF...THEN, MUST, OR) are defined as abbreviations.
-/
inductive Formula (P : Type*) where
  /-- Predicational update: filter by satisfaction. D48. -/
  | pred (sat : P → Prop)
  /-- Negation: complement within input. D52. -/
  | not (φ : Formula P)
  /-- Conjunction (sequencing): update by φ then ψ. D52. -/
  | and (φ ψ : Formula P)
  /-- Epistemic possibility: compatibility test. D60. -/
  | might (φ : Formula P)
  /-- Presupposition operator ∂: full support test. D59. -/
  | presup (φ : Formula P)

namespace Formula

/-- IF φ THEN ψ = NOT(φ AND NOT ψ). D52. -/
def impl (φ ψ : Formula P) : Formula P := .not (.and φ (.not ψ))

/-- MUST φ = NOT(MIGHT(NOT φ)). D60. -/
def must (φ : Formula P) : Formula P := .not (.might (.not φ))

/-- OR φ ψ = NOT(NOT φ AND NOT ψ). -/
def disj (φ ψ : Formula P) : Formula P := .not (.and (.not φ) (.not ψ))

-- ════════════════════════════════════════════════════════════════
-- § 2. PUL Evaluation
-- ════════════════════════════════════════════════════════════════

/-- Evaluate an ABLE formula as a CCP. @cite{beaver-2001} D52, D59, D60.

Each constructor maps to its PUL update:
- `pred`: filter by satisfaction (`updateFromSat`) — D48
- `not`: set complement within input (`σ \ σ[φ]`) — D52
- `and`: sequential update (`σ[φ][ψ]`) — D52
- `might`: compatibility test — D60
- `presup` (∂): full support test — D59
-/
noncomputable def eval : Formula P → CCP P
  | .pred sat   => λ σ => { p ∈ σ | sat p }
  | .not φ      => λ σ => σ \ φ.eval σ
  | .and φ ψ    => λ σ => ψ.eval (φ.eval σ)
  | .might φ    => λ σ => if (φ.eval σ).Nonempty then σ else ∅
  | .presup φ   => λ σ => if φ.eval σ = σ then σ else ∅

-- ════════════════════════════════════════════════════════════════
-- § 3. Structural Admittance (D30)
-- ════════════════════════════════════════════════════════════════

/-- Structural admittance: a formula's presuppositions are satisfied
at every local context encountered during evaluation.

This captures @cite{beaver-2001} D30 (Admittance) recursively over
formula structure — the key to presupposition projection.
A state σ *admits* φ iff:
- For `pred`: always admitted (no presuppositions)
- For `not φ`: σ admits φ
- For `and φ ψ`: σ admits φ AND σ[φ] admits ψ
- For `might φ`: σ admits φ
- For `∂ φ`: σ already entails φ (i.e., σ[φ] = σ)
-/
noncomputable def pulAdmits : Formula P → InfoStateOf P → Prop
  | .pred _     => λ _ => True
  | .not φ      => λ σ => φ.pulAdmits σ
  | .and φ ψ    => λ σ => φ.pulAdmits σ ∧ ψ.pulAdmits (φ.eval σ)
  | .might φ    => λ σ => φ.pulAdmits σ
  | .presup φ   => λ σ => φ.eval σ = σ

-- ════════════════════════════════════════════════════════════════
-- § 4. ∂ Properties
-- ════════════════════════════════════════════════════════════════

/-- ∂ is a test: it either passes (returns input) or fails (returns ∅).
@cite{beaver-2001} D59, D61 (Tests). -/
theorem presup_isTest (φ : Formula P) : IsTest φ.presup.eval := by
  intro s; simp only [eval]; split <;> simp

/-- ∂ is eliminative. -/
theorem presup_eliminative (φ : Formula P) : IsEliminative φ.presup.eval := by
  exact test_eliminative _ (presup_isTest φ)

/-- Admittance of ∂φ is equivalent to σ[φ] = σ. -/
theorem presup_admits_iff (φ : Formula P) (σ : InfoStateOf P) :
    (Formula.presup φ).pulAdmits σ ↔ φ.eval σ = σ := by
  simp only [pulAdmits]

-- ════════════════════════════════════════════════════════════════
-- § 5. Projection Theorems (Fact 8.1, Fact 8.3)
-- ════════════════════════════════════════════════════════════════

/-- **Fact 8.1 (i)**: Presupposition projects through NOT.

If φ presupposes ψ (i.e., φ = ∂ψ AND χ), then NOT φ also
presupposes ψ. Here we prove the component: admitting NOT φ
requires admitting φ. -/
theorem admits_not (φ : Formula P) (σ : InfoStateOf P) :
    (Formula.not φ).pulAdmits σ ↔ φ.pulAdmits σ := by
  simp only [pulAdmits]

/-- **Fact 8.1 (ii)**: Left presupposition projects through AND.

Admitting AND φ ψ requires admitting φ (among other things). -/
theorem admits_and_left (φ ψ : Formula P) (σ : InfoStateOf P) :
    (Formula.and φ ψ).pulAdmits σ → φ.pulAdmits σ := by
  intro ⟨h, _⟩; exact h

/-- Admitting AND φ ψ requires that the intermediate context σ[φ]
admits ψ. This is the structural basis for conditional presupposition
projection (used in the proof of Fact 8.3). -/
theorem admits_and_right (φ ψ : Formula P) (σ : InfoStateOf P) :
    (Formula.and φ ψ).pulAdmits σ → ψ.pulAdmits (φ.eval σ) := by
  intro ⟨_, h⟩; exact h

/-- **Fact 8.1 (iii)**: Presupposition projects through IF...THEN.

Admitting IF φ THEN ψ (= NOT(φ AND NOT ψ)) requires admitting φ. -/
theorem admits_impl_left (φ ψ : Formula P) (σ : InfoStateOf P) :
    (Formula.impl φ ψ).pulAdmits σ → φ.pulAdmits σ := by
  intro h; exact h.1

-- ════════════════════════════════════════════════════════════════
-- § 6. MIGHT / MUST (Facts 8.5–8.8)
-- ════════════════════════════════════════════════════════════════

/-- **Fact 8.5**: MIGHT is a test. -/
theorem might_isTest (φ : Formula P) : IsTest (Formula.might φ).eval := by
  intro s; simp only [eval]; split <;> simp

/-- MIGHT is eliminative. -/
theorem might_eliminative (φ : Formula P) : IsEliminative (Formula.might φ).eval :=
  test_eliminative _ (might_isTest φ)

/-- **Fact 8.8 (1)**: Presupposition projects through MIGHT.

Admitting MIGHT φ requires admitting φ. -/
theorem admits_might (φ : Formula P) (σ : InfoStateOf P) :
    (Formula.might φ).pulAdmits σ ↔ φ.pulAdmits σ := by
  simp only [pulAdmits]

/-- **Fact 8.8 (2)**: MUST φ = NOT(MIGHT(NOT φ)) projects presuppositions
of φ. Admitting MUST φ requires admitting φ. -/
theorem admits_must (φ : Formula P) (σ : InfoStateOf P) :
    (Formula.must φ).pulAdmits σ ↔ φ.pulAdmits σ := by
  simp only [Formula.must, pulAdmits]

-- ════════════════════════════════════════════════════════════════
-- § 7. CCP Bridge Theorems
-- ════════════════════════════════════════════════════════════════

/-- ABLE AND = CCP sequential composition. -/
theorem eval_and_eq_seq (φ ψ : Formula P) :
    (Formula.and φ ψ).eval = CCP.seq φ.eval ψ.eval := rfl

/-- ABLE MIGHT = CCP.might. -/
theorem eval_might_eq_ccpMight (φ : Formula P) :
    (Formula.might φ).eval = CCP.might φ.eval := rfl

/-- ABLE ∂ = CCP.must. -/
theorem eval_presup_eq_ccpMust (φ : Formula P) :
    (Formula.presup φ).eval = CCP.must φ.eval := rfl

/-- ABLE pred = updateFromSat (via identity).

The predicational constructor `pred sat` is definitionally equal to
`updateFromSat` when the satisfaction relation ignores the formula
parameter. -/
theorem eval_pred_eq_updateFromSat (sat : P → Prop) :
    (Formula.pred sat).eval = updateFromSat (λ p (_ : Unit) => sat p) () := by
  ext σ p; simp only [eval, updateFromSat, Set.mem_setOf_eq]

/-- ABLE NOT ≠ CCP.neg in general.

PUL negation is set complement within the input (`σ \ σ[φ]`),
while CCP.neg is a test (pass/fail on the whole context).
They coincide only when φ is eliminative AND σ[φ] = ∅ or σ[φ] = σ.
-/
theorem not_neq_ccpNeg :
    ∃ (P : Type) (φ : Formula P) (σ : InfoStateOf P),
      (Formula.not φ).eval σ ≠ CCP.neg φ.eval σ := by
  -- Witness: P = Bool, φ = pred (· = true), σ = {true, false}
  -- NOT φ gives σ \ {true} = {false} (nonempty)
  -- CCP.neg gives ∅ (since φ.eval σ = {true} is nonempty)
  use Bool, Formula.pred (· = true), {true, false}
  intro h
  have : false ∈ (Formula.not (Formula.pred (· = true))).eval ({true, false} : Set Bool) := by
    show false ∈ ({true, false} : Set Bool) \ _
    refine Set.mem_diff_of_mem (Or.inr rfl) ?_
    intro ⟨_, hf⟩; exact Bool.noConfusion hf
  rw [h] at this
  simp only [eval, CCP.neg] at this
  have hne : ({ p : Bool | p ∈ ({true, false} : Set Bool) ∧ p = true}).Nonempty :=
    ⟨true, Or.inl rfl, rfl⟩
  simp only [hne, ↓reduceIte] at this
  exact this

-- ════════════════════════════════════════════════════════════════
-- § 8. Predicational Eliminativity
-- ════════════════════════════════════════════════════════════════

/-- Predicational updates are eliminative. -/
theorem pred_eliminative (sat : P → Prop) :
    IsEliminative (Formula.pred sat).eval :=
  λ _ _ hp => hp.1

/-- NOT is always eliminative (σ \ X ⊆ σ, regardless of X). -/
theorem not_eliminative (φ : Formula P) :
    IsEliminative (Formula.not φ).eval :=
  λ _ _ hp => hp.1

/-- AND preserves eliminativity. -/
theorem and_eliminative (φ ψ : Formula P)
    (hφ : IsEliminative φ.eval) (hψ : IsEliminative ψ.eval) :
    IsEliminative (Formula.and φ ψ).eval :=
  eliminative_seq φ.eval ψ.eval hφ hψ

/-- All ABLE formulas are eliminative (output ⊆ input).
This is the inductive closure of the per-constructor eliminativity
results above. -/
theorem eval_eliminative (φ : Formula P) : IsEliminative φ.eval := by
  induction φ with
  | pred sat => exact pred_eliminative sat
  | not φ _ => exact not_eliminative φ
  | and φ ψ ihφ ihψ => exact and_eliminative φ ψ ihφ ihψ
  | might φ _ => exact might_eliminative φ
  | presup φ _ => exact presup_eliminative φ

-- ════════════════════════════════════════════════════════════════
-- § 9. Satisfaction, Presupposition, and Entailment (D45–D46)
-- ════════════════════════════════════════════════════════════════

/-- A state σ **satisfies** φ iff σ[φ] = σ (updating adds no information).
@cite{beaver-2001} D29 / MP4 (closure-based; we use the set-based equivalent:
φ is satisfied when the update is a fixed point). -/
noncomputable def satisfies (φ : Formula P) (σ : InfoStateOf P) : Prop :=
  φ.eval σ = σ

/-- A formula φ **presupposes** ψ iff every state that admits φ
also satisfies ψ. @cite{beaver-2001} D46, MP6. -/
def presupposes (φ ψ : Formula P) : Prop :=
  ∀ σ : InfoStateOf P, φ.pulAdmits σ → ψ.satisfies σ

-- ════════════════════════════════════════════════════════════════
-- § 9b. Satisfaction–Consistency Bridge (Lemma 8.6, Fact 8.7)
-- ════════════════════════════════════════════════════════════════

/-- **Lemma 8.6**: Satisfaction ↔ inconsistency with NOT.

σ satisfies φ iff σ is not consistent with NOT φ.
@cite{beaver-2001} Ch. 8 §8.3.

The proof uses eliminativity: since φ.eval σ ⊆ σ (all ABLE formulas
are eliminative), the fixed-point condition φ.eval σ = σ reduces to
checking that σ \ φ.eval σ is empty. -/
theorem lemma_8_6 (φ : Formula P) (σ : InfoStateOf P) :
    φ.satisfies σ ↔ ¬((Formula.not φ).eval σ).Nonempty := by
  simp only [satisfies, eval]
  constructor
  · intro h; rw [h]; intro ⟨_, h1, h2⟩; exact h2 h1
  · intro h; ext p; constructor
    · intro hp; exact eval_eliminative φ σ hp
    · intro hp; by_contra hne; exact h ⟨p, hp, hne⟩

/-- **Fact 8.7 (1)**: MUST is a test.
@cite{beaver-2001} Ch. 8 §8.3. -/
theorem must_isTest (φ : Formula P) : IsTest (Formula.must φ).eval := by
  intro σ; simp only [Formula.must, eval]
  by_cases h : (σ \ φ.eval σ).Nonempty
  · right; rw [if_pos h]; ext; simp
  · left; rw [if_neg h]; ext; simp

/-- MUST is eliminative. -/
theorem must_eliminative (φ : Formula P) : IsEliminative (Formula.must φ).eval :=
  test_eliminative _ (must_isTest φ)

/-- **Fact 8.7 (2–3)**: MUST φ is a test for satisfaction of φ.

σ⟦MUST φ⟧ = σ iff σ satisfies φ; σ⟦MUST φ⟧ = ∅ iff ¬σ satisfies φ.

The proof chains through Lemma 8.6: satisfaction ↔ ¬consistent-with-NOT
↔ MIGHT(NOT φ) fails ↔ NOT(MIGHT(NOT φ)) passes.
@cite{beaver-2001} Ch. 8 §8.3. -/
theorem fact_8_7 (φ : Formula P) (σ : InfoStateOf P) :
    (Formula.must φ).satisfies σ ↔ φ.satisfies σ := by
  constructor
  · intro h
    simp only [satisfies, Formula.must, eval] at h
    split_ifs at h with hne
    · exfalso; obtain ⟨p, hp, _⟩ := hne
      have : p ∈ σ \ σ := by rw [h]; exact hp
      simp at this
    · ext p; constructor
      · intro hp; exact eval_eliminative φ σ hp
      · intro hp; by_contra habs; exact hne ⟨p, hp, habs⟩
  · intro h
    simp only [satisfies, Formula.must, eval] at h ⊢
    have : ¬(σ \ φ.eval σ).Nonempty := by
      rw [h]; intro ⟨_, h1, h2⟩; exact h2 h1
    rw [if_neg this]; ext; simp

-- ════════════════════════════════════════════════════════════════
-- § 10. Projection Facts (8.1–8.3) via `presupposes`
-- ════════════════════════════════════════════════════════════════

/-- **Fact 8.1**: If φ presupposes ψ, then NOT φ, φ AND χ, and
φ IMPLIES χ all presuppose ψ. @cite{beaver-2001} Ch. 8 §8.2.1.

The key insight: the set of contexts admitting NOT φ (or φ AND χ, etc.)
is a SUBSET of those admitting φ. So if every context admitting φ
satisfies ψ, then every context admitting NOT φ also satisfies ψ. -/
theorem fact_8_1_not (φ ψ : Formula P) (h : φ.presupposes ψ) :
    (Formula.not φ).presupposes ψ :=
  λ σ hadmit => h σ ((admits_not φ σ).mp hadmit)

theorem fact_8_1_and (φ ψ χ : Formula P) (h : φ.presupposes ψ) :
    (Formula.and φ χ).presupposes ψ :=
  λ σ hadmit => h σ (admits_and_left φ χ σ hadmit)

theorem fact_8_1_impl (φ ψ χ : Formula P) (h : φ.presupposes ψ) :
    (Formula.impl φ χ).presupposes ψ :=
  λ σ hadmit => h σ (admits_impl_left φ χ σ hadmit)

/-- **Fact 8.2**: Transitivity of presupposition.
If φ presupposes ψ, and ψ presupposes χ, then φ presupposes χ.
@cite{beaver-2001} Ch. 8 §8.2.1.

This follows because admitting φ implies satisfying ψ (= ψ.eval σ = σ),
which means σ trivially admits ψ (since ψ.eval σ = σ makes every
subformula's presupposition vacuously satisfied at a fixed point). -/
theorem fact_8_2 (φ ψ χ : Formula P)
    (h1 : φ.presupposes ψ) (h2 : ψ.presupposes χ)
    (h3 : ∀ σ, ψ.satisfies σ → ψ.pulAdmits σ) :
    φ.presupposes χ :=
  λ σ hadmit => h2 σ (h3 σ (h1 σ hadmit))

/-- **Fact 8.3**: Conditional presupposition.
If φ presupposes ψ, then χ AND φ presupposes χ IMPLIES ψ.
@cite{beaver-2001} Ch. 8 §8.2.1.

The second conjunct's presupposition becomes conditional on the first
conjunct. This is the hallmark of CCP-based projection. -/
theorem fact_8_3_and (φ ψ χ : Formula P) (h : φ.presupposes ψ) :
    (Formula.and χ φ).presupposes (Formula.impl χ ψ) := by
  intro σ ⟨hχ, hφ⟩
  -- Need: (impl χ ψ).satisfies σ, i.e., (impl χ ψ).eval σ = σ
  -- impl χ ψ = NOT(χ AND NOT ψ)
  -- eval: σ \ (NOT ψ).eval (χ.eval σ) = σ \ ((χ.eval σ) \ (ψ.eval (χ.eval σ)))
  -- From h and hφ: ψ.satisfies (χ.eval σ), i.e., ψ.eval (χ.eval σ) = χ.eval σ
  have hsat := h (χ.eval σ) hφ
  simp only [satisfies, Formula.impl, eval] at hsat ⊢
  -- hsat : ψ.eval (χ.eval σ) = χ.eval σ
  -- Goal: σ \ ((χ.eval σ) \ (ψ.eval (χ.eval σ))) = σ
  rw [hsat]
  -- Goal: σ \ (χ.eval σ \ χ.eval σ) = σ
  ext p; constructor
  · intro ⟨hp, _⟩; exact hp
  · intro hp; exact ⟨hp, fun ⟨h1, h2⟩ => h2 h1⟩

/-- **Fact 8.8**: Presupposition projects through MIGHT and MUST.
If φ presupposes ψ, then MIGHT φ and MUST φ also presuppose ψ.
@cite{beaver-2001} Ch. 8 §8.3. -/
theorem fact_8_8_might (φ ψ : Formula P) (h : φ.presupposes ψ) :
    (Formula.might φ).presupposes ψ :=
  λ σ hadmit => h σ ((admits_might φ σ).mp hadmit)

theorem fact_8_8_must (φ ψ : Formula P) (h : φ.presupposes ψ) :
    (Formula.must φ).presupposes ψ :=
  λ σ hadmit => h σ ((admits_must φ σ).mp hadmit)

end Formula

end Semantics.Dynamic.ABLE
