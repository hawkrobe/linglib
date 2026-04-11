import Linglib.Theories.Semantics.Comparison.Metalinguistic
import Linglib.Theories.Semantics.Comparison.MetalinguisticDegree

/-!
# @cite{rudolph-kocurek-2024}: Metalinguistic Gradability

@cite{rudolph-kocurek-2024}

Rachel Etta Rudolph & Alexander W. Kocurek. 2024. Metalinguistic gradability.
*Semantics & Pragmatics* 17, Article 7: 1-58.

## Overview

Finite model verification of the semantic expressivist framework for
metalinguistic comparatives ("Ann is more a linguist than a philosopher"),
equatives, degree modifiers, and conditionals. Verifies the paper's
entailment predictions (§4.4), assertoric content (§3.3), nonclassicality
of acceptance-preservation (§4.4), degree modifiers `very`/`sorta`/
`mostly` (§6.1), metalinguistic conditionals (§6.3), the No Reversal
bridge to delineation comparatives (§7), and the **revised semantics**
for ME transitivity (Supplement §B).

## Models

**Model 1** (3 interpretations, linear order i₀ < i₁ < i₂):
- i₀: Ann is a philosopher, not a linguist
- i₁: Ann is a linguist, not a philosopher
- i₂: Ann is both a linguist and a philosopher

Captures "Ann is more a linguist than a philosopher": at i₂ (top-ranked),
both hold, and the (La∧¬Pa)-witness i₁ outranks the (Pa∧¬La)-witness i₀.

**Model 2** (2 interpretations, tied j₀ ≡ j₁):
- j₀: La true, Pa false
- j₁: La false, Pa true

Witnesses borderline cases, equative satisfaction, and nonclassicality
of acceptance-preservation (parallels informational entailment for
epistemic modals, @cite{yalcin-2007}).

**Model 3** (3 interpretations, linear i₀ < i₁ < i₂, two entities):
- i₀: neither Ann nor Ben is tall
- i₁: Ann is tall, Ben is not
- i₂: both are tall

Satisfies No Reversal for `tall`: extensions are monotonically nested.
Demonstrates that under NR, the MC simplifies to the delineation
comparative (§7). A counterexample model violating NR shows that
MC and delineation diverge without this constraint.

**Model 4** (4 interpretations, 3 propositions, ordering l < j ≡ k < i):
- i: Ann is a linguist, philosopher, and psychologist (1,1,1)
- j: Ann is a linguist and psychologist, not a philosopher (1,0,1)
- k: Ann is a philosopher only (0,1,0)
- l: Ann is a linguist and philosopher, not a psychologist (1,1,0)

Counterexample to ME transitivity in the basic semantics (Supplement §B):
La ≈ Pa and Pa ≈ Ca hold, but La ≈ Ca fails (La ≻ Ca holds vacuously).
The revised semantics (`evalRevised`) blocks La ≻ Ca and restores
transitivity.

## Connections

- **Theory layer**: `Theories/Semantics/Comparison/Metalinguistic.lean`
  (SemanticOrdering, MFormula, eval, evalRevised, evalGen, evalMCond,
  assertoricContent, DistanceFunction, evalVery/evalSorta/evalMostly,
  noReversal, MetalinguisticCG)
- **Delineation**: `Theories/Semantics/Comparison/Delineation.lean`
  (@cite{klein-1980}'s comparison class approach — connected via No Reversal)
- **Hierarchy**: `Theories/Semantics/Comparison/Hierarchy.lean`
  (Klein ← Kennedy ← Measurement strict hierarchy)
-/

namespace Phenomena.Gradability.RudolphKocurek2024

open Semantics.Comparison.Metalinguistic


-- ════════════════════════════════════════════════════════════════
-- § 1. Types (shared across models)
-- ════════════════════════════════════════════════════════════════

/-- One world. -/
inductive W | w0
  deriving DecidableEq, Repr

instance : Fintype W where
  elems := {.w0}
  complete := by intro x; cases x; simp

/-- Two predicates: linguist and philosopher. -/
inductive Pred | linguist | philosopher
  deriving DecidableEq, Repr

instance : Fintype Pred where
  elems := {.linguist, .philosopher}
  complete := by intro x; cases x <;> simp

/-- One entity: Ann. -/
inductive Entity | ann
  deriving DecidableEq, Repr

instance : Fintype Entity where
  elems := {.ann}
  complete := by intro x; cases x; simp

/-- "Ann is a linguist" -/
abbrev La : MFormula Pred Entity := .atom .linguist .ann

/-- "Ann is a philosopher" -/
abbrev Pa : MFormula Pred Entity := .atom .philosopher .ann

/-- "Ann is more a linguist than a philosopher" -/
abbrev La_mc_Pa : MFormula Pred Entity := .mc La Pa

/-- "Ann is (exactly) as much a linguist as a philosopher" -/
abbrev La_me_Pa : MFormula Pred Entity := La.me Pa


-- ════════════════════════════════════════════════════════════════
-- § 2. Model 1: Three interpretations (linear order)
-- ════════════════════════════════════════════════════════════════

/-- Three interpretations: i₀ < i₁ < i₂. -/
inductive I3 | i0 | i1 | i2
  deriving DecidableEq, Repr

instance : Fintype I3 where
  elems := {.i0, .i1, .i2}
  complete := by intro x; cases x <;> simp

/-- Linear ordering: i0 ≤ i1 ≤ i2. -/
def ord₃ : SemanticOrdering I3 :=
  SemanticOrdering.ofBool
    (λ i j => match i, j with
      | .i0, _ => true
      | .i1, .i0 => false
      | .i1, _ => true
      | .i2, .i2 => true
      | .i2, _ => false)
    (by intro i; cases i <;> rfl)
    (by intro i j k hij hjk; cases i <;> cases j <;> cases k <;> simp_all)
    (by intro i j; cases i <;> cases j <;> simp)

/-- Interpretation function:
- i₀: Ann is a philosopher, not a linguist
- i₁: Ann is a linguist, not a philosopher
- i₂: Ann is both -/
def interp₃ : I3 → Interpretation W Pred Entity
  | .i0 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩
  | .i1 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩
  | .i2 => ⟨λ _ _ _ => true⟩


-- ════════════════════════════════════════════════════════════════
-- § 3. Observations on Model 1
-- ════════════════════════════════════════════════════════════════

/-- Observation 1a: MCs are consistent with truth of both constituents.
At i₂, Ann is both a linguist and a philosopher, yet "Ann is more a
linguist than a philosopher" is true — the (La∧¬Pa)-interpretation i₁
outranks the (Pa∧¬La)-interpretation i₀. -/
theorem obs1a_mc_consistent_with_both :
    eval interp₃ La_mc_Pa ord₃ .i2 .w0 = true ∧
    eval interp₃ La ord₃ .i2 .w0 = true ∧
    eval interp₃ Pa ord₃ .i2 .w0 = true := by native_decide

/-- The MC is also true at i₁ (where Ann is a linguist but not a
philosopher). -/
theorem mc_true_at_i1 :
    eval interp₃ La_mc_Pa ord₃ .i1 .w0 = true := by native_decide

/-- The MC is false at i₀ (no (La∧¬Pa)-witness at or below i₀). -/
theorem mc_false_at_i0 :
    eval interp₃ La_mc_Pa ord₃ .i0 .w0 = false := by native_decide

/-- Observation 2: A ≻ B, B ⊨ A.
If the MC holds and Ann is a philosopher, she is a linguist. -/
theorem obs2_mc_B_entails_A :
    ∀ (i : I3),
      eval interp₃ La_mc_Pa ord₃ i .w0 = true →
      eval interp₃ Pa ord₃ i .w0 = true →
      eval interp₃ La ord₃ i .w0 = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 4. Entailment Predictions (§4.4)
-- ════════════════════════════════════════════════════════════════

/-- (e) Asymmetry: A ≻ B ⊨ ¬(B ≻ A) on this model. -/
theorem asymmetry :
    ∀ (i : I3),
      eval interp₃ La_mc_Pa ord₃ i .w0 = true →
      eval interp₃ (.mc Pa La) ord₃ i .w0 = false := by native_decide

/-- (f) Irreflexivity: ⊨ ¬(A ≻ A). No sentence is more the case than itself. -/
theorem irreflexivity :
    ∀ (i : I3),
      eval interp₃ (.mc La La) ord₃ i .w0 = false := by native_decide

/-- (k) Equative reflexivity: ⊨ A ≈ A. -/
theorem equative_reflexivity :
    ∀ (i : I3),
      eval interp₃ (La.me La) ord₃ i .w0 = true := by native_decide

/-- (l) Equative symmetry: A ≈ B ⊨ B ≈ A on this model. -/
theorem equative_symmetry :
    ∀ (i : I3),
      eval interp₃ La_me_Pa ord₃ i .w0 = true →
      eval interp₃ (Pa.me La) ord₃ i .w0 = true := by native_decide

/-- Observation 4: A ≈ B ⊨ ¬(A ≻ B) ∧ ¬(B ≻ A). (By definition.) -/
theorem obs4_me_entails_no_mc :
    ∀ (i : I3),
      eval interp₃ La_me_Pa ord₃ i .w0 = true →
      eval interp₃ (.neg La_mc_Pa) ord₃ i .w0 = true ∧
      eval interp₃ (.neg (.mc Pa La)) ord₃ i .w0 = true := by native_decide

/-- (g) Transitivity: A ≻ B, B ≻ C ⊨ A ≻ C. -/
theorem transitivity :
    ∀ (i : I3),
      eval interp₃ (.mc La Pa) ord₃ i .w0 = true →
      eval interp₃ (.mc Pa (.neg La)) ord₃ i .w0 = true →
      eval interp₃ (.mc La (.neg La)) ord₃ i .w0 = true := by native_decide

/-- (h) Contraposition: A ≻ B ⊨ ¬B ≻ ¬A. -/
theorem contraposition :
    ∀ (i : I3),
      eval interp₃ La_mc_Pa ord₃ i .w0 = true →
      eval interp₃ (.mc (.neg Pa) (.neg La)) ord₃ i .w0 = true := by native_decide

/-- (n) Trichotomy (requires totality of ≤):
⊨ (A ≻ B) ∨ (B ≻ A) ∨ (A ≈ B). -/
theorem trichotomy :
    ∀ (i : I3),
      (eval interp₃ (.mc La Pa) ord₃ i .w0 ||
       eval interp₃ (.mc Pa La) ord₃ i .w0 ||
       eval interp₃ (La.me Pa) ord₃ i .w0) = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 5. Model 2: Two interpretations (tied) for borderline cases
-- ════════════════════════════════════════════════════════════════

/-- Two interpretations for borderline / nonclassicality witnesses. -/
inductive I2 | j0 | j1
  deriving DecidableEq, Repr

instance : Fintype I2 where
  elems := {.j0, .j1}
  complete := by intro x; cases x <;> simp

/-- Tied ordering: j0 ≡ j1 (both maximal). -/
def tiedOrd : SemanticOrdering I2 :=
  SemanticOrdering.ofBool
    (λ _ _ => true)
    (by intro i; cases i <;> rfl)
    (by intro i j k _ _; cases i <;> cases j <;> cases k <;> rfl)
    (by intro i j; left; cases i <;> cases j <;> rfl)

/-- j₀: La true, Pa false; j₁: La false, Pa true. -/
def interp₂ : I2 → Interpretation W Pred Entity
  | .j0 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩
  | .j1 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩

/-- Observation 5: A ≈ ¬A is satisfiable (not contradictory).
With tied interpretations where one makes La true and the other
makes La false, "Ann is (exactly) as much a linguist as not"
is coherent — it expresses a borderline case. -/
theorem obs5_me_neg_consistent :
    eval interp₂ (La.me (.neg La)) tiedOrd .j0 .w0 = true := by native_decide

/-- La ≈ Pa holds on the tied model (both MCs are blocked by ties). -/
theorem me_on_tied :
    ∀ (i : I2),
      eval interp₂ (La.me Pa) tiedOrd i .w0 = true := by native_decide

/-- ¬La -/
abbrev NLa : MFormula Pred Entity := .neg La

/-- ¬Pa -/
abbrev NPa : MFormula Pred Entity := .neg Pa

/-- (m) Negation equative: A ≈ B ⊨ ¬A ≈ ¬B (on the tied model). -/
theorem negation_equative :
    ∀ (i : I2),
      eval interp₂ (La.me Pa) tiedOrd i .w0 = true →
      eval interp₂ (NLa.me NPa) tiedOrd i .w0 = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 6. Assertoric Content and Acceptance-Preservation
-- ════════════════════════════════════════════════════════════════

/-- The assertoric content of "Ann is a linguist" holds on ord₃:
the top-ranked interpretation (i₂) makes La true. -/
theorem la_assertoric :
    assertoricContent interp₃ La ord₃ .w0 = true := by native_decide

/-- The assertoric content of "Ann is a philosopher" also holds
on ord₃ (i₂ makes Pa true). -/
theorem pa_assertoric :
    assertoricContent interp₃ Pa ord₃ .w0 = true := by native_decide

/-- The assertoric content of La_mc_Pa holds on ord₃:
at the unique maximal interpretation i₂, the MC evaluates to true. -/
theorem mc_assertoric :
    assertoricContent interp₃ La_mc_Pa ord₃ .w0 = true := by native_decide

/- Observation 3 (acceptance-preservation): A ∧ ¬B ⊩ A ≻ B.
If assertoric content of (La ∧ ¬Pa) holds, then assertoric content of
La ≻ Pa holds. On ord₃, the premise fails (Pa is true at i₂), so
the implication holds vacuously. We verify the substantive case on a
model where the premise holds. -/

/-- For substantive Obs 3: i₂ is linguist only. -/
def interp₃' : I3 → Interpretation W Pred Entity
  | .i0 => ⟨λ P _ _ => match P with | .linguist => false | .philosopher => true⟩
  | .i1 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => true⟩
  | .i2 => ⟨λ P _ _ => match P with | .linguist => true  | .philosopher => false⟩

theorem obs3_acceptance :
    assertoricContent interp₃' (.conj La (.neg Pa)) ord₃ .w0 = true →
    assertoricContent interp₃' La_mc_Pa ord₃ .w0 = true := by native_decide

/-- The tautology La ∨ ¬La has assertoric content 1 on the tied model. -/
theorem tautology_accepted :
    assertoricContent interp₂ (.disj La (.neg La)) tiedOrd .w0 = true := by
  native_decide

/-- Nonclassicality of acceptance-preservation:
(La ≻ ¬La) ∨ (¬La ≻ La) does NOT have assertoric content 1 on the
tied model. At both maximal interpretations (j₀ ≡ j₁), neither
direction of MC holds because the interpretations are tied.

This is the key result paralleling informational entailment for
epistemic modals (@cite{yalcin-2007}). -/
theorem mc_disj_not_accepted :
    assertoricContent interp₂ (.disj (.mc La (.neg La)) (.mc (.neg La) La))
      tiedOrd .w0 = false := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 7. Degree Modifiers (§6.1)
-- ════════════════════════════════════════════════════════════════

/-- Distance function for ord₃: close(i) includes interpretations at the
same level or one level below.
- d(i₀) = {i₀}
- d(i₁) = {i₀, i₁}
- d(i₂) = {i₁, i₂} -/
def dist₃ : DistanceFunction I3 ord₃ where
  close := λ i i' => match i, i' with
    | .i0, .i0 => true
    | .i1, .i0 => true
    | .i1, .i1 => true
    | .i2, .i1 => true
    | .i2, .i2 => true
    | _, _ => false
  centered := by intro i; cases i <;> rfl
  topBounded := by decide
  convex := by decide
  noncontractive := by decide

/-- very La is true at i₂: all interpretations reasonably close to i₂
(namely i₁ and i₂) make La true. -/
theorem very_la_at_top :
    evalVery interp₃ La ord₃ dist₃ .i2 .w0 = true := by native_decide

/-- very La is false at i₁: i₀ is reasonably close to i₁ but
makes La false. -/
theorem very_la_false_at_mid :
    evalVery interp₃ La ord₃ dist₃ .i1 .w0 = false := by native_decide

/-- very A ⊨ A: if very La holds, then La holds (centeredness). -/
theorem very_entails_positive :
    ∀ (i : I3),
      evalVery interp₃ La ord₃ dist₃ i .w0 = true →
      eval interp₃ La ord₃ i .w0 = true := by native_decide

/-- sorta La holds at i₁: some close interpretation (i₁ itself) makes
La true, even though another close interpretation (i₀) does not. -/
theorem sorta_la_at_mid :
    evalSorta interp₃ La ord₃ dist₃ .i1 .w0 = true := by native_decide

/-- sorta La is false at i₀: d(i₀) = {i₀}, and La is false at i₀. -/
theorem sorta_la_false_at_bot :
    evalSorta interp₃ La ord₃ dist₃ .i0 .w0 = false := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 8. Degree Modifier: mostly (§6.1)
-- ════════════════════════════════════════════════════════════════

/-- mostly La is true at i₂: there is a reasonably high level (i₁) where
La is uniformly true, and the only A-false level (i₀) is below it. -/
theorem mostly_la_at_top :
    evalMostly interp₃ La ord₃ dist₃ .i2 .w0 = true := by native_decide

/-- mostly La is false at i₁: i₀ is the only candidate level below i₁ in
d(i₁), but La is false at i₀. -/
theorem mostly_la_false_at_mid :
    evalMostly interp₃ La ord₃ dist₃ .i1 .w0 = false := by native_decide

/-- mostly A ⊨ sorta A (on this model): if A is mostly the case, then
it is sorta the case. -/
theorem mostly_entails_sorta :
    ∀ (i : I3),
      evalMostly interp₃ La ord₃ dist₃ i .w0 = true →
      evalSorta interp₃ La ord₃ dist₃ i .w0 = true := by native_decide

/-- very A ⊨ mostly A (on this model). -/
theorem very_entails_mostly :
    ∀ (i : I3),
      evalVery interp₃ La ord₃ dist₃ i .w0 = true →
      evalMostly interp₃ La ord₃ dist₃ i .w0 = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 9. Bridge: No Reversal and Ordinary Comparison (§7)
-- ════════════════════════════════════════════════════════════════

/-- No Reversal holds trivially on single-entity models (the antecedent
e₁ ≠ e₂ can never be satisfied). For a substantive NR test, a
two-entity model is needed.

The key consequence of NR: when it holds, `Fa ≻ Gb` simplifies to the
**delineation comparative** `∃ i' ≤ i : Fa∧¬Gb` — the universal clause
of eq. (48) becomes redundant. This connects metalinguistic
comparatives to @cite{klein-1980}'s supervaluation comparative
(see `Theories/Semantics/Comparison/Delineation.lean`) and
@cite{kamp-1975}'s completion-based approach. -/
theorem nr_trivial_single_entity :
    noReversal interp₃ ord₃ .linguist .w0 .ann .ann := by
  intro i _ _ h1 h2; simp_all


-- ════════════════════════════════════════════════════════════════
-- § 10. Two-Entity Model: No Reversal (§7)
-- ════════════════════════════════════════════════════════════════

/-- Two entities for gradable adjective models. -/
inductive Entity2 | ann | ben
  deriving DecidableEq, Repr

instance : Fintype Entity2 where
  elems := {.ann, .ben}
  complete := by intro x; cases x <;> simp

/-- Single predicate: tall. -/
inductive Pred1 | tall
  deriving DecidableEq, Repr

instance : Fintype Pred1 where
  elems := {.tall}
  complete := by intro x; cases x; simp

/-- NR model for "Ann is taller than Ben":
- i₀: neither Ann nor Ben is tall (empty extension)
- i₁: Ann is tall, Ben is not (Ann enters the extension first)
- i₂: both are tall

Satisfies No Reversal: extensions are monotonically nested
({} ⊆ {ann} ⊆ {ann, ben}). Uses the same 3-interpretation
linear order `ord₃` from Model 1. -/
def interpNR : I3 → Interpretation W Pred1 Entity2
  | .i0 => ⟨λ _ _ _ => false⟩
  | .i1 => ⟨λ _ _ e => match e with | .ann => true | .ben => false⟩
  | .i2 => ⟨λ _ _ _ => true⟩

/-- "Ann is tall" -/
abbrev Ta : MFormula Pred1 Entity2 := .atom .tall .ann

/-- "Ben is tall" -/
abbrev Tb : MFormula Pred1 Entity2 := .atom .tall .ben

/-- No Reversal holds for `tall` on the two-entity model.
Since Ann enters the extension before Ben (at i₁ vs i₂), there is no
interpretation where Ben is tall but Ann is not. NR is satisfied
because the extensions are monotonically nested.

Compare with `nr_trivial_single_entity` above, which holds vacuously
on a single-entity model. Here NR constrains the relationship between
two distinct entities' extensions across the ordering. -/
theorem nr_tall_ann_ben :
    noReversal interpNR ord₃ .tall .w0 .ann .ben := by
  intro i i' _ h1 h2 h3; cases i <;> cases i' <;> simp [interpNR] at *

/-- Ann is taller than Ben: the MC `tall(ann) ≻ tall(ben)` is true
at i₁ and i₂. Witness: i₁ (Ann is tall, Ben is not). -/
theorem ann_taller_i1 :
    eval interpNR (.mc Ta Tb) ord₃ .i1 .w0 = true := by native_decide

theorem ann_taller_i2 :
    eval interpNR (.mc Ta Tb) ord₃ .i2 .w0 = true := by native_decide

/-- The MC is false at i₀ (no witness: Ann is not tall at i₀). -/
theorem ann_not_taller_i0 :
    eval interpNR (.mc Ta Tb) ord₃ .i0 .w0 = false := by native_decide

/-- The reverse MC — Ben taller than Ann — is false everywhere.
There is no interpretation where Ben is tall but Ann is not. -/
theorem ben_not_taller :
    ∀ (i : I3), eval interpNR (.mc Tb Ta) ord₃ i .w0 = false := by native_decide

/-- Bridge: under NR, the full MC (eq. 48, with domination clause)
gives the same result as the delineation comparative (eq. 128,
just ∃ i' ≤ i : Fa ∧ ¬Fb, without domination clause).

NR makes clause (ii) of the MC redundant: if Fa is true and Fb is
false at i, then for any i' ≤ i where Fb becomes true, Fa must also
be true — so there are no (Fb∧¬Fa)-witnesses to worry about.

This connects metalinguistic comparatives to @cite{klein-1980}'s
delineation comparative (see `Delineation.lean`). -/
theorem mc_equals_delineation_under_nr :
    ∀ (i : I3),
      -- Full MC with domination clause
      eval interpNR (.mc Ta Tb) ord₃ i .w0 =
      -- Delineation: just check for a witness (no domination needed)
      (decide (∃ i' : I3, ord₃.le i' i ∧
        (interpNR i').ext .tall .w0 .ann = true ∧
        (interpNR i').ext .tall .w0 .ben = false) : Bool) := by native_decide

/-- NR-violating model: Ann and Ben "swap" across interpretations.
- i₀: Ann tall, Ben not
- i₁: Ben tall, Ann not (reversal!)
- i₂: both tall -/
def interpNR_bad : I3 → Interpretation W Pred1 Entity2
  | .i0 => ⟨λ _ _ e => match e with | .ann => true | .ben => false⟩
  | .i1 => ⟨λ _ _ e => match e with | .ann => false | .ben => true⟩
  | .i2 => ⟨λ _ _ _ => true⟩

/-- No Reversal fails on the violating model (for e₁=ben, e₂=ann):
Ben is tall at i₁ and Ann is not, but at i₀ ≤ i₁ where Ann is tall,
Ben is not — a reversal. -/
theorem nr_fails_bad :
    ¬ noReversal interpNR_bad ord₃ .tall .w0 .ben .ann := by
  intro h; exact absurd (h .i1 .i0 rfl rfl rfl rfl) (by native_decide)

/-- Without NR, MC and delineation diverge: the MC `Ta ≻ Tb` is
FALSE at i₂ (the (Tb∧¬Ta)-witness i₁ outranks the (Ta∧¬Tb)-witness
i₀, violating the domination clause), but the simple delineation
condition (∃ Fa∧¬Fb) is TRUE (i₀ is a witness). -/
theorem mc_delineation_diverge_without_nr :
    eval interpNR_bad (.mc Ta Tb) ord₃ .i2 .w0 = false ∧
    (decide (∃ i' : I3, ord₃.le i' .i2 ∧
      (interpNR_bad i').ext .tall .w0 .ann = true ∧
      (interpNR_bad i').ext .tall .w0 .ben = false) : Bool) = true :=
  ⟨by native_decide, by native_decide⟩


-- ════════════════════════════════════════════════════════════════
-- § 11. Metalinguistic Conditional (§6.3)
-- ════════════════════════════════════════════════════════════════

/-- Reflexivity: A → A is true everywhere (every A-interpretation
trivially makes A true on any ordering). -/
theorem mcond_reflexive :
    ∀ (i : I3),
      evalMCond interp₃ La La ord₃ i .w0 = true := by native_decide

/-- La → Pa fails at i₂ on Model 1: the La-restricted ordering ≤_{La}
includes i₁ (where La is true but Pa is false), so there exists
a ranked La-interpretation that does not satisfy Pa.

This shows → is NOT the material conditional — La and Pa are
both true at i₂, but the conditional is false because it quantifies
over all ranked La-interpretations, not just the current one. -/
theorem mcond_la_pa_false :
    evalMCond interp₃ La Pa ord₃ .i2 .w0 = false := by native_decide

/-- Observation M1 (§6.3): ⊨ A → (A ≻ ¬A).

"If Pluto is a planet, then it's more a planet than not" is classically
valid. On ≤_A (restricted to A-interpretations), A ≻ ¬A trivially holds:
every A-interpretation makes A true, so the (A∧¬(¬A))-witness exists,
and there are no (¬A∧¬A)-witnesses in the restricted ordering.

This parallels the validity of epistemic "if p then probably p"
(@cite{yalcin-2007}). -/
theorem mcond_m1 :
    ∀ (i : I3),
      evalMCond interp₃ La (.mc La NLa) ord₃ i .w0 = true := by native_decide

/-- M1 also holds on the tied model (Model 2), where the
A-restricted ordering collapses to the single A-interpretation. -/
theorem mcond_m1_tied :
    ∀ (i : I2),
      evalMCond interp₂ La (.mc La NLa) tiedOrd i .w0 = true := by native_decide

-- ════════════════════════════════════════════════════════════════
-- § 12. ME Transitivity: Basic vs Revised Semantics (Supplement §B)
-- ════════════════════════════════════════════════════════════════

/-! ### ME transitivity counterexample

The basic semantics fails to validate ME transitivity:
`A ≈ B, B ≈ C ⊭ A ≈ C` (Supplement §B). Model 4 provides a minimal
counterexample.

Key insight: the (La∧¬Ca)-witness l has no matching (Ca∧¬La)-witness,
so `La ≻ Ca` holds vacuously under the basic semantics. The revised
semantics blocks this: l must dominate either all Ca-interpretations
(i and j are above it) or all ¬La-interpretations (k is above it),
and it can do neither. -/

/-- Three predicates for the transitivity counterexample. -/
inductive Pred3 | linguist | philosopher | psychologist
  deriving DecidableEq, Repr

instance : Fintype Pred3 where
  elems := {.linguist, .philosopher, .psychologist}
  complete := by intro x; cases x <;> simp

/-- Four interpretations for the transitivity counterexample. -/
inductive I4 | i | j | k | l
  deriving DecidableEq, Repr

instance : Fintype I4 where
  elems := {.i, .j, .k, .l}
  complete := by intro x; cases x <;> simp

/-- Ordering: l < j ≡ k < i (three levels).
j and k are tied at the middle level — this is essential for the
equatives La ≈ Pa and Pa ≈ Ca to hold (witnesses block each other). -/
def ord₄ : SemanticOrdering I4 :=
  SemanticOrdering.ofBool
    (λ x y => match x, y with
      | .l, _ => true
      | .j, .l => false
      | .j, _ => true
      | .k, .l => false
      | .k, _ => true
      | .i, .i => true
      | .i, _ => false)
    (by intro x; cases x <;> rfl)
    (by intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all)
    (by intro x y; cases x <;> cases y <;> simp)

/-- Interpretation function for transitivity counterexample:
- i: all three true  (linguist, philosopher, psychologist)
- j: linguist and psychologist only (philosopher false)
- k: philosopher only (linguist and psychologist false)
- l: linguist and philosopher only (psychologist false)

The (La∧¬Pa)-witness j and (Pa∧¬La)-witness k are at the same level,
ensuring neither MC direction holds for La vs Pa (and similarly for
Pa vs Ca). But the only (La∧¬Ca)-witness is l at the bottom, with no
(Ca∧¬La)-witness anywhere. -/
def interp₄ : I4 → Interpretation W Pred3 Entity
  | .i => ⟨λ _ _ _ => true⟩
  | .j => ⟨λ P _ _ => match P with
    | .linguist => true | .philosopher => false | .psychologist => true⟩
  | .k => ⟨λ P _ _ => match P with
    | .linguist => false | .philosopher => true | .psychologist => false⟩
  | .l => ⟨λ P _ _ => match P with
    | .linguist => true | .philosopher => true | .psychologist => false⟩

/-- "Ann is a linguist" (3-predicate model) -/
abbrev La₄ : MFormula Pred3 Entity := .atom .linguist .ann

/-- "Ann is a philosopher" (3-predicate model) -/
abbrev Pa₄ : MFormula Pred3 Entity := .atom .philosopher .ann

/-- "Ann is a psychologist" -/
abbrev Ca₄ : MFormula Pred3 Entity := .atom .psychologist .ann

-- ── Basic semantics: transitivity fails ──────────────────────

/-- A ≈ B holds: Ann is as much a linguist as a philosopher.
The (La∧¬Pa)-witness j and (Pa∧¬La)-witness k are tied at the middle
level, blocking both MC directions. -/
theorem me_basic_la_pa :
    eval interp₄ (La₄.me Pa₄) ord₄ .i .w0 = true := by native_decide

/-- B ≈ C holds: Ann is as much a philosopher as a psychologist.
The (Pa∧¬Ca)-witnesses k, l and (Ca∧¬Pa)-witness j are balanced:
k is tied with j, blocking both MC directions. -/
theorem me_basic_pa_ca :
    eval interp₄ (Pa₄.me Ca₄) ord₄ .i .w0 = true := by native_decide

/-- A ≈ C FAILS: basic semantics predicts Ann is MORE a linguist
than a psychologist. ME transitivity is violated. -/
theorem me_basic_la_ca_fails :
    eval interp₄ (La₄.me Ca₄) ord₄ .i .w0 = false := by native_decide

/-- The failure mechanism: La ≻ Ca holds in the basic semantics.
The (La∧¬Ca)-witness l dominates all (Ca∧¬La)-interpretations
vacuously — there are none (Ca is true only at i and j, where La
is also true). -/
theorem mc_basic_la_gt_ca :
    eval interp₄ (.mc La₄ Ca₄) ord₄ .i .w0 = true := by native_decide

-- ── Revised semantics: transitivity restored ─────────────────

/-- Under the revised semantics, La ≻ Ca is blocked: the (La∧¬Ca)-
witness l cannot dominate all Ca-interpretations (i and j are above
it) or all ¬La-interpretations (k is above it). -/
theorem mc_revised_la_ca_blocked :
    evalRevised interp₄ (.mc La₄ Ca₄) ord₄ .i .w0 = false := by native_decide

/-- ME transitivity is restored: A ≈ C holds under the revised
semantics, as required by transitivity from A ≈ B and B ≈ C. -/
theorem me_revised_la_ca :
    evalRevised interp₄ (La₄.me Ca₄) ord₄ .i .w0 = true := by native_decide

/-- The revised semantics preserves A ≈ B (no regression). -/
theorem me_revised_la_pa :
    evalRevised interp₄ (La₄.me Pa₄) ord₄ .i .w0 = true := by native_decide

/-- The revised semantics preserves B ≈ C (no regression). -/
theorem me_revised_pa_ca :
    evalRevised interp₄ (Pa₄.me Ca₄) ord₄ .i .w0 = true := by native_decide

-- ── Agreement on Model 1 ────────────────────────────────────

/-- On Model 1 (linear ordering), the revised MC agrees with the basic
MC. The two diverge only when the revised semantics' stronger domination
clause matters — on a linear ordering with no ties at critical levels,
the basic witnesses satisfy the revised conditions too. -/
theorem revised_agrees_model1 :
    ∀ (x : I3),
      eval interp₃ La_mc_Pa ord₃ x .w0 =
      evalRevised interp₃ La_mc_Pa ord₃ x .w0 := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 13. Degree Theory (Supplement §C) — Finite Verifications
-- ════════════════════════════════════════════════════════════════

open Semantics.Comparison.MetalinguisticDegree

/-! ### Degree theory on finite models

Finite model verifications that the degree-theoretic formulation
(Supplement §C) correctly tracks the revised semantics on Models 1–4.
The key bridge theorems (Facts 9–10) are stated in
`MetalinguisticDegree.lean`; here we verify their instances on
concrete models via `native_decide`. -/

-- ── Denotation sets on Model 1 ──────────────────────────────

/-- The denotation of La on Model 1: {i₁, i₂} (La true at i₁ and i₂). -/
theorem la_denotation :
    denotation interp₃ La ord₃ .i2 .w0 = {.i1, .i2} := by native_decide

/-- The denotation of Pa on Model 1: {i₀, i₂} (Pa true at i₀ and i₂). -/
theorem pa_denotation :
    denotation interp₃ Pa ord₃ .i2 .w0 = {.i0, .i2} := by native_decide

-- ── Degree equivalence ∼ on Model 1 ────────────────────────

/-- ∼ reflexivity: ⟦La⟧ ∼ ⟦La⟧ (verified by decidable computation). -/
theorem degreeEquiv_la_la :
    degreeEquivB ord₃ .i2
      (denotation interp₃ La ord₃ .i2 .w0)
      (denotation interp₃ La ord₃ .i2 .w0) = true := by native_decide

/-- La ≻ Pa on Model 1 under revised semantics: the denotation sets
are NOT degree-equivalent (La outranks Pa). -/
theorem degreeEquiv_la_pa_false :
    degreeEquivB ord₃ .i2
      (denotation interp₃ La ord₃ .i2 .w0)
      (denotation interp₃ Pa ord₃ .i2 .w0) = false := by native_decide

/-- ⊐ confirms: ⟦La⟧ ⊐ ⟦Pa⟧ (La's denotation strictly better). -/
theorem strictlyBetter_la_pa :
    strictlyBetterB ord₃ .i2
      (denotation interp₃ La ord₃ .i2 .w0)
      (denotation interp₃ Pa ord₃ .i2 .w0) = true := by native_decide

/-- The reverse direction fails: ⟦Pa⟧ ⋣ ⟦La⟧. -/
theorem strictlyBetter_pa_la_false :
    strictlyBetterB ord₃ .i2
      (denotation interp₃ Pa ord₃ .i2 .w0)
      (denotation interp₃ La ord₃ .i2 .w0) = false := by native_decide

-- ── Degree theory on Model 4 (transitivity) ────────────────

/-- La ≈ Pa on Model 4: denotation sets are degree-equivalent. -/
theorem degreeEquiv_la_pa_model4 :
    degreeEquivB ord₄ .i
      (denotation interp₄ La₄ ord₄ .i .w0)
      (denotation interp₄ Pa₄ ord₄ .i .w0) = true := by native_decide

/-- Pa ≈ Ca on Model 4: denotation sets are degree-equivalent. -/
theorem degreeEquiv_pa_ca_model4 :
    degreeEquivB ord₄ .i
      (denotation interp₄ Pa₄ ord₄ .i .w0)
      (denotation interp₄ Ca₄ ord₄ .i .w0) = true := by native_decide

/-- La ≈ Ca on Model 4 (revised): denotation sets are degree-equivalent.
This is the key test: ∼ transitivity gives us deg(La) = deg(Ca) even
though the basic MC incorrectly predicts La ≻ Ca. -/
theorem degreeEquiv_la_ca_model4 :
    degreeEquivB ord₄ .i
      (denotation interp₄ La₄ ord₄ .i .w0)
      (denotation interp₄ Ca₄ ord₄ .i .w0) = true := by native_decide

/-- ⊐ correctly blocks La ⊐ Ca on Model 4. -/
theorem strictlyBetter_la_ca_model4_false :
    strictlyBetterB ord₄ .i
      (denotation interp₄ La₄ ord₄ .i .w0)
      (denotation interp₄ Ca₄ ord₄ .i .w0) = false := by native_decide


end Phenomena.Gradability.RudolphKocurek2024
