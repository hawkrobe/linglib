/-
# RSA Core

Core RSA infrastructure with exact rational arithmetic (Frank & Goodman 2012).
Provides `RSAScenario`, `RSA.L0/S0/S1/L1_world`, and smart constructors.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.FinEnum
import Linglib.Theories.Pragmatics.RSA.Core.Distribution

section ChainVariant

/-- RSA chain variant: L0-based (standard) or S0-based (production-first). -/
inductive RSA.ChainVariant
  | L0Based  -- L0 → S1 → L1 (literal listener base, standard)
  | S0Based  -- S0 → L1 → S1 (literal speaker base)
  deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString RSA.ChainVariant where
  toString
    | .L0Based => "L0-based (L0→S1→L1)"
    | .S0Based => "S0-based (S0→L1→S1)"

end ChainVariant

section UtilityFunctions

/-- Convert Bool to ℚ (1 if true, 0 if false). -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

end UtilityFunctions

section RSAScenario

/-- Parametric RSA scenario with Fintype constraints for exact computation. -/
structure RSAScenario (U W : Type) [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W] where
  /-- Interpretation type -/
  Interp : Type := Unit
  /-- Lexicon type -/
  Lexicon : Type := Unit
  /-- Belief state type -/
  BeliefState : Type := Unit
  /-- Goal/QUD type -/
  Goal : Type := Unit
  /-- Agreement function φ(i,l,u,w) ∈ [0,1] -/
  φ : Interp → Lexicon → U → W → ℚ
  /-- Goal projection equivalence -/
  goalProject : Goal → W → W → Bool
  /-- Speaker credence P(w|a) -/
  speakerCredence : BeliefState → W → ℚ := λ _ _ => 1
  /-- World prior -/
  worldPrior : W → ℚ := λ _ => 1
  /-- Interpretation prior -/
  interpPrior : Interp → ℚ := λ _ => 1
  /-- Lexicon prior -/
  lexiconPrior : Lexicon → ℚ := λ _ => 1
  /-- Belief state prior -/
  beliefStatePrior : BeliefState → ℚ := λ _ => 1
  /-- Goal prior -/
  goalPrior : Goal → ℚ := λ _ => 1
  /-- Rationality parameter -/
  α : ℕ := 1
  /-- Utterance cost -/
  cost : U → ℚ := λ _ => 0
  /-- Utterance prior (salience) -/
  utterancePrior : U → ℚ := λ _ => 1
  φ_nonneg : ∀ i l u w, 0 ≤ φ i l u w := by intros; decide
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide
  interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide
  lexiconPrior_nonneg : ∀ l, 0 ≤ lexiconPrior l := by intros; decide
  beliefStatePrior_nonneg : ∀ a, 0 ≤ beliefStatePrior a := by intros; decide
  goalPrior_nonneg : ∀ q, 0 ≤ goalPrior q := by intros; decide
  speakerCredence_nonneg : ∀ a w, 0 ≤ speakerCredence a w := by intros; decide
  cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide
  utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide
  [interpFintype : Fintype Interp]
  [lexiconFintype : Fintype Lexicon]
  [beliefStateFintype : Fintype BeliefState]
  [goalFintype : Fintype Goal]
  [interpDecEq : DecidableEq Interp]
  [lexiconDecEq : DecidableEq Lexicon]
  [beliefStateDecEq : DecidableEq BeliefState]
  [goalDecEq : DecidableEq Goal]

attribute [instance] RSAScenario.interpFintype RSAScenario.lexiconFintype
  RSAScenario.beliefStateFintype RSAScenario.goalFintype
  RSAScenario.interpDecEq RSAScenario.lexiconDecEq
  RSAScenario.beliefStateDecEq RSAScenario.goalDecEq

section SmartConstructors

/-- Basic RSA scenario with no latent variables. -/
def RSAScenario.basic {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (prior : W → ℚ := λ _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ _ _ u w := φ u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := prior
  interpPrior := λ _ => 1
  lexiconPrior := λ _ => 1
  beliefStatePrior := λ _ => 1
  goalPrior := λ _ => 1
  α := α
  cost := cost
  utterancePrior := utterancePrior
  φ_nonneg := λ _ _ u w => φ_nonneg u w
  worldPrior_nonneg := prior_nonneg
  interpPrior_nonneg := λ _ => le_refl 0 |> λ _ => by decide
  lexiconPrior_nonneg := λ _ => le_refl 0 |> λ _ => by decide
  beliefStatePrior_nonneg := λ _ => le_refl 0 |> λ _ => by decide
  goalPrior_nonneg := λ _ => le_refl 0 |> λ _ => by decide
  speakerCredence_nonneg := λ _ _ => le_refl 0 |> λ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/-- Basic RSA scenario from Boolean semantics -/
def RSAScenario.basicBool {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (satisfies : W → U → Bool)
    (prior : W → ℚ := λ _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.basic (λ u w => boolToRat (satisfies w u))
    (λ _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    prior prior_nonneg α cost cost_nonneg utterancePrior utterancePrior_nonneg

/-- Scenario with interpretation ambiguity -/
def RSAScenario.ambiguous {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (φ : I → U → W → ℚ)
    (φ_nonneg : ∀ i u w, 0 ≤ φ i u w := by intros; decide)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (interpPrior : I → ℚ := λ _ => 1)
    (interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
  Interp := I
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ i _ u w := φ i u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := interpPrior
  lexiconPrior := λ _ => 1
  beliefStatePrior := λ _ => 1
  goalPrior := λ _ => 1
  α := α
  cost := cost
  utterancePrior := utterancePrior
  φ_nonneg := λ i _ u w => φ_nonneg i u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := interpPrior_nonneg
  lexiconPrior_nonneg := λ _ => by decide
  beliefStatePrior_nonneg := λ _ => by decide
  goalPrior_nonneg := λ _ => by decide
  speakerCredence_nonneg := λ _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/-- Ambiguous scenario from Boolean semantics -/
def RSAScenario.ambiguousBool {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (interpPrior : I → ℚ := λ _ => 1)
    (interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.ambiguous (λ i u w => boolToRat (satisfies i w u))
    (λ _ _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    worldPrior worldPrior_nonneg interpPrior interpPrior_nonneg α cost cost_nonneg
    utterancePrior utterancePrior_nonneg

/-- QUD-sensitive scenario -/
def RSAScenario.qud {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (qudPrior : Q → ℚ := λ _ => 1)
    (qudPrior_nonneg : ∀ q, 0 ≤ qudPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Q
  φ _ _ u w := φ u w
  goalProject := qudProject
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := λ _ => 1
  lexiconPrior := λ _ => 1
  beliefStatePrior := λ _ => 1
  goalPrior := qudPrior
  α := α
  cost := cost
  utterancePrior := utterancePrior
  φ_nonneg := λ _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := λ _ => by decide
  lexiconPrior_nonneg := λ _ => by decide
  beliefStatePrior_nonneg := λ _ => by decide
  goalPrior_nonneg := qudPrior_nonneg
  speakerCredence_nonneg := λ _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/-- QUD-sensitive scenario from Boolean semantics -/
def RSAScenario.qudBool {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (qudPrior : Q → ℚ := λ _ => 1)
    (qudPrior_nonneg : ∀ q, 0 ≤ qudPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.qud (λ u w => boolToRat (satisfies w u))
    (λ _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    qudProject worldPrior worldPrior_nonneg qudPrior qudPrior_nonneg α cost cost_nonneg
    utterancePrior utterancePrior_nonneg

/-- Scenario with belief state inference -/
def RSAScenario.mentalState {U W A Q : Type}
    [Fintype U] [Fintype W] [Fintype A] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq A] [DecidableEq Q]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (speakerCredence : A → W → ℚ)
    (speakerCredence_nonneg : ∀ a w, 0 ≤ speakerCredence a w := by intros; decide)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (beliefStatePrior : A → ℚ := λ _ => 1)
    (beliefStatePrior_nonneg : ∀ a, 0 ≤ beliefStatePrior a := by intros; decide)
    (goalPrior : Q → ℚ := λ _ => 1)
    (goalPrior_nonneg : ∀ q, 0 ≤ goalPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
  Interp := Unit
  Lexicon := Unit
  BeliefState := A
  Goal := Q
  φ _ _ := φ
  goalProject := goalProject
  speakerCredence := speakerCredence
  worldPrior := worldPrior
  interpPrior := λ _ => 1
  lexiconPrior := λ _ => 1
  beliefStatePrior := beliefStatePrior
  goalPrior := goalPrior
  α := α
  cost := cost
  utterancePrior := utterancePrior
  φ_nonneg := λ _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := λ _ => by decide
  lexiconPrior_nonneg := λ _ => by decide
  beliefStatePrior_nonneg := beliefStatePrior_nonneg
  goalPrior_nonneg := goalPrior_nonneg
  speakerCredence_nonneg := speakerCredence_nonneg
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/-- Scenario with lexical uncertainty -/
def RSAScenario.lexicalUncertainty {U W L : Type}
    [Fintype U] [Fintype W] [Fintype L]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (φ : L → U → W → ℚ)
    (φ_nonneg : ∀ l u w, 0 ≤ φ l u w := by intros; decide)
    (worldPrior : W → ℚ := λ _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (lexiconPrior : L → ℚ := λ _ => 1)
    (lexiconPrior_nonneg : ∀ l, 0 ≤ lexiconPrior l := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := λ _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
  Interp := Unit
  Lexicon := L
  BeliefState := Unit
  Goal := Unit
  φ _ l u w := φ l u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := λ _ => 1
  lexiconPrior := lexiconPrior
  beliefStatePrior := λ _ => 1
  goalPrior := λ _ => 1
  α := α
  cost := cost
  utterancePrior := utterancePrior
  φ_nonneg := λ _ l u w => φ_nonneg l u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := λ _ => by decide
  lexiconPrior_nonneg := lexiconPrior_nonneg
  beliefStatePrior_nonneg := λ _ => by decide
  goalPrior_nonneg := λ _ => by decide
  speakerCredence_nonneg := λ _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

end SmartConstructors
end RSAScenario

section RSAComputations

namespace RSA

variable {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
variable (S : RSAScenario U W)

/-- Helper: sum scores over Fintype. -/
private def sumScores (scores : W → ℚ) : ℚ :=
  ∑ w : W, scores w

/-- Helper: try to normalize scores to ExactDist. -/
private def tryNormalize {α : Type*} [Fintype α]
    (scores : α → ℚ) (hnonneg : ∀ x, 0 ≤ scores x) : Option (ExactDist α) :=
  ExactDist.tryNormalize scores hnonneg

/-- L0: Literal listener P(w|u,i,l,a,q) ∝ φ · prior · credence. -/
def L0 (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (_q : S.Goal)
    : Option (ExactDist W) :=
  let scores := λ w => S.worldPrior w * S.φ i l u w * S.speakerCredence a w
  let hnonneg : ∀ w, 0 ≤ scores w := λ w =>
    mul_nonneg (mul_nonneg (S.worldPrior_nonneg w) (S.φ_nonneg i l u w)) (S.speakerCredence_nonneg a w)
  tryNormalize scores hnonneg

/-- L0 projected onto QUD equivalence classes. -/
def L0_projected (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  match L0 S u i l a q with
  | none => none
  | some l0 =>
    let scores := λ w =>
      ∑ w' : W, if S.goalProject q w w' then l0.mass w' else 0
    let hnonneg : ∀ w, 0 ≤ scores w := λ _ => by
      apply Finset.sum_nonneg
      intro w' _
      split_ifs
      · exact l0.nonneg w'
      · exact le_refl 0
    tryNormalize scores hnonneg

/-- S0: Literal speaker P(u|w) ∝ utterancePrior · φ. -/
def S0 (w : W)
    (i : S.Interp) (l : S.Lexicon) (_a : S.BeliefState) (_q : S.Goal)
    : Option (ExactDist U) :=
  let scores := λ u => S.utterancePrior u * S.φ i l u w
  let hnonneg : ∀ u, 0 ≤ scores u := λ u =>
    mul_nonneg (S.utterancePrior_nonneg u) (S.φ_nonneg i l u w)
  tryNormalize scores hnonneg

/-- L1 from S0: P(w|u) ∝ prior · S0(u|w). -/
def L1_fromS0 (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  let scores := λ w =>
    let s0Score := match S0 S w i l a q with
      | some d => d.mass u
      | none => 0
    S.worldPrior w * s0Score
  let hnonneg : ∀ w, 0 ≤ scores w := λ w => by
    apply mul_nonneg
    · exact S.worldPrior_nonneg w
    · cases h : S0 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- S1: Pragmatic speaker P(u|w) ∝ φ · L0^α · cost^(-α). -/
def S1 (w : W)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
  let scores := λ u =>
    let truthful := S.φ i l u w
    let l0Score : ℚ := match L0_projected S u i l a q with
      | some d => d.mass w
      | none => 0
    let costDiscount : ℚ := 1 / ((1 + S.cost u) ^ S.α)
    truthful * (l0Score ^ S.α : ℚ) * costDiscount
  let hnonneg : ∀ u, 0 ≤ scores u := λ u => by
    apply mul_nonneg
    apply mul_nonneg
    · exact S.φ_nonneg i l u w
    · apply pow_nonneg
      cases h : L0_projected S u i l a q with
      | none => simp
      | some d => exact d.nonneg w
    · apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
      apply pow_nonneg
      exact add_nonneg (by norm_num : (0 : ℚ) ≤ 1) (S.cost_nonneg u)
  tryNormalize scores hnonneg

/-- L1 marginal P(w|u) summing over all latent variables. -/
def L1_world (u : U) : Option (ExactDist W) :=
  let scores := λ w =>
    ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ w, 0 ≤ scores w := λ w => by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- L1 marginal over interpretations. -/
def L1_interp (u : U) : Option (ExactDist S.Interp) :=
  let scores := λ i =>
    ∑ w : W, ∑ l : S.Lexicon, ∑ a : S.BeliefState, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ i, 0 ≤ scores i := λ i => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- L1 marginal over belief states. -/
def L1_beliefState (u : U) : Option (ExactDist S.BeliefState) :=
  let scores := λ a =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ a, 0 ≤ scores a := λ a => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- L1 marginal over goals. -/
def L1_goal (u : U) : Option (ExactDist S.Goal) :=
  let scores := λ q =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ q, 0 ≤ scores q := λ q => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- L1 over worlds conditioned on specific goal. -/
def L1_world_givenGoal (u : U) (q : S.Goal)
    : Option (ExactDist W) :=
  let scores := λ w =>
    ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState,
      let credence := S.speakerCredence a w
      let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                   S.beliefStatePrior a
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      prior * credence * s1Score
  let hnonneg : ∀ w, 0 ≤ scores w := λ w => by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply mul_nonneg
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
    · exact S.speakerCredence_nonneg a w
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

/-- L1 over belief states conditioned on specific goal. -/
def L1_beliefState_givenGoal (u : U) (q : S.Goal)
    : Option (ExactDist S.BeliefState) :=
  let scores := λ a =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon,
      let credence := S.speakerCredence a w
      let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                   S.beliefStatePrior a
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      prior * credence * s1Score
  let hnonneg : ∀ a, 0 ≤ scores a := λ a => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply mul_nonneg
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
    · exact S.speakerCredence_nonneg a w
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

-- S2: Second-Level Pragmatic Speaker

/-- S2: Second-level pragmatic speaker -/
def S2 (w : W) : Option (ExactDist U) :=
  let scores := λ u =>
    let l1Score : ℚ := match L1_world S u with
      | some d => d.mass w
      | none => 0
    (l1Score ^ S.α : ℚ)
  let hnonneg : ∀ u, 0 ≤ scores u := λ u => by
    apply pow_nonneg
    cases h : L1_world S u with
    | none => simp
    | some d => exact d.nonneg w
  tryNormalize scores hnonneg

-- S1 from L1_fromS0: Pragmatic Speaker via Production-First Chain

/-- S1 from L1_fromS0: production-first chain -/
def S1_fromL1S0 (w : W)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
  let scores := λ u =>
    let l1Score : ℚ := match L1_fromS0 S u i l a q with
      | some d => d.mass w
      | none => 0
    let costDiscount : ℚ := 1 / ((1 + S.cost u) ^ S.α)
    S.utterancePrior u * (l1Score ^ S.α : ℚ) * costDiscount
  let hnonneg : ∀ u, 0 ≤ scores u := λ u => by
    apply mul_nonneg
    apply mul_nonneg
    · exact S.utterancePrior_nonneg u
    · apply pow_nonneg
      cases h : L1_fromS0 S u i l a q with
      | none => simp
      | some d => exact d.nonneg w
    · apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
      apply pow_nonneg
      exact add_nonneg (by norm_num : (0 : ℚ) ≤ 1) (S.cost_nonneg u)
  tryNormalize scores hnonneg

-- Unified API with ChainVariant (Primary Interface)

/-- Pragmatic speaker with chain selection -/
def speaker (chain : ChainVariant := .L0Based)
    (w : W) (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
  match chain with
  | .L0Based => S1 S w i l a q
  | .S0Based => S1_fromL1S0 S w i l a q

/-- Pragmatic listener with chain selection -/
def listener (chain : ChainVariant := .L0Based)
    (u : U) (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  match chain with
  | .L0Based => L1_world S u  -- marginalizes over latent variables
  | .S0Based => L1_fromS0 S u i l a q

end RSA

-- FinEnum-Based Eval Bridge (for #eval with RSAScenario)


namespace RSAScenario

variable {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]

/-- Get list of all utterances via FinEnum -/
def allUtterances (s : RSAScenario U W) [FinEnum U] : List U :=
  FinEnum.toList U

/-- Get list of all worlds via FinEnum -/
def allWorlds (s : RSAScenario U W) [FinEnum W] : List W :=
  FinEnum.toList W

/-- Get list of all interpretations via FinEnum -/
def allInterps (s : RSAScenario U W) [FinEnum s.Interp] : List s.Interp :=
  FinEnum.toList s.Interp

/-- Get list of all lexica via FinEnum -/
def allLexica (s : RSAScenario U W) [FinEnum s.Lexicon] : List s.Lexicon :=
  FinEnum.toList s.Lexicon

/-- Get list of all belief states via FinEnum -/
def allBeliefStates (s : RSAScenario U W) [FinEnum s.BeliefState] : List s.BeliefState :=
  FinEnum.toList s.BeliefState

/-- Get list of all goals via FinEnum -/
def allGoals (s : RSAScenario U W) [FinEnum s.Goal] : List s.Goal :=
  FinEnum.toList s.Goal

-- List-based helpers (inlined to avoid circular import with RSA.Eval)

private def sumScores (scores : List ℚ) : ℚ :=
  scores.foldl (· + ·) 0

private def getScore {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  match dist.find? (·.1 == x) with
  | some (_, s) => s
  | none => 0

private def normalize {α : Type} (dist : List (α × ℚ)) : List (α × ℚ) :=
  let total := sumScores (dist.map (·.2))
  dist.map λ (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

private def L0_projected' {U W : Type} [BEq W]
    (_utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (u : U)
    : List (W × ℚ) :=
  let scores := worlds.map λ w => (w, worldPrior w * φ u w)
  normalize scores

private def S1' {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (cost : U → ℚ)
    (α : ℕ)
    (w : W)
    : List (U × ℚ) :=
  let scores := utterances.map λ u =>
    let truthful := φ u w
    let l0Score := getScore (L0_projected' utterances worlds φ worldPrior u) w
    let costDiscount := 1 / ((1 + cost u) ^ α)
    (u, truthful * l0Score ^ α * costDiscount)
  normalize scores

private def L1_world' {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (W × ℚ) :=
  let scores := worlds.map λ w =>
    let s1 := S1' utterances worlds φ worldPrior cost α w
    let s1Score := getScore s1 u
    (w, worldPrior w * s1Score)
  normalize scores

-- Eval Methods for RSAScenario (Basic: Interp/Lexicon/BeliefState/Goal = Unit)

/-- L0 eval for basic scenarios -/
def evalL0 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq W]
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  let φ := λ u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  L0_projected' s.allUtterances s.allWorlds φ s.worldPrior u

/-- S1 eval for basic scenarios -/
def evalS1 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq U] [BEq W]
    (w : W)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (U × ℚ) :=
  let φ := λ u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  S1' s.allUtterances s.allWorlds φ s.worldPrior s.cost s.α w

/-- L1 eval for basic scenarios -/
def evalL1 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq U] [BEq W]
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  let φ := λ u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  L1_world' s.allUtterances s.allWorlds φ s.worldPrior s.cost s.α u

end RSAScenario

-- Top-level FinEnum Eval Functions (simpler API)

namespace RSA

/-- L0 eval (top-level) -/
def evalL0 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq W]
    (s : RSAScenario U W)
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  s.evalL0 u hi hl ha hg

/-- S1 eval (top-level) -/
def evalS1 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq U] [BEq W]
    (s : RSAScenario U W)
    (w : W)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (U × ℚ) :=
  s.evalS1 w hi hl ha hg

/-- L1 eval (top-level) -/
def evalL1 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq U] [BEq W]
    (s : RSAScenario U W)
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  s.evalL1 u hi hl ha hg

end RSA

