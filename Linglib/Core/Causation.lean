import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Rat

/-!
# Causation

Theory-neutral infrastructure for causal and counterfactual reasoning.

## Structural Layer (Nadathur & Lauer 2020)

- **Variable**: Named causal variables
- **Situation**: Partial valuations (Variable → Option Bool)
- **CausalLaw**: Structural equations (preconditions → effect)
- **CausalDynamics**: Collections of causal laws
- **normalDevelopment**: Forward propagation to fixpoint
- **intervene**: Pearl's do-operator (set variable, cut incoming laws)
- **causallyNecessary / causallySufficient**: Counterfactual tests
- **manipulates**: Does intervening on X change Y?

## Probabilistic Layer (Grusdt, Lassiter & Franke 2022)

- **WorldState**: Distribution over two binary variables
- **CausalRelation**: A→C, C→A, or A⊥C causal structure
- **NoisyOR**: Noisy-OR parameterization for probabilistic causal links

## References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. *Glossa*.
- Pearl, J. (2000/2009). *Causality: Models, Reasoning, and Inference*.
- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
- Cheng, P. (1997). From covariation to causation.
-/

namespace Core.Causation

-- ============================================================
-- § Structural Layer
-- ============================================================

-- Variables

/-- A variable in a causal model.
    Variables are named entities whose values are determined by causal laws. -/
structure Variable where
  name : String
  deriving DecidableEq, Hashable, Repr, BEq, Inhabited

instance : ToString Variable where
  toString v := v.name

/-- Create a variable from a string literal. -/
def mkVar (name : String) : Variable := ⟨name⟩

-- Situations (Def 9)

/-- **Situation** (Definition 9 from Nadathur & Lauer 2020)

    A partial valuation: some variables have known values, others are
    undetermined.  Situations are *partial* functions — crucial for
    modeling what's "given" vs what's computed, and for counterfactual
    reasoning (removing a cause = setting it to false). -/
structure Situation where
  /-- The partial valuation: Variable → Option Bool -/
  valuation : Variable → Option Bool

namespace Situation

/-- The empty situation: nothing is determined. -/
def empty : Situation := ⟨λ _ => none⟩

/-- Get the value of a variable (if determined). -/
def get (s : Situation) (v : Variable) : Option Bool := s.valuation v

/-- Check if a variable has a specific value in the situation. -/
def hasValue (s : Situation) (v : Variable) (val : Bool) : Bool :=
  s.valuation v == some val

/-- **Extend** a situation with a new assignment: s ⊕ {v = val}.
    If the variable was already determined, the new value overwrites. -/
def extend (s : Situation) (v : Variable) (val : Bool) : Situation :=
  ⟨λ v' => if v' == v then some val else s.valuation v'⟩

/-- Remove a variable from the situation (set to undetermined). -/
def remove (s : Situation) (v : Variable) : Situation :=
  ⟨λ v' => if v' == v then none else s.valuation v'⟩

/-- Combine two situations (right takes precedence). -/
def merge (s1 s2 : Situation) : Situation :=
  ⟨λ v => s2.valuation v <|> s1.valuation v⟩

instance : Inhabited Situation := ⟨Situation.empty⟩

end Situation

-- Causal Laws (Def 10)

/-- **Causal Law** (Definition 10 from Nadathur & Lauer 2020)

    A causal law specifies: if all preconditions hold, the effect follows.
    In notation: ⟨{(v₁, val₁), …, (vₙ, valₙ)}, (vₑ, valₑ)⟩. -/
structure CausalLaw where
  /-- Preconditions that must all hold -/
  preconditions : List (Variable × Bool)
  /-- The variable affected by this law -/
  effect : Variable
  /-- The value the effect variable gets (default: true) -/
  effectValue : Bool := true
  deriving Repr, Inhabited

namespace CausalLaw

/-- Check if all preconditions of a law are satisfied in a situation. -/
def preconditionsMet (law : CausalLaw) (s : Situation) : Bool :=
  law.preconditions.all λ (v, val) => s.hasValue v val

/-- Apply a law to a situation (if preconditions met, set effect). -/
def apply (law : CausalLaw) (s : Situation) : Situation :=
  if law.preconditionsMet s then
    s.extend law.effect law.effectValue
  else
    s

/-- Create a simple law: if cause = true, then effect = true. -/
def simple (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, true)], effect := effect }

/-- Create a conjunctive law: if cause1 = true ∧ cause2 = true, then effect = true. -/
def conjunctive (cause1 cause2 effect : Variable) : CausalLaw :=
  { preconditions := [(cause1, true), (cause2, true)], effect := effect }

end CausalLaw

-- Causal Dynamics

/-- **Causal Dynamics**: A collection of causal laws.
    Represents the structural equations of a causal model.
    Multiple laws can affect the same variable (disjunctive causation). -/
structure CausalDynamics where
  /-- The laws governing causal propagation -/
  laws : List CausalLaw
  deriving Repr, Inhabited

namespace CausalDynamics

/-- Empty dynamics (no causal laws). -/
def empty : CausalDynamics := ⟨[]⟩

/-- Create dynamics from a list of laws. -/
def ofList (laws : List CausalLaw) : CausalDynamics := ⟨laws⟩

/-- Disjunctive causation: A ∨ B → C.  Either cause alone suffices. -/
def disjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple cause1 effect, CausalLaw.simple cause2 effect]⟩

/-- Conjunctive causation: A ∧ B → C.  Both causes required. -/
def conjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.conjunctive cause1 cause2 effect]⟩

/-- Causal chain: A → B → C. -/
def causalChain (a b c : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple a b, CausalLaw.simple b c]⟩

end CausalDynamics

-- Normal Causal Development (Def 15)

/-- Apply all laws once to a situation (one step of forward propagation). -/
def applyLawsOnce (dyn : CausalDynamics) (s : Situation) : Situation :=
  dyn.laws.foldl (λ s' law => law.apply s') s

/-- Check if a situation is a fixpoint (no law can change it). -/
def isFixpoint (dyn : CausalDynamics) (s : Situation) : Bool :=
  dyn.laws.all λ law =>
    !law.preconditionsMet s ||
    s.hasValue law.effect law.effectValue

/-- **Normal Causal Development** (Definition 15)

    Iterate forward propagation until fixpoint.  Uses bounded iteration
    (fuel) to ensure termination. -/
def normalDevelopment (dyn : CausalDynamics) (s : Situation)
    (fuel : Nat := 100) : Situation :=
  match fuel with
  | 0 => s
  | n + 1 =>
    let s' := applyLawsOnce dyn s
    if isFixpoint dyn s' then s'
    else normalDevelopment dyn s' n

-- Fixpoint Theorems

/-- Unfold normalDevelopment one step. -/
@[simp] theorem normalDevelopment_succ (dyn : CausalDynamics) (s : Situation) (n : Nat) :
    normalDevelopment dyn s (n + 1) =
      let s' := applyLawsOnce dyn s
      if isFixpoint dyn s' then s' else normalDevelopment dyn s' n := rfl

/-- If the result of one round of law application is a fixpoint,
    normalDevelopment returns that result. -/
theorem normalDevelopment_fixpoint_after_one (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopment dyn s (fuel + 1) = applyLawsOnce dyn s := by
  simp [h]

/-- Empty dynamics: any situation is a fixpoint. -/
theorem empty_dynamics_fixpoint (s : Situation) :
    isFixpoint CausalDynamics.empty s = true := by
  simp only [isFixpoint, CausalDynamics.empty, List.all_eq_true]
  intro x hx
  simp at hx

/-- Normal development of empty dynamics returns the input unchanged. -/
theorem empty_dynamics_unchanged (s : Situation) (fuel : Nat) :
    normalDevelopment CausalDynamics.empty s fuel = s := by
  induction fuel with
  | zero => rfl
  | succ n _ =>
    simp only [normalDevelopment, applyLawsOnce, CausalDynamics.empty, List.foldl_nil,
               isFixpoint, List.all_eq_true]
    simp

-- Convenience Functions

/-- Check if a variable develops to a specific value. -/
def developsToBe (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) : Bool :=
  (normalDevelopment dyn s).hasValue v val

/-- Check if a variable becomes true after normal development. -/
def developsToTrue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Bool :=
  developsToBe dyn s v true

/-- The cause is present and the effect holds after normal development.

    Shared primitive for `actuallyCaused` (Necessity.lean) and
    `complementActualized` (Ability.lean). -/
def factuallyDeveloped (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  s.hasValue cause true &&
  (normalDevelopment dyn s).hasValue effect true

/-- `factuallyDeveloped` unfolds to a conjunction of two `hasValue` checks. -/
theorem factuallyDeveloped_iff (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    factuallyDeveloped dyn s cause effect =
      (s.hasValue cause true && (normalDevelopment dyn s).hasValue effect true) := rfl

-- Structural Graph Queries

/-- Does any causal law directly connect `cause` to `effect`? -/
def hasDirectLaw (dyn : CausalDynamics) (cause effect : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.preconditions.any (fun (v, _) => v == cause) && law.effect == effect

/-- Does the intermediate have a causal law not depending on `cause`? -/
def hasIndependentSource (dyn : CausalDynamics)
    (cause intermediate : Variable) : Bool :=
  dyn.laws.any fun law =>
    law.effect == intermediate &&
    !(law.preconditions.any (fun (v, _) => v == cause))

-- Intervention (Pearl's do-operator)

/-- **Intervene**: Pearl's do(X = val).

    Sets variable `target` to `val` and removes all laws that would
    determine `target`, so the intervention overrides the structural
    equations rather than being overwritten by them. -/
def intervene (dyn : CausalDynamics) (s : Situation)
    (target : Variable) (val : Bool) : CausalDynamics × Situation :=
  let dyn' : CausalDynamics := ⟨dyn.laws.filter (·.effect != target)⟩
  let s' := s.extend target val
  (dyn', s')

/-- **Manipulates**: Does intervening on `cause` change the value of `effect`?

    Compares normal development under do(cause = true) vs do(cause = false).
    If the effect's value differs, then `cause` manipulates `effect`.

    This is the interventionist criterion for causation (Woodward 2003):
    X causes Y iff there exists an intervention on X that changes Y. -/
def manipulates (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let (dynT, sT) := intervene dyn s cause true
  let (dynF, sF) := intervene dyn s cause false
  let valT := (normalDevelopment dynT sT).get effect
  let valF := (normalDevelopment dynF sF).get effect
  valT != valF

-- Counterfactual Queries (N&L 2020 Definitions 23-24)

/-- **Causal Sufficiency** (N&L 2020, Definition 23).
    C is causally sufficient for E in situation s iff adding C and
    developing normally produces E. -/
def causallySufficient (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithCause := s.extend cause true
  let developed := normalDevelopment dyn sWithCause
  developed.hasValue effect true

/-- **Causal Necessity** (N&L 2020, Definition 24).
    C is causally necessary for E in situation s iff removing C and
    developing normally does NOT produce E. -/
def causallyNecessary (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) : Bool :=
  let sWithoutCause := s.extend cause false
  let developed := normalDevelopment dyn sWithoutCause
  !developed.hasValue effect true

/-- Causal profile: packages the counterfactual properties of a
    cause-effect pair in a structural model. -/
structure CausalProfile where
  sufficient : Bool
  necessary : Bool
  direct : Bool
  deriving DecidableEq, Repr, BEq

/-- Extract the causal profile of a cause-effect pair. -/
def extractProfile (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : CausalProfile :=
  { sufficient := causallySufficient dyn bg cause effect
  , necessary := causallyNecessary dyn bg cause effect
  , direct := hasDirectLaw dyn cause effect }

-- ============================================================
-- § Probabilistic Layer
-- ============================================================

-- Causal Relations

/-- Causal relations between two binary variables A and C.
    Used by Grusdt, Lassiter & Franke (2022) for conditional semantics. -/
inductive CausalRelation
  | ACausesC    -- A → C
  | CCausesA    -- C → A
  | Independent -- A ⊥ C
  deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString CausalRelation where
  toString
    | .ACausesC => "A→C"
    | .CCausesA => "C→A"
    | .Independent => "A⊥C"

-- Noisy-OR Parameterization

/-- Noisy-OR parameterization for a causal link (Cheng 1997).

    - `background` (b): P(C | ¬A) — background rate
    - `power` (Δ): P(C | A) - P(C | ¬A) — causal power -/
structure NoisyOR where
  /-- Background rate: P(C | ¬A) -/
  background : ℚ
  /-- Causal power: P(C | A) - P(C | ¬A) -/
  power : ℚ
  deriving Repr, DecidableEq, BEq

namespace NoisyOR

/-- P(C | A) in the Noisy-OR model. -/
def pCGivenA (n : NoisyOR) : ℚ := n.background + n.power

/-- P(C | ¬A) in the Noisy-OR model. -/
def pCGivenNotA (n : NoisyOR) : ℚ := n.background

/-- Check if parameters are valid. -/
def isValid (n : NoisyOR) : Bool :=
  0 ≤ n.background && n.background ≤ 1 &&
  0 ≤ n.background + n.power && n.background + n.power ≤ 1

/-- Deterministic cause: P(C|A) = 1, P(C|¬A) = 0. -/
def deterministic : NoisyOR := { background := 0, power := 1 }

/-- No effect: P(C|A) = P(C|¬A) = 0. -/
def noEffect : NoisyOR := { background := 0, power := 0 }

/-- Always-on: P(C|A) = P(C|¬A) = 1. -/
def alwaysOn : NoisyOR := { background := 1, power := 0 }

end NoisyOR

-- World States as Probability Distributions

/-- A probability distribution over two binary variables A and C.

    Used by Grusdt et al. (2022): a "world" is a probability distribution
    because conditionals make claims about probabilities (P(C|A) > θ). -/
structure WorldState where
  /-- Marginal probability P(A) -/
  pA : ℚ
  /-- Marginal probability P(C) -/
  pC : ℚ
  /-- Joint probability P(A ∧ C) -/
  pAC : ℚ
  deriving Repr, DecidableEq, BEq

namespace WorldState

-- Validity

/-- Check if a WorldState represents a valid probability distribution. -/
def isValid (w : WorldState) : Bool :=
  0 ≤ w.pA && w.pA ≤ 1 &&
  0 ≤ w.pC && w.pC ≤ 1 &&
  0 ≤ w.pAC && w.pAC ≤ min w.pA w.pC &&
  w.pA + w.pC - w.pAC ≤ 1

-- Derived Probabilities

/-- P(A ∧ ¬C) -/
def pANotC (w : WorldState) : ℚ := w.pA - w.pAC

/-- P(¬A ∧ C) -/
def pNotAC (w : WorldState) : ℚ := w.pC - w.pAC

/-- P(¬A ∧ ¬C) -/
def pNotANotC (w : WorldState) : ℚ := 1 - w.pA - w.pC + w.pAC

/-- P(¬A) -/
def pNotA (w : WorldState) : ℚ := 1 - w.pA

/-- P(¬C) -/
def pNotC (w : WorldState) : ℚ := 1 - w.pC

-- Conditional Probabilities

/-- P(C | A), or 0 if P(A) = 0. -/
def pCGivenA (w : WorldState) : ℚ :=
  if w.pA > 0 then w.pAC / w.pA else 0

/-- P(C | ¬A), or 0 if P(¬A) = 0. -/
def pCGivenNotA (w : WorldState) : ℚ :=
  let pNotA := 1 - w.pA
  if pNotA > 0 then w.pNotAC / pNotA else 0

/-- P(A | C), or 0 if P(C) = 0. -/
def pAGivenC (w : WorldState) : ℚ :=
  if w.pC > 0 then w.pAC / w.pC else 0

/-- P(A | ¬C), or 0 if P(¬C) = 0. -/
def pAGivenNotC (w : WorldState) : ℚ :=
  let pNotC := 1 - w.pC
  if pNotC > 0 then w.pANotC / pNotC else 0

-- Independence and Correlation

/-- P(A ∧ C) = P(A) · P(C). -/
def isIndependent (w : WorldState) : Bool :=
  w.pAC == w.pA * w.pC

/-- P(A ∧ C) > P(A) · P(C). -/
def isPositivelyCorrelated (w : WorldState) : Bool :=
  w.pAC > w.pA * w.pC

/-- P(A ∧ C) < P(A) · P(C). -/
def isNegativelyCorrelated (w : WorldState) : Bool :=
  w.pAC < w.pA * w.pC

-- Constructors

/-- WorldState from marginals assuming independence. -/
def independent (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := pA * pC }

/-- WorldState with perfect correlation (A ↔ C). -/
def perfectCorrelation (p : ℚ) : WorldState :=
  { pA := p, pC := p, pAC := p }

/-- WorldState where A ∧ C never happens. -/
def mutuallyExclusive (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := 0 }

-- Validity Theorems

/-- Propositional version of isValid for theorem proving. -/
def IsValid (w : WorldState) : Prop :=
  0 ≤ w.pA ∧ w.pA ≤ 1 ∧
  0 ≤ w.pC ∧ w.pC ≤ 1 ∧
  0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC ∧
  w.pA + w.pC - w.pAC ≤ 1

theorem valid_implies_pA_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pA ∧ w.pA ≤ 1 := ⟨h.1, h.2.1⟩

theorem valid_implies_pC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pC ∧ w.pC ≤ 1 := ⟨h.2.2.1, h.2.2.2.1⟩

theorem valid_implies_pAC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC := ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Validity implies 0 ≤ P(C|A) ≤ 1. -/
theorem valid_implies_pCGivenA_bounded (w : WorldState) (h : w.IsValid) (hA : 0 < w.pA) :
    0 ≤ w.pCGivenA ∧ w.pCGivenA ≤ 1 := by
  simp only [pCGivenA, gt_iff_lt, hA, ↓reduceIte]
  constructor
  · apply div_nonneg h.2.2.2.2.1 (le_of_lt hA)
  · have hAC_le : w.pAC ≤ w.pA := le_trans h.2.2.2.2.2.1 (min_le_left w.pA w.pC)
    have hA_ne : w.pA ≠ 0 := ne_of_gt hA
    calc w.pAC / w.pA ≤ w.pA / w.pA := by
             apply div_le_div_of_nonneg_right hAC_le (le_of_lt hA)
         _ = 1 := div_self hA_ne

/-- Validity implies 0 ≤ P(C|¬A) ≤ 1. -/
theorem valid_implies_pCGivenNotA_bounded (w : WorldState) (h : w.IsValid) (hA : w.pA < 1) :
    0 ≤ w.pCGivenNotA ∧ w.pCGivenNotA ≤ 1 := by
  simp only [pCGivenNotA, pNotAC]
  have hNotA_pos : 0 < 1 - w.pA := by linarith
  simp only [gt_iff_lt, hNotA_pos, ↓reduceIte]
  constructor
  · apply div_nonneg
    · have : w.pAC ≤ w.pC := le_trans h.2.2.2.2.2.1 (min_le_right w.pA w.pC)
      linarith
    · exact le_of_lt hNotA_pos
  · have hNotAC_le : w.pC - w.pAC ≤ 1 - w.pA := by linarith [h.2.2.2.2.2.2]
    have hNotA_ne : 1 - w.pA ≠ 0 := ne_of_gt hNotA_pos
    calc (w.pC - w.pAC) / (1 - w.pA) ≤ (1 - w.pA) / (1 - w.pA) := by
             apply div_le_div_of_nonneg_right hNotAC_le (le_of_lt hNotA_pos)
         _ = 1 := div_self hNotA_ne

/-- **Law of Total Probability**: P(C) = P(C|A)·P(A) + P(C|¬A)·P(¬A). -/
theorem law_of_total_probability (w : WorldState) (_h : w.IsValid)
    (hA_pos : 0 < w.pA) (hA_lt_one : w.pA < 1) :
    w.pC = w.pCGivenA * w.pA + w.pCGivenNotA * (1 - w.pA) := by
  simp only [pCGivenA, pCGivenNotA, pNotAC]
  have hNotA_pos : 0 < 1 - w.pA := by linarith
  simp only [gt_iff_lt, hA_pos, hNotA_pos, ↓reduceIte]
  have hA_ne : w.pA ≠ 0 := ne_of_gt hA_pos
  have hNotA_ne : 1 - w.pA ≠ 0 := ne_of_gt hNotA_pos
  field_simp
  ring

/-- **Bayes' Theorem**: P(A|C) = P(C|A)·P(A) / P(C). -/
theorem bayes_theorem (w : WorldState) (hA : 0 < w.pA) (hC : 0 < w.pC) :
    w.pAGivenC = w.pCGivenA * w.pA / w.pC := by
  simp only [pAGivenC, pCGivenA]
  simp only [gt_iff_lt, hA, hC, ↓reduceIte]
  have hA_ne : w.pA ≠ 0 := ne_of_gt hA
  rw [div_mul_eq_mul_div]
  congr 1
  rw [mul_div_assoc, div_self hA_ne, mul_one]

end WorldState

end Core.Causation
