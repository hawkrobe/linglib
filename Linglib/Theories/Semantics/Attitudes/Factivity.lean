/-!
# Factive vs Non-Factive Attitude Verb Semantics
@cite{karttunen-1971} @cite{kiparsky-kiparsky-1970} @cite{scontras-tonhauser-2025}

Generic infrastructure for the factive/non-factive distinction in Boolean
world models: world-dimension typeclasses, lexical semantics for know-type
(factive) and think-type (non-factive) verbs, entailment properties, QUD
projection, and conditional embedding.

These definitions are parametric in the world type `W` via typeclasses,
allowing instantiation for any model with belief and complement dimensions
(e.g., Scontras & Tonhauser 2025's projection model).

## World Dimensions

A world type may carry orthogonal Boolean dimensions:

| Dimension | Typeclass       | Gloss                              |
|-----------|-----------------|-------------------------------------|
| C         | `HasComplement` | Whether the complement is true      |
| BEL       | `HasBelief`     | Whether the agent believes C        |
| A         | `HasAntecedent` | Whether a conditional antecedent holds |

## Lexical Semantics

| Verb form        | Semantics          | Factivity |
|------------------|--------------------|-----------|
| "X knows C"      | BEL ∧ C            | factive   |
| "X doesn't know" | ¬(BEL ∧ C)         | factive   |
| "X thinks C"     | BEL                | non-factive |
| "X doesn't think"| ¬BEL               | non-factive |

-/

namespace Semantics.Attitudes.Factivity

-- ============================================================================
-- §1. World Dimension Typeclasses
-- ============================================================================

/-- World type has a complement dimension (C: whether the complement is true). -/
class HasComplement (W : Type _) where
  c : W → Bool

/-- World type has a belief dimension (BEL: whether the agent believes C). -/
class HasBelief (W : Type _) where
  bel : W → Bool

/-- World type has an antecedent dimension (A: whether the conditional
    antecedent holds). Used for conditional embedding of attitude reports. -/
class HasAntecedent (W : Type _) where
  a : W → Bool

-- ============================================================================
-- §2. Lexical Semantics
-- ============================================================================

variable {W : Type _}

/-- Factive positive: "X knows C" = BEL ∧ C (veridical). -/
def factivePos [HasBelief W] [HasComplement W] (w : W) : Bool :=
  HasBelief.bel w && HasComplement.c w

/-- Factive negative: "X doesn't know C" = ¬(BEL ∧ C). -/
def factiveNeg [HasBelief W] [HasComplement W] (w : W) : Bool :=
  !(HasBelief.bel w && HasComplement.c w)

/-- Non-factive positive: "X thinks C" = BEL (non-veridical). -/
def nonFactivePos [HasBelief W] (w : W) : Bool :=
  HasBelief.bel w

/-- Non-factive negative: "X doesn't think C" = ¬BEL. -/
def nonFactiveNeg [HasBelief W] (w : W) : Bool :=
  !HasBelief.bel w

-- ============================================================================
-- §3. Entailment Properties
-- ============================================================================

/-- Factive positive entails C (the defining property of factivity). -/
theorem factivePos_entails_c [HasBelief W] [HasComplement W] (w : W) :
    factivePos w = true → HasComplement.c w = true := by
  simp only [factivePos, Bool.and_eq_true]
  intro ⟨_, h⟩; exact h

/-- Factive positive entails BEL. -/
theorem factivePos_entails_bel [HasBelief W] [HasComplement W] (w : W) :
    factivePos w = true → HasBelief.bel w = true := by
  simp only [factivePos, Bool.and_eq_true]
  intro ⟨h, _⟩; exact h

/-- Non-factive does NOT entail C (given a world where BEL ∧ ¬C is
    possible). -/
theorem nonFactivePos_not_entails_c [HasBelief W] [HasComplement W]
    (h : ∃ w : W, HasBelief.bel w = true ∧ HasComplement.c w = false) :
    ∃ w, nonFactivePos (W := W) w = true ∧ HasComplement.c w = false := by
  obtain ⟨w, hb, hc⟩ := h; exact ⟨w, hb, hc⟩

/-- Know entails think (factivity is strictly stronger than belief). -/
theorem factive_entails_nonfactive [HasBelief W] [HasComplement W] (w : W) :
    factivePos w = true → nonFactivePos w = true := by
  simp only [factivePos, nonFactivePos, Bool.and_eq_true]
  intro ⟨h, _⟩; exact h

-- ============================================================================
-- §4. QUD and Projection
-- ============================================================================

/-- QUD for factive/non-factive models: a question about belief or complement
    truth. These are the two orthogonal dimensions of a world with
    `HasBelief` and `HasComplement`. -/
inductive QUD where
  | bel   -- "Does X believe C?"
  | c     -- "Is C true?"
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All QUDs. -/
def allQUDs : List QUD := [.bel, .c]

/-- QUD equivalence: two worlds agree on the relevant dimension. -/
def qudProject [HasBelief W] [HasComplement W] : QUD → W → W → Bool
  | .bel, w1, w2 => HasBelief.bel w1 == HasBelief.bel w2
  | .c, w1, w2 => HasComplement.c w1 == HasComplement.c w2

/-- Whether a belief state (given as membership over worlds) entails C.
    A speaker "assumes C" iff C holds at every world they consider
    possible. -/
def assumesComplement [HasComplement W] (membership : W → Bool)
    (allWorlds : List W) : Bool :=
  allWorlds.all λ w => !membership w || HasComplement.c w

-- ============================================================================
-- §5. Conditional Embedding
-- ============================================================================

/-- Material conditional operator: ⟦if⟧ = λp.λq.λw. ¬p(w) ∨ q(w). -/
def condOp (antecedent consequent : W → Bool) : W → Bool :=
  λ w => !antecedent w || consequent w

/-- Composed "if A, X knows C". -/
def composeCondFactive [HasAntecedent W] [HasBelief W]
    [HasComplement W] : W → Bool :=
  condOp (HasAntecedent.a) (factivePos)

/-- Composed "if A, X thinks C". -/
def composeCondNonFactive [HasAntecedent W] [HasBelief W] : W → Bool :=
  condOp (HasAntecedent.a) (nonFactivePos)

/-- Composed "if A, X doesn't know C". -/
def composeCondFactiveNeg [HasAntecedent W] [HasBelief W]
    [HasComplement W] : W → Bool :=
  condOp (HasAntecedent.a) (factiveNeg)

/-- Composed "if A, X doesn't think C". -/
def composeCondNonFactiveNeg [HasAntecedent W] [HasBelief W] : W → Bool :=
  condOp (HasAntecedent.a) (nonFactiveNeg)

end Semantics.Attitudes.Factivity
