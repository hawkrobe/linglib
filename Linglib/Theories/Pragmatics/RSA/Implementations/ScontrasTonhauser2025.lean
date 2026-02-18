import Mathlib.Data.Rat.Defs

/-!
# Scontras & Tonhauser (2025) @cite{scontras-tonhauser-2025}

Projection emerges from RSA over speaker's private assumptions, not lexical
presupposition. L1 infers what speaker takes for granted (dcS in F&B terms).

This is a BToM model (Baker et al. 2017): L1 inverts S1's generative model
to jointly infer the speaker's belief state and the world state.
-/

namespace RSA.BToM

/-- World type has a complement dimension (C: whether the complement is true). -/
class HasComplement (W : Type*) where
  c : W → Bool

/-- World type has a belief dimension (BEL: whether the holder believes C). -/
class HasBelief (W : Type*) where
  bel : W → Bool

/-- World type has an antecedent dimension (A: whether the conditional antecedent holds). -/
class HasAntecedent (W : Type*) where
  a : W → Bool

variable {W : Type*}

/-- Factive positive: "X knows C" = BEL ∧ C (veridical). -/
def factivePos [HasBelief W] [HasComplement W] (w : W) : Bool :=
  HasBelief.bel w && HasComplement.c w

/-- Factive negative: "X doesn't know C" = not(BEL ∧ C). -/
def factiveNeg [HasBelief W] [HasComplement W] (w : W) : Bool :=
  !(HasBelief.bel w && HasComplement.c w)

/-- Non-factive positive: "X thinks C" = BEL (non-veridical). -/
def nonFactivePos [HasBelief W] (w : W) : Bool :=
  HasBelief.bel w

/-- Non-factive negative: "X doesn't think C" = not-BEL. -/
def nonFactiveNeg [HasBelief W] (w : W) : Bool :=
  !HasBelief.bel w

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

/-- Non-factive does NOT entail C (given a world where BEL ∧ not-C is possible). -/
theorem nonFactivePos_not_entails_c [HasBelief W] [HasComplement W]
    (h : ∃ w : W, HasBelief.bel w = true ∧ HasComplement.c w = false) :
    ∃ w, nonFactivePos (W := W) w = true ∧ HasComplement.c w = false := by
  obtain ⟨w, hb, hc⟩ := h; exact ⟨w, hb, hc⟩

/-- Know entails think (factivity is stronger than belief). -/
theorem factive_entails_nonfactive [HasBelief W] [HasComplement W] (w : W) :
    factivePos w = true → nonFactivePos w = true := by
  simp only [factivePos, nonFactivePos, Bool.and_eq_true]
  intro ⟨h, _⟩; exact h

/-- QUD for BToM models: question about belief or complement truth. -/
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
    A speaker "assumes C" iff C holds at every world they consider possible. -/
def assumesComplement [HasComplement W] (membership : W → Bool) (allWorlds : List W) : Bool :=
  allWorlds.all λ w => !membership w || HasComplement.c w

/-- Material conditional operator: ⟦if⟧ = λp.λq.λw. not-p(w) ∨ q(w). -/
def condOp (antecedent consequent : W → Bool) : W → Bool :=
  λ w => !antecedent w || consequent w

/-- Composed "if A, X knows C". -/
def composeCondFactive [HasAntecedent W] [HasBelief W] [HasComplement W] : W → Bool :=
  condOp (HasAntecedent.a) (factivePos)

/-- Composed "if A, X thinks C". -/
def composeCondNonFactive [HasAntecedent W] [HasBelief W] : W → Bool :=
  condOp (HasAntecedent.a) (nonFactivePos)

/-- Composed "if A, X doesn't know C". -/
def composeCondFactiveNeg [HasAntecedent W] [HasBelief W] [HasComplement W] : W → Bool :=
  condOp (HasAntecedent.a) (factiveNeg)

/-- Composed "if A, X doesn't think C". -/
def composeCondNonFactiveNeg [HasAntecedent W] [HasBelief W] : W → Bool :=
  condOp (HasAntecedent.a) (nonFactiveNeg)

end RSA.BToM

namespace RSA.ScontrasTonhauser2025


/--
World state: tracks belief and complement truth.

(BEL, C) where:
- BEL: Cole believes the complement
- C: The complement is actually true
-/
structure WorldState where
  bel : Bool  -- Cole believes C
  c : Bool    -- C is true
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All four world states -/
def allWorlds : List WorldState := [
  ⟨true, true⟩,   -- Cole believes C, C is true
  ⟨true, false⟩,  -- Cole believes C, C is false
  ⟨false, true⟩,  -- Cole doesn't believe C, C is true
  ⟨false, false⟩  -- Cole doesn't believe C, C is false
]


/--
Attitude verb utterances about Cole's mental state.
-/
inductive Utterance where
  | knowPos     -- "Cole knows that C"
  | knowNeg     -- "Cole doesn't know that C"
  | thinkPos    -- "Cole thinks that C"
  | thinkNeg    -- "Cole doesn't think that C"
  deriving DecidableEq, Repr, BEq, Inhabited

def allUtterances : List Utterance := [.knowPos, .knowNeg, .thinkPos, .thinkNeg]


/--
Literal truth conditions.

"know" is factive: requires both belief AND truth
"think" is non-factive: requires only belief
-/
def literalMeaning : Utterance → WorldState → Bool
  -- "Cole knows C" = Cole believes C AND C is true
  | .knowPos, w => w.bel && w.c
  -- "Cole doesn't know C" = NOT (Cole believes C AND C is true)
  | .knowNeg, w => !(w.bel && w.c)
  -- "Cole thinks C" = Cole believes C
  | .thinkPos, w => w.bel
  -- "Cole doesn't think C" = Cole doesn't believe C
  | .thinkNeg, w => !w.bel

/-- "know" entails C -/
theorem know_entails_c : ∀ w, literalMeaning .knowPos w = true → w.c = true := by
  intro ⟨bel, c⟩ h
  simp [literalMeaning] at h
  exact h.2

/-- "think" does NOT entail C -/
theorem think_not_entails_c : ∃ w, literalMeaning .thinkPos w = true ∧ w.c = false := by
  use ⟨true, false⟩
  simp [literalMeaning]


/--
Two possible QUDs:
- BEL?: Is Cole's belief state the question?
- C?: Is the complement truth the question?
-/
inductive QUD where
  | bel   -- "Does Cole believe C?"
  | c     -- "Is C true?"
  deriving DecidableEq, Repr, BEq, Inhabited

def allQUDs : List QUD := [.bel, .c]

/--
QUD projection: two worlds are equivalent if they agree on the QUD dimension.
-/
def qudProject : QUD → WorldState → WorldState → Bool
  | .bel, w1, w2 => w1.bel == w2.bel  -- Same belief state
  | .c, w1, w2 => w1.c == w2.c        -- Same complement truth


/--
Speaker's private assumptions: a non-empty subset of worlds.

We represent this as a named subset for efficiency.
In the paper, A ranges over all non-empty subsets of W.
-/
inductive BeliefState where
  | all           -- Speaker considers all worlds possible
  | cTrue         -- Speaker assumes C is true: {(1,1), (0,1)}
  | cFalse        -- Speaker assumes C is false: {(1,0), (0,0)}
  | belTrue       -- Speaker assumes Cole believes: {(1,1), (1,0)}
  | belFalse      -- Speaker assumes Cole doesn't believe: {(0,1), (0,0)}
  | cTrueBelTrue  -- {(1,1)}
  | cTrueBelFalse -- {(0,1)}
  | cFalseBelTrue -- {(1,0)}
  | cFalseBelFalse -- {(0,0)}
  deriving DecidableEq, Repr, BEq, Inhabited

def allBeliefStates : List BeliefState := [
  .all, .cTrue, .cFalse, .belTrue, .belFalse,
  .cTrueBelTrue, .cTrueBelFalse, .cFalseBelTrue, .cFalseBelFalse
]

/--
Membership in belief state (as credence).
-/
def speakerCredenceBool : BeliefState → WorldState → Bool
  | .all, _ => true
  | .cTrue, w => w.c
  | .cFalse, w => !w.c
  | .belTrue, w => w.bel
  | .belFalse, w => !w.bel
  | .cTrueBelTrue, w => w.c && w.bel
  | .cTrueBelFalse, w => w.c && !w.bel
  | .cFalseBelTrue, w => !w.c && w.bel
  | .cFalseBelFalse, w => !w.c && !w.bel

/--
Whether C is true in all worlds of the belief state.
This is what it means for C to be "assumed" by the speaker.
-/
def assumesC : BeliefState → Bool
  | .cTrue => true
  | .cTrueBelTrue => true
  | .cTrueBelFalse => true
  | _ => false


/--
World prior parameterized by P(C).

P(BEL, C) = P(BEL | C) * P(C)

We assume P(BEL | C) is uniform for simplicity.
-/
def worldPrior (pC : ℚ) : WorldState → ℚ
  | ⟨_, true⟩ => pC / 2      -- C true, split between bel/not-bel
  | ⟨_, false⟩ => (1 - pC) / 2  -- C false, split between bel/not-bel

/--
Belief state prior following Section 4 of Scontras & Tonhauser (2025):
- Knowledge of C is 4x as likely as knowledge of BEL
- Full knowledge (singletons) is 0.5x as likely as knowledge of BEL
- No beliefs (all) is 0.5x as likely as singletons

This captures that speakers more often have knowledge about C than about BEL.
-/
def beliefStatePrior : BeliefState → ℚ
  | .all => 1/4           -- No beliefs: 0.25 (half of singletons)
  | .cTrue => 4           -- Knowledge of C: 4x base
  | .cFalse => 4          -- Knowledge of C: 4x base
  | .belTrue => 1         -- Knowledge of BEL: 1 (base)
  | .belFalse => 1        -- Knowledge of BEL: 1 (base)
  | _ => 1/2              -- Singletons: 0.5 (half of knowledge of BEL)


-- BToM Typeclass Instances

instance : RSA.BToM.HasComplement WorldState where c := WorldState.c
instance : RSA.BToM.HasBelief WorldState where bel := WorldState.bel

/-- The literal meaning of "know" agrees with the generic factive semantics. -/
theorem know_is_factive : ∀ w : WorldState,
    literalMeaning .knowPos w = RSA.BToM.factivePos w := by
  intro ⟨_, _⟩; rfl

/-- The literal meaning of "think" agrees with the generic non-factive semantics. -/
theorem think_is_nonFactive : ∀ w : WorldState,
    literalMeaning .thinkPos w = RSA.BToM.nonFactivePos w := by
  intro ⟨_, _⟩; rfl

/-- The local QUD projection agrees with the generic BToM projection. -/
theorem qud_matches_btom : ∀ (q : QUD) (w1 w2 : WorldState),
    qudProject q w1 w2 = RSA.BToM.qudProject (W := WorldState)
      (match q with | .bel => .bel | .c => .c) w1 w2 := by
  intro q ⟨_, _⟩ ⟨_, _⟩; cases q <;> rfl

/-- The `assumesC` predicate agrees with the generic `assumesComplement`. -/
theorem assumesC_matches_generic : ∀ bs : BeliefState,
    assumesC bs = RSA.BToM.assumesComplement (speakerCredenceBool bs) allWorlds := by
  intro bs; cases bs <;> decide

end RSA.ScontrasTonhauser2025
