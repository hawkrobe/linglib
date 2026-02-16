/-
# Potts et al. (2016): Embedded Scalar Implicatures

Lexical uncertainty model for DE/UE asymmetry in embedded SIs.

## Main definitions

`WorldClass`, `LexParams`, `pottsScenario`, `l1Worlds`, `l1Prob`

## References

Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic inferences under
compositional lexical uncertainty. Journal of Semantics.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

namespace RSA.PottsLU

open RSA.Eval LURSA


/-- Outcome for a single player (N/S/A). -/
inductive Outcome where
  | N | S | A
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Did this player score (solve at least one)? -/
def Outcome.scored : Outcome → Bool
  | .N => false
  | .S => true
  | .A => true

/-- Did this player ace (solve all)? -/
def Outcome.aced : Outcome → Bool
  | .N => false
  | .S => false
  | .A => true

/-- Did this player score-but-not-ace? -/
def Outcome.scoredNotAced : Outcome → Bool
  | .N => false
  | .S => true
  | .A => false


/-- World state as equivalence class (10 classes from outcome counts). -/
inductive WorldClass where
  | NN | NS | NA | SS | SA | AA | SSS | SSA | SAA | AAA
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Count of players who scored (at least one) -/
def WorldClass.numScored : WorldClass → Nat
  | .NN  => 0
  | .NS  => 1
  | .NA  => 1
  | .SS  => 2
  | .SA  => 2
  | .AA  => 2
  | .SSS => 3
  | .SSA => 3
  | .SAA => 3
  | .AAA => 3

/-- Count of players who aced -/
def WorldClass.numAced : WorldClass → Nat
  | .NN  => 0
  | .NS  => 0
  | .NA  => 1
  | .SS  => 0
  | .SA  => 1
  | .AA  => 2
  | .SSS => 0
  | .SSA => 1
  | .SAA => 2
  | .AAA => 3

/-- Count of players who scored-but-not-aced -/
def WorldClass.numScoredNotAced : WorldClass → Nat
  | .NN  => 0
  | .NS  => 1
  | .NA  => 0
  | .SS  => 2
  | .SA  => 1
  | .AA  => 0
  | .SSS => 3
  | .SSA => 2
  | .SAA => 1
  | .AAA => 0

/-- Did at least one player score? -/
def WorldClass.someScored (w : WorldClass) : Bool := w.numScored > 0

/-- Did all players score? -/
def WorldClass.allScored (w : WorldClass) : Bool := w.numScored == 3

/-- Did no one score? -/
def WorldClass.noOneScored (w : WorldClass) : Bool := w.numScored == 0

/-- Did at least one player ace? -/
def WorldClass.someAced (w : WorldClass) : Bool := w.numAced > 0

/-- Did all players ace? -/
def WorldClass.allAced (w : WorldClass) : Bool := w.numAced == 3

/-- Did no one ace? -/
def WorldClass.noOneAced (w : WorldClass) : Bool := w.numAced == 0

/-- Did at least one player score-but-not-ace? -/
def WorldClass.someScoredNotAced (w : WorldClass) : Bool := w.numScoredNotAced > 0

/-- All world classes -/
def allWorlds : List WorldClass :=
  [.NN, .NS, .NA, .SS, .SA, .AA, .SSS, .SSA, .SAA, .AAA]


/-- Quantifiers. -/
inductive Quant where
  | no | some_ | exactlyOne | exactlyTwo | every | null
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Predicates: "scored" vs "aced". -/
inductive Pred where
  | scored | aced
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Utterance: Quantifier + Predicate. -/
structure Utterance where
  quant : Quant
  pred : Pred
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Shorthand constructors -/
def noScored : Utterance := ⟨.no, .scored⟩
def noAced : Utterance := ⟨.no, .aced⟩
def someScored : Utterance := ⟨.some_, .scored⟩
def someAced : Utterance := ⟨.some_, .aced⟩
def exactlyOneScored : Utterance := ⟨.exactlyOne, .scored⟩
def exactlyOneAced : Utterance := ⟨.exactlyOne, .aced⟩
def exactlyTwoScored : Utterance := ⟨.exactlyTwo, .scored⟩
def exactlyTwoAced : Utterance := ⟨.exactlyTwo, .aced⟩
def everyScored : Utterance := ⟨.every, .scored⟩
def everyAced : Utterance := ⟨.every, .aced⟩
def nullUtt : Utterance := ⟨.null, .scored⟩

/-- All non-null utterances -/
def allUtterances : List Utterance :=
  [noScored, noAced, someScored, someAced,
   exactlyOneScored, exactlyOneAced, exactlyTwoScored, exactlyTwoAced,
   everyScored, everyAced, nullUtt]


/-- Lexicon parameters: which items are refined. -/
structure LexParams where
  refineQuant : Bool
  refinePred : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All 4 lexica from the cross-product -/
def allLexParams : List LexParams :=
  [ ⟨false, false⟩,  -- L_base: weak "some", weak "scored"
    ⟨true, false⟩,   -- "some" = some-not-all, "scored" = scored
    ⟨false, true⟩,   -- "some" = some, "scored" = scored-not-aced
    ⟨true, true⟩ ]   -- "some" = some-not-all, "scored" = scored-not-aced

/-- Truth value under lexicon parameters. -/
def utteranceTruth (params : LexParams) (u : Utterance) (w : WorldClass) : Bool :=
  -- First, determine the predicate extension
  let predCount : Nat :=
    if params.refinePred then
      -- "scored" means scored-but-not-aced
      if u.pred == .scored then w.numScoredNotAced
      else w.numAced  -- "aced" is unambiguous
    else
      -- "scored" means scored-or-aced
      if u.pred == .scored then w.numScored
      else w.numAced
  -- Now apply the quantifier
  match u.quant with
  | .no => predCount == 0
  | .some_ =>
    if params.refineQuant then
      -- "some" = some-but-not-all
      predCount > 0 && predCount < 3
    else
      -- "some" = at-least-one
      predCount > 0
  | .exactlyOne => predCount == 1
  | .exactlyTwo => predCount == 2
  | .every => predCount == 3
  | .null => true

/-- Create a Lexicon from LexParams -/
def lexiconOfParams (params : LexParams) : Lexicon Utterance WorldClass where
  meaning u w := boolToRat (utteranceTruth params u w)

/-- All 4 lexica as Lexicon objects -/
def allLexica : List (Lexicon Utterance WorldClass) :=
  allLexParams.map lexiconOfParams


/-- Complete Potts et al. (2016) scenario with flat priors. -/
def pottsScenario : LUScenario where
  Utterance := Utterance
  World := WorldClass
  baseLexicon := lexiconOfParams ⟨false, false⟩
  lexica := allLexica
  lexPrior := λ _ => 1  -- Flat prior per paper
  worldPrior := λ _ => 1  -- Flat prior per paper
  utterances := allUtterances
  worlds := allWorlds
  α := 1  -- Note: paper uses λ=0.1, we analyze effects below


/-- L₁ distribution over worlds for a given utterance -/
def l1Worlds (u : Utterance) : List (WorldClass × ℚ) :=
  LURSA.L1 pottsScenario u

/-- L₁ probability for a specific world -/
def l1Prob (u : Utterance) (w : WorldClass) : ℚ :=
  LURSA.L1_prob pottsScenario u w



/-- L₁ for "No one scored" -/
def l1NoScored : List (WorldClass × ℚ) := l1Worlds noScored

#eval l1NoScored

/-- Sum probabilities for worlds consistent with global reading (just NN) -/
def pGlobalDE : ℚ := l1Prob noScored .NN

/-- Sum probabilities for worlds consistent only with local reading -/
def pLocalOnlyDE : ℚ :=
  l1Prob noScored .NA + l1Prob noScored .AA + l1Prob noScored .AAA

#eval (pGlobalDE, pLocalOnlyDE)
#eval decide (pGlobalDE > pLocalOnlyDE)


/-- L₁ for "Someone scored" -/
def l1SomeScored : List (WorldClass × ℚ) := l1Worlds someScored

#eval l1SomeScored

/-- Worlds where local reading is informative (scored-not-aced exists) -/
def pLocalUE : ℚ :=
  l1Prob someScored .NS + l1Prob someScored .SS + l1Prob someScored .SA +
  l1Prob someScored .SSS + l1Prob someScored .SSA + l1Prob someScored .SAA

/-- Worlds where only global is true (everyone who scored also aced) -/
def pGlobalOnlyUE : ℚ :=
  l1Prob someScored .NA + l1Prob someScored .AA + l1Prob someScored .AAA

#eval (pLocalUE, pGlobalOnlyUE)
#eval decide (pLocalUE > pGlobalOnlyUE)


/-- DE context: global reading preferred (NN > others). -/
theorem potts_model_derives_de_blocking : pGlobalDE > pLocalOnlyDE := by
  native_decide

/-- UE context: local reading preferred. -/
theorem potts_model_derives_ue_implicature : pLocalUE > pGlobalOnlyUE := by
  native_decide

/-- Combined DE/UE asymmetry. -/
theorem potts_model_derives_de_ue_asymmetry :
    pGlobalDE > pLocalOnlyDE ∧ pLocalUE > pGlobalOnlyUE := by
  exact ⟨potts_model_derives_de_blocking, potts_model_derives_ue_implicature⟩


-- NOTE: Paper uses λ=0.1 (nearly uniform speaker). Our α=1 is more rational;
-- qualitative predictions match but exact replication needs ℚ-valued exponentiation.

/-- Pretty-print L₁ distribution -/
def showL1 (u : Utterance) : List (String × ℚ) :=
  (l1Worlds u).map λ (w, p) => (toString (repr w), p)

#eval showL1 noScored
#eval showL1 someScored
#eval showL1 noAced
#eval showL1 someAced


/-- Reduced lexicon: only predicate refinement (2 lexica). -/
def twoLexParams_pred : List LexParams :=
  [ ⟨false, false⟩,  -- weak "some", weak "scored"
    ⟨false, true⟩ ]  -- weak "some", strong "scored"

def twoLexica_pred : List (Lexicon Utterance WorldClass) :=
  twoLexParams_pred.map lexiconOfParams

def reducedLexiconScenario : LUScenario where
  Utterance := Utterance
  World := WorldClass
  baseLexicon := lexiconOfParams ⟨false, false⟩
  lexica := twoLexica_pred
  lexPrior := λ _ => 1
  worldPrior := λ _ => 1
  utterances := allUtterances
  worlds := allWorlds
  α := 1

/-- L₁ for "no one scored" with only 2 lexica (predicate refinement) -/
def l1NoScoredReduced : List (WorldClass × ℚ) :=
  LURSA.L1 reducedLexiconScenario noScored

def pGlobalDE_reduced : ℚ := getScore l1NoScoredReduced .NN

def pLocalOnlyDE_reduced : ℚ :=
  getScore l1NoScoredReduced .NA +
  getScore l1NoScoredReduced .AA +
  getScore l1NoScoredReduced .AAA

#eval (pGlobalDE_reduced, pLocalOnlyDE_reduced)
#eval decide (pGlobalDE_reduced > pLocalOnlyDE_reduced)

/-- 2-lexicon model succeeds for DE: predicate refinement is the operative mechanism. -/
theorem two_lexicon_pred_model_succeeds_de :
    pGlobalDE_reduced > pLocalOnlyDE_reduced := by
  native_decide

-- Now test UE with this reduced model
def l1SomeScoredReduced : List (WorldClass × ℚ) :=
  LURSA.L1 reducedLexiconScenario someScored

def pLocalUE_reduced : ℚ :=
  getScore l1SomeScoredReduced .NS + getScore l1SomeScoredReduced .SS +
  getScore l1SomeScoredReduced .SA + getScore l1SomeScoredReduced .SSS +
  getScore l1SomeScoredReduced .SSA + getScore l1SomeScoredReduced .SAA

def pGlobalOnlyUE_reduced : ℚ :=
  getScore l1SomeScoredReduced .NA + getScore l1SomeScoredReduced .AA +
  getScore l1SomeScoredReduced .AAA

#eval (pLocalUE_reduced, pGlobalOnlyUE_reduced)
#eval decide (pLocalUE_reduced > pGlobalOnlyUE_reduced)

/-- 2-lexicon model also works for UE. -/
theorem two_lexicon_pred_model_succeeds_ue :
    pLocalUE_reduced > pGlobalOnlyUE_reduced := by
  native_decide


end RSA.PottsLU
