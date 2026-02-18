/-!
# Potts et al. (2016): Embedded Scalar Implicatures @cite{potts-etal-2016}

Lexical uncertainty model for DE/UE asymmetry in embedded SIs.

## Main definitions

`WorldClass`, `LexParams`, `Outcome`, `Utterance`, `utteranceTruth`

## The Model

The key innovation is lexical uncertainty: L1 marginalizes over possible
lexica (refinements of "some" and "scored"), rather than using a fixed
literal semantics.

Two refinement dimensions:
1. "some" can mean "some" (weak) or "some-but-not-all" (strong)
2. "scored" can mean "scored-or-aced" (weak) or "scored-but-not-aced" (strong)

## Key Predictions

1. DE context ("No one scored"): global reading preferred -- the model
   blocks local enrichment under negation
2. UE context ("Someone scored"): local reading preferred -- the model
   derives embedded implicature in upward-entailing contexts

## References

Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic inferences under
compositional lexical uncertainty. Journal of Semantics.
-/

namespace RSA.PottsLU

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


/-!
## Key Predictions (stated as theorems, pending RSA computation infrastructure)

1. DE context: global reading preferred (NN > others) for "No one scored"
2. UE context: local reading preferred for "Someone scored"

These predictions require the lexical uncertainty RSA computation
(L0 parameterized by lexicon, S1 given lexicon, L1 marginalizing over lexica).
The computational infrastructure for this is being rebuilt.
-/

-- NOTE: Paper uses lambda=0.1 (nearly uniform speaker). The qualitative
-- predictions (DE blocking, UE local enrichment) hold across a range
-- of rationality parameters.

end RSA.PottsLU
