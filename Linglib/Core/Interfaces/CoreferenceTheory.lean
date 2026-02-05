import Linglib.Core.Basic

/-!
# CoreferenceTheory

Abstract interface for coreference predictions.
-/

namespace Interfaces

/-- The possible coreference relationships between two positions. -/
inductive CoreferenceStatus where
  /-- Coreference is obligatory (reflexives with local antecedent) -/
  | obligatory
  /-- Coreference is possible but not required -/
  | possible
  /-- Coreference is blocked (Principle B/C violations) -/
  | blocked
  /-- No prediction (positions not in relevant configuration) -/
  | unspecified
  deriving Repr, DecidableEq

/-- A theory that makes predictions about coreference patterns. -/
class CoreferenceTheory (T : Type) where
  /-- The theory's internal representation of a sentence/structure -/
  Structure : Type

  /-- Parse a list of words into the theory's representation.
      Returns `none` if the theory can't parse this input. -/
  parse : List Word → Option Structure

  /-- Predict the coreference status between positions i and j.

      Positions are indexed from the word list:
      - "John sees himself" → position 0 = John, position 2 = himself

      Returns the theory's prediction about whether these positions
      can/must/cannot corefer. -/
  coreferenceStatus : Structure → Nat → Nat → CoreferenceStatus

  /-- Does the theory predict this sentence is grammatical for coreference?

      A sentence is "grammatical for coreference" if:
      - All obligatory coreferences have valid antecedents
      - No blocked coreferences are forced

      This is the primary prediction we test against empirical data. -/
  grammaticalForCoreference : Structure → Bool

variable {T : Type} [CoreferenceTheory T]

/-- Check if coreference is possible at positions i, j -/
def canCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | .possible => true
  | .blocked => false
  | .unspecified => true  -- No constraint means possible

/-- Check if coreference is obligatory at positions i, j -/
def mustCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | _ => false

/-- Check if coreference is blocked at positions i, j -/
def cannotCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .blocked => true
  | _ => false

/-- Does the theory correctly predict a minimal pair? -/
def capturesMinimalPair (pair : MinimalPair) : Bool :=
  match CoreferenceTheory.parse (T := T) pair.grammatical,
        CoreferenceTheory.parse (T := T) pair.ungrammatical with
  | some sg, some su =>
    CoreferenceTheory.grammaticalForCoreference sg &&
    !CoreferenceTheory.grammaticalForCoreference su
  | _, _ => false  -- Can't parse → doesn't capture

/-- Does the theory capture all pairs in a phenomenon dataset? -/
def capturesPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (capturesMinimalPair (T := T))

variable {T1 T2 : Type} [CoreferenceTheory T1] [CoreferenceTheory T2]

/-- Two theories agree on a sentence if they make the same grammaticality prediction -/
def theoriesAgreeOn (ws : List Word) : Bool :=
  match CoreferenceTheory.parse (T := T1) ws,
        CoreferenceTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    CoreferenceTheory.grammaticalForCoreference s1 ==
    CoreferenceTheory.grammaticalForCoreference s2
  | none, none => true   -- Both can't parse → vacuous agreement
  | _, _ => false        -- One parses, other doesn't → disagreement

/-- Two theories agree on all sentences in a list -/
def theoriesAgreeOnAll (sentences : List (List Word)) : Bool :=
  sentences.all (theoriesAgreeOn (T1 := T1) (T2 := T2))

/-- Two theories agree on a phenomenon dataset -/
def theoriesAgreeOnPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (λ pair =>
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.grammatical &&
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.ungrammatical)

/-- Two theories are extensionally equivalent on a class of sentences. -/
def ExtensionallyEquivalentOn (sentences : List (List Word)) : Prop :=
  ∀ ws ∈ sentences, theoriesAgreeOn (T1 := T1) (T2 := T2) ws = true

end Interfaces
