/-!
# Clarification Ellipsis: Empirical Data
@cite{ginzburg-cooper-2004}

Theory-neutral data on clarification ellipsis (CE) — bare fragments
used to request clarification of a preceding utterance.

## The Phenomenon

After any utterance, a hearer can produce a bare fragment echoing
part of it to request clarification:

  A: "Did Bo finagle a raise?"
  B: "Bo?" → two readings:
    (i)  "Are you asking if BO finagled a raise?" (clausal)
    (ii) "Who is Bo? / What does 'finagle' mean?" (constituent)

## Key Properties (@cite{ginzburg-cooper-2004} §1.2)

1. **Any sub-constituent** can be clarified (NPs, Vs, PPs — not just referential NPs)
2. **Two readings** typically available: clausal and constituent
3. **Syntactic parallelism**: CE fragment must categorially match
   the antecedent sub-utterance (ex. 10)
4. **No phonological identity required** for either reading (ex. 8):
   "Did Bo leave?" / "My cousin?" is a valid CE
5. **Clausal readings require shared belief** about the sub-utterance's
   content; **constituent readings do not** (ex. 11–13)
6. **No island constraints**: CE antecedents can come from inside
   relative clauses, conjuncts, etc. (ex. 14)

## Distinction from Other Ellipsis Types

- **Fragment answers**: fill an argument slot in a question
- **Sluicing**: wh-phrase + elided TP
- **CE**: echoed fragment requesting clarification — no wh-movement,
  no island sensitivity

-/

namespace Phenomena.Ellipsis.ClarificationEllipsis

-- ════════════════════════════════════════════════════
-- § 1. Reading Types
-- ════════════════════════════════════════════════════

/-- The two readings of a clarification ellipsis.
@cite{ginzburg-cooper-2004} ex. 4b–c. -/
inductive CEReading where
  /-- "Are you asking whether p?" — polar question about propositional content.
      Paraphrasable as a polar interrogative. Presupposes shared belief about
      the sub-utterance's content. -/
  | clausal
  /-- "Who/what do you mean by X?" — wh-question about the referent/predicate.
      Paraphrasable as a wh-interrogative. No shared-belief presupposition. -/
  | constituent
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════
-- § 2. CE Data
-- ════════════════════════════════════════════════════

/-- A clarification ellipsis datum. -/
structure CEDatum where
  /-- The antecedent utterance being clarified -/
  antecedent : String
  /-- The CE fragment -/
  fragment : String
  /-- Available readings -/
  readings : List CEReading
  /-- Whether the fragment is phonologically identical to the antecedent sub-utterance -/
  phonIdentical : Bool := true
  /-- Syntactic category of the fragment -/
  category : String := "NP"
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 3. Core Examples
-- ════════════════════════════════════════════════════

/-- CE of a proper name: the running example.
@cite{ginzburg-cooper-2004} ex. 4a. -/
def ceProperName : CEDatum where
  antecedent := "Did Bo finagle a raise?"
  fragment := "Bo?"
  readings := [.clausal, .constituent]
  category := "NP"
  notes := "The paradigm case. Both readings available."
  source := "Ginzburg & Cooper (2004) ex. 4a"

/-- CE of a rare word: clarifying lexical content.
@cite{ginzburg-cooper-2004} ex. 4a. -/
def ceRareWord : CEDatum where
  antecedent := "Did Bo finagle a raise?"
  fragment := "finagle?"
  readings := [.clausal, .constituent]
  category := "V"
  notes := "Constituent reading requests lexical clarification, not referent identification."
  source := "Ginzburg & Cooper (2004) ex. 4a"

/-- Non-identical CE: fragment is not phonologically identical to antecedent.
@cite{ginzburg-cooper-2004} ex. 8a. -/
def ceNonIdentical : CEDatum where
  antecedent := "Did Bo leave?"
  fragment := "My cousin?"
  readings := [.clausal, .constituent]
  phonIdentical := false
  category := "NP"
  notes := "Neither reading requires phonological identity between fragment and antecedent sub-utterance."
  source := "Ginzburg & Cooper (2004) ex. 8a"

/-- Non-identical CE with category switch.
@cite{ginzburg-cooper-2004} ex. 8c. -/
def ceNonIdenticalVerb : CEDatum where
  antecedent := "Did you bike to work yesterday?"
  fragment := "Cycle?"
  readings := [.clausal, .constituent]
  phonIdentical := false
  category := "V"
  notes := "Clausal: 'Are you asking if I cycled to work yesterday?'; constituent: 'When you say bike, are you referring to cycling?'"
  source := "Ginzburg & Cooper (2004) ex. 8c"

/-- CE of an indexical with distinct locations: constituent reading only.
@cite{ginzburg-cooper-2004} ex. 11. -/
def ceDistinctLocations : CEDatum where
  antecedent := "Let's hold the conference here."
  fragment := "Here?"
  readings := [.constituent]
  category := "AdvP"
  notes := "A in Gothenburg, B in Hyderabad. Content of 'here' differs across participants, so clausal reading (which presupposes shared belief about content) is unavailable."
  source := "Ginzburg & Cooper (2004) ex. 11"

/-- CE of an indexical pronoun across speakers: constituent reading only.
@cite{ginzburg-cooper-2004} ex. 13a. -/
def ceIndexicalI : CEDatum where
  antecedent := "Can I come in?"
  fragment := "I?"
  readings := [.constituent]
  category := "NP"
  notes := "'I' refers to A when A says it, but would refer to B if B said it. Since the reference changes across speakers, the clausal reading (which requires shared belief about content) is blocked."
  source := "Ginzburg & Cooper (2004) ex. 13a"

/-- BNC example: CE of an unknown word.
@cite{ginzburg-cooper-2004} ex. 6a. -/
def ceSpunyarn : CEDatum where
  antecedent := "you always had er er say every foot he had with a piece of spunyarn in the wire"
  fragment := "Spunyarn?"
  readings := [.clausal, .constituent]
  category := "N"
  notes := "BNC file H5G. Constituent reading dominant: 'What's spunyarn?'"
  source := "Ginzburg & Cooper (2004) ex. 6a"

-- ════════════════════════════════════════════════════
-- § 4. Parallelism Conditions
-- ════════════════════════════════════════════════════

/-- Syntactic parallelism: CE fragment must categorially match antecedent sub-utterance.
@cite{ginzburg-cooper-2004} ex. 10. -/
structure SyntacticParallelismDatum where
  antecedent : String
  fragment : String
  /-- Is this CE form acceptable? -/
  acceptable : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Accusative pronoun matching accusative antecedent: acceptable.
@cite{ginzburg-cooper-2004} ex. 10a. -/
def accMatchOK : SyntacticParallelismDatum where
  antecedent := "I phoned him."
  fragment := "Him?"
  acceptable := true
  notes := "Accusative 'him' matches accusative antecedent."
  source := "Ginzburg & Cooper (2004) ex. 10a"

/-- Nominative pronoun for accusative antecedent: unacceptable.
@cite{ginzburg-cooper-2004} ex. 10a. -/
def nomMismatchBad : SyntacticParallelismDatum where
  antecedent := "I phoned him."
  fragment := "#he?"
  acceptable := false
  notes := "Nominative 'he' does not categorially match accusative 'him'."
  source := "Ginzburg & Cooper (2004) ex. 10a"

-- ════════════════════════════════════════════════════
-- § 5. Shared-Belief Condition
-- ════════════════════════════════════════════════════

/-- Clausal readings require shared belief about the sub-utterance's content;
constituent readings do not. This is the key condition that distinguishes
the two readings. @cite{ginzburg-cooper-2004} §1.2, ex. 11–13. -/
structure SharedBeliefDatum where
  antecedent : String
  fragment : String
  /-- Do A and B share a belief about the fragment's content? -/
  sharedBelief : Bool
  /-- Which readings are available? -/
  readings : List CEReading
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Same location: shared belief → both readings.
@cite{ginzburg-cooper-2004} ex. 12. -/
def sameLocation : SharedBeliefDatum where
  antecedent := "Let's hold the conference here."
  fragment := "Here?"
  sharedBelief := true
  readings := [.clausal, .constituent]
  notes := "Both A and B in Gothenburg. Clausal: 'Are you asking if we should hold the conference in Gothenburg of all places?'"
  source := "Ginzburg & Cooper (2004) ex. 12"

/-- Different locations: no shared belief → constituent only.
@cite{ginzburg-cooper-2004} ex. 11. -/
def differentLocations : SharedBeliefDatum where
  antecedent := "Let's hold the conference here."
  fragment := "Here?"
  sharedBelief := false
  readings := [.constituent]
  notes := "A in Gothenburg, B in Hyderabad. Clausal reading unavailable."
  source := "Ginzburg & Cooper (2004) ex. 11"

-- ════════════════════════════════════════════════════
-- § 6. Collected Data & Verification
-- ════════════════════════════════════════════════════

def coreExamples : List CEDatum := [
  ceProperName, ceRareWord, ceNonIdentical, ceNonIdenticalVerb,
  ceDistinctLocations, ceIndexicalI, ceSpunyarn
]

def parallelismData : List SyntacticParallelismDatum := [
  accMatchOK, nomMismatchBad
]

/-- CE typically has at least one reading available. -/
theorem all_have_readings :
    coreExamples.all (fun d => !d.readings.isEmpty) = true := by native_decide

/-- CE does NOT require phonological identity.
Some valid CEs have non-identical fragments. -/
theorem phon_identity_not_required :
    coreExamples.any (fun d => !d.phonIdentical) = true := by native_decide

/-- Syntactic parallelism is required: matching case is acceptable,
mismatched case is not. -/
theorem syntactic_parallelism_required :
    accMatchOK.acceptable = true ∧ nomMismatchBad.acceptable = false := ⟨rfl, rfl⟩

/-- Shared belief blocks clausal readings when absent:
same-location context has both, different-location has constituent only. -/
theorem shared_belief_conditions :
    sameLocation.readings.length > differentLocations.readings.length := by native_decide

/-- Indexicals with reference shift yield constituent-only readings. -/
theorem indexical_shift_blocks_clausal :
    ceIndexicalI.readings = [CEReading.constituent] := rfl

end Phenomena.Ellipsis.ClarificationEllipsis
