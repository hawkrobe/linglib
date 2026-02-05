/-
# Valency-Based Binding: CRDC

Implements Osborne & Li's (2023) Conjunct Referential Dependency Constraint,
a valency-based approach to binding in Dependency Grammar.

## Key Concepts

1. **Valency Frame**: The combinatory potential of a predicate (Tesnière 1959)
2. **Argument vs. Valent**: Arguments are semantically selected; valents are syntactic
   dependents that may or may not be arguments (Osborne 2019, Ch. 6)
3. **Full Valent vs. Conjunct Valent**: Full valents can bind conjunct valents

## The CRDC

A reflexive anaphor must be a conjunct valent of a predicate P, and its
antecedent must be a full valent of P that precedes it in the valency frame.

## How This Differs from D-Command

| D-Command (Hudson 1990) | CRDC (Osborne & Li 2023) |
|-------------------------|--------------------------|
| Co-dependents of same head | Valents in same frame |
| Subject label = binder | Full valent = binder |
| No argument/valent distinction | Explicit distinction |

For simple transitives, predictions are identical. Differences emerge with:
- Raising constructions (valent ≠ argument)
- Complex valency patterns (ditransitives, control)

## Valency Frame Notation (from Osborne 2019)

- `Na` = Nominal argument (subscript `a` marks argument status)
- `N` = Nominal valent (no subscript = not semantically selected)
- `↑` = Raised (appears elsewhere in structure)
- Underline = subject/object of embedded predicate

## References

- Osborne, T. & Li, J. (2023). Conjunct Referential Dependency Constraint.
- Osborne, T. (2019). A Dependency Grammar of English, Ch. 6.
- Tesnière, L. (1959). Éléments de syntaxe structurale.
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Theories.Core.Interfaces.CoreferenceTheory

private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev they := Fragments.English.Pronouns.they.toWord
private abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
private abbrev see := Fragments.English.Predicates.Verbal.see.toWordPl
private abbrev himself := Fragments.English.Pronouns.himself.toWord
private abbrev herself := Fragments.English.Pronouns.herself.toWord
private abbrev themselves := Fragments.English.Pronouns.themselves.toWord
private abbrev him := Fragments.English.Pronouns.him.toWord
private abbrev her := Fragments.English.Pronouns.her.toWord
private abbrev them := Fragments.English.Pronouns.them.toWord

namespace DepGrammar.CRDC

-- ============================================================================
-- Part 1: Valent Types and Valency Frames
-- ============================================================================

/-- Syntactic types of valents in a valency frame -/
inductive ValentType where
  | N      -- Nominal (noun, pronoun, NP)
  | T      -- To-infinitive phrase
  | I      -- Bare infinitive
  | A      -- Adjectival
  | Pa     -- Past participle
  | Pr     -- Present participle
  | C      -- Clausal (can be nominal or clausal)
  | P      -- Prepositional
  | R      -- Raised (unrestricted category)
  deriving Repr, DecidableEq

/-- A slot in a valency frame

    Captures the notation from Osborne (2019):
    - `isArgument` corresponds to the `a` subscript
    - `isRaised` corresponds to the `↑` marker
    - `label` captures grammatical function (subj, obj, etc.) -/
structure ValentSlot where
  /-- The syntactic type of this valent -/
  type : ValentType
  /-- Is this valent semantically selected (an argument)? -/
  isArgument : Bool
  /-- Is this valent "raised" (appears elsewhere in structure)? -/
  isRaised : Bool := false
  /-- Grammatical function label -/
  label : Option String := none
  deriving Repr, DecidableEq

/-- A valency frame specifies the combinatory potential of a word

    Following Osborne (2019), valents are ordered by obliqueness:
    subject > direct object > indirect object > oblique -/
structure ValencyFrame where
  /-- The word this frame belongs to -/
  carrier : String
  /-- Whether this is for a finite form -/
  isFinite : Bool
  /-- The valent slots, ordered by obliqueness (subject first) -/
  valents : List ValentSlot
  deriving Repr

-- ----------------------------------------------------------------------------
-- Valent Slot Constructors (mirroring textbook notation)
-- ----------------------------------------------------------------------------

/-- Na = Nominal argument (subject position) -/
def Na_subj : ValentSlot := ⟨.N, true, false, some "subj"⟩

/-- Na = Nominal argument (object position) -/
def Na_obj : ValentSlot := ⟨.N, true, false, some "obj"⟩

/-- Na = Nominal argument (indirect object) -/
def Na_iobj : ValentSlot := ⟨.N, true, false, some "iobj"⟩

/-- N = Nominal non-argument (raised element) -/
def N_raised : ValentSlot := ⟨.N, false, true, none⟩

/-- Ta = To-infinitive argument -/
def Ta : ValentSlot := ⟨.T, true, false, none⟩

/-- R = Raised subject (unrestricted category, not selected) -/
def R_subj : ValentSlot := ⟨.R, false, false, some "subj"⟩

-- ============================================================================
-- Part 2: Full Valents vs. Conjunct Valents
-- ============================================================================

/-- Valent status for CRDC binding

    In Osborne & Li's terms:
    - **Full valent**: Can serve as antecedent (typically subject arguments)
    - **Conjunct valent**: Must find antecedent among preceding full valents -/
inductive ValentStatus where
  | full      -- Can bind conjunct valents
  | conjunct  -- Must be bound by preceding full valent
  deriving Repr, DecidableEq

/-- Determine if a valent slot is a "full valent" or "conjunct valent"

    The key insight from CRDC: binding is determined by position in
    the valency frame, not by tree geometry or obliqueness hierarchy.

    For simple transitives:
    - Position 0 (subject) = full valent
    - Position 1+ = conjunct valent (if reflexive)

    This captures the intuition that subjects can bind objects,
    but not vice versa, purely from valency frame structure. -/
def valentStatus (slot : ValentSlot) (position : Nat) : ValentStatus :=
  -- Full valent: first position AND is an argument
  if position == 0 && slot.isArgument then .full
  else .conjunct

-- ============================================================================
-- Part 3: The CRDC (Conjunct Referential Dependency Constraint)
-- ============================================================================

/-- Configuration for checking CRDC

    The CRDC states: A reflexive (conjunct valent) must be bound by a
    preceding full valent in the same valency frame. -/
structure CRDCConfig where
  /-- The valency frame of the predicate -/
  frame : ValencyFrame
  /-- Index of the potential antecedent in the frame -/
  antecedentIdx : Nat
  /-- Index of the anaphor in the frame -/
  anaphorIdx : Nat

/-- Get element at index from list -/
def getAt? {α : Type} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, n + 1 => getAt? rest n

/-- Check if CRDC is satisfied

    Requirements:
    1. Antecedent must be a full valent
    2. Anaphor must be a conjunct valent
    3. Antecedent must precede anaphor in valency frame -/
def crdcSatisfied (config : CRDCConfig) : Bool :=
  match getAt? config.frame.valents config.antecedentIdx,
        getAt? config.frame.valents config.anaphorIdx with
  | some ante, some ana =>
    -- Antecedent must be a full valent
    valentStatus ante config.antecedentIdx == ValentStatus.full &&
    -- Anaphor must be a conjunct valent
    valentStatus ana config.anaphorIdx == ValentStatus.conjunct &&
    -- Antecedent must precede anaphor in valency frame
    config.antecedentIdx < config.anaphorIdx
  | _, _ => false

-- ============================================================================
-- Part 4: Standard Valency Frames
-- ============================================================================

/-- Valency frame for intransitive verbs: sleepf [Na]

    Example: "They slept" -/
def intransitiveFrame (verb : String) : ValencyFrame :=
  { carrier := verb
  , isFinite := true
  , valents := [Na_subj]
  }

/-- Valency frame for transitive verbs: discussf [Na, Na]

    Example: "We discussed the issue" -/
def transitiveFrame (verb : String) : ValencyFrame :=
  { carrier := verb
  , isFinite := true
  , valents := [Na_subj, Na_obj]
  }

/-- Valency frame for ditransitive verbs: givef [Na, Na, Na]

    Example: "Sam gave them a pie" -/
def ditransitiveFrame (verb : String) : ValencyFrame :=
  { carrier := verb
  , isFinite := true
  , valents := [Na_subj, Na_iobj, Na_obj]
  }

/-- Valency frame for raising verbs: appearf [N, Ta]

    Example: "Tom appears to be upset"
    Note: First N lacks `a` subscript (not semantically selected) -/
def raisingFrame (verb : String) : ValencyFrame :=
  { carrier := verb
  , isFinite := true
  , valents := [N_raised, Ta]
  }

-- ============================================================================
-- Part 5: Simple Clause with Valency Analysis
-- ============================================================================

/-- A clause analyzed with its valency frame -/
structure ValencyClause where
  subject : Word
  verb : Word
  object : Option Word
  /-- The valency frame for this verb form -/
  frame : ValencyFrame
  deriving Repr

/-- Is this a nominal category? -/
def isNominalCat (c : Cat) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Parse a sentence into a valency clause -/
def parseValencyClause (ws : List Word) : Option ValencyClause :=
  match ws with
  | [subj, v, obj] =>
    if isNominalCat subj.cat && v.cat == .VERB && isNominalCat obj.cat then
      some ⟨subj, v, some obj, transitiveFrame v.form⟩
    else none
  | [subj, v] =>
    if isNominalCat subj.cat && v.cat == .VERB then
      some ⟨subj, v, none, intransitiveFrame v.form⟩
    else none
  | _ => none

-- ============================================================================
-- Part 6: Nominal Classification
-- ============================================================================

/-- Types of nominal expressions for coreference -/
inductive NominalType where
  | reflexive   -- himself, herself, themselves
  | pronoun     -- he, she, they, him, her, them
  | rExpression -- John, Mary, the cat
  deriving Repr, DecidableEq

/-- Classify a word as a nominal type -/
def classifyNominal (w : Word) : Option NominalType :=
  if w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"] then
    some .reflexive
  else if w.form ∈ ["he", "she", "they", "him", "her", "them", "it"] then
    some .pronoun
  else if isNominalCat w.cat then
    some .rExpression
  else
    none

-- ============================================================================
-- Part 7: Agreement (Phi-Feature Matching)
-- ============================================================================

/-- Do two nominals agree in phi-features?

    Agreement is required between anaphor and antecedent regardless
    of which binding theory we use. -/
def phiAgree (w1 w2 : Word) : Bool :=
  let personMatch := match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 == p2
    | _, _ => true
  let numberMatch := match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 == n2
    | _, _ => true
  let genderMatch :=
    if w2.form == "himself" then
      w1.form ∈ ["John", "he", "him"]
    else if w2.form == "herself" then
      w1.form ∈ ["Mary", "she", "her"]
    else if w2.form ∈ ["themselves", "ourselves"] then
      w1.features.number == some .pl
    else
      true
  personMatch && numberMatch && genderMatch

-- ============================================================================
-- Part 8: CRDC-Based Binding Constraints
-- ============================================================================

/-- Reflexive licensing under CRDC

    A reflexive must be:
    1. A conjunct valent in some valency frame
    2. Preceded by a full valent in that frame
    3. In agreement with the full valent -/
def reflexiveLicensed (clause : ValencyClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      -- Check CRDC: subject (idx 0) is full valent, object (idx 1) is conjunct
      let config : CRDCConfig := {
        frame := clause.frame
        antecedentIdx := 0
        anaphorIdx := 1
      }
      crdcSatisfied config && phiAgree clause.subject obj
    | _ => true

/-- Pronoun constraint under CRDC

    A pronoun as conjunct valent cannot corefer with the full valent
    in the same valency frame. -/
def pronounLocallyFree (_clause : ValencyClause) : Bool :=
  -- Under CRDC, a pronoun in conjunct valent position cannot be
  -- coreferent with the full valent (same prediction as Principle B)
  false

/-- Is a sentence grammatical for coreference under CRDC? -/
def grammaticalForCoreference (ws : List Word) : Bool :=
  match parseValencyClause ws with
  | none => false
  | some clause =>
    -- Reflexive in subject position: no preceding full valent to bind it
    match classifyNominal clause.subject with
    | some .reflexive => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .pronoun => false  -- Pronoun coreference blocked locally
        | _ => true

-- ============================================================================
-- Part 9: Helper Functions
-- ============================================================================

/-- Check if reflexive is licensed in a sentence -/
def reflexiveLicensedInSentence (ws : List Word) : Bool :=
  match parseValencyClause ws with
  | none => false
  | some clause => reflexiveLicensed clause

/-- Check if pronoun coreference is blocked -/
def pronounCoreferenceBlocked (ws : List Word) : Bool :=
  match parseValencyClause ws with
  | none => false
  | some _ => true  -- Always blocked locally under CRDC

-- ============================================================================
-- Part 10: Tests
-- ============================================================================

-- reflexiveCoreferenceData pairs:
#eval reflexiveLicensedInSentence [john, sees, himself]     -- true
#eval grammaticalForCoreference [himself, sees, john]       -- false

#eval reflexiveLicensedInSentence [mary, sees, herself]     -- true
#eval grammaticalForCoreference [herself, sees, mary]       -- false

#eval reflexiveLicensedInSentence [they, see, themselves]   -- true
#eval grammaticalForCoreference [themselves, see, them]     -- false

-- Agreement violations:
#eval reflexiveLicensedInSentence [john, sees, herself]     -- false (gender)
#eval reflexiveLicensedInSentence [they, see, himself]      -- false (number)

-- Pronoun coreference blocked:
#eval pronounCoreferenceBlocked [john, sees, him]           -- true
#eval pronounCoreferenceBlocked [mary, sees, her]           -- true

-- ============================================================================
-- Part 11: Capturing Phenomena Data
-- ============================================================================

/-- Check if CRDC correctly predicts a minimal pair -/
def capturesCoreferenceMinimalPair (pair : MinimalPair) : Bool :=
  grammaticalForCoreference pair.grammatical &&
  !grammaticalForCoreference pair.ungrammatical

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all capturesCoreferenceMinimalPair

-- ============================================================================
-- Part 12: Theorems - CRDC Captures Coreference Phenomena
-- ============================================================================

/-- CRDC captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  native_decide

/-- CRDC captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  native_decide

/-- CRDC captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  native_decide

/-- Detailed verification of each reflexive pair -/
theorem reflexive_pairs_captured :
    -- Pair 1: john sees himself vs himself sees john
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself vs herself sees mary
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves vs themselves see them
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself vs john sees herself
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves vs they see himself
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  native_decide

-- ============================================================================
-- Part 13: CoreferenceTheory Interface Implementation
-- ============================================================================

/-- Marker type for CRDC as a coreference theory -/
structure CRDCTheory

/-- Compute coreference status using CRDC -/
def computeCoreferenceStatus (clause : ValencyClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i == 0 && j == 2 then
    -- Subject-object: check CRDC
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyNominal obj with
      | some .reflexive =>
        let config : CRDCConfig := {
          frame := clause.frame
          antecedentIdx := 0
          anaphorIdx := 1
        }
        if crdcSatisfied config && phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .pronoun => .blocked
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    -- Object-subject: object is conjunct, cannot bind subject
    match classifyNominal clause.subject with
    | some .reflexive => .blocked
    | some .pronoun => .possible
    | _ => .possible
  else
    .unspecified

/-- CRDC implements the CoreferenceTheory interface -/
instance : Interfaces.CoreferenceTheory CRDCTheory where
  Structure := ValencyClause
  parse := parseValencyClause
  coreferenceStatus := computeCoreferenceStatus
  grammaticalForCoreference := λ clause =>
    match classifyNominal clause.subject with
    | some .reflexive => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .pronoun => false
        | _ => true

-- ============================================================================
-- Part 14: Theoretical Notes
-- ============================================================================

/-
## Why CRDC?

Osborne & Li argue that traditional "command" relations (c-command, o-command,
d-command) are artifacts of specific representational choices:

- C-command requires phrase structure trees
- O-command requires obliqueness hierarchies
- D-command requires dependency labels

CRDC instead derives binding from **valency frames**, which are independently
needed for capturing the combinatory potential of predicates. The binding domain
is simply the valency frame itself.

## Equivalence for Simple Transitives

For simple transitive clauses like "John sees himself":

| Theory | Why subject binds object |
|--------|-------------------------|
| Minimalism | Subject c-commands object (tree geometry) |
| HPSG | Subject o-commands object (obliqueness) |
| DG (d-command) | Subject d-commands object (co-dependents + label) |
| DG (CRDC) | Subject is full valent, object is conjunct valent |

All four make identical predictions because they all encode the same
fundamental insight: **subjects are structurally/semantically prominent**.

## Where Theories Might Diverge

CRDC might make different predictions for:

1. **Raising constructions**: The raised element is a valent but not an argument.
   Under CRDC, whether it can bind depends on its valent status, not argument status.

2. **Ditransitives**: "John gave Mary herself" vs "John gave herself Mary"
   Valency frame order determines binding possibilities.

3. **Control vs. Raising**: Control predicates semantically select all valents;
   raising predicates don't. This affects what counts as a "full valent".

## Future Work

- Extend to ditransitive and control/raising constructions
- Compare predictions with other theories on complex cases
- Formalize the relationship between valent status and binding
-/

end DepGrammar.CRDC
