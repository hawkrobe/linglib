/-
HPSG Coreference (Binding).

Binding theory using MODE and ARG-ST outranking,
per @cite{sag-wasow-bender-2003} Ch. 7 and @cite{pollard-sag-1994} (binding theory).

SWB2003 has two binding principles (not three):
- **Principle A**: [MODE ana] must be outranked by a coindexed element
- **Principle B**: [MODE ref] must NOT be outranked by a coindexed element

Both pronouns and R-expressions are [MODE ref], so Principle B subsumes
the Chomskyan Principle C. No separate "Principle C" is needed.
-/

import Linglib.Theories.Syntax.HPSG.Core.Basic
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Core.CoreferenceStatus
import Linglib.Core.Grammar

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
private abbrev eachOther := Fragments.English.Pronouns.eachOther.toWord

namespace HPSG.Coreference

-- ============================================================================
-- MODE Classification
-- ============================================================================

section ModeClassification

/-- Is this a nominal category? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Derive MODE feature from a word.

    Per @cite{sag-wasow-bender-2003} Ch. 7:
    - Reflexives and reciprocals → [MODE ana]
    - Personal pronouns and R-expressions → [MODE ref] -/
def classifyMode (w : Word) : Option HPSG.Mode :=
  if w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"] then
    some .ana
  else if w.form ∈ ["each other", "one another"] then
    some .ana
  else if isNominalCat w.cat then
    some .ref
  else
    none

/-- Is this word an anaphor ([MODE ana])? -/
def isAnaphor (w : Word) : Bool :=
  classifyMode w == some .ana

/-- Is this word a reflexive specifically? -/
def isReflexive (w : Word) : Bool :=
  w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"]

/-- Is this word a reciprocal? -/
def isReciprocal (w : Word) : Bool :=
  w.form ∈ ["each other", "one another"]

/-- Types of nominal expressions for coreference.

    Implementation convenience for dispatching agreement checks.
    Both `pronoun` and `rExpression` map to [MODE ref] in SWB2003. -/
inductive NominalType where
  | reflexive   -- himself, herself, themselves
  | reciprocal  -- each other, one another
  | pronoun     -- he, she, they, him, her, them
  | rExpression -- John, Mary, the cat
  deriving Repr, DecidableEq

/-- Classify a word as a nominal type.

    This maps to MODE as follows:
    - reflexive, reciprocal → [MODE ana]
    - pronoun, rExpression → [MODE ref]

    The pronoun/rExpression distinction is useful for implementation
    (e.g., agreement checks) but both are [MODE ref] in SWB2003. -/
def classifyNominal (w : Word) : Option NominalType :=
  if w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"] then
    some .reflexive
  else if w.form ∈ ["each other", "one another"] then
    some .reciprocal
  else if w.form ∈ ["he", "she", "they", "him", "her", "them", "it"] then
    some .pronoun
  else if isNominalCat w.cat then
    some .rExpression
  else
    none

end ModeClassification

-- ============================================================================
-- ARG-ST and Outranking
-- ============================================================================

section ArgStOutranking

/-- Simple clause structure with ARG-ST for binding.

    ARG-ST is implicitly [subject, object] — subject at position 0
    outranks object at position 1. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  /-- Whether the subject denotes a plurality. Defaults to matching
      syntactic number. Override for languages where syntactic and
      semantic number diverge (@cite{rakosi-2019}). -/
  semanticPl : Bool := subject.features.number == some .pl
  deriving Repr

/-- Parse a simple transitive sentence into a clause. -/
def parseSimpleClause (ws : List Word) : Option SimpleClause :=
  match ws with
  | [subj, v, obj] =>
    if isNominalCat subj.cat && v.cat == .VERB && isNominalCat obj.cat then
      some { subject := subj, verb := v, object := some obj }
    else none
  | [subj, v] =>
    if isNominalCat subj.cat && v.cat == .VERB then
      some { subject := subj, verb := v, object := none }
    else none
  | _ => none

/-- Convert a word to a minimal HPSG Synsem for ARG-ST construction. -/
private def wordToSynsem (w : Word) : HPSG.Synsem :=
  { cat := w.cat }

/-- Build the ARG-ST for a simple clause from its arguments.

    ARG-ST = [subject, object] — the verb's argument structure list,
    ordered by obliqueness (@cite{sag-wasow-bender-2003} Ch. 7). -/
def SimpleClause.toArgSt (clause : SimpleClause) : HPSG.ArgSt :=
  match clause.object with
  | none => { args := [wordToSynsem clause.subject] }
  | some obj => { args := [wordToSynsem clause.subject, wordToSynsem obj] }

/-- Does the subject outrank the object on ARG-ST?

    Derived from `ArgSt.outranks`: subject at position 0 outranks
    object at position 1 iff `0 < 1 ∧ 1 < args.length`. -/
def subjectOutranksObject (clause : SimpleClause) : Bool :=
  clause.toArgSt.outranks 0 1

/-- Subject and object are on the same ARG-ST list: both are valid
    indices in the ARG-ST built from the verb's argument structure. -/
def sameArgSt (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some _ => 1 < clause.toArgSt.args.length

end ArgStOutranking

-- ============================================================================
-- Anaphoric Agreement Principle
-- ============================================================================

section Agreement

/-- Anaphoric Agreement Principle (AAP): coindexed elements must agree.

    Per @cite{sag-wasow-bender-2003} Ch. 7: "Coindexed NPs agree." -/
def phiAgree (w1 w2 : Word) : Bool :=
  let personMatch := match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 == p2
    | _, _ => true  -- Compatible if unspecified
  let numberMatch := match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 == n2
    | _, _ => true
  let genderMatch :=
    if w2.form == "himself" then
      w1.form ∈ ["John", "he", "him"]  -- masculine antecedents
    else if w2.form == "herself" then
      w1.form ∈ ["Mary", "she", "her"]  -- feminine antecedents
    else if w2.form ∈ ["themselves", "ourselves"] then
      w1.features.number == some .pl  -- plural
    else
      true
  personMatch && numberMatch && genderMatch

end Agreement

-- ============================================================================
-- Binding Principles
-- ============================================================================

section BindingConstraints

/-- Principle A (SWB2003): An anaphor ([MODE ana]) must be outranked by a
    coindexed element on the same ARG-ST list.

    For reflexives, the coindexed antecedent must also satisfy the AAP. -/
def reflexiveLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      subjectOutranksObject clause &&
      sameArgSt clause &&
      phiAgree clause.subject obj
    | _ => true

/-- Principle A for reciprocals: a reciprocal ([MODE ana]) must be outranked
    by a semantically plural coindexed element. The plurality requirement
    is semantic (LF), not morphosyntactic — reciprocals are licensed by
    quantified NPs, singular coordinate DPs, and collective nouns that
    are syntactically singular (@cite{rakosi-2019}). -/
def reciprocalLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reciprocal =>
      subjectOutranksObject clause &&
      sameArgSt clause &&
      clause.semanticPl
    | _ => true

/-- Principle B (SWB2003): A [MODE ref] element must NOT be outranked
    by a coindexed element on the same ARG-ST list.

    This applies to both pronouns and R-expressions (both are [MODE ref]).
    In a simple clause, the subject outranks the object, so any [MODE ref]
    object that is coindexed with the subject violates Principle B.

    Note: `grammaticalForCoreference` only tests this for pronouns, since
    R-expression objects are typically not coindexed with the subject.
    `computeCoreferenceStatus` applies Principle B to all [MODE ref] elements
    for explicit coindexation queries. -/
def refLocallyFree (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some obj =>
    match classifyMode obj with
    | some .ref =>
      !(subjectOutranksObject clause && sameArgSt clause)
    | _ => true

end BindingConstraints

-- ============================================================================
-- Combined Check
-- ============================================================================

section CombinedCheck

/-- Is a sentence free of binding violations under HPSG binding theory?

    Checks Principle A (anaphors must be outranked) and
    Principle B (pronouns must not be locally bound).

    For R-expression objects, no binding violation arises because
    coindexation with the subject is not assumed. Use
    `computeCoreferenceStatus` for explicit coindexation queries. -/
def grammaticalForCoreference (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause =>
    -- Anaphors cannot be subjects (no outranker available)
    match classifyNominal clause.subject with
    | some .reflexive => false
    | some .reciprocal => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .reciprocal => reciprocalLicensed clause
        | some .pronoun => false  -- Principle B: [MODE ref] locally bound → blocked
        | _ => true  -- R-expressions: no coindexation assumed, no violation

/-- Check if reflexive is licensed in a sentence -/
def reflexiveLicensedInSentence (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => reflexiveLicensed clause

/-- Check if local coreference is blocked by Principle B ([MODE ref]).

    Applies to both pronouns and R-expressions. -/
def localCoreferenceBlocked (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => !refLocallyFree clause

-- ============================================================================
-- Tests
-- ============================================================================

-- Principle A: reflexives licensed when outranked with agreement
#guard reflexiveLicensedInSentence [john, sees, himself]     -- ✓
#guard !grammaticalForCoreference [himself, sees, john]      -- ✗ anaphor in subject
#guard reflexiveLicensedInSentence [mary, sees, herself]     -- ✓
#guard !grammaticalForCoreference [herself, sees, mary]      -- ✗
#guard reflexiveLicensedInSentence [they, see, themselves]   -- ✓
#guard !grammaticalForCoreference [themselves, see, them]    -- ✗

-- AAP violations (agreement mismatches)
#guard !reflexiveLicensedInSentence [john, sees, herself]    -- ✗ gender mismatch
#guard !reflexiveLicensedInSentence [they, see, himself]     -- ✗ number mismatch

-- Principle A: reciprocals require plural antecedent
#guard grammaticalForCoreference [they, see, eachOther]      -- ✓ plural antecedent
#guard !grammaticalForCoreference [eachOther, see, them]     -- ✗ anaphor in subject
#guard !grammaticalForCoreference [john, sees, eachOther]    -- ✗ singular antecedent

-- Principle B: [MODE ref] must be locally free
#guard localCoreferenceBlocked [john, sees, him]             -- ✓ pronoun
#guard localCoreferenceBlocked [mary, sees, her]             -- ✓ pronoun
#guard localCoreferenceBlocked [john, sees, mary]            -- ✓ R-expression

-- ============================================================================
-- Capturing Phenomena Data
-- ============================================================================

/-- Check if HPSG correctly predicts a minimal pair for coreference

    Grammatical sentence should pass, ungrammatical should fail. -/
def capturesCoreferenceMinimalPair (pair : MinimalPair) : Bool :=
  grammaticalForCoreference pair.grammatical &&
  !grammaticalForCoreference pair.ungrammatical

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all capturesCoreferenceMinimalPair

-- ============================================================================
-- Per-Pair Verification
-- ============================================================================

/-- Check each pair individually for reflexive coreference -/
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
     grammaticalForCoreference [they, see, himself] = false) ∧
    -- Pair 6: reciprocal - they see each other vs each other see them
    (grammaticalForCoreference [they, see, eachOther] = true ∧
     grammaticalForCoreference [eachOther, see, them] = false) ∧
    -- Pair 7: reciprocal requires plural antecedent
    (grammaticalForCoreference [they, see, eachOther] = true ∧
     grammaticalForCoreference [john, sees, eachOther] = false) := by
  native_decide

-- ============================================================================
-- CoreferenceTheory Interface Implementation
-- ============================================================================

/-- Compute coreference status for positions i and j using ARG-ST outranking.

    Position 0 = subject, position 2 = object.

    Applies both binding principles uniformly:
    - Principle A: [MODE ana] at j outranked by coindexed i → obligatory
    - Principle B: [MODE ref] at j outranked by coindexed i → blocked -/
def computeCoreferenceStatus (clause : SimpleClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i == 0 && j == 2 then
    -- Subject outranks object on ARG-ST
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyMode obj with
      | some .ana =>
        -- Principle A: anaphor must be outranked — check agreement
        if subjectOutranksObject clause && sameArgSt clause && phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .ref =>
        -- Principle B: [MODE ref] must NOT be outranked by coindexed element
        -- Applies to both pronouns and R-expressions
        if subjectOutranksObject clause && sameArgSt clause
        then .blocked
        else .possible
      | _ => .unspecified
  else if i == 2 && j == 0 then
    -- Does the object outrank the subject on ARG-ST?
    -- Derived: outranks requires i < j, but object (1) > subject (0)
    let objectOutranks := clause.toArgSt.outranks 1 0
    match classifyMode clause.subject with
    | some .ana =>
      if objectOutranks && sameArgSt clause
      then .obligatory
      else .blocked
    | some .ref =>
      if objectOutranks && sameArgSt clause
      then .blocked
      else .possible
    | _ => .unspecified
  else
    .unspecified

-- Principle B applies uniformly to [MODE ref] — both pronouns and R-expressions
private def johnSeesHim : SimpleClause := { subject := john, verb := sees, object := some him }
private def johnSeesMary : SimpleClause := { subject := john, verb := sees, object := some mary }
private def johnSeesHimself : SimpleClause := { subject := john, verb := sees, object := some himself }

-- Principle A: anaphor must be outranked → obligatory coreference
#guard computeCoreferenceStatus johnSeesHimself 0 2 == .obligatory
-- Principle B: pronoun outranked → blocked
#guard computeCoreferenceStatus johnSeesHim 0 2 == .blocked
-- Principle B: R-expression outranked → also blocked (subsumes Principle C)
#guard computeCoreferenceStatus johnSeesMary 0 2 == .blocked

end CombinedCheck

-- ============================================================================
-- Theoretical Notes
-- ============================================================================

/-
## SWB2003 Binding Theory

### MODE (not PPRO)

SWB2003 replaces the Chomskyan three-way classification
(anaphor / pronoun / R-expression → Principles A/B/C) with a
single-feature system based on MODE:

- [MODE ana]: anaphors (reflexives, reciprocals)
- [MODE ref]: both personal pronouns AND R-expressions

This yields exactly two binding principles:
- **Principle A**: [MODE ana] must be outranked by a coindexed element
- **Principle B**: [MODE ref] must NOT be outranked by a coindexed element

There is no "Principle C" — Principle B subsumes it, since both pronouns
and R-expressions are [MODE ref]. Both are blocked from being locally
bound by a coindexed element.

Note: Some secondary sources incorrectly attribute a PPRO feature to
SWB2003. The textbook's binding theory uses only MODE and ARG-ST.

### ARG-ST and Outranking

Binding is defined over the ARG-ST (argument structure) list, not over
tree geometry:

    ARG-ST = SPR ⊕ COMPS

"X outranks Y" iff X precedes Y on some ARG-ST list.

### Comparison with Minimalism

Both theories make the same predictions for simple cases:
1. Subject outranks object ↔ Subject c-commands object
2. Same ARG-ST list ↔ Same binding domain (local clause)
3. AAP (agreement) ↔ Feature checking

The difference is in mechanism:
- Minimalism: structural (tree geometry, c-command via `cCommandsInB`)
- HPSG: feature-based (ARG-ST ordering via `ArgSt.outranks`, constraint satisfaction)

In this implementation, HPSG outranking is derived from the actual ARG-ST
list built from the clause's arguments, not hardcoded.
-/

end HPSG.Coreference
