/-
Shared nominal classification and phi-feature agreement for DG coreference theories.

Used by both d-command (Coreference.lean) and CRDC (CRDC.lean) binding analyses.
-/

import Linglib.Core.Basic
import Linglib.Phenomena.Anaphora.Coreference

namespace DepGrammar.Nominal

-- ============================================================================
-- Nominal Classification
-- ============================================================================

/-- Types of nominal expressions for coreference. -/
inductive NominalType where
  | reflexive   -- himself, herself, themselves
  | pronoun     -- he, she, they, him, her, them
  | rExpression -- John, Mary, the cat
  deriving Repr, DecidableEq

/-- Is this a nominal category? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Classify a word as a nominal type. -/
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
-- Phi-Feature Agreement
-- ============================================================================

/-- Check phi-feature agreement (person, number, gender) between two nominals. -/
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
-- Phenomena Capture (parameterized by grammaticality predicate)
-- ============================================================================

/-- Check if a grammaticality predicate captures a minimal pair. -/
def capturesMinimalPair (grammatical : List Word → Bool) (pair : MinimalPair) : Bool :=
  grammatical pair.grammatical && !grammatical pair.ungrammatical

/-- Check if a grammaticality predicate captures all pairs in a PhenomenonData. -/
def capturesPhenomenonData (grammatical : List Word → Bool) (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all (capturesMinimalPair grammatical)

end DepGrammar.Nominal
