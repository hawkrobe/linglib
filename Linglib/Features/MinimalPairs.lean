import Linglib.Features.Acceptability
import Linglib.Features.ClauseForm
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Minimal Pairs — Theory-Neutral Judgment Data Vocabulary

Shared vocabulary for **introspective grammaticality contrasts** — the
minimal-pair tradition in which a datum is a pair of minimally-different
sentences with a per-side acceptability judgment (typically the
analyst's). This is the methodological tradition that the
factorial-design machinery of [sprouse-2007] / [sprouse-et-al-2012]
(`Linglib/Studies/SprouseEtAl2012.lean`) was introduced to discipline.

Two parallel families:

* **Word-based** (`MinimalPair`, `PhenomenonData`): sentences are
  `List Word`, requiring feature specifications. Used by analyses
  that operate on parsed/featural representations (HPSG, DG, Minimalism).
* **String-based** (`SentencePair`, `StringPhenomenonData`): sentences
  are raw strings, parseable by any theory. Used by data files that
  should remain free of theoretical commitments.

Judgments use the five-level `Features.Judgment` scale
(`Linglib/Features/Acceptability.lean`).
-/

namespace Features.MinimalPairs


open Features

/-! ### Word-based -/

/-- A minimal pair: two candidate forms with per-side acceptability
    judgments. The judgment fields default to the traditional binary
    (`lhs` = `.acceptable`, `rhs` = `.ungrammatical`) so most data sites
    only need to provide `lhs` and `rhs`; studies of graded phenomena
    (e.g. CRDC marginality, [osborne-li-2023]) override the
    judgments with the appropriate `Judgment` constructor. -/
structure MinimalPair where
  lhs : List Word
  rhs : List Word
  lhsJudgment : Judgment := .acceptable
  rhsJudgment : Judgment := .ungrammatical
  clauseType : ClauseForm
  description : String
  citation : String := ""
  deriving Repr

/-- Collection of minimal pairs for a phenomenon. -/
structure PhenomenonData where
  name : String
  pairs : List MinimalPair
  generalization : String
  deriving Repr

/-- Whether a Bool-valued grammaticality prediction agrees with a
    `Judgment`. Categorical predicates can only adjudicate the endpoints
    of the scale; for graded judgments (`.marginal`, `.questionable`,
    `.unacceptable`) the predicate is treated as vacuously consistent,
    since a Bool theory is not equipped to make those distinctions. -/
def predictionAgrees (predicted : Bool) : Judgment → Bool
  | .acceptable    => predicted
  | .ungrammatical => !predicted
  | _              => true

/-- Check if a grammaticality predicate captures a minimal pair.

    Captures iff the predicate's Bool result agrees with each side's
    `Judgment` per `predictionAgrees`. With default judgments this is
    the traditional `pred lhs && !pred rhs`. -/
def capturesMinimalPairBy (pred : List Word → Bool) (pair : MinimalPair) : Bool :=
  predictionAgrees (pred pair.lhs) pair.lhsJudgment &&
  predictionAgrees (pred pair.rhs) pair.rhsJudgment

/-- Check if a grammaticality predicate captures all minimal pairs in a
    phenomenon dataset. -/
def capturesPhenomenonData (pred : List Word → Bool) (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all (capturesMinimalPairBy pred)

/-! ### String-based (theory-neutral) -/

/-- String-based minimal pair for theory-neutral phenomena.

    Unlike `MinimalPair` which uses `List Word` (requiring feature
    specifications), this type uses raw strings that can be parsed by any
    theory. This keeps empirical data free from theoretical
    commitments. -/
structure SentencePair where
  /-- The grammatical sentence -/
  grammatical : String
  /-- The ungrammatical sentence -/
  ungrammatical : String
  /-- Clause form (declarative, question, etc.) -/
  clauseType : ClauseForm
  /-- Description of what the pair tests -/
  description : String
  /-- Citation for the data; empty string for uncited examples. -/
  citation : String := ""
  deriving Repr, BEq

/-- String-based phenomenon data for theory-neutral representation.

    This is the string-based analogue of `PhenomenonData`. Data files
    should use this type so that empirical data is decoupled from any
    particular grammatical theory's representation. -/
structure StringPhenomenonData where
  /-- Name of the phenomenon -/
  name : String
  /-- List of minimal pairs -/
  pairs : List SentencePair
  /-- Generalization captured by this data -/
  generalization : String
  deriving Repr

end Features.MinimalPairs
