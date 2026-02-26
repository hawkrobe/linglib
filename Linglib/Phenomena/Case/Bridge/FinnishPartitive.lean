import Linglib.Core.Case.Basic
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Finnish Partitive–Aspect Bridge @cite{karlsson-2018}

The Finnish partitive case is the primary formal link between case marking
and aspectual interpretation in the language (Karlsson 2018, Chs. 9, 12–13).
The case of the direct object determines — or reflects — the telicity of
the VP:

- **Accusative/genitive object** → telic (bounded, resultative):
  *Luin   kirja-n.*  'I read the book (completely).'

- **Partitive object** → atelic (unbounded, irresultative):
  *Luin   kirja-a.*  'I read the book / was reading the book (partially).'

The partitive also appears obligatorily under negation:
  *En lukenut kirja-a.*  'I didn't read the book.'

This is the first bridge in linglib connecting `Core.Case` to
`Semantics.Lexical.Verb.Aspect.Telicity`, making the case–aspect
interaction formally verifiable.

## Theoretical significance

Finnish partitive is evidence for the **Incremental Theme** hypothesis
(Krifka 1989, 1992): the object's referential properties (bounded vs.
unbounded) compose with the verb's event structure to determine VP-level
telicity. The case morphology makes this composition visible.

## References

- Karlsson, F. (2018). *Finnish: A Comprehensive Grammar*. Routledge.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics. In *Semantics and Contextual Expression*.
- Krifka, M. (1992). Thematic relations as links between nominal reference
  and temporal constitution. In Sag, I. & Szabolcsi, A. (eds.),
  *Lexical Matters*. CSLI.
- Kiparsky, P. (1998). Partitive case and aspect. In Butt, M. & Geuder, W.
  (eds.), *The Projection of Arguments*. CSLI.
-/

namespace Phenomena.Case.Bridge.FinnishPartitive

open Core (Case)
open Semantics.Lexical.Verb.Aspect (Telicity)

-- ============================================================================
-- § 1: Case–Aspect Mapping
-- ============================================================================

/-- The case of the Finnish direct object maps to VP telicity.
    Accusative/genitive → telic; partitive → atelic. -/
def objectCaseToTelicity : Case → Option Telicity
  | .acc | .gen => some .telic     -- bounded object → telic VP
  | .part      => some .atelic    -- unbounded object → atelic VP
  | _          => none            -- not an object case

/-- Context in which partitive case is obligatory (Karlsson §12.3). -/
inductive PartitiveLicensor where
  /-- Negation: *en lukenut kirja-a* -/
  | negation
  /-- Unbounded quantity: *join vettä* ('I drank water') -/
  | unboundedQuantity
  /-- Irresultative action: *luin kirjaa* ('I was reading the book') -/
  | irresultative
  deriving DecidableEq, BEq, Repr

/-- A partitive licensing datum: object case + licensing context + telicity. -/
structure PartitiveDatum where
  finnish : String
  gloss : String
  objectCase : Case
  licensor : Option PartitiveLicensor
  vpTelicity : Telicity
  deriving Repr, BEq

-- ============================================================================
-- § 2: Data
-- ============================================================================

/-- Accusative object, telic VP: 'I read the book (completely).' -/
def readBookComplete : PartitiveDatum :=
  { finnish := "Luin kirjan"
  , gloss := "I read the book (completely)"
  , objectCase := .acc
  , licensor := none
  , vpTelicity := .telic }

/-- Partitive object, atelic VP (irresultative): 'I was reading the book.' -/
def readBookPartial : PartitiveDatum :=
  { finnish := "Luin kirjaa"
  , gloss := "I was reading the book (partially)"
  , objectCase := .part
  , licensor := some .irresultative
  , vpTelicity := .atelic }

/-- Partitive under negation: 'I didn't read the book.' -/
def readBookNegated : PartitiveDatum :=
  { finnish := "En lukenut kirjaa"
  , gloss := "I didn't read the book"
  , objectCase := .part
  , licensor := some .negation
  , vpTelicity := .atelic }

/-- Partitive with mass noun (unbounded quantity): 'I drank water.' -/
def drankWater : PartitiveDatum :=
  { finnish := "Join vettä"
  , gloss := "I drank (some) water"
  , objectCase := .part
  , licensor := some .unboundedQuantity
  , vpTelicity := .atelic }

def allData : List PartitiveDatum :=
  [readBookComplete, readBookPartial, readBookNegated, drankWater]

-- ============================================================================
-- § 3: Bridge Theorems
-- ============================================================================

/-- Accusative object maps to telic VP. -/
theorem acc_telic : objectCaseToTelicity .acc = some .telic := rfl

/-- Partitive object maps to atelic VP. -/
theorem part_atelic : objectCaseToTelicity .part = some .atelic := rfl

/-- Genitive object (used for total objects in some environments) maps
    to telic, same as accusative. -/
theorem gen_telic : objectCaseToTelicity .gen = some .telic := rfl

/-- For every datum, the `objectCaseToTelicity` mapping agrees with the
    annotated `vpTelicity`. -/
theorem mapping_agrees_with_data :
    allData.all (fun d =>
      objectCaseToTelicity d.objectCase == some d.vpTelicity) = true := by
  native_decide

/-- All partitive data have atelic VP interpretation. -/
theorem partitive_implies_atelic :
    (allData.filter (·.objectCase == .part)).all
      (·.vpTelicity == .atelic) = true := by native_decide

/-- All accusative data have telic VP interpretation. -/
theorem accusative_implies_telic :
    (allData.filter (·.objectCase == .acc)).all
      (·.vpTelicity == .telic) = true := by native_decide

/-- Every partitive datum has a licensor (negation, quantity, or aspect). -/
theorem partitive_has_licensor :
    (allData.filter (·.objectCase == .part)).all
      (fun d => d.licensor.isSome) = true := by native_decide

end Phenomena.Case.Bridge.FinnishPartitive
