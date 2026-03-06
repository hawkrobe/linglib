import Linglib.Core.Lexical.Word
import Linglib.Core.Lexical.Binominal

/-!
# NP-Ellipsis in Spanish Binominals @cite{saab-2026}
@cite{lobeck-1995} @cite{pesetsky-2013}

Theory-neutral data on NP-ellipsis patterns across three types of
Spanish binominal constructions that are superficially syncretic
(all use *de*) but differ in ellipsis licensing and agreement.

## The Three Binominal Types

1. **Pseudo-partitive**: *un grupo de estudiantes* 'a group of students'
   - NP-ellipsis OK: *un grupo* ✓
   - Verb agrees with plural (students)

2. **Quantificational**: *un montón de estudiantes* 'a lot of students'
   - NP-ellipsis OK: *un montón* ✓
   - Verb agrees with plural (students)

3. **Qualitative**: *una mierda de departamento* 'a shit of apartment'
   - NP-ellipsis BLOCKED: *una mierda ✗ (with intended referent reading)
   - Verb agrees with singular (mierda)

## Key Diagnostic

NP-ellipsis distinguishes pseudo-partitive/quantificational (which share
a primeval genitive structure with Num[E]) from qualitative (which have
an equative structure lacking Num[E]).

`BinominalType` and its core structural properties (`licensesNPE`, `hasNumE`)
are defined in `Core.Lexical.Binominal`. This file adds ellipsis-specific
data (genitive sources, agreement, concrete examples).
-/

namespace Phenomena.Ellipsis.NPEllipsis

open Core.Lexical.Binominal

-- ═══════════════════════════════════════════════════════════════
-- § 1: Genitive Structure
-- ═══════════════════════════════════════════════════════════════

/-- The structural source of the genitive *de* (@cite{saab-2026} §4). -/
inductive GenitiveSource where
  | primeval    -- @cite{pesetsky-2013}: default case when D blocks structural case
  | equative   -- @cite{dendikken-2006}: EquP predication, not true genitive
  deriving DecidableEq, BEq, Repr

/-- Map binominal type to its genitive source. -/
def genitiveSource : BinominalType → GenitiveSource
  | .pseudoPartitive  => .primeval
  | .quantificational => .primeval
  | .qualitative      => .equative

-- ═══════════════════════════════════════════════════════════════
-- § 2: Agreement Data
-- ═══════════════════════════════════════════════════════════════

/-- Agreement number on the verb in binominal constructions.
    @cite{saab-2026} §2: the controller is always Num, not QP in Spec,DP. -/
inductive AgreementNumber where
  | singular
  | plural
  deriving DecidableEq, BEq, Repr

/-- Which element controls verbal agreement?
    @cite{saab-2026}: Num in all three types, never QP in Spec,DP. -/
inductive AgreementController where
  | num       -- Num head (correct: @cite{saab-2026})
  | specDP    -- QP in Spec,DP (incorrect alternative)
  deriving DecidableEq, BEq, Repr

/-- In all three types, Num controls agreement. -/
def agreementController : BinominalType → AgreementController
  | .pseudoPartitive  => .num
  | .quantificational => .num
  | .qualitative      => .num

/-- The agreement number on the verb for each type.
    Pseudo-partitive/quantificational: Num inherits plural from complement NP.
    Qualitative: Num gets singular from the expressive noun. -/
def verbAgreement : BinominalType → AgreementNumber
  | .pseudoPartitive  => .plural
  | .quantificational => .plural
  | .qualitative      => .singular

/-- Agreement controller is uniformly Num across all three types. -/
theorem agreement_from_num (b : BinominalType) :
    agreementController b = .num := by
  cases b <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 3: Concrete Examples
-- ═══════════════════════════════════════════════════════════════

/-- An NP-ellipsis datum: a Spanish binominal sentence with its
    ellipsis and agreement properties. -/
structure NPEDatum where
  /-- The full sentence -/
  sentence : String
  /-- The attempted ellipsis form -/
  ellipsisForm : String
  /-- Is NP-ellipsis grammatical? -/
  npeGrammatical : Bool
  /-- Binominal type -/
  binominalType : BinominalType
  /-- Agreement number on the verb -/
  agreement : AgreementNumber
  /-- Source -/
  source : String := "Saab 2026"
  deriving Repr

-- Pseudo-partitive examples (§2.1)

def grupoDeEstudiantes : NPEDatum :=
  { sentence := "un grupo de estudiantes"
    ellipsisForm := "un grupo"
    npeGrammatical := true
    binominalType := .pseudoPartitive
    agreement := .plural
    source := "Saab 2026, (6a)" }

def conjuntoDeProblemas : NPEDatum :=
  { sentence := "un conjunto de problemas"
    ellipsisForm := "un conjunto"
    npeGrammatical := true
    binominalType := .pseudoPartitive
    agreement := .plural
    source := "Saab 2026, (6b)" }

-- Quantificational examples (§2.2)

def montonDeEstudiantes : NPEDatum :=
  { sentence := "un montón de estudiantes"
    ellipsisForm := "un montón"
    npeGrammatical := true
    binominalType := .quantificational
    agreement := .plural
    source := "Saab 2026, (7a)" }

def pilaDeLibros : NPEDatum :=
  { sentence := "una pila de libros"
    ellipsisForm := "una pila"
    npeGrammatical := true
    binominalType := .quantificational
    agreement := .plural
    source := "Saab 2026, (7b)" }

-- Qualitative examples (§2.3) — NP-ellipsis BLOCKED

def mierdaDeDepartamento : NPEDatum :=
  { sentence := "una mierda de departamento"
    ellipsisForm := "*una mierda"
    npeGrammatical := false
    binominalType := .qualitative
    agreement := .singular
    source := "Saab 2026, (9)" }

def maravillaDeMujer : NPEDatum :=
  { sentence := "una maravilla de mujer"
    ellipsisForm := "*una maravilla"
    npeGrammatical := false
    binominalType := .qualitative
    agreement := .singular
    source := "Saab 2026, (10)" }

/-- All NP-ellipsis data. -/
def allExamples : List NPEDatum :=
  [ grupoDeEstudiantes, conjuntoDeProblemas
  , montonDeEstudiantes, pilaDeLibros
  , mierdaDeDepartamento, maravillaDeMujer ]

/-- Per-datum verification: each example's grammaticality matches
    its binominal type's NPE licensing prediction. -/
theorem grupo_npe_ok :
    grupoDeEstudiantes.npeGrammatical =
    grupoDeEstudiantes.binominalType.licensesNPE := rfl

theorem monton_npe_ok :
    montonDeEstudiantes.npeGrammatical =
    montonDeEstudiantes.binominalType.licensesNPE := rfl

theorem mierda_npe_blocked :
    mierdaDeDepartamento.npeGrammatical =
    mierdaDeDepartamento.binominalType.licensesNPE := rfl

theorem maravilla_npe_blocked :
    maravillaDeMujer.npeGrammatical =
    maravillaDeMujer.binominalType.licensesNPE := rfl

-- ═══════════════════════════════════════════════════════════════
-- § 4: Structural Properties
-- ═══════════════════════════════════════════════════════════════

/-- Qualitative binominals contain an indexical empty noun whose
    reference is contextually determined (like a pronoun). This
    is why NP-ellipsis fails: the empty noun cannot be recovered
    from the antecedent. -/
def hasIndexicalEmptyNoun : BinominalType → Bool
  | .pseudoPartitive  => false
  | .quantificational => false
  | .qualitative      => true

/-- Qualitative binominals contain an equative phrase (EquP)
    establishing a predication relation between the expressive
    noun and the referent. -/
def hasEquP : BinominalType → Bool
  | .pseudoPartitive  => false
  | .quantificational => false
  | .qualitative      => true

/-- The presence of an indexical empty noun entails no Num[E]:
    if the ellipsis site would include an unrecoverable element,
    NP-ellipsis is blocked. -/
theorem indexical_blocks_numE (b : BinominalType) :
    hasIndexicalEmptyNoun b = true → b.hasNumE = false := by
  cases b <;> simp [hasIndexicalEmptyNoun, BinominalType.hasNumE]

/-- Primeval genitive ↔ Num[E] ↔ NP-ellipsis licensed.
    The three properties are coextensive across binominal types. -/
theorem primeval_iff_npe (b : BinominalType) :
    (genitiveSource b == .primeval) = b.licensesNPE := by
  cases b <;> rfl

end Phenomena.Ellipsis.NPEllipsis
