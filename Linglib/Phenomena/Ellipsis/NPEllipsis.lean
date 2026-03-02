import Linglib.Core.Lexical.Word

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

-/

namespace Phenomena.Ellipsis.NPEllipsis

-- ═══════════════════════════════════════════════════════════════
-- § 1: Binominal Classification
-- ═══════════════════════════════════════════════════════════════

/-- The three types of Spanish binominal construction (Saab 2026 §2).
    All surface with *de* but differ in internal structure. -/
inductive BinominalType where
  | pseudoPartitive   -- *un grupo de estudiantes* (group nouns)
  | quantificational  -- *un montón de estudiantes* (quantity nouns)
  | qualitative       -- *una mierda de departamento* (expressive nouns)
  deriving DecidableEq, BEq, Repr

/-- The structural source of the genitive *de* (Saab 2026 §4). -/
inductive GenitiveSource where
  | primeval    -- Pesetsky (2013): default case when D blocks structural case
  | equative   -- den Dikken (2006): EquP predication, not true genitive
  deriving DecidableEq, BEq, Repr

/-- Map binominal type to its genitive source. -/
def BinominalType.genitiveSource : BinominalType → GenitiveSource
  | .pseudoPartitive  => .primeval
  | .quantificational => .primeval
  | .qualitative      => .equative

-- ═══════════════════════════════════════════════════════════════
-- § 2: NP-Ellipsis Data
-- ═══════════════════════════════════════════════════════════════

/-- Does this binominal type license NP-ellipsis?
    Saab 2026 §3: pseudo-partitive and quantificational yes;
    qualitative no. -/
def BinominalType.licensesNPE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Does the Num head in this structure carry [E]?
    Saab 2026 §4: Num[E] is present iff the complement of Num
    is a standard nP (not an EquP with an indexical empty noun). -/
def BinominalType.hasNumE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Core result: NP-ellipsis is licensed iff Num has [E]. -/
theorem npe_iff_numE (b : BinominalType) :
    b.licensesNPE = b.hasNumE := by
  cases b <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 3: Agreement Data
-- ═══════════════════════════════════════════════════════════════

/-- Agreement number on the verb in binominal constructions.
    Saab 2026 §2: the controller is always Num, not QP in Spec,DP. -/
inductive AgreementNumber where
  | singular
  | plural
  deriving DecidableEq, BEq, Repr

/-- Which element controls verbal agreement?
    Saab 2026: Num in all three types, never QP in Spec,DP. -/
inductive AgreementController where
  | num       -- Num head (correct: Saab 2026)
  | specDP    -- QP in Spec,DP (incorrect alternative)
  deriving DecidableEq, BEq, Repr

/-- In all three types, Num controls agreement. -/
def BinominalType.agreementController : BinominalType → AgreementController
  | .pseudoPartitive  => .num
  | .quantificational => .num
  | .qualitative      => .num

/-- The agreement number on the verb for each type.
    Pseudo-partitive/quantificational: Num inherits plural from complement NP.
    Qualitative: Num gets singular from the expressive noun. -/
def BinominalType.verbAgreement : BinominalType → AgreementNumber
  | .pseudoPartitive  => .plural
  | .quantificational => .plural
  | .qualitative      => .singular

/-- Agreement controller is uniformly Num across all three types. -/
theorem agreement_from_num (b : BinominalType) :
    b.agreementController = .num := by
  cases b <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 4: Concrete Examples
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
-- § 5: Structural Properties
-- ═══════════════════════════════════════════════════════════════

/-- Qualitative binominals contain an indexical empty noun whose
    reference is contextually determined (like a pronoun). This
    is why NP-ellipsis fails: the empty noun cannot be recovered
    from the antecedent. -/
def BinominalType.hasIndexicalEmptyNoun : BinominalType → Bool
  | .pseudoPartitive  => false
  | .quantificational => false
  | .qualitative      => true

/-- Qualitative binominals contain an equative phrase (EquP)
    establishing a predication relation between the expressive
    noun and the referent. -/
def BinominalType.hasEquP : BinominalType → Bool
  | .pseudoPartitive  => false
  | .quantificational => false
  | .qualitative      => true

/-- The presence of an indexical empty noun entails no Num[E]:
    if the ellipsis site would include an unrecoverable element,
    NP-ellipsis is blocked. -/
theorem indexical_blocks_numE (b : BinominalType) :
    b.hasIndexicalEmptyNoun = true → b.hasNumE = false := by
  cases b <;> simp [BinominalType.hasIndexicalEmptyNoun, BinominalType.hasNumE]

/-- Primeval genitive ↔ Num[E] ↔ NP-ellipsis licensed.
    The three properties are coextensive across binominal types. -/
theorem primeval_iff_npe (b : BinominalType) :
    (b.genitiveSource == .primeval) = b.licensesNPE := by
  cases b <;> rfl

end Phenomena.Ellipsis.NPEllipsis
