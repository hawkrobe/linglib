/-
# Multiple Wh-Questions
@cite{belnap-1982} @cite{groenendijk-stokhof-1984}

Questions with multiple wh-phrases require n-place term answers.
@cite{belnap-1982} §4 argues for simultaneous introduction of multiple
*which*-phrases (as opposed to one-at-a-time introduction) — the question
asks for a unique pair, not sequential individuals.

(Separately, @cite{belnap-1982} §5 argues that different wh-words —
*which*, *who*, *where*, *what* — should be treated as distinct syntactic
categories with different answer types, contra the assumption that all
wh-words are interchangeable.)

## Examples

- "Which man loves which woman?" → "John, Mary; and Bill, Suzy"
- Expresses: John loves Mary, Bill loves Suzy, and no other man-woman pairs

## Insight

An n-constituent interrogative asks for an n-place relation.
The answer specifies which n-tuples satisfy the relation exhaustively.

-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.MultipleWh


/-- A multiple wh-question with its answer patterns -/
structure MultipleWhDatum where
  /-- The question -/
  question : String
  /-- Number of wh-phrases -/
  numWh : Nat
  /-- Example constituent answer (short form) -/
  constituentAnswer : String
  /-- Example sentential answer (long form) -/
  sententialAnswer : String
  /-- The exhaustive interpretation -/
  exhaustiveReading : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 310: "Which man loves which woman?" -/
def whichManWoman : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy"
  , sententialAnswer := "John loves Suzy"
  , exhaustiveReading := "The only man-woman loving pair is ⟨John, Suzy⟩"
  , source := "G&S 1984, p. 310"
  }

/-- Conjunctive answer: multiple pairs -/
def whichManWoman_conj : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy; and Bill, Mary"
  , sententialAnswer := "John loves Suzy, and Bill loves Mary"
  , exhaustiveReading := "The only man-woman loving pairs are ⟨John, Suzy⟩ and ⟨Bill, Mary⟩"
  , source := "G&S 1984, p. 312"
  }

/-- Disjunctive answer: uncertain which pair -/
def whichManWoman_disj : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy; or Bill, Mary"
  , sententialAnswer := "John loves Suzy, or Bill loves Mary"
  , exhaustiveReading := "Either ⟨John, Suzy⟩ is the only pair, or ⟨Bill, Mary⟩ is the only pair"
  , source := "G&S 1984, p. 312"
  }

/-- Complex answer with quantifiers -/
def whichManWoman_quant : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "Every man, a girl"
  , sententialAnswer := "Every man loves a girl"
  , exhaustiveReading := "For each man x, there's exactly one girl y such that x loves y"
  , source := "G&S 1984, p. 313"
  }

def multipleWhExamples : List MultipleWhDatum :=
  [whichManWoman, whichManWoman_conj, whichManWoman_disj, whichManWoman_quant]


/-- Constituent and sentential answers express the same proposition.
    @cite{groenendijk-stokhof-1984}: Both derived from the same abstract + term.
-/
structure AnswerEquivalence where
  /-- The question -/
  question : String
  /-- Short (constituent) answer -/
  shortAnswer : String
  /-- Long (sentential) answer -/
  longAnswer : String
  /-- They express the same proposition -/
  equivalent : Bool := true
  deriving Repr

def johnSuzy_equiv : AnswerEquivalence :=
  { question := "Which man loves which woman?"
  , shortAnswer := "John, Suzy"
  , longAnswer := "John loves Suzy"
  }

def answerEquivalenceExamples : List AnswerEquivalence :=
  [johnSuzy_equiv]


/-- Some multiple-wh questions have both pair-list and single-pair readings.
    G&S focus on exhaustive (pair-list) readings.
-/
inductive MultiWhReading where
  | pairList    -- Lists all satisfying pairs exhaustively
  | singlePair  -- Asks for one satisfying pair (mention-some)
  deriving DecidableEq, Repr

/-- G&S: The default/semantic reading is pair-list (exhaustive).
    Single-pair readings are pragmatic/mention-some.
-/
def defaultReading : MultiWhReading := .pairList


/-- G&S define a hierarchy of term categories:
    T^0 = S/S (sentence adverbs: yes, no)
    T^1 = S/AB^1 (ordinary terms: John, everyone)
    T^2 = S/AB^2 (2-place terms: John, Mary)
    T^n = S/AB^n (n-place terms)
-/
structure TermCategory where
  /-- The arity -/
  arity : Nat
  /-- Example expressions -/
  examples : List String
  /-- Type description -/
  typeDesc : String
  deriving Repr

def t0_category : TermCategory :=
  { arity := 0
  , examples := ["yes", "no", "if Mary walks"]
  , typeDesc := "S/S (sentence adverbs)"
  }

def t1_category : TermCategory :=
  { arity := 1
  , examples := ["John", "everyone", "the student who left"]
  , typeDesc := "S/(S/e) (ordinary terms)"
  }

def t2_category : TermCategory :=
  { arity := 2
  , examples := ["John, Mary", "every man, a girl"]
  , typeDesc := "S/((S/e)/e) (2-place terms)"
  }

def termCategories : List TermCategory :=
  [t0_category, t1_category, t2_category]

-- ============================================================================
-- § Cross-linguistic MWF parameter (Rudin 1988, Bošković 2002, …)
-- ============================================================================

/-! Languages vary in whether multiple wh-specifiers at a phase edge are
tolerable at PF. The textbook contrast (@cite{rudin-1988}) splits:

- **MWF languages** (Bulgarian, Romanian): all wh-phrases overtly front;
  phase edges with multiple wh-specifiers do not crash.
- **Non-MWF languages** (English, German, Greek): only one wh-phrase
  fronts in questions.

Within non-MWF, @cite{citko-gracanin-yuksek-2025} (p. 19) further splits
by *which* phase edges incur the PF asterisk:

- **vP-only** (German, Greek): sluicing — which deletes the vP edge —
  licenses multiple-wh-remnant configurations.
- **both vP and CP**: even sluicing leaves the CP-edge asterisk; no
  repair possible.

This tripartition lets the multiple-sluicing asymmetry be **derived**
from the parameter rather than stipulated as an independent Bool. -/

/-- Where the PF asterisk lands for multiple wh-specifiers in a non-MWF
    language. @cite{citko-gracanin-yuksek-2025} (p. 19). -/
inductive MWFParameter where
  /-- Multiple wh-fronting language (Bulgarian, Romanian). No PF asterisk
      at any edge. -/
  | fronts
  /-- Non-MWF with vP-only asterisk (German, Greek; @cite{citko-gracanin-yuksek-2025}
      "English variety B"). Sluicing (deleting the vP edge) repairs. -/
  | nonFrontsVPOnly
  /-- Non-MWF with asterisks at *both* vP and CP edges
      (@cite{citko-gracanin-yuksek-2025} "English variety A"). Sluicing
      cannot repair — the CP-edge asterisk survives ellipsis. -/
  | nonFrontsBothEdges
  deriving Repr, DecidableEq

namespace MWFParameter

/-- Whether the language allows multiple wh-fronting in matrix questions. -/
def allowsMWF : MWFParameter → Bool
  | .fronts => true
  | .nonFrontsVPOnly | .nonFrontsBothEdges => false

/-- Whether the vP edge incurs an asterisk for `n > 1` wh-specifiers. -/
def vPEdgeAsterisk : MWFParameter → Nat → Bool
  | .fronts, _ => false
  | .nonFrontsVPOnly, n | .nonFrontsBothEdges, n => decide (n > 1)

/-- Whether the CP edge incurs an asterisk for `n > 1` wh-specifiers. -/
def cPEdgeAsterisk : MWFParameter → Nat → Bool
  | .fronts, _ => false
  | .nonFrontsVPOnly, _ => false
  | .nonFrontsBothEdges, n => decide (n > 1)

end MWFParameter

/-- A phase edge has a multiple-wh-fronting violation when *some* edge
    receives an asterisk. -/
def mwfViolation (p : MWFParameter) (numWhSpecifiers : Nat) : Bool :=
  p.vPEdgeAsterisk numWhSpecifiers || p.cPEdgeAsterisk numWhSpecifiers

/-- Ellipsis of the vP edge repairs a MWF violation iff doing so eliminates
    every asterisk — i.e., there is no surviving CP-edge asterisk. -/
def ellipsisRepairsMWF (p : MWFParameter) (numWhSpecifiers : Nat)
    (vpEdgeDeleted : Bool) : Bool :=
  if mwfViolation p numWhSpecifiers then
    vpEdgeDeleted && !p.cPEdgeAsterisk numWhSpecifiers
  else true

/-- Single wh-specifier never triggers an MWF violation. -/
theorem single_wh_no_violation (p : MWFParameter) :
    mwfViolation p 1 = false := by
  cases p <;> decide

/-- Zero wh-specifiers never trigger an MWF violation. -/
theorem zero_wh_no_violation (p : MWFParameter) :
    mwfViolation p 0 = false := by
  cases p <;> decide

/-- MWF languages never have violations. -/
theorem mwf_language_no_violation (p : MWFParameter)
    (h : p.allowsMWF = true) (n : Nat) : mwfViolation p n = false := by
  cases p <;> simp_all [MWFParameter.allowsMWF, mwfViolation,
    MWFParameter.vPEdgeAsterisk, MWFParameter.cPEdgeAsterisk]

-- ============================================================================
-- § Cross-linguistic MWF data
-- ============================================================================

/-- Cross-linguistic MWF datum. Records the parameter setting and an
    example question. `allowsMultipleSluicing` is **derived** from the
    parameter via `ellipsisRepairsMWF`. -/
structure MWFLanguageDatum where
  language : String
  mwfParam : MWFParameter
  /-- Example multiple wh-question. -/
  exampleQuestion : String
  /-- Is the bare multiple-wh question grammatical? -/
  grammatical : Bool
  notes : String := ""
  deriving Repr

/-- Multiple sluicing is licensed iff vP-edge ellipsis repairs the MWF
    violation for `n = 2` wh-specifiers. Derived, not stipulated. -/
def MWFLanguageDatum.allowsMultipleSluicing (d : MWFLanguageDatum) : Bool :=
  ellipsisRepairsMWF d.mwfParam 2 (vpEdgeDeleted := true)

/-- Bulgarian: MWF language (@cite{rudin-1988} canonical case). -/
def bulgarian : MWFLanguageDatum :=
  { language := "Bulgarian"
  , mwfParam := .fronts
  , exampleQuestion := "Koj kakvo e kupil?"
  , grammatical := true
  , notes := "All wh-phrases front; @cite{rudin-1988} canonical MWF language" }

/-- German: non-MWF; vP-only asterisk; multiple sluicing repairs.
    @cite{citko-gracanin-yuksek-2025} ex 31a. -/
def german : MWFLanguageDatum :=
  { language := "German"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Wer was hat gesehen?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing (@cite{citko-gracanin-yuksek-2025} ex 31a)" }

/-- Greek: non-MWF; vP-only asterisk; multiple sluicing repairs.
    @cite{citko-gracanin-yuksek-2025} ex 31b. -/
def greek : MWFLanguageDatum :=
  { language := "Greek"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Pços ti efere?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing (@cite{citko-gracanin-yuksek-2025} ex 31b)" }

/-- Cross-linguistic MWF table (textbook-consensus subset). The
    intra-English variety A/B split is paper-specific to
    @cite{citko-gracanin-yuksek-2025} and lives there. -/
def mwfLanguageTable : List MWFLanguageDatum := [bulgarian, german, greek]

/-- Bulgarian: MWF language → no violations on bare multiple wh. -/
theorem bulgarian_no_violation : mwfViolation bulgarian.mwfParam 2 = false := by decide

/-- German question with two wh-phrases is starred. -/
theorem german_violates_in_questions :
    mwfViolation german.mwfParam 2 = true := by decide

/-- Sluicing repairs in German and Greek (vP-only asterisk eliminated). -/
theorem german_greek_sluicing_repairs :
    german.allowsMultipleSluicing = true ∧
    greek.allowsMultipleSluicing = true := by decide

end Phenomena.Questions.MultipleWh
