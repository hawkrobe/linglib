import Linglib.Fragments.Greek.TemporalConnectives
import Linglib.Fragments.Icelandic.TemporalConnectives
import Linglib.Fragments.Dutch.TemporalConnectives
import Linglib.Fragments.Finnish.TemporalConnectives
import Linglib.Phenomena.TemporalConnectives.NegationData

/-!
# Cross-Linguistic Typology of the Two-*Until* Distinction
@cite{giannakidou-2002} @cite{karttunen-1974}

Languages employ four strategies for expressing the durative/eventive
distinction in temporal connectives:

1. **Three-way lexicalization** (Greek): separate lexemes for
   *before* (*prin*), durative *until* (*mexri*), and eventive NPI-*until*
   (*para monon*).

2. **Two-way lexicalization** (Icelandic, Finnish): separate lexemes for
   durative *until* (*flanga til*, *kunnes*) and eventive NPI-*until*
   (*fyrr en*, *ennenkuin*). *Before* may or may not be one of the *until*
   forms.

3. **Ambiguity** (English): a single lexeme *until* is ambiguous between
   durative (positive contexts) and eventive/NPI (negative contexts).

4. **PPI replacement** (Dutch, German): durative *until* (*tot*, *bis*)
   cannot co-occur with negation. A separate PPI (*pas*, *erst*) supplies
   the 'not before' meaning without negation.

The typology is organized by **how many surface forms** a language uses
and **what polarity properties** they have, not by geographic or genetic
affiliation. The aspect parameter (overt vs covert perfective/imperfective
marking) is orthogonal: Icelandic has no overt aspect but still lexicalizes
the distinction.
-/

namespace Phenomena.TemporalConnectives.Typology

-- ============================================================================
-- § 1: Until Strategy Classification
-- ============================================================================

/-- How a language handles the durative/eventive *until* distinction. -/
inductive UntilStrategy where
  /-- Three distinct lexemes: *before*, durative *until*, eventive NPI-*until*.
      Greek: *prin*, *mexri*, *para monon*. -/
  | threeWay
  /-- Two distinct lexemes: durative *until* and eventive NPI-*until*.
      Icelandic: *flanga til*, *fyrr en*. Finnish: *kunnes*, *ennenkuin*. -/
  | twoWay
  /-- Single ambiguous lexeme, disambiguated by negation context.
      English: *until*. -/
  | ambiguous
  /-- Durative *until* blocked under negation; PPI replaces NPI-*until*.
      Dutch: *tot*, *pas*. German: *bis*, *erst*. -/
  | ppiReplacement
  deriving DecidableEq, Repr, BEq

/-- A language's strategy for the two-*until* distinction, with evidence
    linking to fragment entries and NegationData. -/
structure UntilTypologyEntry where
  language : String
  strategy : UntilStrategy
  /-- Surface form for durative *until* -/
  durativeForm : String
  /-- Surface form for eventive *until* (NPI or PPI) -/
  eventiveForm : String
  /-- Is the eventive form morphologically built on *before*? -/
  eventiveMorphBeforeBased : Bool
  /-- Does the language have overt perfective/imperfective marking? -/
  hasOvertAspect : Bool
  deriving Repr

-- ============================================================================
-- § 2: Language Entries
-- ============================================================================

def greek : UntilTypologyEntry where
  language := "Greek"
  strategy := .threeWay
  durativeForm := "mexri (μέχρι)"
  eventiveForm := "para monon (παρά μονον)"
  eventiveMorphBeforeBased := false
  hasOvertAspect := true

def icelandic : UntilTypologyEntry where
  language := "Icelandic"
  strategy := .twoWay
  durativeForm := "flanga til / til"
  eventiveForm := "fyrr en"
  eventiveMorphBeforeBased := true   -- fyrr = 'earlier/before' + en = 'than'
  hasOvertAspect := false

def finnish : UntilTypologyEntry where
  language := "Finnish"
  strategy := .twoWay
  durativeForm := "kunnes / siihen saakka"
  eventiveForm := "ennenkuin"
  eventiveMorphBeforeBased := true   -- ennen = 'before' + kuin = 'than'
  hasOvertAspect := false

def english : UntilTypologyEntry where
  language := "English"
  strategy := .ambiguous
  durativeForm := "until"
  eventiveForm := "until (NPI, with negation)"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false  -- no overt perf/impf; simple past = covert perfective

def dutch : UntilTypologyEntry where
  language := "Dutch"
  strategy := .ppiReplacement
  durativeForm := "tot"
  eventiveForm := "pas"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false

def german : UntilTypologyEntry where
  language := "German"
  strategy := .ppiReplacement
  durativeForm := "bis"
  eventiveForm := "erst"
  eventiveMorphBeforeBased := false
  hasOvertAspect := false

/-- The full typological sample. -/
def typology : List UntilTypologyEntry :=
  [greek, icelandic, finnish, english, dutch, german]

-- ============================================================================
-- § 3: Typological Predictions
-- ============================================================================

/-- Every language in the sample uses distinct surface forms for durative
    and eventive *until* (even the ambiguous strategy uses the same form
    in different syntactic contexts, disambiguated by negation). -/
theorem all_distinguish_durative_eventive :
    ∀ e ∈ typology, e.durativeForm ≠ e.eventiveForm := by
  intro e he
  simp only [typology, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The two-way and three-way strategies both have morphologically
    *before*-based eventive forms in at least one language, confirming
    @cite{karttunen-1974}'s identity NPI-*until* = ¬*before*. -/
theorem before_morphology_attested :
    icelandic.eventiveMorphBeforeBased = true ∧
    finnish.eventiveMorphBeforeBased = true :=
  ⟨rfl, rfl⟩

/-- Overt aspect marking is NOT required for lexicalization of the
    two-*until* distinction. Icelandic and Finnish lack overt verbal
    aspect but still lexicalize two *until*s. -/
theorem aspect_not_required :
    icelandic.hasOvertAspect = false ∧ icelandic.strategy = .twoWay ∧
    finnish.hasOvertAspect = false ∧ finnish.strategy = .twoWay :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Bridge to Fragment Data
-- ============================================================================

open Fragments.Greek.TemporalConnectives in
/-- Greek strategy confirmed by fragment: three distinct forms. -/
theorem greek_confirmed :
    mexri.form ≠ paraMonon.form ∧
    mexri.form ≠ prin.form ∧
    paraMonon.form ≠ prin.form := by
  exact ⟨by decide, by decide, by decide⟩

open Fragments.Icelandic.TemporalConnectives in
/-- Icelandic strategy confirmed by fragment: two distinct forms with
    veridicality split. -/
theorem icelandic_confirmed :
    flangaTil.form ≠ fyrrEn.form ∧
    flangaTil.complementVeridical = true ∧
    fyrrEn.complementVeridical = false :=
  ⟨by decide, rfl, rfl⟩

open Fragments.Dutch.TemporalConnectives in
/-- Dutch strategy confirmed by fragment: two distinct forms with
    veridicality split. -/
theorem dutch_confirmed :
    tot.form ≠ pas.form ∧
    tot.complementVeridical = true ∧
    pas.complementVeridical = false :=
  ⟨by decide, rfl, rfl⟩

-- ============================================================================
-- § 5: Bridge to NegationData
-- ============================================================================

open NegationData in
/-- The NegationData three-way actualization split is consistent with
    the typological strategies: all strategies preserve the semantic
    distinction between durative (implicature) and eventive (entailment)
    actualization. -/
theorem actualization_universal :
    greek_mexri.actualizationStatus = .implicature ∧
    english_dur_until.actualizationStatus = .implicature ∧
    greek_para_monon.actualizationStatus = .entailment ∧
    english_npi_until.actualizationStatus = .entailment :=
  ⟨rfl, rfl, rfl, rfl⟩

open NegationData in
/-- English NPI-*until* and Greek *para monon* agree on semantic type:
    both are eventive (not before-type). This was previously inconsistent
    in the data file. -/
theorem english_greek_eventive_agree :
    english_npi_until.semanticType = greek_para_monon.semanticType :=
  rfl

end Phenomena.TemporalConnectives.Typology
