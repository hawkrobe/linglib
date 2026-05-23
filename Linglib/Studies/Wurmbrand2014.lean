import Linglib.Data.Examples.Schema
import Linglib.Core.Time.Reichenbach
import Linglib.Semantics.Tense.Basic
import Linglib.Theories.Syntax.Minimalist.Tense.InfinitivalTense
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{wurmbrand-2014}: Tense and aspect in English infinitives
@cite{wurmbrand-2014}

Wurmbrand (Linguistic Inquiry 45(3), 2014) classifies English infinitival
complements into three types based on tense-aspect behavior:

1. **Future irrealis** (`decide`, `want`, `plan`, `hope`): no independent
   tense; future orientation comes from a woll-like operator selected by
   the matrix verb. Example: "Leo decided to read a book" — reading is
   future of deciding.
2. **Propositional** (`believe`, `claim`): NOW-anchored tense. The
   embedded event is simultaneous with the matrix attitude. Example: "Leo
   believes Julia to be a princess" — princess-status at believing time.
3. **Restructuring** (`try`, `begin`): dependent on matrix tense; embedded
   event in the same temporal domain as the matrix.

## Empirical anchors

- (1a) "Leo decided to read a book." — future irrealis
- (1b) "Leo believes Julia to be a princess." — propositional
- (2a) "Leo decided to bring the toys tomorrow." — future-irrealis +
  episodic adverbial OK
- (2b) "*Leo believed Julia to bring the toys right then." — propositional
  + episodic adverbial blocks bare infinitive (needs progressive)

## Lean encoding

The classification theorems use Fragment entries (`want`, `believe`,
`try_`) from `Fragments.English.Predicates.Verbal` + `tenseClass`
from `Minimalist.Tense.InfinitivalTense`. The Fragment field carries
Wurmbrand's classification.

-/

namespace Wurmbrand2014

open Core.Time.Reichenbach
open Data.Examples (LinguisticExample)
open Minimalist.Tense.InfinitivalTense
open Fragments.English.Predicates.Verbal (want believe try_)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Wurmbrand2014.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex1a : LinguisticExample :=
  { id := "wurmbrand2014_ex1a"
    source := ⟨"wurmbrand-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to read a book."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo decided to read a book."
    context := "Future-irrealis infinitive: the reading is future of the deciding. No tense morphology on the complement; the future orientation comes from `decide`'s lexical semantics (woll-like operator selected by the matrix verb)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-irrealis (reading after deciding)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (1a), LI 45(3) p. 403–404. First diagnostic in her classification of infinitival tense — future irrealis with `decide` (and the `want` class more generally)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b : LinguisticExample :=
  { id := "wurmbrand2014_ex1b"
    source := ⟨"wurmbrand-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believes Julia to be a princess."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo believes Julia to be a princess."
    context := "Propositional (NOW-anchored) infinitive: the believing time and Julia-being-a-princess time coincide. Simultaneous, not future-shifted."
    judgment := .acceptable
    alternatives := []
    readings := [("propositional (Julia princess at believing time)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (1b), p. 403. Second class in her classification: propositional infinitives anchor to the matrix's NOW."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "wurmbrand2014_ex2a"
    source := ⟨"wurmbrand-2014", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to bring the toys tomorrow."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo decided to bring the toys tomorrow."
    context := "Future-irrealis infinitive with episodic interpretation: the bringing is at a specific future time (tomorrow relative to the deciding)."
    judgment := .acceptable
    alternatives := []
    readings := [("episodic-future (bringing tomorrow-relative-to-deciding)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (2a), p. 404. Diagnoses that future-irrealis infinitives admit episodic readings."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "wurmbrand2014_ex2b"
    source := ⟨"wurmbrand-2014", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believed Julia to bring the toys right then."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo believed Julia to bring the toys right then."
    context := "Propositional infinitive + episodic adverbial. The bare infinitive does NOT admit an episodic reading; needs the progressive (`to be bringing`) instead."
    judgment := .ungrammatical
    alternatives := [("Leo believed Julia to be bringing the toys right then.", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (2b), p. 404. Diagnoses that propositional infinitives BLOCK bare episodic readings — needs the progressive. The contrast (2a)/(2b) is the cornerstone of her propositional vs future-irrealis classification."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b]

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § Per-class theorems (consume Fragment + InfinitivalTense substrate)
-- ════════════════════════════════════════════════════════════════

/-- `want` is future-irrealis → future-oriented complement. -/
theorem wurmbrandClassifiesWant :
    want.tenseClass = .futureIrrealis ∧
    classOrientation .futureIrrealis = .futureOriented := ⟨rfl, rfl⟩

/-- `believe` is propositional → simultaneous complement. -/
theorem wurmbrandClassifiesBelieve :
    believe.tenseClass = .propositional ∧
    classOrientation .propositional = .simultaneous := ⟨rfl, rfl⟩

/-- `try` is restructuring → dependent on matrix temporal domain. -/
theorem wurmbrandClassifiesTry :
    try_.tenseClass = .restructuring ∧
    classOrientation .restructuring = .dependent := ⟨rfl, rfl⟩

end Wurmbrand2014
