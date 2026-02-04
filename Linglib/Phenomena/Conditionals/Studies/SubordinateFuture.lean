/-
# Subordinate Future (SF) Data

Empirical data from Mendes (2025) "Indefiniteness in future reference"
Semantics & Pragmatics 18(10).

## What is the Subordinate Future?

The **Subordinate Future** (SF) is a verbal form in Romance languages that:
1. Uses **present tense morphology** (not future morphology)
2. Appears in **subordinate contexts** (conditionals, relative clauses)
3. Receives **future reference** interpretation

Example (Portuguese):
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF at home, she will answer."
  (≈ "If Maria is/will-be home, she will answer.")

The puzzle: Why does present morphology yield future interpretation?

Mendes' answer: SF is **subjunctive**, not indicative. The subjunctive
introduces a situation dref from the historical modal base, which can
include future times.

## Key Data Points

1. SF vs Indicative Present in conditionals
2. Temporal anchoring asymmetries
3. Modal donkey anaphora
4. Cross-linguistic parallels (Spanish, Italian)

## References

- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
- Comrie, B. (1985). Tense. Cambridge University Press.
- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
-/

namespace Phenomena.SubordinateFuture


/--
Portuguese verbal forms relevant to SF analysis.

Following standard Portuguese grammar, the forms are:
- Indicative Present: "está" (is)
- Indicative Future: "estará" (will be)
- Subjunctive Present: "esteja" (be.SUBJ)
- Subjunctive Future: "estiver" (be.SF) ← The Subordinate Future

The SF "estiver" is traditionally called "futuro do subjuntivo"
(future subjunctive), but Mendes argues it's present tense + subjunctive mood.
-/
inductive PortugueseForm where
  | indPresent    -- "está" (is)
  | indFuture     -- "estará" (will be)
  | subjPresent   -- "esteja" (be.SUBJ.PRES)
  | subjFuture    -- "estiver" (be.SF)
  deriving DecidableEq, Repr, BEq

/--
Morphological decomposition of SF according to Mendes.

The key claim: SF = SUBJ + PRES (not SUBJ + FUT)
The future interpretation comes from the subjunctive introducing
a situation in the historical alternatives, not from tense.
-/
structure SFDecomposition where
  mood : String := "Subjunctive"
  tense : String := "Present"
  futureFromMood : Bool := true  -- Future interpretation from mood, not tense

def mendesSFAnalysis : SFDecomposition :=
  { mood := "Subjunctive"
  , tense := "Present"
  , futureFromMood := true }


/--
An example with its interpretation and key properties.
-/
structure SFExample where
  /-- Example number from the paper -/
  exampleNum : String
  /-- Portuguese sentence -/
  portuguese : String
  /-- English gloss -/
  gloss : String
  /-- Free translation -/
  translation : String
  /-- Does it have future reference? -/
  hasFutureRef : Bool
  /-- Is it in a subordinate context? -/
  isSubordinate : Bool
  /-- What triggers the SF? -/
  trigger : String
  deriving Repr

/--
Example (1): Basic SF in conditional antecedent.

"Se a Maria estiver em casa, ela vai atender o telefone."
"If Maria be.SF at home, she will answer the phone."

Key observations:
- SF "estiver" has present morphology
- Interpretation is future-oriented
- Main clause anchored to antecedent time
-/
def ex1_basicConditional : SFExample :=
  { exampleNum := "1"
  , portuguese := "Se a Maria estiver em casa, ela vai atender o telefone."
  , gloss := "If the Maria be.SF at home, she will answer the phone"
  , translation := "If Maria is home (tomorrow), she will answer the phone."
  , hasFutureRef := true
  , isSubordinate := true
  , trigger := "Conditional antecedent (se)" }

/--
Example (2): Indicative present in conditional (contrast).

"Se a Maria está em casa, ela vai atender o telefone."
"If Maria is.IND at home, she will answer the phone."

Key observation: Indicative present has PRESENT reading, not future.
This contrasts with SF which gets future reading.
-/
def ex2_indicativeContrast : SFExample :=
  { exampleNum := "2"
  , portuguese := "Se a Maria está em casa, ela vai atender o telefone."
  , gloss := "If the Maria is.IND at home, she will answer the phone"
  , translation := "If Maria is home (right now), she will answer the phone."
  , hasFutureRef := false  -- Present reference, not future
  , isSubordinate := true
  , trigger := "Conditional antecedent (se)" }

/--
Example (3): SF in temporal clause.

"Quando a Maria estiver em casa, ela vai atender."
"When Maria be.SF at home, she will answer."

SF also appears with "quando" (when), "depois que" (after), etc.
-/
def ex3_temporalClause : SFExample :=
  { exampleNum := "3"
  , portuguese := "Quando a Maria estiver em casa, ela vai atender."
  , gloss := "When the Maria be.SF at home, she will answer"
  , translation := "When Maria is home (in the future), she will answer."
  , hasFutureRef := true
  , isSubordinate := true
  , trigger := "Temporal clause (quando)" }

/--
Example (4): SF in relative clause.

"O aluno que estiver preparado pode sair."
"The student who be.SF prepared can leave."

SF in relative clauses gets future/generic interpretation.
-/
def ex4_relativeClause : SFExample :=
  { exampleNum := "4"
  , portuguese := "O aluno que estiver preparado pode sair."
  , gloss := "The student who be.SF prepared can leave"
  , translation := "The student who is (will be) prepared can leave."
  , hasFutureRef := true
  , isSubordinate := true
  , trigger := "Relative clause (que)" }


/--
Modal donkey anaphora data structure.

Mendes' key evidence: SF licenses donkey anaphora across clause boundaries
in a way that requires a situation dref analysis.
-/
structure ModalDonkeyExample where
  exampleNum : String
  portuguese : String
  gloss : String
  /-- Is the anaphora felicitous? -/
  felicitous : Bool
  /-- What is the antecedent? -/
  antecedent : String
  /-- What is the anaphor? -/
  anaphor : String
  deriving Repr

/--
Example (5): Donkey anaphora with SF.

"Se um estudante estiver preparado, ele pode sair."
"If a student be.SF prepared, he can leave."

The pronoun "ele" (he) is bound by "um estudante" (a student)
across the conditional boundary. This is modal donkey anaphora.
-/
def ex5_donkeyWithSF : ModalDonkeyExample :=
  { exampleNum := "5"
  , portuguese := "Se um estudante estiver preparado, ele pode sair."
  , gloss := "If a student be.SF prepared, he can leave"
  , felicitous := true
  , antecedent := "um estudante (a student)"
  , anaphor := "ele (he)" }

/--
Example (6): Temporal anchoring evidence.

"Se a Maria estiver em casa às 5h, ela vai estar cansada."
"If Maria be.SF at home at 5pm, she will be tired."

Key: The tiredness is evaluated at the ANTECEDENT time (5pm),
not the speech time. This shows temporal anchoring to the
situation introduced by SF.
-/
def ex6_temporalAnchoring : SFExample :=
  { exampleNum := "6"
  , portuguese := "Se a Maria estiver em casa às 5h, ela vai estar cansada."
  , gloss := "If the Maria be.SF at home at-the 5pm, she will be tired"
  , translation := "If Maria is home at 5pm, she will be tired (at that time)."
  , hasFutureRef := true
  , isSubordinate := true
  , trigger := "Conditional with explicit time" }


/--
Cross-linguistic data: Spanish parallel.

Spanish has a similar "futuro de subjuntivo" form, though it's archaic
in modern Spanish (preserved in legal language and some dialects).
-/
structure CrossLinguisticExample where
  language : String
  form : String
  sentence : String
  gloss : String
  isParallelToPortugueseSF : Bool
  deriving Repr

def spanish_sf : CrossLinguisticExample :=
  { language := "Spanish"
  , form := "futuro de subjuntivo"
  , sentence := "Si alguien lo supiere, dígamelo."
  , gloss := "If someone it know.SF, tell-me-it"
  , isParallelToPortugueseSF := true }

def italian_congiuntivo : CrossLinguisticExample :=
  { language := "Italian"
  , form := "congiuntivo presente"
  , sentence := "Se Maria sia a casa, risponderà."
  , gloss := "If Maria be.SUBJ at home, she-will-answer"
  , isParallelToPortugueseSF := true }


/--
Predictions of Mendes' analysis.

The key predictions that follow from treating SF as subjunctive
(introducing a situation dref) rather than future indicative.
-/
structure MendesPrediction where
  prediction : String
  confirmed : Bool
  evidence : String
  deriving Repr

def prediction_futureFromMood : MendesPrediction :=
  { prediction := "Future reference comes from mood (SUBJ), not tense"
  , confirmed := true
  , evidence := "SF has present morphology but future interpretation" }

def prediction_temporalShift : MendesPrediction :=
  { prediction := "Main clause time is anchored to antecedent situation"
  , confirmed := true
  , evidence := "Example 6: tiredness evaluated at 5pm, not speech time" }

def prediction_donkeyAnaphora : MendesPrediction :=
  { prediction := "SF licenses modal donkey anaphora"
  , confirmed := true
  , evidence := "Example 5: cross-clausal binding with SF" }

def prediction_indicativeContrast : MendesPrediction :=
  { prediction := "Indicative present gets present reading, not future"
  , confirmed := true
  , evidence := "Example 2 vs Example 1 contrast" }


/-- All SF examples -/
def sfExamples : List SFExample :=
  [ ex1_basicConditional
  , ex2_indicativeContrast
  , ex3_temporalClause
  , ex4_relativeClause
  , ex6_temporalAnchoring ]

/-- All donkey examples -/
def donkeyExamples : List ModalDonkeyExample :=
  [ ex5_donkeyWithSF ]

/-- All cross-linguistic examples -/
def crossLinguisticExamples : List CrossLinguisticExample :=
  [ spanish_sf
  , italian_congiuntivo ]

/-- All predictions -/
def predictions : List MendesPrediction :=
  [ prediction_futureFromMood
  , prediction_temporalShift
  , prediction_donkeyAnaphora
  , prediction_indicativeContrast ]

-- Summary

/-
## What This File Provides

### Morphological Types
- `PortugueseForm`: Portuguese verbal forms
- `SFDecomposition`: Mendes' morphological analysis of SF

### Example Data
- `SFExample`: Structure for SF examples
- `ex1_basicConditional` through `ex6_temporalAnchoring`: Core examples

### Modal Donkey Evidence
- `ModalDonkeyExample`: Structure for donkey anaphora data
- `ex5_donkeyWithSF`: Key donkey example

### Cross-Linguistic
- `CrossLinguisticExample`: Parallel data from other languages
- `spanish_sf`, `italian_congiuntivo`: Romance parallels

### Theoretical Predictions
- `MendesPrediction`: Testable predictions
- `prediction_*`: Four key predictions from Mendes' analysis

### Connection to Theory Files
- `Theories/Montague/Sentence/Mood/Basic.lean`: SUBJ/IND operators
- `Theories/Montague/Sentence/Tense/Basic.lean`: PAST/PRES/FUT operators
- `Theories/DynamicSemantics/IntensionalCDRT/Situations.lean`: Dynamic implementation
-/

end Phenomena.SubordinateFuture
