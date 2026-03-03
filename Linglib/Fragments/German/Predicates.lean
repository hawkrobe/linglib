import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# German Predicate Lexicon Fragment
@cite{qing-uegaki-2025} @cite{song-1996} @cite{solstad-bott-2024}

German causative and attitude verb entries, extending `VerbCore` with the
German inflectional paradigm (3sg present, Präteritum, Partizip II).

## Causative verbs

German has both analytic and lexical causatives:
- *lassen* — permissive COMPACT causative (like French *laisser*)
- *machen* — productive analytic causative ("make")
- *töten*, *zerbrechen* — lexical COMPACT causatives

## Attitude verbs

German preferential attitudes pattern with other Indo-European languages:
- *hoffen* / *wünschen* — Class 3 (positive, C-distributive, anti-rogative)
- *fürchten* / *befürchten* — Class 2 (negative, C-distributive, takes questions)
- *sich sorgen* — Class 1 (uncertainty-based, non-C-distributive)

-/

namespace Fragments.German.Predicates

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)

/-- German verb entry: extends VerbCore with German inflectional paradigm. -/
structure GermanVerbEntry extends VerbCore where
  /-- 3sg present (er/sie/es) -/
  form3sg : String
  /-- Past (Präteritum) -/
  formPast : String
  /-- Past participle (Partizip II) -/
  formPastPart : String
  deriving Repr, BEq

-- ============================================================================
-- § 1: Causative Verbs
-- ============================================================================

/-- *lassen* — COMPACT permissive causative (like French *laisser*).
    "Sie ließ ihn gehen" = "She let him go." -/
def lassen : GermanVerbEntry where
  form := "lassen"
  form3sg := "lässt"
  formPast := "ließ"
  formPastPart := "gelassen"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .enable

/-- *machen* — productive analytic causative.
    "Das macht mich traurig" = "That makes me sad." -/
def machen : GermanVerbEntry where
  form := "machen"
  form3sg := "macht"
  formPast := "machte"
  formPastPart := "gemacht"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make

/-- *töten* — lexical COMPACT causative ("kill" = tot + -en).
    Deadjectival causative: *tot* "dead" → *töten* "make dead". -/
def toeten : GermanVerbEntry where
  form := "töten"
  form3sg := "tötet"
  formPast := "tötete"
  formPastPart := "getötet"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  causativeBuilder := some .make

/-- *zerbrechen* — lexical COMPACT causative ("break").
    Prefix *zer-* marks destructive result state. -/
def zerbrechen : GermanVerbEntry where
  form := "zerbrechen"
  form3sg := "zerbricht"
  formPast := "zerbrach"
  formPastPart := "zerbrochen"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  causativeBuilder := some .make

-- ============================================================================
-- § 2: Attitude Verbs (@cite{qing-uegaki-2025})
-- ============================================================================

/-- *hoffen* — "hope" (Class 3: positive, C-distributive, anti-rogative). -/
def hoffen : GermanVerbEntry where
  form := "hoffen"
  form3sg := "hofft"
  formPast := "hoffte"
  formPastPart := "gehofft"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- *fürchten* — "fear" (Class 2: negative, C-distributive, takes questions). -/
def fuerchten : GermanVerbEntry where
  form := "fürchten"
  form3sg := "fürchtet"
  formPast := "fürchtete"
  formPastPart := "gefürchtet"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- *befürchten* — "be afraid / apprehend" (Class 2: negative, C-distributive). -/
def befuerchten : GermanVerbEntry where
  form := "befürchten"
  form3sg := "befürchtet"
  formPast := "befürchtete"
  formPastPart := "befürchtet"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- *wünschen* — "wish" (Class 3: positive, C-distributive, anti-rogative). -/
def wuenschen : GermanVerbEntry where
  form := "wünschen"
  form3sg := "wünscht"
  formPast := "wünschte"
  formPastPart := "gewünscht"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- *sich sorgen* — "worry" (Class 1: uncertainty-based, non-C-distributive). -/
def sorgen : GermanVerbEntry where
  form := "sich sorgen"
  form3sg := "sorgt sich"
  formPast := "sorgte sich"
  formPastPart := "sich gesorgt"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

-- ============================================================================
-- § 3: Occasion Verbs (@cite{solstad-bott-2024}, S&P 17:11)
-- ============================================================================

/-! German interpersonal occasion verbs presuppose a prior occasioning
    eventuality. The subject performs an
    interpersonal action triggered by the object's prior behavior.

    These verbs were tested for projectivity in Experiments 1–3 of the
    S&P paper and for IC bias (as "agent-evocator" verbs) in @cite{solstad-bott-2022}. -/

/-- *bestrafen* — "punish": presupposes the object did something wrong -/
def bestrafen : GermanVerbEntry where
  form := "bestrafen"
  form3sg := "bestraft"
  formPast := "bestrafte"
  formPastPart := "bestraft"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *belohnen* — "reward": presupposes the object did something praiseworthy -/
def belohnen : GermanVerbEntry where
  form := "belohnen"
  form3sg := "belohnt"
  formPast := "belohnte"
  formPastPart := "belohnt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *loben* — "praise": presupposes praiseworthy behavior by the object -/
def loben : GermanVerbEntry where
  form := "loben"
  form3sg := "lobt"
  formPast := "lobte"
  formPastPart := "gelobt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *kritisieren* — "criticise": presupposes the object did something wrong -/
def kritisieren : GermanVerbEntry where
  form := "kritisieren"
  form3sg := "kritisiert"
  formPast := "kritisierte"
  formPastPart := "kritisiert"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *danken* — "thank": presupposes the object did something helpful -/
def danken : GermanVerbEntry where
  form := "danken"
  form3sg := "dankt"
  formPast := "dankte"
  formPastPart := "gedankt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .experiencer
  presupType := some .softTrigger
  senseTag := .occasion

/-- *verklagen* — "sue": presupposes the object caused harm -/
def verklagen : GermanVerbEntry where
  form := "verklagen"
  form3sg := "verklagt"
  formPast := "verklagte"
  formPastPart := "verklagt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *gratulieren* — "congratulate": presupposes the object achieved something -/
def gratulieren : GermanVerbEntry where
  form := "gratulieren"
  form3sg := "gratuliert"
  formPast := "gratulierte"
  formPastPart := "gratuliert"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

/-- *zurechtweisen* — "rebuke": presupposes the object misbehaved -/
def zurechtweisen : GermanVerbEntry where
  form := "zurechtweisen"
  form3sg := "weist zurecht"
  formPast := "wies zurecht"
  formPastPart := "zurechtgewiesen"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  presupType := some .softTrigger
  senseTag := .occasion

-- ============================================================================
-- § 4: Verb List
-- ============================================================================

def allVerbs : List GermanVerbEntry :=
  [lassen, machen, toeten, zerbrechen,
   hoffen, fuerchten, befuerchten, wuenschen, sorgen,
   bestrafen, belohnen, loben, kritisieren, danken,
   verklagen, gratulieren, zurechtweisen]

def lookup (form : String) : Option GermanVerbEntry :=
  allVerbs.find? (·.form == form)

-- ============================================================================
-- § 5: Occasion Verb Grounding Theorems
-- ============================================================================

/-- All 8 German occasion verbs are soft presupposition triggers. -/
theorem occasion_verbs_soft_trigger :
    bestrafen.presupType = some .softTrigger ∧
    belohnen.presupType = some .softTrigger ∧
    loben.presupType = some .softTrigger ∧
    kritisieren.presupType = some .softTrigger ∧
    danken.presupType = some .softTrigger ∧
    verklagen.presupType = some .softTrigger ∧
    gratulieren.presupType = some .softTrigger ∧
    zurechtweisen.presupType = some .softTrigger :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All German occasion verbs use the `.occasion` sense tag. -/
theorem occasion_verbs_sense_tag :
    bestrafen.senseTag = .occasion ∧
    belohnen.senseTag = .occasion ∧
    loben.senseTag = .occasion ∧
    kritisieren.senseTag = .occasion := ⟨rfl, rfl, rfl, rfl⟩

/-- German occasion verbs have agent subjects (unlike English semi-modal
    occasion verbs which have experiencer subjects). These are interpersonal
    action verbs, not implicative/semi-modal verbs. -/
theorem occasion_verbs_agent_subject :
    bestrafen.subjectTheta = some .agent ∧
    belohnen.subjectTheta = some .agent ∧
    kritisieren.subjectTheta = some .agent := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Causative Grounding Theorems
-- ============================================================================

/-- *lassen* uses `.enable` builder (permissive). -/
theorem lassen_is_enable :
    lassen.causativeBuilder = some .enable := rfl

/-- *machen* uses `.make` builder. -/
theorem machen_is_make :
    machen.causativeBuilder = some .make := rfl

/-- *lassen* and *machen* have different builders. -/
theorem lassen_machen_different :
    lassen.causativeBuilder ≠ machen.causativeBuilder := by decide

/-- Lexical causatives (*töten*, *zerbrechen*) use `.make`. -/
theorem lexical_causatives_use_make :
    toeten.causativeBuilder = some .make ∧
    zerbrechen.causativeBuilder = some .make := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Attitude Grounding Theorems
-- ============================================================================

/-- *hoffen* and *wünschen* are positive preferential (Class 3). -/
theorem hoffen_is_positive :
    hoffen.attitudeBuilder = some (.preferential (.degreeComparison .positive)) ∧
    wuenschen.attitudeBuilder = some (.preferential (.degreeComparison .positive)) :=
  ⟨rfl, rfl⟩

/-- *fürchten* and *befürchten* are negative preferential (Class 2). -/
theorem fuerchten_is_negative :
    fuerchten.attitudeBuilder = some (.preferential (.degreeComparison .negative)) ∧
    befuerchten.attitudeBuilder = some (.preferential (.degreeComparison .negative)) :=
  ⟨rfl, rfl⟩

/-- *sich sorgen* is uncertainty-based (Class 1). -/
theorem sorgen_is_uncertainty :
    sorgen.attitudeBuilder = some (.preferential .uncertaintyBased) := rfl

-- ============================================================================
-- § 8: Cross-Linguistic Bridge Theorems
-- ============================================================================

/-- German *fürchten* matches Japanese 恐れ *osore* and Turkish *kork-*:
    all are Class 2 negative preferential (degreeComparison.negative). -/
theorem fuerchten_matches_crosslinguistic :
    fuerchten.attitudeBuilder =
      some (.preferential (.degreeComparison .negative)) := rfl

/-- German *sich sorgen* matches Japanese 心配 *shinpai* and Turkish *endişelen-*:
    all are Class 1 uncertainty-based. -/
theorem sorgen_matches_crosslinguistic :
    sorgen.attitudeBuilder = some (.preferential .uncertaintyBased) := rfl

/-- German *lassen* matches French *laisser*: both use `.enable` (permissive). -/
theorem lassen_matches_french_laisser :
    lassen.causativeBuilder = some .enable := rfl

end Fragments.German.Predicates
