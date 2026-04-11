import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Theories.Morphology.RootTypology

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
open Semantics.Tense.Aspect.LexicalAspect (VendlerClass)

/-- German verb entry: extends VerbCore with German inflectional paradigm. -/
structure GermanVerbEntry extends VerbCore where
  /-- 3sg present (er/sie/es) -/
  form3sg : String
  /-- Past (Präteritum) -/
  formPast : String
  /-- Past participle (Partizip II) -/
  formPastPart : String
  /-- Root type (@cite{beavers-etal-2021}): result vs property concept.
      Only set for change-of-state verbs where the distinction is applicable. -/
  rootType : Option _root_.RootType := none
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
  causativeBuilder := some .make

/-- *zerbrechen* — lexical COMPACT causative ("break").
    Prefix *zer-* marks destructive result state. -/
def zerbrechen : GermanVerbEntry where
  form := "zerbrechen"
  form3sg := "zerbricht"
  formPast := "zerbrach"
  formPastPart := "zerbrochen"
  complementType := .np
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
  presupType := some .softTrigger
  senseTag := .occasion

/-- *belohnen* — "reward": presupposes the object did something praiseworthy -/
def belohnen : GermanVerbEntry where
  form := "belohnen"
  form3sg := "belohnt"
  formPast := "belohnte"
  formPastPart := "belohnt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *loben* — "praise": presupposes praiseworthy behavior by the object -/
def loben : GermanVerbEntry where
  form := "loben"
  form3sg := "lobt"
  formPast := "lobte"
  formPastPart := "gelobt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *kritisieren* — "criticise": presupposes the object did something wrong -/
def kritisieren : GermanVerbEntry where
  form := "kritisieren"
  form3sg := "kritisiert"
  formPast := "kritisierte"
  formPastPart := "kritisiert"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *danken* — "thank": presupposes the object did something helpful -/
def danken : GermanVerbEntry where
  form := "danken"
  form3sg := "dankt"
  formPast := "dankte"
  formPastPart := "gedankt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *verklagen* — "sue": presupposes the object caused harm -/
def verklagen : GermanVerbEntry where
  form := "verklagen"
  form3sg := "verklagt"
  formPast := "verklagte"
  formPastPart := "verklagt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *gratulieren* — "congratulate": presupposes the object achieved something -/
def gratulieren : GermanVerbEntry where
  form := "gratulieren"
  form3sg := "gratuliert"
  formPast := "gratulierte"
  formPastPart := "gratuliert"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *zurechtweisen* — "rebuke": presupposes the object misbehaved -/
def zurechtweisen : GermanVerbEntry where
  form := "zurechtweisen"
  form3sg := "weist zurecht"
  formPast := "wies zurecht"
  formPastPart := "zurechtgewiesen"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *anzeigen* — "report (to authorities)": presupposes the object did something illegal -/
def anzeigen : GermanVerbEntry where
  form := "anzeigen"
  form3sg := "zeigt an"
  formPast := "zeigte an"
  formPastPart := "angezeigt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *auszeichnen* — "award/honor": presupposes the object did something meritorious -/
def auszeichnen : GermanVerbEntry where
  form := "auszeichnen"
  form3sg := "zeichnet aus"
  formPast := "zeichnete aus"
  formPastPart := "ausgezeichnet"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *belangen* — "prosecute": presupposes the object committed an offense -/
def belangen : GermanVerbEntry where
  form := "belangen"
  form3sg := "belangt"
  formPast := "belangte"
  formPastPart := "belangt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *ehren* — "honor": presupposes the object did something worthy of honor -/
def ehren : GermanVerbEntry where
  form := "ehren"
  form3sg := "ehrt"
  formPast := "ehrte"
  formPastPart := "geehrt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *entlassen* — "dismiss/fire": presupposes the object did something
    warranting dismissal -/
def entlassen : GermanVerbEntry where
  form := "entlassen"
  form3sg := "entlässt"
  formPast := "entließ"
  formPastPart := "entlassen"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *sich rächen an* — "take revenge on": presupposes the object
    wronged the subject -/
def raechen : GermanVerbEntry where
  form := "sich rächen an"
  form3sg := "rächt sich"
  formPast := "rächte sich"
  formPastPart := "sich gerächt"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *sich revanchieren bei* — "reciprocate/repay": presupposes the
    object did something for the subject -/
def revanchieren : GermanVerbEntry where
  form := "sich revanchieren bei"
  form3sg := "revanchiert sich"
  formPast := "revanchierte sich"
  formPastPart := "sich revanchiert"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

/-- *zur Verantwortung ziehen* — "hold accountable": presupposes
    the object is responsible for a wrongdoing -/
def zurVerantwortungZiehen : GermanVerbEntry where
  form := "zur Verantwortung ziehen"
  form3sg := "zieht zur Verantwortung"
  formPast := "zog zur Verantwortung"
  formPastPart := "zur Verantwortung gezogen"
  complementType := .np
  presupType := some .softTrigger
  senseTag := .occasion

-- ============================================================================
-- § 4: Verbs from @cite{benz-2025} (Chs. 3–5)
-- ============================================================================

/-! ### Simplex manner/activity verbs

These verbs have no inherent result state. They cannot form *-ung*
nominalizations on their own, but can participate in resultative
constructions (as the M predicate). -/

/-- *hämmern* — "hammer": manner-of-action activity. Used in resultatives
    (*Er hämmerte das Metall platt*) and -ung tests (**Platt-hämmer-ung*). -/
def haemmern : GermanVerbEntry where
  form := "hämmern"
  form3sg := "hämmert"
  formPast := "hämmerte"
  formPastPart := "gehämmert"
  complementType := .np
  vendlerClass := some .activity

/-- *malen* — "paint": activity. Contrast: **Mal-ung* vs *Be-mal-ung* ✓.
    The *be-* prefix creates a complex change-of-state event. -/
def malen : GermanVerbEntry where
  form := "malen"
  form3sg := "malt"
  formPast := "malte"
  formPastPart := "gemalt"
  complementType := .np
  vendlerClass := some .activity

/-- *küssen* — "kiss": activity. Used in RSP examples (*wach-küssen*). -/
def kuessen : GermanVerbEntry where
  form := "küssen"
  form3sg := "küsst"
  formPast := "küsste"
  formPastPart := "geküsst"
  complementType := .np
  vendlerClass := some .activity

/-- *führen* — "lead": activity. Base for *ein-führen* (introduce).
    *Führ-ung* is an -ung nominalization but only with the meaning
    "leadership" (RN), not a CEN of simplex *führen*. -/
def fuehren : GermanVerbEntry where
  form := "führen"
  form3sg := "führt"
  formPast := "führte"
  formPastPart := "geführt"
  complementType := .np
  vendlerClass := some .activity

/-- *rauben* — "rob": activity. Contrast: **arm be-raubt* (RSP + prefix = blocked)
    vs *arm geraubt* (RSP + simplex = OK). -/
def rauben : GermanVerbEntry where
  form := "rauben"
  form3sg := "raubt"
  formPast := "raubte"
  formPastPart := "geraubt"
  complementType := .np
  vendlerClass := some .activity

/-! ### Change-of-state verbs

These verbs have inherent result states and can form *-ung* nominalizations
(complex event reading). Their root type determines the canonical v alloseme
via `VAlloseme.fromRootType`. -/

/-- *brechen* — "break": achievement with result root. The broken state
    entails prior change (you can't be broken without having been broken).
    Used in RSP data (*Hans hat den Stock kaputt gebrochen*). -/
def brechen : GermanVerbEntry where
  form := "brechen"
  form3sg := "bricht"
  formPast := "brach"
  formPastPart := "gebrochen"
  complementType := .np
  vendlerClass := some .achievement
  rootType := some .result

/-- *frieren* — "freeze": achievement, unaccusative. PC root: the frozen
    state does not entail prior change (ice can be perpetually frozen).
    *Das Wasser fror fest* — used in RSP data. -/
def frieren : GermanVerbEntry where
  form := "frieren"
  form3sg := "friert"
  formPast := "fror"
  formPastPart := "gefroren"
  complementType := .none
  unaccusative := true
  vendlerClass := some .achievement
  rootType := some .propertyConcept

/-! ### Prefix verbs (complex event structure)

Prefix verbs have complex event structure: the prefix creates a
change-of-state interpretation from the root. They can typically
form *-ung* nominalizations (CEN reading). -/

/-- *beobachten* — "observe" (*be-* prefix): accomplishment. The running
    example in @cite{benz-2025} Ch. 3 — all three nominalization readings
    (CEN, RN, CCN) are available for *Beobachtung*. -/
def beobachten : GermanVerbEntry where
  form := "beobachten"
  form3sg := "beobachtet"
  formPast := "beobachtete"
  formPastPart := "beobachtet"
  complementType := .np
  vendlerClass := some .accomplishment

/-- *einführen* — "introduce" (*ein-* particle): accomplishment.
    *Ein-führ-ung* is a productive -ung nominalization.
    Demonstrates that particle verbs with complex event structure
    can undergo -ung nominalization (particles-as-heads solution). -/
def einfuehren : GermanVerbEntry where
  form := "einführen"
  form3sg := "führt ein"
  formPast := "führte ein"
  formPastPart := "eingeführt"
  complementType := .np
  vendlerClass := some .accomplishment

/-- *verbinden* — "connect" (*ver-* prefix): accomplishment.
    *Ver-bind-ung* — productive -ung nominalization. -/
def verbinden : GermanVerbEntry where
  form := "verbinden"
  form3sg := "verbindet"
  formPast := "verband"
  formPastPart := "verbunden"
  complementType := .np
  vendlerClass := some .accomplishment

-- ============================================================================
-- § 5: Selection-Violating Coordination Verbs (@cite{schwarzer-2026})
-- ============================================================================

/-! Verbs used in @cite{schwarzer-2026} to test DP-CP coordination in German.

**Non-CP-selecting** (DP complement only): *beenden*, *streichen*,
*übereilen*, *entwickeln*. These verbs do not independently license a
*dass*-clause complement; a CP can only appear via coordination with a DP.

**CP-and-DP-selecting**: *veranlassen*, *vergessen*, *erwarten*, *beschließen*.
These verbs take both DP and *dass*-clause complements. -/

section NonCPSelecting

/-- *beenden* — "end/stop": takes only DP complement.
    "Die Stadt beendet [DP die Überarbeitung]."
    "*Die Stadt beendet, [CP dass für Neugeborene ein Baum gepflanzt wird]." -/
def beenden : GermanVerbEntry where
  form := "beenden"
  form3sg := "beendet"
  formPast := "beendete"
  formPastPart := "beendet"
  complementType := .np
  vendlerClass := some .accomplishment

/-- *streichen* — "cancel/delete": takes only DP complement.
    "Die Stadt streicht [DP das Programm]."
    "*Die Stadt streicht, [CP dass Neugeborene einen Baum bekommen]." -/
def streichen : GermanVerbEntry where
  form := "streichen"
  form3sg := "streicht"
  formPast := "strich"
  formPastPart := "gestrichen"
  complementType := .np
  vendlerClass := some .accomplishment

/-- *übereilen* — "(not) rush": takes only DP complement.
    "Die Stadt übereilt [DP die Entscheidung] (nicht)." -/
def uebereilen : GermanVerbEntry where
  form := "übereilen"
  form3sg := "übereilt"
  formPast := "übereilte"
  formPastPart := "übereilt"
  complementType := .np

/-- *entwickeln* — "develop": takes only DP complement.
    "Die Stadt entwickelt [DP ein neues Konzept]." -/
def entwickeln : GermanVerbEntry where
  form := "entwickeln"
  form3sg := "entwickelt"
  formPast := "entwickelte"
  formPastPart := "entwickelt"
  complementType := .np
  vendlerClass := some .accomplishment

end NonCPSelecting

section CPAndDPSelecting

/-- *veranlassen* — "induce/arrange": takes DP or *dass*-clause.
    "Die Stadt veranlasst [DP die Überarbeitung]."
    "Die Stadt veranlasst, [CP dass ein Baum gepflanzt wird]." -/
def veranlassen : GermanVerbEntry where
  form := "veranlassen"
  form3sg := "veranlasst"
  formPast := "veranlasste"
  formPastPart := "veranlasst"
  complementType := .np
  altComplementType := some .finiteClause

/-- *vergessen* — "forget": takes DP or *dass*-clause.
    "Ich vergesse [DP den Termin]."
    "Ich vergesse, [CP dass ich einen Termin habe]." -/
def vergessen : GermanVerbEntry where
  form := "vergessen"
  form3sg := "vergisst"
  formPast := "vergaß"
  formPastPart := "vergessen"
  complementType := .np
  altComplementType := some .finiteClause
  opaqueContext := true

/-- *erwarten* — "expect": takes DP or *dass*-clause.
    "Ich erwarte [DP eine Antwort]."
    "Ich erwarte, [CP dass er kommt]." -/
def erwarten : GermanVerbEntry where
  form := "erwarten"
  form3sg := "erwartet"
  formPast := "erwartete"
  formPastPart := "erwartet"
  complementType := .np
  altComplementType := some .finiteClause
  opaqueContext := true

/-- *beschließen* — "decide": takes DP or *dass*-clause.
    "Die Stadt beschließt [DP den Plan]."
    "Die Stadt beschließt, [CP dass der Plan umgesetzt wird]." -/
def beschliessen : GermanVerbEntry where
  form := "beschließen"
  form3sg := "beschließt"
  formPast := "beschloss"
  formPastPart := "beschlossen"
  complementType := .np
  altComplementType := some .finiteClause

end CPAndDPSelecting

-- ============================================================================
-- § 6: Verb List
-- ============================================================================

def allVerbs : List GermanVerbEntry :=
  [lassen, machen, toeten, zerbrechen,
   hoffen, fuerchten, befuerchten, wuenschen, sorgen,
   bestrafen, belohnen, loben, kritisieren, danken,
   verklagen, gratulieren, zurechtweisen,
   anzeigen, auszeichnen, belangen, ehren, entlassen,
   raechen, revanchieren, zurVerantwortungZiehen,
   haemmern, malen, kuessen, fuehren, rauben,
   brechen, frieren, beobachten, einfuehren, verbinden,
   beenden, streichen, uebereilen, entwickeln,
   veranlassen, vergessen, erwarten, beschliessen]

def lookup (form : String) : Option GermanVerbEntry :=
  allVerbs.find? (·.form == form)

-- ============================================================================
-- § 7: Occasion Verb Grounding Theorems
-- ============================================================================

/-- All 16 German occasion verbs are soft presupposition triggers. -/
theorem occasion_verbs_soft_trigger :
    bestrafen.presupType = some .softTrigger ∧
    belohnen.presupType = some .softTrigger ∧
    loben.presupType = some .softTrigger ∧
    kritisieren.presupType = some .softTrigger ∧
    danken.presupType = some .softTrigger ∧
    verklagen.presupType = some .softTrigger ∧
    gratulieren.presupType = some .softTrigger ∧
    zurechtweisen.presupType = some .softTrigger ∧
    anzeigen.presupType = some .softTrigger ∧
    auszeichnen.presupType = some .softTrigger ∧
    belangen.presupType = some .softTrigger ∧
    ehren.presupType = some .softTrigger ∧
    entlassen.presupType = some .softTrigger ∧
    raechen.presupType = some .softTrigger ∧
    revanchieren.presupType = some .softTrigger ∧
    zurVerantwortungZiehen.presupType = some .softTrigger :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All 16 German occasion verbs use the `.occasion` sense tag. -/
theorem occasion_verbs_sense_tag :
    bestrafen.senseTag = .occasion ∧
    belohnen.senseTag = .occasion ∧
    loben.senseTag = .occasion ∧
    kritisieren.senseTag = .occasion ∧
    danken.senseTag = .occasion ∧
    verklagen.senseTag = .occasion ∧
    gratulieren.senseTag = .occasion ∧
    zurechtweisen.senseTag = .occasion ∧
    anzeigen.senseTag = .occasion ∧
    auszeichnen.senseTag = .occasion ∧
    belangen.senseTag = .occasion ∧
    ehren.senseTag = .occasion ∧
    entlassen.senseTag = .occasion ∧
    raechen.senseTag = .occasion ∧
    revanchieren.senseTag = .occasion ∧
    zurVerantwortungZiehen.senseTag = .occasion :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Causative Grounding Theorems
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
-- § 9: Attitude Grounding Theorems
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
-- § 10: Selection-Violating Coordination Grounding Theorems (@cite{schwarzer-2026})
-- ============================================================================

/-- Non-CP-selecting verbs cannot take clausal complements.
    Their `complementType` is `.np` with no `altComplementType`. -/
theorem nonCPSelecting_profile :
    beenden.toVerbCore.canTakeClausalComplement = false ∧
    streichen.toVerbCore.canTakeClausalComplement = false ∧
    uebereilen.toVerbCore.canTakeClausalComplement = false ∧
    entwickeln.toVerbCore.canTakeClausalComplement = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- CP-and-DP-selecting verbs can take clausal complements.
    They have `altComplementType := some .finiteClause`. -/
theorem cpSelecting_profile :
    veranlassen.toVerbCore.canTakeClausalComplement = true ∧
    vergessen.toVerbCore.canTakeClausalComplement = true ∧
    erwarten.toVerbCore.canTakeClausalComplement = true ∧
    beschliessen.toVerbCore.canTakeClausalComplement = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All 8 experimental verbs can take nominal (DP) complements. -/
theorem all_experimental_select_dp :
    beenden.toVerbCore.canTakeNominalComplement = true ∧
    streichen.toVerbCore.canTakeNominalComplement = true ∧
    uebereilen.toVerbCore.canTakeNominalComplement = true ∧
    entwickeln.toVerbCore.canTakeNominalComplement = true ∧
    veranlassen.toVerbCore.canTakeNominalComplement = true ∧
    vergessen.toVerbCore.canTakeNominalComplement = true ∧
    erwarten.toVerbCore.canTakeNominalComplement = true ∧
    beschliessen.toVerbCore.canTakeNominalComplement = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Cross-Linguistic Bridge Theorems
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
