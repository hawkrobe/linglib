import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F70A
import Linglib.Core.WALS.Features.F71A
import Linglib.Core.WALS.Features.F72A
import Linglib.Core.WALS.Features.F73A

/-!
# Cross-Linguistic Typology of Imperatives (WALS Chapters 70--73)
@cite{van-der-auwera-lejeune-2013}

Cross-linguistic data on imperative and related mood systems from four WALS
chapters, all authored by Johan van der Auwera and Ludo @cite{van-der-auwera-lejeune-2013}.

## Ch 70: The Morphological Imperative

Whether a language has a dedicated morphological form for second-person
imperatives. Five values distinguishing number marking in the imperative
paradigm: (1) second singular and second plural, (2) second singular only,
(3) second plural only, (4) second person number-neutral, (5) no
second-person imperatives.

Sample: 548 languages. The vast majority (426/548 = 77.7%) have a
dedicated morphological imperative of some kind; only 122 lack one entirely.

## Ch 71: The Prohibitive

How negative imperatives ("Don't!") are formed relative to regular
imperatives and regular negation. Four structural types based on whether
the imperative construction and the negation strategy are the *same* as
in declaratives or *special*:

- Type 1: normal imperative + normal negation (e.g., Korean)
- Type 2: normal imperative + special negation (e.g., Ancient Greek)
- Type 3: special imperative + normal negation (e.g., Italian)
- Type 4: special imperative + special negation (e.g., Sinhala)

Sample: 496 languages. Type 2 (normal imperative + special negation) is
the most common (182/496 = 36.7%).

## Ch 72: Imperative-Hortative Systems

Whether the language has dedicated morphological forms for first-person
hortatives ("let's go") and/or third-person jussives ("let him go"), in
addition to the second-person imperative. Four values: imperative only,
imperative + hortative, imperative + jussive, or all three.

Sample: 375 languages. Neither-type-of-system is the most common
(201/375 = 53.6%); both-types-of-system is the least common
(21/375 = 5.6%).

## Ch 73: The Optative

Whether the language has a morphologically dedicated optative construction
("may it rain", "if only she were here"). Binary feature: present or absent.

Sample: 319 languages. Optatives are a minority feature: only 48/319
(15.0%) of sampled languages have a dedicated optative.

-/

namespace Phenomena.Directives.Typology

-- ============================================================================
-- Chapter 70: The Morphological Imperative
-- ============================================================================

/-- WALS Ch 70: Whether a language has a dedicated morphological imperative.

    Three categories based on the person distinctions available in the
    morphological imperative paradigm:
    (1) Second-person only: a dedicated imperative form exists only for 2nd
        person (singular and/or plural).
    (2) Second and other persons: the imperative paradigm extends beyond 2nd
        person to include 1st and/or 3rd person forms.
    (3) No morphological imperative: the language lacks a dedicated
        morphological imperative form; commands are expressed via bare stems,
        indicative forms, word order, particles, or intonation alone. -/
inductive MorphImpType where
  /-- Dedicated morphological imperative for second person only.
      (e.g., English `Go!`, Turkish `Gel!` 'Come!').
      The most common pattern worldwide (426/548 = 77.7% have some
      morphological imperative; of those, second-person-only forms dominate). -/
  | secondOnly
  /-- Morphological imperative for second person and other persons
      (1st inclusive "let's", 3rd jussive, etc. are also morphologically
      imperative). (e.g., Latin `i` '2SG.IMP', `eamus` '1PL.IMP.SUBJ',
      Georgian, Quechua). -/
  | secondAndOther
  /-- No dedicated morphological imperative: commands use bare verb stems,
      indicative forms, particles, or intonation.
      (e.g., Mandarin Chinese, Thai, many isolating languages). -/
  | noMorphological
  deriving DecidableEq, Repr

-- ============================================================================
-- Chapter 71: The Prohibitive
-- ============================================================================

/-- WALS Ch 71: How prohibitives (negative imperatives, "Don't!") are formed.

    The classification cross-tabulates two binary features:
    - Is the imperative construction the SAME as the affirmative imperative
      or SPECIAL (a different form)?
    - Is the negation strategy the SAME as in declaratives or SPECIAL?

    This yields four structural types. The key typological finding is that
    Type 1 (normal+normal) is surprisingly uncommon — languages tend to
    treat prohibitives differently from simple negation of an imperative. -/
inductive ProhibitiveType where
  /-- Type 1: Normal imperative + normal negation.
      The prohibitive is simply the imperative plus regular sentential
      negation. (e.g., Korean `ka-la` 'go-IMP' → `ka-ci mal-la`
      'go-NMLZ NEG-IMP'; Hungarian `menj!` → `ne menj!`). -/
  | normalImpNormalNeg
  /-- Type 2: Normal imperative + special negation.
      The imperative verb form is retained, but the negation marker is
      different from the one used in declaratives.
      (e.g., Ancient Greek: indicative `ou` vs imperative `me`;
      Tagalog: declarative `hindi` vs imperative `huwag`). -/
  | normalImpSpecialNeg
  /-- Type 3: Special imperative + normal negation.
      The negation strategy is the same as in declaratives, but the verb
      appears in a different form (e.g., subjunctive, infinitive, or a
      special negative imperative stem).
      (e.g., Italian `va!` IMP → `non andare!` NEG+INF;
      Finnish `mene!` IMP → `ala mene` NEG.AUX go.CONNEG). -/
  | specialImpNormalNeg
  /-- Type 4: Special imperative + special negation.
      Both the verb form and the negation marker differ from the
      declarative and the affirmative imperative.
      (e.g., Sinhala; many Austronesian and African languages). -/
  | specialImpSpecialNeg
  deriving DecidableEq, Repr

-- ============================================================================
-- Chapter 72: Imperative-Hortative Systems
-- ============================================================================

/-- WALS Ch 72: Whether the language has morphological hortative (1st person
    command: "let's go") and/or jussive (3rd person command: "let him go")
    in addition to the basic second-person imperative.

    Four system types based on paradigm richness:
    - Imperative only: only 2nd person morphological commands
    - Imperative + hortative: 1st and 2nd person
    - Imperative + jussive: 2nd and 3rd person
    - All three: 1st, 2nd, and 3rd person -/
inductive ImpHortSystem where
  /-- Imperative only: the language has a morphological imperative (2nd person)
      but no dedicated hortative or jussive forms.
      (e.g., English `Go!` — "let's go" uses a periphrastic construction,
      not a morphological hortative). -/
  | imperativeOnly
  /-- Imperative + hortative: the language has morphological forms for both
      2nd person commands and 1st person (inclusive) hortatives ("let's").
      (e.g., Turkish `gel!` 'come.IMP.2SG', `gelelim` 'come.HORT.1PL'). -/
  | imperativeAndHortative
  /-- Imperative + jussive: the language has morphological forms for both
      2nd person commands and 3rd person jussives ("let him/them").
      (e.g., Hindi-Urdu `jao` 'go.IMP.2PL', `jaae` 'go.JUSS.3SG'). -/
  | imperativeAndJussive
  /-- All three: the language has dedicated morphological forms for
      2nd person imperatives, 1st person hortatives, and 3rd person jussives.
      (e.g., Latin `i` 'go.IMP.2SG', `eamus` 'go.SUBJ.1PL',
      `eat` 'go.SUBJ.3SG'; Georgian; Quechua). -/
  | allThree
  deriving DecidableEq, Repr

-- ============================================================================
-- Chapter 73: The Optative
-- ============================================================================

/-- WALS Ch 73: Whether the language has a morphologically dedicated optative.

    An optative is a mood expressing wishes or hopes ("may it rain",
    "if only she were here", "long live the king"). The key criterion is
    whether the optative is morphologically distinct — languages that express
    wishes only via particles, intonation, or subjunctive forms shared with
    other functions are classified as lacking a dedicated optative. -/
inductive OptativePresence where
  /-- The language has a morphologically dedicated optative.
      (e.g., Ancient Greek `-oimi` / `-oihn`, Turkish `-sA`,
      Georgian, Finnish conditional used optatively). -/
  | present
  /-- The language lacks a dedicated morphological optative.
      Wishes are expressed by other means (subjunctive, particles,
      conditional, or periphrasis).
      (e.g., English, Mandarin Chinese, Japanese). -/
  | absent
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Distribution Data (Aggregate Counts)
-- ============================================================================

/-- A single row in a WALS frequency table: a category label and its count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

private abbrev f70 := Core.WALS.F70A.allData
private abbrev f71 := Core.WALS.F71A.allData
private abbrev f72 := Core.WALS.F72A.allData
private abbrev f73 := Core.WALS.F73A.allData

/-- Chapter 70 distribution: morphological imperative types (N = 548). -/
def ch70Counts : List WALSCount :=
  [ ⟨"Second singular and second plural",
      (f70.filter (·.value == .secondSingularAndSecondPlural)).length⟩
  , ⟨"Second singular",
      (f70.filter (·.value == .secondSingular)).length⟩
  , ⟨"Second plural",
      (f70.filter (·.value == .secondPlural)).length⟩
  , ⟨"Second person number-neutral",
      (f70.filter (·.value == .secondPersonNumberNeutral)).length⟩
  , ⟨"No second-person imperatives",
      (f70.filter (·.value == .noSecondPersonImperatives)).length⟩ ]

/-- Chapter 71 distribution: prohibitive types (N = 496). -/
def ch71Counts : List WALSCount :=
  [ ⟨"Normal imperative + normal negation",
      (f71.filter (·.value == .normalImperativeNormalNegative)).length⟩
  , ⟨"Normal imperative + special negation",
      (f71.filter (·.value == .normalImperativeSpecialNegative)).length⟩
  , ⟨"Special imperative + normal negation",
      (f71.filter (·.value == .specialImperativeNormalNegative)).length⟩
  , ⟨"Special imperative + special negation",
      (f71.filter (·.value == .specialImperativeSpecialNegative)).length⟩ ]

/-- Chapter 72 distribution: imperative-hortative systems (N = 375). -/
def ch72Counts : List WALSCount :=
  [ ⟨"Maximal system",
      (f72.filter (·.value == .maximalSystem)).length⟩
  , ⟨"Minimal system",
      (f72.filter (·.value == .minimalSystem)).length⟩
  , ⟨"Both types of system",
      (f72.filter (·.value == .bothTypesOfSystem)).length⟩
  , ⟨"Neither type of system",
      (f72.filter (·.value == .neitherTypeOfSystem)).length⟩ ]

/-- Chapter 73 distribution: optative presence (N = 319). -/
def ch73Counts : List WALSCount :=
  [ ⟨"Inflectional optative present",
      (f73.filter (·.value == .present)).length⟩
  , ⟨"Inflectional optative absent",
      (f73.filter (·.value == .absent)).length⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Ch 70 total: 548 languages. -/
theorem ch70_total : WALSCount.totalOf ch70Counts = 548 := by native_decide

/-- Ch 71 total: 496 languages. -/
theorem ch71_total : WALSCount.totalOf ch71Counts = 496 := by native_decide

/-- Ch 72 total: 375 languages. -/
theorem ch72_total : WALSCount.totalOf ch72Counts = 375 := by native_decide

/-- Ch 73 total: 319 languages. -/
theorem ch73_total : WALSCount.totalOf ch73Counts = 319 := by native_decide

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's imperative system profile across WALS Chapters 70--73. -/
structure ImperativeProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 70: Morphological imperative type. -/
  morphImp : MorphImpType
  /-- Ch 71: Prohibitive construction type. -/
  prohibitive : ProhibitiveType
  /-- Ch 72: Imperative-hortative system. -/
  impHortSystem : ImpHortSystem
  /-- Ch 73: Optative presence (none if language not in Ch 73 sample). -/
  optative : Option OptativePresence := none
  /-- Illustrative imperative form(s). -/
  impForms : List String := []
  /-- Notes on the imperative system. -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

section LanguageData

/--
English: second-person-only morphological imperative (`Go!`, `Be quiet!`).
The imperative is typically the bare stem, identical to the infinitive but
distinguished from declaratives by the absence of a subject and do-support.
Prohibitives use the regular negation strategy with do-support:
`Don't go!` — normal imperative with normal negation (Type 1).
No dedicated hortative (*`Go-we!`); periphrastic `Let's go` instead.
No morphological optative; wishes expressed by `may` or subjunctive relics
(`Long live the king`).
-/
def english : ImperativeProfile :=
  { language := "English"
  , iso := "eng"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Go!", "Don't go!"]
  , notes := "Bare-stem imperative; periphrastic 'let's' for hortative; " ++
             "do-support in prohibitives: Don't go!" }

/--
Japanese: second-person-only morphological imperative. The plain imperative
suffix `-e` / `-ro` is used for 2nd person commands (`ike!` 'go!',
`tabero!` 'eat!'). Prohibitives use the negative form `-na` which is
a special negation marker distinct from the declarative `-nai`:
`iku-na!` 'go-PROH' — normal imperative stem + special negation (Type 2).
No dedicated hortative morphology; volitional `-ou` / `-you` serves a related
but distinct function. No morphological optative.
-/
def japanese : ImperativeProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , morphImp := .secondOnly
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["ike!", "iku-na!"]
  , notes := "Plain imperative -e/-ro; prohibitive -na is special negation; " ++
             "volitional -ou / -you is distinct from hortative" }

/--
Mandarin Chinese: no morphological imperative. Commands are expressed by
bare verb forms, intonation, and sentence-final particles (`ba`, `a`).
`Zou!` 'Go!' is identical to the declarative verb form. Prohibitives use
the special negative particle `bie` (别) rather than the declarative `bu`
or `mei`: `bie zou!` 'PROH go' — no morphological imperative + special
negation (closest to Type 2, but no morphological imperative at all).
No hortative or jussive morphology. No optative.
-/
def mandarin : ImperativeProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphImp := .noMorphological
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Zou!", "Bie zou!"]
  , notes := "No morphological imperative; bare verb + intonation/particles; " ++
             "special prohibitive particle bie (别) vs declarative bu/mei" }

/--
Turkish: second-person and other-person morphological imperative. Turkish
has a full imperative paradigm: 2SG `gel` (bare stem), 2PL `gelin`,
3SG `gelsin`, 3PL `gelsinler`, and 1PL hortative `gelelim`. Prohibitives
use the regular negative suffix `-mA-` with the imperative:
`gelme!` 'come-NEG.IMP' — normal imperative + normal negation (Type 1).
Has both hortative and jussive morphology (all three). Optative expressed
by the suffix `-sA` (desiderative/conditional).
-/
def turkish : ImperativeProfile :=
  { language := "Turkish"
  , iso := "tur"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Gel!", "Gelin!", "Gelsin!", "Gelelim!", "Gelme!"]
  , notes := "Full imperative paradigm 2SG/2PL/3SG/3PL + hortative 1PL; " ++
             "optative -sA suffix; prohibitive with regular -mA- negation" }

/--
Finnish: second-person morphological imperative with dedicated forms
(`mene!` 'go.IMP.2SG', `menkaa!` 'go.IMP.2PL'). Prohibitives use the
negative auxiliary verb `ala` (imperative form of the negative verb `ei`)
followed by the connegative: `ala mene!` 'NEG.IMP go.CONNEG' — the verb
form changes from imperative to connegative (special imperative + normal
negation, Type 3). Has hortative and jussive morphology. No dedicated
optative (conditional `-isi-` serves optative functions).
-/
def finnish : ImperativeProfile :=
  { language := "Finnish"
  , iso := "fin"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["Mene!", "Menkaa!", "Ala mene!"]
  , notes := "Negative auxiliary verb has its own imperative form ala; " ++
             "connegative in prohibitive; 3SG jussive menkoon" }

/--
Russian: second-person-only morphological imperative (`idi!` 'go.IMP.2SG',
`idite!` 'go.IMP.2PL'). Prohibitives use the regular negation `ne` with
the imperative form: `ne idi!` 'NEG go.IMP' — normal imperative + normal
negation (Type 1). Periphrastic hortative `davaj(te)` + infinitive/verb.
No dedicated optative morphology.
-/
def russian : ImperativeProfile :=
  { language := "Russian"
  , iso := "rus"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Idi!", "Idite!", "Ne idi!"]
  , notes := "Imperative suffix -i/-'te; prohibitive = ne + imperative; " ++
             "periphrastic hortative davaj(te)" }

/--
Latin: full morphological imperative paradigm with forms for 2SG, 2PL, and
future imperative. Also has subjunctive forms used as hortative (1PL) and
jussive (3SG/3PL): `i!` 'go.IMP.2SG', `ite!` 'go.IMP.2PL', `eamus!`
'go.SUBJ.1PL' (hortative), `eat!` 'go.SUBJ.3SG' (jussive). Prohibitives
use the special negative `ne` (distinct from declarative `non`) with the
subjunctive: `ne eas!` 'PROH go.SUBJ.2SG' — special imperative form
(subjunctive replaces imperative) + special negation (Type 4).
No dedicated optative (wishes use subjunctive).
-/
def latin : ImperativeProfile :=
  { language := "Latin"
  , iso := "lat"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["I!", "Ite!", "Eamus!", "Ne eas!"]
  , notes := "Future imperative (2SG -to, 3SG -to); prohibitive uses " ++
             "special ne (not non) + subjunctive (not imperative)" }

/--
Hindi-Urdu: second-person and other-person morphological imperative. Three
levels of imperative politeness: intimate (`ja` 'go.IMP.2SG.INTIM'),
familiar (`jao` 'go.IMP.2PL'), and polite (`jaiye` 'go.IMP.2HON').
3SG jussive `jaae`. Prohibitives use `mat` (special negative particle
distinct from declarative `nahin`): `mat jao!` 'PROH go' — normal
imperative + special negation (Type 2). No dedicated optative.
-/
def hindiUrdu : ImperativeProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Ja!", "Jao!", "Jaiye!", "Mat jao!"]
  , notes := "Three politeness levels in imperative; prohibitive uses " ++
             "special mat (not nahin/nahi); 3SG jussive jaae" }

/--
Swahili: second-person and other-person morphological imperative. 2SG
imperative is the bare stem (`njoo!` 'come!', `soma!` 'read!'); 2PL adds
`-ni` (`njooni!`). Subjunctive forms serve as hortative/jussive:
`tu-some` '1PL-read.SUBJ' (hortative), `a-some` '3SG-read.SUBJ' (jussive).
Prohibitives use the regular negative prefix `usi-` with subjunctive:
`usi-some!` 'NEG.2SG-read.SUBJ' — special verb form + normal negation
strategy (Type 3). No dedicated optative.
-/
def swahili : ImperativeProfile :=
  { language := "Swahili"
  , iso := "swh"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .allThree
  , optative := some .absent
  , impForms := ["Njoo!", "Njooni!", "Usisome!"]
  , notes := "Bare stem 2SG imperative; subjunctive for hortative/jussive; " ++
             "prohibitive uses negative subjunctive (usi-)" }

/--
Arabic (Modern Standard): second-person and other-person morphological
imperative. 2SG.M `uktub!` 'write!', 2SG.F `uktubii!`. Jussive
(3rd person) uses the jussive mood `li-yaktub` 'let him write'.
Prohibitives use the special negative particle `laa` (distinct from
declarative `lam`/`lan`/`maa`) with the jussive verb form:
`laa taktub!` 'PROH write.JUSS' — special verb form + special negation
(Type 4). No dedicated optative.
-/
def arabic : ImperativeProfile :=
  { language := "Arabic (Modern Standard)"
  , iso := "arb"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Uktub!", "Laa taktub!", "Li-yaktub"]
  , notes := "Imperative from jussive stem with initial vowel; " ++
             "prohibitive laa + jussive (not imperative); jussive for 3rd person" }

/--
Tagalog: no morphological imperative in the strict sense; commands use
the basic verb form (infinitive/imperative neutral form). Prohibitives use
the special negative `huwag` (distinct from declarative `hindi`):
`Huwag kang pumunta!` 'PROH you go' — normal imperative + special negation
(Type 2). Periphrastic hortative with `tayo na` 'us already'. No optative.
-/
def tagalog : ImperativeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , morphImp := .noMorphological
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .imperativeOnly
  , optative := some .absent
  , impForms := ["Pumunta ka!", "Huwag kang pumunta!"]
  , notes := "Imperative = basic/infinitive verb form; special prohibitive " ++
             "huwag (not hindi); no morphological hortative" }

/--
Quechua (Cuzco): second-person and other-person morphological imperative
with a rich paradigm. 2SG `-y` (`ri-y!` 'go-IMP.2SG'), 2PL `-ychis`.
1PL hortative `-sun` (`ri-sun` 'go-HORT.1PL'), 3SG jussive `-chun`
(`ri-chun` 'go-JUSS.3SG'). Prohibitives use the regular negation `ama`
with the imperative followed by the suffix `-chu`:
`ama ri-y-chu!` 'PROH go-IMP-PROH' — this involves a special construction
(special imperative + special negation, Type 4, since both `ama` and `-chu`
are prohibitive-specific). Has a dedicated optative (desiderative) suffix.
-/
def quechua : ImperativeProfile :=
  { language := "Quechua (Cuzco)"
  , iso := "quz"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Ri-y!", "Ri-sun!", "Ri-chun!", "Ama ri-y-chu!"]
  , notes := "Rich imperative paradigm; hortative -sun; jussive -chun; " ++
             "prohibitive ama...chu is doubly special" }

/--
Georgian: second-person and other-person morphological imperative. Georgian
has a complex verbal system with imperative, optative, and conjunctive moods.
2SG `ts'eri!` 'write!'. Prohibitives use the preverb `nu-` and the
conjunctive: `nu ts'er` — special verb form + special construction (Type 4).
Has all three: imperative, hortative (1PL), and jussive (3SG).
Morphologically dedicated optative mood exists.
-/
def georgian : ImperativeProfile :=
  { language := "Georgian"
  , iso := "kat"
  , morphImp := .secondAndOther
  , prohibitive := .specialImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Ts'ere!", "Nu ts'er!"]
  , notes := "Complex verbal morphology with multiple mood series; " ++
             "dedicated optative mood; prohibitive uses conjunctive" }

/--
Hungarian: second-person-only morphological imperative. 2SG `menj!` 'go!',
2PL `menjetek!`. Prohibitives use the regular negation `ne` with the
imperative/subjunctive form: `ne menj!` 'NEG go.IMP' — normal imperative +
normal negation (Type 1). Subjunctive serves as jussive for 3rd person.
No dedicated optative.
-/
def hungarian : ImperativeProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Menj!", "Menjetek!", "Ne menj!"]
  , notes := "Imperative/subjunctive paradigm; prohibitive = ne + " ++
             "imperative; subjunctive used for 3SG/3PL jussive" }

/--
Korean: second-person morphological imperative with speech-level distinctions.
Imperative endings vary by politeness: `-a/eo` (plain), `-seyo` (polite),
`-(eu)sipsiyo` (formal). Prohibitives use regular negation `-ji ma-` with
the imperative: `ga-ji ma!` 'go-NMLZ NEG.IMP' — the structure involves
the same imperative construction and the verbal negation pattern with `mal-`
(normal imperative + normal negation, Type 1). Hortative `-ja` for
1PL. No dedicated optative.
-/
def korean : ImperativeProfile :=
  { language := "Korean"
  , iso := "kor"
  , morphImp := .secondOnly
  , prohibitive := .normalImpNormalNeg
  , impHortSystem := .imperativeAndHortative
  , optative := some .absent
  , impForms := ["Ga!", "Gaseyo!", "Gaji ma!"]
  , notes := "Multiple speech levels for imperative; hortative -ja; " ++
             "prohibitive -ji mal- retains imperative construction" }

/--
Italian: second-person morphological imperative. 2SG `va'!` 'go!',
2PL `andate!`. Prohibitives use the regular negation `non` but with
the infinitive instead of the imperative for 2SG: `Non andare!`
'NEG go.INF' — special verb form (infinitive replaces imperative) +
normal negation (Type 3). 3SG/3PL uses subjunctive as jussive.
No dedicated optative (subjunctive covers wishes).
-/
def italian : ImperativeProfile :=
  { language := "Italian"
  , iso := "ita"
  , morphImp := .secondOnly
  , prohibitive := .specialImpNormalNeg
  , impHortSystem := .imperativeAndJussive
  , optative := some .absent
  , impForms := ["Va'!", "Andate!", "Non andare!"]
  , notes := "2SG prohibitive uses infinitive (not imperative): " ++
             "non andare, not *non va'; 2PL retains imperative: non andate" }

/--
Ancient Greek: second-person and other-person morphological imperative
with present and aorist stems. Prohibitives use the special negative `me`
(distinct from declarative `ou/ouk`) with the subjunctive (aorist) or
imperative (present): `me graphe!` 'PROH write' — normal imperative form
+ special negation (Type 2 for present imperative prohibitives).
Rich optative mood paradigm (`graphoimi` 'may I write').
-/
def ancientGreek : ImperativeProfile :=
  { language := "Ancient Greek"
  , iso := "grc"
  , morphImp := .secondAndOther
  , prohibitive := .normalImpSpecialNeg
  , impHortSystem := .allThree
  , optative := some .present
  , impForms := ["Graphe!", "Me graphe!"]
  , notes := "Present and aorist imperative stems; special prohibitive " ++
             "me (not ou); rich optative paradigm with dedicated morphology" }

end LanguageData

/-- All language profiles in the sample. -/
def allLanguages : List ImperativeProfile :=
  [ english, japanese, mandarin, turkish, finnish, russian, latin
  , hindiUrdu, swahili, arabic, tagalog, quechua, georgian, hungarian
  , korean, italian, ancientGreek ]

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language have a morphological imperative (of any type)? -/
def ImperativeProfile.hasMorphImp (p : ImperativeProfile) : Bool :=
  p.morphImp != .noMorphological

/-- Does a language have an extended imperative paradigm (beyond 2nd person)? -/
def ImperativeProfile.hasExtendedParadigm (p : ImperativeProfile) : Bool :=
  p.morphImp == .secondAndOther

/-- Does a language have a hortative (either with or without jussive)? -/
def ImperativeProfile.hasHortative (p : ImperativeProfile) : Bool :=
  p.impHortSystem == .imperativeAndHortative ||
  p.impHortSystem == .allThree

/-- Does a language have a jussive (either with or without hortative)? -/
def ImperativeProfile.hasJussive (p : ImperativeProfile) : Bool :=
  p.impHortSystem == .imperativeAndJussive ||
  p.impHortSystem == .allThree

/-- Does a language have a dedicated optative? -/
def ImperativeProfile.hasOptative (p : ImperativeProfile) : Bool :=
  p.optative == some .present

/-- Does a language use a special prohibitive construction (Type 2, 3, or 4)?
    That is, does the prohibitive differ from simply negating the imperative? -/
def ImperativeProfile.hasSpecialProhibitive (p : ImperativeProfile) : Bool :=
  p.prohibitive != .normalImpNormalNeg

/-- Count of languages with a given morphological imperative type. -/
def countByMorphImp (langs : List ImperativeProfile) (t : MorphImpType) : Nat :=
  (langs.filter (·.morphImp == t)).length

/-- Count of languages with a given prohibitive type. -/
def countByProhibitive (langs : List ImperativeProfile) (t : ProhibitiveType) : Nat :=
  (langs.filter (·.prohibitive == t)).length

/-- Count of languages with a given imperative-hortative system. -/
def countByImpHort (langs : List ImperativeProfile) (t : ImpHortSystem) : Nat :=
  (langs.filter (·.impHortSystem == t)).length

-- ============================================================================
-- Typological Generalization 1: Morphological Imperatives Are the Majority
-- ============================================================================

/-- Ch 70: Languages with a morphological imperative (426/548 = 77.7%)
    vastly outnumber those without (122/548 = 22.3%). -/
theorem morph_imp_dominant :
    (f70.filter (·.value != .noSecondPersonImperatives)).length >
    (f70.filter (·.value == .noSecondPersonImperatives)).length * 3 := by native_decide

/-- Ch 70: Second-singular-and-second-plural imperatives (292) are the most
    common single type. -/
theorem sg_pl_most_common :
    (f70.filter (·.value == .secondSingularAndSecondPlural)).length >
    (f70.filter (·.value == .secondPersonNumberNeutral)).length ∧
    (f70.filter (·.value == .secondSingularAndSecondPlural)).length >
    (f70.filter (·.value == .noSecondPersonImperatives)).length ∧
    (f70.filter (·.value == .secondSingularAndSecondPlural)).length >
    (f70.filter (·.value == .secondSingular)).length ∧
    (f70.filter (·.value == .secondSingularAndSecondPlural)).length >
    (f70.filter (·.value == .secondPlural)).length := by native_decide

-- ============================================================================
-- Typological Generalization 2: Prohibitives Tend to Be Special
-- ============================================================================

/-- Ch 71: The majority of languages (383/496 = 77.2%) use a special
    construction for prohibitives — they do NOT simply negate the imperative.
    Only 113/496 (22.8%) use normal imperative + normal negation (Type 1).
    This is van der Auwera's key finding: prohibitives are typologically
    marked relative to affirmative imperatives. -/
theorem prohibitive_mostly_special :
    (f71.filter (·.value != .normalImperativeNormalNegative)).length >
    (f71.filter (·.value == .normalImperativeNormalNegative)).length * 3 := by
  native_decide

/-- Ch 71: Type 2 (normal imperative + special negation) is the single most
    common prohibitive type: 182 > 146 > 113 > 55. -/
theorem type2_most_common_prohibitive :
    (f71.filter (·.value == .normalImperativeSpecialNegative)).length >
    (f71.filter (·.value == .specialImperativeSpecialNegative)).length ∧
    (f71.filter (·.value == .specialImperativeSpecialNegative)).length >
    (f71.filter (·.value == .normalImperativeNormalNegative)).length ∧
    (f71.filter (·.value == .normalImperativeNormalNegative)).length >
    (f71.filter (·.value == .specialImperativeNormalNegative)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 3: Imperative-Only Systems Dominate
-- ============================================================================

/-- Ch 72: More than half of languages (201/375 = 53.6%) have neither type
    of imperative-hortative system. -/
theorem neither_system_majority :
    (f72.filter (·.value == .neitherTypeOfSystem)).length >
    f72.length / 2 := by native_decide

/-- Ch 72: Minimal systems (20/375 = 5.3%) are the rarest type. -/
theorem minimal_system_rarest :
    (f72.filter (·.value == .minimalSystem)).length <
    (f72.filter (·.value == .bothTypesOfSystem)).length ∧
    (f72.filter (·.value == .minimalSystem)).length <
    (f72.filter (·.value == .maximalSystem)).length ∧
    (f72.filter (·.value == .minimalSystem)).length <
    (f72.filter (·.value == .neitherTypeOfSystem)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 72: Maximal systems (133) are much more common than minimal
    systems (20) or both-types systems (21). -/
theorem maximal_more_common_than_minimal :
    (f72.filter (·.value == .maximalSystem)).length >
    (f72.filter (·.value == .minimalSystem)).length +
    (f72.filter (·.value == .bothTypesOfSystem)).length := by native_decide

-- ============================================================================
-- Typological Generalization 4: Optatives Are a Minority Feature
-- ============================================================================

/-- Ch 73: The majority of languages lack a dedicated optative (271/319).
    Only 48/319 (15.0%) have one. Optatives outnumbered by non-optatives
    more than 5:1. -/
theorem optative_minority :
    (f73.filter (·.value == .absent)).length >
    (f73.filter (·.value == .present)).length * 5 := by native_decide

-- ============================================================================
-- Typological Generalization 5: Extended Paradigms Correlate with
-- Hortative/Jussive
-- ============================================================================

/-- In our sample, every language with an "all three" imperative-hortative
    system (Ch 72) also has a second-and-other morphological imperative
    (Ch 70). This makes sense: if a language has morphological hortative
    and jussive forms, its imperative paradigm extends beyond 2nd person. -/
theorem all_three_implies_extended_paradigm :
    let allThreeLangs := allLanguages.filter
      (·.impHortSystem == .allThree)
    allThreeLangs.all (·.hasExtendedParadigm) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 6: Special Prohibitives Are Cross-Lingually
-- Common
-- ============================================================================

/-- In our sample, more languages have a special prohibitive construction
    (Type 2, 3, or 4) than a normal one (Type 1). This mirrors the WALS
    finding that simply negating the imperative is the exception, not the
    rule. -/
theorem sample_special_prohibitive_majority :
    let special := allLanguages.filter (·.hasSpecialProhibitive)
    let normal := allLanguages.filter (¬ ·.hasSpecialProhibitive)
    special.length > normal.length := by
  native_decide

-- ============================================================================
-- Typological Generalization 7: Optatives Correlate with Rich Paradigms
-- ============================================================================

/-- In our sample, every language with a dedicated optative also has a
    second-and-other morphological imperative (extended paradigm). Rich
    mood morphology tends to come as a package. -/
theorem optative_implies_extended_paradigm :
    let optLangs := allLanguages.filter (·.hasOptative)
    optLangs.all (·.hasExtendedParadigm) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 8: No Morphological Imperative Implies
-- Imperative-Only System
-- ============================================================================

/-- In our sample, languages without a morphological imperative (Ch 70)
    are always classified as imperative-only for Ch 72. This is expected:
    if a language lacks even a 2nd-person morphological imperative, it is
    unlikely to have morphological hortatives or jussives. -/
theorem no_morph_imp_implies_imp_only :
    let noMorph := allLanguages.filter (·.morphImp == .noMorphological)
    noMorph.all (·.impHortSystem == .imperativeOnly) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 9: Jussives Tend to Co-occur with
-- Extended Paradigms
-- ============================================================================

/-- In our sample, most languages with a jussive (Ch 72) also have a
    second-and-other morphological imperative (Ch 70). The exception is
    Hungarian, where the subjunctive serves as jussive while the imperative
    paradigm is second-person-only. At least 3/4 of jussive languages
    have extended paradigms. -/
theorem jussive_mostly_extended_paradigm :
    let jussLangs := allLanguages.filter (·.hasJussive)
    let extended := jussLangs.filter (·.hasExtendedParadigm)
    extended.length * 4 ≥ jussLangs.length * 3 := by
  native_decide

-- ============================================================================
-- Typological Generalization 10: Type 1 Prohibitives and Agglutinative
-- Languages
-- ============================================================================

/-- In our sample, Turkish, Russian, Hungarian, English, and Korean all use
    Type 1 prohibitives (normal imperative + normal negation). These include
    agglutinative languages where negation is a regular affix/particle that
    combines freely with the imperative morphology. -/
theorem type1_languages :
    let type1 := allLanguages.filter
      (·.prohibitive == .normalImpNormalNeg)
    type1.length = 5 := by
  native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Ch 70 verifications
theorem english_second_only : english.morphImp == .secondOnly := by native_decide
theorem japanese_second_only : japanese.morphImp == .secondOnly := by native_decide
theorem mandarin_no_morph : mandarin.morphImp == .noMorphological := by native_decide
theorem turkish_extended : turkish.hasExtendedParadigm = true := by native_decide
theorem finnish_extended : finnish.hasExtendedParadigm = true := by native_decide
theorem latin_extended : latin.hasExtendedParadigm = true := by native_decide
theorem tagalog_no_morph : tagalog.morphImp == .noMorphological := by native_decide

-- Ch 71 verifications
theorem english_type1 : english.prohibitive == .normalImpNormalNeg := by native_decide
theorem japanese_type2 : japanese.prohibitive == .normalImpSpecialNeg := by native_decide
theorem finnish_type3 : finnish.prohibitive == .specialImpNormalNeg := by native_decide
theorem latin_type4 : latin.prohibitive == .specialImpSpecialNeg := by native_decide
theorem italian_type3 : italian.prohibitive == .specialImpNormalNeg := by native_decide
theorem arabic_type4 : arabic.prohibitive == .specialImpSpecialNeg := by native_decide
theorem hindiUrdu_type2 : hindiUrdu.prohibitive == .normalImpSpecialNeg := by native_decide

-- Ch 72 verifications
theorem english_imp_only : english.impHortSystem == .imperativeOnly := by native_decide
theorem turkish_all_three : turkish.impHortSystem == .allThree := by native_decide
theorem korean_imp_hort : korean.impHortSystem == .imperativeAndHortative := by native_decide
theorem hungarian_imp_juss : hungarian.impHortSystem == .imperativeAndJussive := by native_decide
theorem quechua_all_three : quechua.impHortSystem == .allThree := by native_decide
theorem georgian_all_three : georgian.impHortSystem == .allThree := by native_decide

-- Ch 73 verifications
theorem turkish_has_optative : turkish.hasOptative = true := by native_decide
theorem english_no_optative : english.optative == some .absent := by native_decide
theorem greek_has_optative : ancientGreek.hasOptative = true := by native_decide
theorem quechua_has_optative : quechua.hasOptative = true := by native_decide
theorem georgian_has_optative : georgian.hasOptative = true := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-- In our sample, every language with a morphological imperative that extends
    to other persons (Ch 70 = secondAndOther) has at least some non-second-person
    command morphology (Ch 72 ≠ imperativeOnly), unless the extension is limited
    to features like number or formality within 2nd person.
    In fact, all secondAndOther languages in our sample have hortative or
    jussive or both. -/
theorem extended_implies_beyond_imp_only :
    let extended := allLanguages.filter (·.hasExtendedParadigm)
    extended.all (·.impHortSystem != .imperativeOnly) = true := by
  native_decide

/-- In our sample, no language without a morphological imperative has a
    dedicated optative. Mood-poor languages tend to be consistently
    mood-poor across the board. -/
theorem no_morph_imp_no_optative :
    let noMorph := allLanguages.filter (·.morphImp == .noMorphological)
    noMorph.all (¬ ·.hasOptative) = true := by
  native_decide

/-- In our sample, most languages with a dedicated optative also have a
    special prohibitive construction (Type 2, 3, or 4). The exception is
    Turkish, where both the optative (-sA) and the prohibitive (regular
    negation + imperative) are well-integrated into the agglutinative
    morphology. At least 3/4 of optative languages have special
    prohibitives. -/
theorem optative_mostly_special_prohibitive :
    let optLangs := allLanguages.filter (·.hasOptative)
    let special := optLangs.filter (·.hasSpecialProhibitive)
    special.length * 4 ≥ optLangs.length * 3 := by
  native_decide

/-- Chapters 70--73 have different sample sizes. -/
theorem ch_sample_sizes :
    WALSCount.totalOf ch70Counts = 548 ∧
    WALSCount.totalOf ch71Counts = 496 ∧
    WALSCount.totalOf ch72Counts = 375 ∧
    WALSCount.totalOf ch73Counts = 319 := by
  native_decide

-- ============================================================================
-- Summary Statistics for Our Sample
-- ============================================================================

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 17 := by native_decide

/-- Morphological imperative distribution in our sample. -/
theorem sample_second_only_count :
    countByMorphImp allLanguages .secondOnly = 6 := by native_decide
theorem sample_second_and_other_count :
    countByMorphImp allLanguages .secondAndOther = 9 := by native_decide
theorem sample_no_morph_count :
    countByMorphImp allLanguages .noMorphological = 2 := by native_decide

/-- Prohibitive type distribution in our sample. -/
theorem sample_type1_count :
    countByProhibitive allLanguages .normalImpNormalNeg = 5 := by native_decide
theorem sample_type2_count :
    countByProhibitive allLanguages .normalImpSpecialNeg = 5 := by native_decide
theorem sample_type3_count :
    countByProhibitive allLanguages .specialImpNormalNeg = 3 := by native_decide
theorem sample_type4_count :
    countByProhibitive allLanguages .specialImpSpecialNeg = 4 := by native_decide

/-- Imperative-hortative system distribution in our sample. -/
theorem sample_imp_only_count :
    countByImpHort allLanguages .imperativeOnly = 5 := by native_decide
theorem sample_imp_hort_count :
    countByImpHort allLanguages .imperativeAndHortative = 1 := by native_decide
theorem sample_imp_juss_count :
    countByImpHort allLanguages .imperativeAndJussive = 4 := by native_decide
theorem sample_all_three_count :
    countByImpHort allLanguages .allThree = 7 := by native_decide

/-- Optative distribution in our sample. -/
theorem sample_optative_present_count :
    (allLanguages.filter (·.hasOptative)).length = 4 := by native_decide
theorem sample_optative_absent_count :
    (allLanguages.filter (·.optative == some .absent)).length = 13 := by native_decide

/-- Every language in our sample has a Ch 73 classification. -/
theorem sample_all_have_optative_data :
    allLanguages.all (·.optative != none) = true := by native_decide

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Convert F70A (morphological imperative number distinction) to
    `MorphImpType`. F70A tracks whether 2nd-person imperatives distinguish
    singular vs plural; it does not encode whether the paradigm extends to
    other persons (`secondAndOther`). We can only reliably identify
    `noMorphological` (when F70A = noSecondPersonImperatives) and distinguish
    it from the presence of some morphological imperative. Returns `none`
    when the F70A value indicates a morphological imperative exists but
    does not determine whether it extends beyond 2nd person. -/
private def fromWALS70A : Core.WALS.F70A.MorphologicalImperative → Option MorphImpType
  | .noSecondPersonImperatives => some .noMorphological
  | _ => none

/-- Convert F71A (prohibitive type) to `ProhibitiveType`. The mapping is
    one-to-one between WALS 71A categories and our four-way classification. -/
private def fromWALS71A : Core.WALS.F71A.Prohibitive → ProhibitiveType
  | .normalImperativeNormalNegative => .normalImpNormalNeg
  | .normalImperativeSpecialNegative => .normalImpSpecialNeg
  | .specialImperativeNormalNegative => .specialImpNormalNeg
  | .specialImperativeSpecialNegative => .specialImpSpecialNeg

/-- Convert F72A (imperative-hortative systems) to `ImpHortSystem`. The
    WALS v2020.4 coding uses `maximalSystem` / `minimalSystem` /
    `bothTypesOfSystem` / `neitherTypeOfSystem`. Only two values map cleanly:
    `neitherTypeOfSystem` → `imperativeOnly`, `maximalSystem` → `allThree`.
    The other two are ambiguous and return `none`. -/
private def fromWALS72A : Core.WALS.F72A.ImperativeHortativeSystems → Option ImpHortSystem
  | .neitherTypeOfSystem => some .imperativeOnly
  | .maximalSystem => some .allThree
  | _ => none

/-- Convert F73A (optative presence) to `OptativePresence`. One-to-one. -/
private def fromWALS73A : Core.WALS.F73A.Optative → OptativePresence
  | .present => .present
  | .absent => .absent

-- ============================================================================
-- WALS Dataset Size Verification
-- ============================================================================

theorem ch70_wals_total : f70.length = 548 := by native_decide
theorem ch71_wals_total : f71.length = 496 := by native_decide
theorem ch72_wals_total : f72.length = 375 := by native_decide
theorem ch73_wals_total : f73.length = 319 := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 70 (Morphological Imperative)
--
-- F70A tracks number distinctions in the 2nd-person imperative, not the
-- person-extension distinction (secondOnly vs secondAndOther). We can only
-- ground the `noMorphological` value via `noSecondPersonImperatives`.
-- Languages like English, Georgian, and Hungarian are coded differently in
-- F70A than in our profile (different categorization criteria), so they are
-- omitted.
-- ============================================================================

theorem mandarin_ch70 :
    (Core.WALS.F70A.lookup "mnd").map (fromWALS70A ·.value) =
    some (some mandarin.morphImp) := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 71 (Prohibitive)
--
-- The F71A four-way classification maps one-to-one to our ProhibitiveType.
-- Grounding theorems cover languages where both the WALS code exists and
-- the value agrees with our profile. Finnish (WALS: normalImp+specialNeg
-- vs profile: specialImp+normalNeg), Swahili (WALS: specialImp+specialNeg
-- vs profile: specialImp+normalNeg), Hungarian (WALS: normalImp+specialNeg
-- vs profile: normalImp+normalNeg), and Korean (WALS: normalImp+specialNeg
-- vs profile: normalImp+normalNeg) are omitted due to coding disagreements
-- between WALS v2020.4 and our profiles.
-- ============================================================================

theorem english_ch71 :
    (Core.WALS.F71A.lookup "eng").map (fromWALS71A ·.value) =
    some english.prohibitive := by
  native_decide

theorem japanese_ch71 :
    (Core.WALS.F71A.lookup "jpn").map (fromWALS71A ·.value) =
    some japanese.prohibitive := by
  native_decide

theorem mandarin_ch71 :
    (Core.WALS.F71A.lookup "mnd").map (fromWALS71A ·.value) =
    some mandarin.prohibitive := by
  native_decide

theorem turkish_ch71 :
    (Core.WALS.F71A.lookup "tur").map (fromWALS71A ·.value) =
    some turkish.prohibitive := by
  native_decide

theorem russian_ch71 :
    (Core.WALS.F71A.lookup "rus").map (fromWALS71A ·.value) =
    some russian.prohibitive := by
  native_decide

theorem hindiUrdu_ch71 :
    (Core.WALS.F71A.lookup "hin").map (fromWALS71A ·.value) =
    some hindiUrdu.prohibitive := by
  native_decide

theorem tagalog_ch71 :
    (Core.WALS.F71A.lookup "tag").map (fromWALS71A ·.value) =
    some tagalog.prohibitive := by
  native_decide

theorem italian_ch71 :
    (Core.WALS.F71A.lookup "ita").map (fromWALS71A ·.value) =
    some italian.prohibitive := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 72 (Imperative-Hortative Systems)
--
-- F72A uses maximal/minimal/both/neither, which partially maps to our
-- four-way system. `neitherTypeOfSystem` → `imperativeOnly` and
-- `maximalSystem` → `allThree` are the clean mappings. Languages where
-- WALS and our profile disagree (Georgian, Hindi-Urdu, Hungarian, Korean,
-- Italian) are omitted.
-- ============================================================================

theorem english_ch72 :
    (Core.WALS.F72A.lookup "eng").map (fromWALS72A ·.value) =
    some (some english.impHortSystem) := by
  native_decide

theorem japanese_ch72 :
    (Core.WALS.F72A.lookup "jpn").map (fromWALS72A ·.value) =
    some (some japanese.impHortSystem) := by
  native_decide

theorem mandarin_ch72 :
    (Core.WALS.F72A.lookup "mnd").map (fromWALS72A ·.value) =
    some (some mandarin.impHortSystem) := by
  native_decide

theorem turkish_ch72 :
    (Core.WALS.F72A.lookup "tur").map (fromWALS72A ·.value) =
    some (some turkish.impHortSystem) := by
  native_decide

theorem finnish_ch72 :
    (Core.WALS.F72A.lookup "fin").map (fromWALS72A ·.value) =
    some (some finnish.impHortSystem) := by
  native_decide

theorem russian_ch72 :
    (Core.WALS.F72A.lookup "rus").map (fromWALS72A ·.value) =
    some (some russian.impHortSystem) := by
  native_decide

theorem swahili_ch72 :
    (Core.WALS.F72A.lookup "swa").map (fromWALS72A ·.value) =
    some (some swahili.impHortSystem) := by
  native_decide

theorem tagalog_ch72 :
    (Core.WALS.F72A.lookup "tag").map (fromWALS72A ·.value) =
    some (some tagalog.impHortSystem) := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 73 (Optative)
--
-- F73A is a binary feature (present/absent) with a clean one-to-one mapping.
-- Turkish (WALS: absent vs profile: present) and Tagalog (WALS: present vs
-- profile: absent) are omitted due to coding disagreements. Italian, Ancient
-- Greek, Arabic (MSA), Quechua (Cuzco), and Latin are not in the F73A sample.
-- ============================================================================

theorem english_ch73 :
    (Core.WALS.F73A.lookup "eng").map (fromWALS73A ·.value) =
    some (english.optative.getD .absent) := by
  native_decide

theorem japanese_ch73 :
    (Core.WALS.F73A.lookup "jpn").map (fromWALS73A ·.value) =
    some (japanese.optative.getD .absent) := by
  native_decide

theorem mandarin_ch73 :
    (Core.WALS.F73A.lookup "mnd").map (fromWALS73A ·.value) =
    some (mandarin.optative.getD .absent) := by
  native_decide

theorem finnish_ch73 :
    (Core.WALS.F73A.lookup "fin").map (fromWALS73A ·.value) =
    some (finnish.optative.getD .absent) := by
  native_decide

theorem russian_ch73 :
    (Core.WALS.F73A.lookup "rus").map (fromWALS73A ·.value) =
    some (russian.optative.getD .absent) := by
  native_decide

theorem georgian_ch73 :
    (Core.WALS.F73A.lookup "geo").map (fromWALS73A ·.value) =
    some (georgian.optative.getD .absent) := by
  native_decide

theorem hindiUrdu_ch73 :
    (Core.WALS.F73A.lookup "hin").map (fromWALS73A ·.value) =
    some (hindiUrdu.optative.getD .absent) := by
  native_decide

theorem hungarian_ch73 :
    (Core.WALS.F73A.lookup "hun").map (fromWALS73A ·.value) =
    some (hungarian.optative.getD .absent) := by
  native_decide

theorem korean_ch73 :
    (Core.WALS.F73A.lookup "kor").map (fromWALS73A ·.value) =
    some (korean.optative.getD .absent) := by
  native_decide

theorem swahili_ch73 :
    (Core.WALS.F73A.lookup "swa").map (fromWALS73A ·.value) =
    some (swahili.optative.getD .absent) := by
  native_decide

end Phenomena.Directives.Typology
