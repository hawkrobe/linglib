import Linglib.Core.Word

/-!
# Cross-Linguistic Typology of Imperatives (WALS Chapters 70--73)

Cross-linguistic data on imperative and related mood systems from four WALS
chapters, all authored by Johan van der Auwera and Ludo Lejeune (2013).

## Ch 70: The Morphological Imperative (van der Auwera & Lejeune 2013)

Whether a language has a dedicated morphological form for second-person
imperatives. Three values: (1) a second-person-only morphological imperative,
(2) a morphological imperative for second and other persons, (3) no
morphological imperative (imperative expressed by structural means such as
word order, intonation, or bare stems identical to the indicative).

Sample: 495 languages. The vast majority (388/495 = 78.4%) have a
dedicated morphological imperative of some kind; only 107 lack one entirely.

## Ch 71: The Prohibitive (van der Auwera & Lejeune 2013)

How negative imperatives ("Don't!") are formed relative to regular
imperatives and regular negation. Four structural types based on whether
the imperative construction and the negation strategy are the *same* as
in declaratives or *special*:

- Type 1: normal imperative + normal negation (e.g., Korean)
- Type 2: normal imperative + special negation (e.g., Ancient Greek)
- Type 3: special imperative + normal negation (e.g., Italian)
- Type 4: special imperative + special negation (e.g., Sinhala)

Sample: 495 languages. Type 4 (special+special) is the most common
(182/495 = 36.8%).

## Ch 72: Imperative-Hortative Systems (van der Auwera & Lejeune 2013)

Whether the language has dedicated morphological forms for first-person
hortatives ("let's go") and/or third-person jussives ("let him go"), in
addition to the second-person imperative. Four values: imperative only,
imperative + hortative, imperative + jussive, or all three.

Sample: 495 languages. Imperative-only systems are the most common
(263/495 = 53.1%); systems with all three forms are the least common
(43/495 = 8.7%).

## Ch 73: The Optative (van der Auwera & Lejeune 2013)

Whether the language has a morphologically dedicated optative construction
("may it rain", "if only she were here"). Binary feature: present or absent.

Sample: 319 languages. Optatives are a minority feature: only 77/319
(24.1%) of sampled languages have a dedicated optative.

## References

- van der Auwera, J. & Lejeune, L. (2013). The morphological imperative.
  In Dryer & Haspelmath (eds.), WALS Online (v2020.3).
  https://wals.info/chapter/70
- van der Auwera, J. & Lejeune, L. (2013). The prohibitive.
  In Dryer & Haspelmath (eds.), WALS Online (v2020.3).
  https://wals.info/chapter/71
- van der Auwera, J. & Lejeune, L. (2013). Imperative-hortative systems.
  In Dryer & Haspelmath (eds.), WALS Online (v2020.3).
  https://wals.info/chapter/72
- van der Auwera, J. & Lejeune, L. (2013). The optative.
  In Dryer & Haspelmath (eds.), WALS Online (v2020.3).
  https://wals.info/chapter/73
- van der Auwera, J. (2006). Why languages prefer prohibitives.
  Journal of Foreign Languages 161: 2--25.
- Aikhenvald, A. Y. (2010). Imperatives and Commands. Oxford University Press.
-/

namespace Phenomena.Imperatives.Typology

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
      The most common pattern worldwide (213/495 = 43.0%). -/
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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- WALS Distribution Data (Aggregate Counts)
-- ============================================================================

/-- A single row in a WALS frequency table: a category label and its count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

/-- Chapter 70 distribution: morphological imperative types (N = 495). -/
def ch70Counts : List WALSCount :=
  [ ⟨"Second person only", 213⟩
  , ⟨"Second and other persons", 175⟩
  , ⟨"No morphological imperative", 107⟩ ]

/-- Chapter 71 distribution: prohibitive types (N = 495). -/
def ch71Counts : List WALSCount :=
  [ ⟨"Normal imperative + normal negation", 93⟩
  , ⟨"Normal imperative + special negation", 75⟩
  , ⟨"Special imperative + normal negation", 145⟩
  , ⟨"Special imperative + special negation", 182⟩ ]

/-- Chapter 72 distribution: imperative-hortative systems (N = 495). -/
def ch72Counts : List WALSCount :=
  [ ⟨"Imperative only", 263⟩
  , ⟨"Imperative + hortative", 117⟩
  , ⟨"Imperative + jussive", 72⟩
  , ⟨"All three (imperative + hortative + jussive)", 43⟩ ]

/-- Chapter 73 distribution: optative presence (N = 319). -/
def ch73Counts : List WALSCount :=
  [ ⟨"Optative present", 77⟩
  , ⟨"Optative absent", 242⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Ch 70 total: 495 languages. -/
theorem ch70_total : WALSCount.totalOf ch70Counts = 495 := by native_decide

/-- Ch 71 total: 495 languages. -/
theorem ch71_total : WALSCount.totalOf ch71Counts = 495 := by native_decide

/-- Ch 72 total: 495 languages. -/
theorem ch72_total : WALSCount.totalOf ch72Counts = 495 := by native_decide

/-- Ch 73 total: 319 languages. -/
theorem ch73_total : WALSCount.totalOf ch73Counts = 319 := by native_decide

/-- Chapters 70, 71, and 72 share the same sample size (495). -/
theorem ch70_ch71_ch72_same_sample :
    WALSCount.totalOf ch70Counts = WALSCount.totalOf ch71Counts ∧
    WALSCount.totalOf ch71Counts = WALSCount.totalOf ch72Counts := by
  native_decide

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

/-- Ch 70: Languages with a morphological imperative (388/495 = 78.4%)
    vastly outnumber those without (107/495 = 21.6%). -/
theorem morph_imp_dominant : (213 + 175 : Nat) > 107 * 3 := by native_decide

/-- Ch 70: Second-person-only imperatives (213) are the most common single
    type, slightly outnumbering second-and-other (175). -/
theorem second_only_most_common : (213 : Nat) > 175 := by native_decide

-- ============================================================================
-- Typological Generalization 2: Prohibitives Tend to Be Special
-- ============================================================================

/-- Ch 71: The majority of languages (402/495 = 81.2%) use a special
    construction for prohibitives — they do NOT simply negate the imperative.
    Only 93/495 (18.8%) use normal imperative + normal negation (Type 1).
    This is van der Auwera's key finding: prohibitives are typologically
    marked relative to affirmative imperatives. -/
theorem prohibitive_mostly_special : (75 + 145 + 182 : Nat) > 93 * 4 := by
  native_decide

/-- Ch 71: Type 4 (special+special) is the single most common prohibitive
    type: 182 > 145 > 93 > 75. -/
theorem type4_most_common_prohibitive :
    (182 : Nat) > 145 ∧ (145 : Nat) > 93 ∧ (93 : Nat) > 75 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 3: Imperative-Only Systems Dominate
-- ============================================================================

/-- Ch 72: More than half of languages (263/495 = 53.1%) have only an
    imperative and lack dedicated hortative or jussive morphology. -/
theorem imp_only_majority : (263 : Nat) > 495 / 2 := by native_decide

/-- Ch 72: Systems with all three (imperative + hortative + jussive) are
    the rarest type (43/495 = 8.7%). -/
theorem all_three_rarest :
    (43 : Nat) < 72 ∧ (43 : Nat) < 117 ∧ (43 : Nat) < 263 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 72: Hortatives are more common than jussives. Languages with
    hortative (imp+hort 117 + all three 43 = 160) vs jussive
    (imp+juss 72 + all three 43 = 115). -/
theorem hortatives_more_common_than_jussives :
    (117 + 43 : Nat) > 72 + 43 := by native_decide

-- ============================================================================
-- Typological Generalization 4: Optatives Are a Minority Feature
-- ============================================================================

/-- Ch 73: The majority of languages lack a dedicated optative (242/319).
    Only 77/319 (24.1%) have one. Optatives outnumbered by non-optatives
    more than 3:1. -/
theorem optative_minority : (242 : Nat) > 77 * 3 := by native_decide

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

/-- Chapters 70--72 use the same sample (495 languages each). -/
theorem ch70_71_72_same_n :
    WALSCount.totalOf ch70Counts = 495 ∧
    WALSCount.totalOf ch71Counts = 495 ∧
    WALSCount.totalOf ch72Counts = 495 := by
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

end Phenomena.Imperatives.Typology
