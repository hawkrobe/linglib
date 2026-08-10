/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Ga.Basic
import Linglib.Syntax.Clause.Complementation
import Linglib.Semantics.Causation.VerbClass

/-!
# Gã Complement-Taking Predicates
[allotey-2021]

Inventory of Gã verbs that take embedded clausal complements, classified
by the clause types they are attested with, the control relation of
their `ni`-frame, and Karttunen implicativity. Several verbs alternate
between frames — *kai* 'remember' takes the controlled irrealis
`ni`-clause (ex 43) or a finite `akɛ`-clause (ex 89a), *kɛɛ* 'say/tell'
takes `akɛ` (exx 47–49) or an object-control `ni`-clause (ex 117b) —
and this C-selection is [allotey-2021]'s first non-finiteness
diagnostic (§5.5.1, exx 104–108), so `selects` is list-valued. All
entries are attested in her example data, cited by example number.

## Identifier policy

ASCII identifiers; IPA orthography lives in `.form` strings.
See `Fragments/Ga/Basic.lean` for rationale.
-/

namespace Ga


/-- A Gã complement-taking predicate: form, gloss, the embedded clause
    types it is attested with, the control relation of its `ni`-frame
    (`ControlType.none` exactly for verbs without one), and its
    Karttunen implicativity ([karttunen-1971]: `positive` = complement
    entailed realized, `negative` = entailed unrealized, `none` =
    non-implicative). Implicativity has a grammatical reflex in Gã:
    implicatives alternate into realis complement frames, where the
    irrealis marker is impossible (`Studies/Allotey2021.lean`). -/
structure CTP where
  form    : String
  gloss   : String
  /-- Embedded clause types attested with this verb. -/
  selects : List EmbeddedClauseType
  /-- The control relation of the verb's irrealis `ni`-frame. -/
  control : ControlType
  /-- Karttunen implicative class; `none` for non-implicatives. -/
  implicative : Option Implicative
  deriving Repr, DecidableEq

/-! ### Subject-control verbs (irrealis `ni`-clause) -/

/-- 'want' — subject control; `ni` optionally overt ([allotey-2021]
    ex 34: *Mi-i tao (ni) ma na bo* 'I want to see you'; the embedded
    1SG is the irrealis portmanteau *má*, exx 88, 100). -/
def tao : CTP := ⟨"tao", "want", [.irrealisNi], .subjectControl, none⟩

/-- 'hope' (lit. 'face-place-upon') — subject control; `ni` obligatory
    ([allotey-2021] ex 35: *Mi hiɛ-kã-nɔ ni ma ya skul gbi ko*
    'I hope to go to school one day'). -/
def hiekano : CTP := ⟨"hiɛ-kã-nɔ", "hope", [.irrealisNi], .subjectControl, none⟩

/-- 'forget' (lit. 'face-stop-upon') — subject control; `ni` obligatory
    ([allotey-2021] exx 37–38: *O hiɛ-kpa-nɔ ni o kɔ aspaatere lɛ*
    'You forgot to pick up the shoe'). Negative implicative (*forget to*
    entails the complement unrealized — textbook [karttunen-1971], not
    her classification), and its `ni`-clause duly carries the irrealis
    marker (exx 102–103: *ó*, *é*). -/
def hiekpano : CTP := ⟨"hiɛ-kpa-nɔ", "forget", [.irrealisNi], .subjectControl, some .negative⟩

/-- 'try' (lit. 'squeeze-my-face') — subject control; `ni` obligatory
    ([allotey-2021] exx 36, 60a: 'I tried to close the door'). -/
def miamihie : CTP := ⟨"mia-mi-hiɛ", "try", [.irrealisNi], .subjectControl, none⟩

/-- 'remember' — subject control in the `ni`-frame ([allotey-2021]
    exx 42–43: *Mi kai ni ma he wolo* 'I remembered to buy a book');
    positive implicative. Alternates into a finite `akɛ`-frame
    'remember that' whose realis past complement excludes the irrealis
    marker (ex 89a: *Mi kai akɛ mi/\*má he wolo lɛ*); under matrix
    negation the `ni`-frame carries the marker (ex 117a: *é*). -/
def kai : CTP := ⟨"kai", "remember", [.irrealisNi, .finiteAke], .subjectControl, some .positive⟩

/-- 'manage / be able to' — subject control; `ni` optionally overt
    ([allotey-2021] ex 39: 'The children managed to buy a home');
    positive implicative. Also attested with a bare complementizer-less
    realis past complement where the irrealis marker is excluded
    (ex 89b: *Mi nyɛ mi/\*má sha tsensii lɛ*); the zero-frame is not a
    member of the three-way clause typology and is recorded only in
    `Studies/Allotey2021.lean`'s marker data. -/
def nye : CTP := ⟨"nyɛ", "manage", [.irrealisNi], .subjectControl, some .positive⟩

/-- 'agree' — subject control; the `ni`-frame requires the irrealis
    marker ([allotey-2021] exx 52, 89c: *\*mi/má*; also 109, 122a).
    Alternates into `akɛ` with a true subjunctive complement
    ('agree that…', ex 105: *Osa kplɛnɔ ni/akɛ Taki á-tsɛ́ Momo*). -/
def kpleno : CTP := ⟨"kplɛnɔ", "agree", [.irrealisNi, .finiteAke], .subjectControl, none⟩

/-- 'plan / decide' — subject control; only `ni` — never `akɛ` or
    `kɛji` — introduces the complement ([allotey-2021] ex 106), and the
    irrealis marker is obligatory (ex 89d: *\*mi/má*). -/
def kpang : CTP := ⟨"kpaŋ", "plan", [.irrealisNi], .subjectControl, none⟩

/-! ### Object-control verbs (irrealis `ni`-clause) -/

/-- 'help' — object control ([allotey-2021] exx 44, 54: *Mi wa Ama ni
    e-ya skul* 'I helped Ama to go to school'). Whether *help* is
    (partially) implicative is contested in the post-Karttunen
    literature; left unclassified. -/
def wa : CTP := ⟨"wa", "help", [.irrealisNi], .objectControl, none⟩

/-- 'urge / encourage' — object control ([allotey-2021] exx 55, 60b). -/
def kenya : CTP := ⟨"kenya", "urge", [.irrealisNi], .objectControl, none⟩

/-- 'force' — object control ([allotey-2021] ex 56). Coded positive
    implicative: forcing entails the forced event realized, though
    two-place coercives postdate [karttunen-1971]'s one-place
    inventory. -/
def dai : CTP := ⟨"dai", "force", [.irrealisNi], .objectControl, some .positive⟩

/-- 'persuade / coax / deceive' (context-dependent, the paper's fn 4) —
    object control ([allotey-2021] exx 57–58). -/
def laka : CTP := ⟨"laka", "persuade", [.irrealisNi], .objectControl, none⟩

/-- 'ask' — object control ([allotey-2021] ex 59: 'I asked Ayele to
    tell me a story'). -/
def bi : CTP := ⟨"bi", "ask", [.irrealisNi], .objectControl, none⟩

/-- 'say / tell' — finite `akɛ`-clause as the paper's standard
    utterance-verb exemplar ([allotey-2021] exx 47–49: *Jojo kɛɛ akɛ …*
    'Jojo said that …'), and object control in the `ni`-frame ('tell
    someone to …', ex 117b: *John é-kee-ee Mary ni é he noko-noko*
    'John didn't tell Mary to buy anything'; *tell* is on her
    object-control predicate list). -/
def kee : CTP := ⟨"kɛɛ", "say", [.finiteAke, .irrealisNi], .objectControl, none⟩

/-! ### Finite-complement-only verbs -/

/-- 'know' — selects a finite `kɛji`-clause for if/whether complements
    ([allotey-2021] exx 104, 108: 'know if they will be coming',
    'doesn't know whether you or he bought the book'). -/
def le : CTP := ⟨"le", "know", [.finiteKeji], .none, none⟩

/-- The attested complement-taking predicate inventory. -/
def gaCTPs : List CTP :=
  [tao, hiekano, hiekpano, miamihie, kai, nye, kpleno, kpang,
   wa, kenya, dai, laka, bi, kee, le]

end Ga
