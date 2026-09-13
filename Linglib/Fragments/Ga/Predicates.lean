/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Ga.Basic
import Linglib.Syntax.Category.Verb.Complement.Takes

/-!
# Gã complement-taking verbs

This file records the Gã verbs of [allotey-2021] that embed clauses, as `Verb`
entries whose frames are the clause frames of `Fragments/Ga/Basic` and whose
`ni`-frame reading carries the control relation. Several verbs alternate between
frames: *kai* 'remember' takes the controlled `ni`-clause (ex 43) or a finite
`akɛ`-clause (ex 89a), *kɛɛ* 'say' takes `akɛ` (exx 47–49) or an
object-controlled `ni`-clause (ex 117b). Complementizer selection is the paper's
first non-finiteness diagnostic (§5.5.1, exx 104–108); the selection relation
itself is `Verb.takes` over `Ga.complementizers`.

## Implementation notes

Karttunen implicativity (`Verb.implicative`) is recorded where it is textbook
([karttunen-1971]); the paper uses it for the contrast of ex 89, where the
irrealis marker is absent exactly under the implicatives, but does not classify
the verbs itself. Vendler class stays unset, the convention for clause-embedding
verbs. Identifiers are ASCII (see `Fragments/Ga/Basic`); the IPA orthography is
in `form`.

## References

* [allotey-2021]
* [karttunen-1971]
* [nadathur-lauer-2020]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

namespace Ga

/-- The reading of the controlled `ni`-frame under control relation `c`, with
    the complement's [wurmbrand-lohninger-2023] sort where [wurmbrand-2024]
    classes the verb. -/
def niReading (c : ControlType) (size : Option Clause.Size := none) : Verb.Reading :=
  { frame := niFrame, control := some c, size }

/-- The reading of a finite `akɛ`-frame: a proposition. -/
def akeReading : Verb.Reading := { frame := Frame.finiteClause, size := some .proposition }

/-! ### Subject control -/

/-- *tao* 'want' — subject control; `ni` optionally overt (ex 34: *Mi-i tao (ni)
    ma na bo* 'I want to see you'); the embedded 1SG is the irrealis portmanteau
    *má* (exx 88, 100). -/
def tao : Verb where
  form := "tao"
  frames := [niFrame]
  readings := [niReading .subjectControl (some .situation)]

/-- *sumɔ* 'like' — subject control, with no complementizer under negation
    (ex 3a: *Dida sumɔ-ɔɔ e-na bo* 'Father is reluctant to see you') and with
    `ni` in the future (ex 92); the embedded pronoun cannot be obviative. -/
def sumo : Verb where
  form := "sumɔ"
  frames := [niFrame]
  readings := [niReading .subjectControl]

/-- *hiɛ-kã-nɔ* 'hope' (lit. 'face-place-upon') — subject control; `ni`
    obligatory (ex 35: *Mi hiɛ-kã-nɔ ni ma ya skul gbi ko* 'I hope to go to
    school one day'). -/
def hiekano : Verb where
  form := "hiɛ-kã-nɔ"
  frames := [niFrame]
  readings := [niReading .subjectControl]

/-- *hiɛ-kpa-nɔ* 'forget' (lit. 'face-stop-upon') — subject control; `ni`
    obligatory (exx 37–38: *O hiɛ-kpa-nɔ ni o kɔ aspaatere lɛ* 'You forgot to
    pick up the shoe'). Negative implicative by the textbook classification
    (*forget to* entails the complement unrealized), and its `ni`-clause duly
    carries the irrealis marker (exx 102–103). -/
def hiekpano : Verb where
  form := "hiɛ-kpa-nɔ"
  frames := [niFrame]
  readings := [niReading .subjectControl]
  implicative := some .negative

/-- *mia-mi-hiɛ* 'try' (lit. 'squeeze-my-face') — subject control; `ni`
    obligatory (exx 36, 60a: 'I tried to close the door'). -/
def miamihie : Verb where
  form := "mia-mi-hiɛ"
  frames := [niFrame]
  readings := [niReading .subjectControl (some .event)]

/-- *kai* 'remember' — subject control in the `ni`-frame (exx 42–43: *Mi kai ni
    ma he wolo* 'I remembered to buy a book'), positive implicative. Alternates
    into a finite `akɛ`-frame 'remember that', whose realis past complement
    excludes the irrealis marker (ex 89a); under matrix negation the `ni`-frame
    keeps it (ex 117a). -/
def kai : Verb where
  form := "kai"
  frames := [niFrame, Frame.finiteClause]
  readings := [niReading .subjectControl]
  implicative := some .positive

/-- *nyɛ* 'manage' — subject control; `ni` optionally overt (ex 39: 'The children
    managed to buy a home'), positive implicative. Also attested with a bare
    realis past complement that excludes the irrealis marker (ex 89b), a frame
    outside the three-way clause typology. -/
def nye : Verb where
  form := "nyɛ"
  frames := [niFrame]
  readings := [niReading .subjectControl]
  implicative := some .positive

/-- *kplɛnɔ* 'agree' — subject control; the `ni`-frame requires the irrealis
    marker (exx 52, 89c, 109, 122a). Alternates into `akɛ` with a subjunctive
    complement, 'agree that' (ex 105: *Osa kplɛnɔ ni/akɛ Taki á-tsɛ́ Momo*). -/
def kpleno : Verb where
  form := "kplɛnɔ"
  frames := [niFrame, Frame.finiteClause]
  readings := [niReading .subjectControl]

/-- *kpaŋ* 'plan, decide' — subject control; only `ni` introduces the complement
    (ex 106) and the irrealis marker is obligatory (ex 89d). -/
def kpang : Verb where
  form := "kpaŋ"
  frames := [niFrame]
  readings := [niReading .subjectControl (some .situation)]

/-- *kpã-gbɛ* 'expect' — subject control (ex 53: *Ajele kpã-gbɛ ni e-ye
    jweremɔ lɛ* 'Ajele expects to win the prize', infelicitous when Ajele does
    not self-ascribe winning: the *de se* diagnostic). -/
def kpagbe : Verb where
  form := "kpã-gbɛ"
  frames := [niFrame]
  readings := [niReading .subjectControl (some .situation)]

/-- *dwɛŋ* 'think' — a finite complement with a low-tone, freely referring
    subject (exx 110–111: 'Aku thought s/he bought the book', under `akɛ` or a
    low-tone `ni`), and a controlled `ni`-clause with the high-tone anaphoric
    subject (ex 112: 'Aku thought to buy a book'). -/
def dweng : Verb where
  form := "dwɛŋ"
  frames := [Frame.finiteClause, niFrame]
  readings := [akeReading, niReading .subjectControl]
  attitude := some (.doxastic .nonVeridical)

/-! ### Object control -/

/-- *wa* 'help' — object control (exx 44, 54: *Mi wa Ama ni e-ya skul* 'I helped
    Ama to go to school'). Whether *help* is implicative is contested in the
    literature after [karttunen-1971]; left unclassified. -/
def wa : Verb where
  form := "wa"
  frames := [niFrame]
  readings := [niReading .objectControl]

/-- *kenya* 'urge, encourage' — object control (exx 55, 60b). -/
def kenya : Verb where
  form := "kenya"
  frames := [niFrame]
  readings := [niReading .objectControl]

/-- *dai* 'force' — object control (ex 56: 'I forced Kofi to go to school'); a
    coercive causative whose complement is entailed ([nadathur-lauer-2020]). -/
def dai : Verb where
  form := "dai"
  frames := [niFrame]
  readings := [niReading .objectControl]
  implicative := some .positive
  causative := some .force

/-- *laka* 'persuade, coax, deceive' (context-dependent, fn 4) — object control
    (exx 57–58). -/
def laka : Verb where
  form := "laka"
  frames := [niFrame]
  readings := [niReading .objectControl]

/-- *bi* 'ask' — object control (ex 59: 'I asked Ayele to tell me a story'). -/
def bi : Verb where
  form := "bi"
  frames := [niFrame]
  readings := [niReading .objectControl]

/-- *kɛɛ* 'say, tell' — the paper's utterance-verb exemplar with a finite
    `akɛ`-clause (exx 47–49: *Jojo kɛɛ akɛ …* 'Jojo said that …'), and object
    control in the `ni`-frame, 'tell someone to' (ex 117b: *John é-kee-ee Mary
    ni é he noko-noko* 'John didn't tell Mary to buy anything'). -/
def kee : Verb where
  form := "kɛɛ"
  frames := [Frame.finiteClause, niFrame]
  readings := [akeReading, niReading .objectControl]
  speechActVerb := true

/-! ### Finite complements only -/

/-- *le* 'know' — a finite `kɛji`-clause for if/whether complements (exx 104,
    108: 'know if they will be coming', 'know whether you or he bought the
    book'). -/
def le : Verb where
  form := "le"
  frames := [kejiFrame]
  attitude := some (.doxastic .veridical)

/-- The clause-embedding verbs attested in the paper's examples. -/
def verbs : List Verb :=
  [tao, sumo, hiekano, hiekpano, miamihie, kai, nye, kpleno, kpang, kpagbe, dweng,
   wa, kenya, dai, laka, bi, kee, le]

end Ga
