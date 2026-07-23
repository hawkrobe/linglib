import Linglib.Fragments.Ga.Basic

/-!
# Gã Complement-Taking Predicates
[allotey-2021]

Inventory of Gã verbs that take embedded clausal complements, classified
by the clause type they select and (for `ni`-clause selectors) whether
they induce subject or object control. All entries are attested in
[allotey-2021]'s example data, cited by example number. `kee` 'say' is
the standard `akɛ`-clause exemplar the paper uses throughout (exx 47–49)
rather than a member of its control-predicate inventory.

## Identifier policy

ASCII identifiers; IPA orthography lives in `.form` strings.
See `Fragments/Ga/Basic.lean` for rationale.
-/

namespace Ga

/-- Which matrix argument controls the embedded `ni`-clause subject. -/
inductive Control where
  | subject
  | object
  deriving DecidableEq, Repr

/-- A Gã complement-taking predicate: form, gloss, selected embedded
    clause type, and (for `ni`-clause selectors) its control type;
    `none` for finite-complement verbs that are not control verbs. -/
structure CTP where
  form    : String
  gloss   : String
  selects : EmbeddedClauseType
  control : Option Control
  deriving Repr, DecidableEq

/-! ### Subject-control verbs (irrealis `ni`-clause) -/

/-- 'want' — subject control; `ni` optionally overt
    ([allotey-2021] ex 34: *Mi-i tao (ni) ma na bo* 'I want to see you'). -/
def tao : CTP := ⟨"tao", "want", .irrealisNi, some .subject⟩

/-- 'hope' (lit. 'face-place-upon') — subject control; `ni` obligatory
    ([allotey-2021] ex 35: *Mi hiɛ-kã-nɔ ni ma ya skul gbi ko*
    'I hope to go to school one day'). -/
def hiekano : CTP := ⟨"hiɛ-kã-nɔ", "hope", .irrealisNi, some .subject⟩

/-- 'forget' (lit. 'face-stop-upon') — subject control; `ni` obligatory
    ([allotey-2021] exx 37–38: *O hiɛ-kpa-nɔ ni o kɔ aspaatere lɛ*
    'You forgot to pick up the shoe'). -/
def hiekpano : CTP := ⟨"hiɛ-kpa-nɔ", "forget", .irrealisNi, some .subject⟩

/-- 'try' (lit. 'squeeze-my-face') — subject control; `ni` obligatory
    ([allotey-2021] ex 36: 'I tried to close the door'). -/
def miamihie : CTP := ⟨"mia-mi-hiɛ", "try", .irrealisNi, some .subject⟩

/-- 'remember' — subject control ([allotey-2021] ex 43: *Mi kai ni ma he
    wolo* 'I remembered to buy a book'). With `akɛ` instead of `ni` the
    complement is finite 'remember that' (ex 89a); implicative in the
    control use, so the embedded irrealis marker is suppressed
    (*mi*, not *má*; the paper's §5.2.3 asymmetry). -/
def kai : CTP := ⟨"kai", "remember", .irrealisNi, some .subject⟩

/-- 'manage / be able to' — subject control; `ni` optionally overt
    ([allotey-2021] ex 39: 'The children managed to buy a home').
    Implicative like `kai`: the embedded irrealis marker is suppressed
    (ex 89b *mi/\*má*). -/
def nye : CTP := ⟨"nyɛ", "manage", .irrealisNi, some .subject⟩

/-- 'agree' — subject control ([allotey-2021] ex 52; ex 89c shows the
    embedded irrealis marker obligatory: *\*mi/má*). With `akɛ` it takes
    a finite subjunctive complement instead ('agree that…', ex 105). -/
def kpleno : CTP := ⟨"kplɛnɔ", "agree", .irrealisNi, some .subject⟩

/-- 'plan / decide' — subject control ([allotey-2021] exx 89d, 106; the
    embedded irrealis marker is obligatory, and only `ni` — never `akɛ`
    or `kɛji` — introduces the complement). -/
def kpang : CTP := ⟨"kpaŋ", "plan", .irrealisNi, some .subject⟩

/-! ### Object-control verbs (irrealis `ni`-clause) -/

/-- 'help' — object control ([allotey-2021] ex 54: *Mi wa Ama ni e-ya
    skul* 'I helped Ama to go to school'). -/
def wa : CTP := ⟨"wa", "help", .irrealisNi, some .object⟩

/-- 'urge / encourage' — object control ([allotey-2021] ex 55). -/
def kenya : CTP := ⟨"kenya", "urge", .irrealisNi, some .object⟩

/-- 'force' — object control ([allotey-2021] ex 56). -/
def dai : CTP := ⟨"dai", "force", .irrealisNi, some .object⟩

/-- 'persuade / coax / deceive' (context-dependent, the paper's fn 4) —
    object control ([allotey-2021] exx 57–58). -/
def laka : CTP := ⟨"laka", "persuade", .irrealisNi, some .object⟩

/-- 'ask' — object control ([allotey-2021] ex 59: 'I asked Ayele to
    tell me a story'). -/
def bi : CTP := ⟨"bi", "ask", .irrealisNi, some .object⟩

/-! ### Finite-complement verbs (`akɛ`- and `kɛji`-clauses) -/

/-- 'say' — utterance verb, finite `akɛ`-clause ([allotey-2021]
    exx 47–49: *Jojo kɛɛ akɛ …* 'Jojo said that …'). -/
def kee : CTP := ⟨"kɛɛ", "say", .finiteAke, none⟩

/-- 'know' — selects a finite `kɛji`-clause for if/whether complements
    ([allotey-2021] exx 104, 108: 'know if they will be coming',
    'doesn't know whether you or he bought the book'). -/
def le : CTP := ⟨"le", "know", .finiteKeji, none⟩

end Ga
