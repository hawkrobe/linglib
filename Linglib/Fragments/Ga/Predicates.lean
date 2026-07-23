import Linglib.Fragments.Ga.Basic

/-!
# Gã Complement-Taking Predicates
[allotey-2021]

Inventory of Gã verbs that take embedded clausal complements, classified
by the clause type they select and (for `ni`-clause selectors) whether
they induce subject or object control.

Entries attested in the accessible portion of [allotey-2021] are cited
by example number (*tao* 'want' ex 2a, *hiɛ-ka-nɔ* 'hope' ex 16); the
remaining entries are UNVERIFIED against the paper's own verb list
(its complement-selection sections are not in the available galley) and
are flagged in their docstrings. `kee` 'say' is the standard `akɛ`-clause
exemplar the paper uses in passing rather than a member of its CTP
inventory; it is kept because without at least one finite-complement
verb the OC-vs-non-OC contrast cannot be exhibited end-to-end.

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
    ([allotey-2021] ex 2a: *Mi tao (ni) ma na bo* 'I want to see you'). -/
def tao : CTP := ⟨"tao", "want", .irrealisNi, some .subject⟩

/-- 'hope' (lit. 'face-place-upon') — subject control; `ni` obligatory
    ([allotey-2021] ex 16: *Mi hiɛ-ka-nɔ ni ma ya skul gbi ko*
    'I hope to go to school one day'). -/
def hiekano : CTP := ⟨"hiɛ-ka-nɔ", "hope", .irrealisNi, some .subject⟩

/-- 'manage / be able to' — subject control.
    UNVERIFIED against [allotey-2021]'s verb list. -/
def nye : CTP := ⟨"nyɛ", "manage", .irrealisNi, some .subject⟩

/-- 'agree' — subject control. UNVERIFIED against [allotey-2021]'s verb list. -/
def kpleno : CTP := ⟨"kplɛnɔ", "agree", .irrealisNi, some .subject⟩

/-- 'plan' — subject control. UNVERIFIED against [allotey-2021]'s verb list. -/
def kpang : CTP := ⟨"kpaŋ", "plan", .irrealisNi, some .subject⟩

/-! ### Object-control verbs (irrealis `ni`-clause) -/

/-- 'urge' — object control. UNVERIFIED against [allotey-2021]'s verb list. -/
def kenya : CTP := ⟨"kenya", "urge", .irrealisNi, some .object⟩

/-- 'persuade' — object control. UNVERIFIED against [allotey-2021]'s verb list. -/
def laka : CTP := ⟨"laka", "persuade", .irrealisNi, some .object⟩

/-- 'force' — object control. UNVERIFIED against [allotey-2021]'s verb list. -/
def dai : CTP := ⟨"dai", "force", .irrealisNi, some .object⟩

/-- 'help' — object control. UNVERIFIED against [allotey-2021]'s verb list
    (Gã 'help' is commonly *bua*; *wa* is 'be strong/hard'). -/
def wa : CTP := ⟨"wa", "help", .irrealisNi, some .object⟩

/-! ### Finite-complement verb (`akɛ`-clause) -/

/-- 'say' — utterance verb, finite `akɛ`-clause.

    Not part of [allotey-2021]'s CTP inventory, but used in passing as
    the canonical `akɛ`-clause selector (the cross-Kwa standard
    utterance verb). Kept so the library can exhibit the OC-vs-non-OC
    contrast end-to-end. -/
def kee : CTP := ⟨"kɛɛ", "say", .finiteAke, none⟩

end Ga
