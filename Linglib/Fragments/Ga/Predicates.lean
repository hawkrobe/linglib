import Linglib.Fragments.Ga.Basic
import Linglib.Phenomena.Control.Studies.Landau2015

/-!
# Gã Complement-Taking Predicates
@cite{allotey-2021}

Inventory of Gã verbs that take embedded clausal complements, classified
by the clause type they select and (where the semantic class is clear)
their @cite{landau-2015} predicate class.

All entries here are attested in @cite{allotey-2021}'s example data
(the only verb-list source). The single exception is `kee` 'say', which
the paper uses in passing as the standard `akɛ`-clause exemplar but
does not pull out as part of its CTP inventory; it is kept because
without at least one finite-complement verb the OC-vs-non-OC contrast
cannot be exhibited end-to-end. The docstring on `kee` records this.

## Coverage

- Subject-control verbs selecting irrealis `ni`-clauses: `tao` 'want',
  `nye` 'manage/be.able', `kpleno` 'agree', `kpang` 'plan',
  `hiekpano` 'forget' (Allotey ex 37–38)
- Object-control verbs selecting irrealis `ni`-clauses: `kenya` 'urge',
  `dai` 'force', `laka` 'persuade', `wa` 'help'
- Finite-clause verb selecting `akɛ`-clauses: `kee` 'say' (standard
  exemplar; see note above)

## Identifier policy

ASCII identifiers; IPA orthography lives in `.form` strings.
See `Fragments/Ga/Basic.lean` for rationale.
-/

namespace Fragments.Ga

open Landau2015 (LandauPredicateClass ControlTier)

/-- Whether a Gã CTP induces subject control or object control over the
    embedded `ni`-clause subject. `none` for finite-complement verbs
    that are not control verbs. -/
inductive Control where
  | subjectControl
  | objectControl
  | noneControl
  deriving DecidableEq, Repr

/-- A Gã complement-taking predicate.

    The Landau predicate class is recorded for verbs whose semantic
    classification is clear; for verbs like `wa` 'help' (no clean fit
    in any of Landau's eight classes), it is left as `none` —
    paralleling the treatment of English `try` in
    `Landau2015.try_unclassifiable`. -/
structure CTP where
  form         : String
  gloss        : String
  selects      : EmbeddedClauseType
  control      : Control
  landauClass  : Option LandauPredicateClass
  deriving Repr, DecidableEq

/-- The control tier induced by a Gã CTP, derived from its Landau class.
    Returns `none` for unclassifiable verbs and finite-complement verbs. -/
def CTP.controlTier (c : CTP) : Option ControlTier :=
  c.landauClass.map (·.controlTier)

-- ════════════════════════════════════════════════════════════════
-- § 1: Subject-Control Verbs (irrealis `ni`-clause)
-- ════════════════════════════════════════════════════════════════

/-- 'want' — desiderative, subject control. Logophoric tier. -/
def tao : CTP :=
  ⟨"tao", "want", .irrealisNi, .subjectControl, some .desiderative⟩

/-- 'agree' — desiderative, subject control. Logophoric tier. -/
def kpleno : CTP :=
  ⟨"kplɛnɔ", "agree", .irrealisNi, .subjectControl, some .desiderative⟩

/-- 'plan' — desiderative, subject control. Logophoric tier. -/
def kpang : CTP :=
  ⟨"kpaŋ", "plan", .irrealisNi, .subjectControl, some .desiderative⟩

/-- 'forget' — implicative (negative), subject control. Predicative tier.
    Allotey ex 37–38: *e-hiɛ-kpa-nɔ akɛ è-fee shi̇kpɔ̃ɔ̃ lε* 'he forgot
    to do that work'. Like English `forget` (@cite{karttunen-1971}):
    failure entails the complement. -/
def hiekpano : CTP :=
  ⟨"hiɛ-kpa-nɔ", "forget", .irrealisNi, .subjectControl, some .implicative⟩

/-- 'manage / be able to' — implicative (modal-flavored), subject control.
    Predicative tier. Allotey treats it as a modal/implicative verb;
    the semantics parallels English `manage`. -/
def nye : CTP :=
  ⟨"nyɛ", "manage", .irrealisNi, .subjectControl, some .implicative⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Object-Control Verbs (irrealis `ni`-clause)
-- ════════════════════════════════════════════════════════════════

/-- 'urge' — desiderative, object control. Logophoric tier. -/
def kenya : CTP :=
  ⟨"kenya", "urge", .irrealisNi, .objectControl, some .desiderative⟩

/-- 'persuade' — desiderative, object control. Logophoric tier. -/
def laka : CTP :=
  ⟨"laka", "persuade", .irrealisNi, .objectControl, some .desiderative⟩

/-- 'force' — implicative causative, object control. Predicative tier.
    Treated like English `force` per @cite{landau-2015}'s (4a):
    coercive causatives pattern as implicatives. -/
def dai : CTP :=
  ⟨"dai", "force", .irrealisNi, .objectControl, some .implicative⟩

/-- 'help' — object control. Landau class left unspecified
    (`help` does not fit any of Landau's eight classes cleanly). -/
def wa : CTP :=
  ⟨"wa", "help", .irrealisNi, .objectControl, none⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Finite-Complement Verb (`akɛ`-clause)
-- ════════════════════════════════════════════════════════════════

/-- 'say' — utterance verb, finite `akɛ`-clause.

    Not pulled out as a CTP entry by @cite{allotey-2021}, but used in
    passing as the canonical example of an `akɛ`-clause selector
    (the cross-Kwa standard utterance verb). Kept here so that the
    library can exhibit the OC-vs-non-OC contrast end-to-end. -/
def kee : CTP :=
  ⟨"kɛɛ", "say", .finiteAke, .noneControl, some .propositional⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Per-Verb Verification Theorems
-- ════════════════════════════════════════════════════════════════

-- Subject-control verbs select irrealis `ni`-clauses.
theorem tao_irrealisNi      : tao.selects      = .irrealisNi := rfl
theorem hiekpano_irrealisNi : hiekpano.selects = .irrealisNi := rfl
theorem nye_irrealisNi      : nye.selects      = .irrealisNi := rfl
theorem kpleno_irrealisNi   : kpleno.selects   = .irrealisNi := rfl
theorem kpang_irrealisNi    : kpang.selects    = .irrealisNi := rfl

-- Object-control verbs select irrealis `ni`-clauses.
theorem kenya_irrealisNi : kenya.selects = .irrealisNi := rfl
theorem laka_irrealisNi  : laka.selects  = .irrealisNi := rfl
theorem dai_irrealisNi   : dai.selects   = .irrealisNi := rfl
theorem wa_irrealisNi    : wa.selects    = .irrealisNi := rfl

-- Finite-complement verb selects `akɛ`-clauses.
theorem kee_finiteAke : kee.selects = .finiteAke := rfl

-- Landau control tier: implicative verbs are predicative, desiderative
-- verbs are logophoric. Direct application of `LandauPredicateClass.controlTier`.
theorem hiekpano_predicative : hiekpano.controlTier = some .predicative := rfl
theorem nye_predicative      : nye.controlTier      = some .predicative := rfl
theorem dai_predicative      : dai.controlTier      = some .predicative := rfl

theorem tao_logophoric    : tao.controlTier    = some .logophoric := rfl
theorem kpleno_logophoric : kpleno.controlTier = some .logophoric := rfl
theorem kpang_logophoric  : kpang.controlTier  = some .logophoric := rfl
theorem kenya_logophoric  : kenya.controlTier  = some .logophoric := rfl
theorem laka_logophoric   : laka.controlTier   = some .logophoric := rfl

end Fragments.Ga
