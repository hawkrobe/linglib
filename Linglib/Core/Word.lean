import Linglib.Core.UD
import Linglib.Core.Valence

/-!
# Word
[biberauer-roberts-2014] [dryer-1992]

The lexical unit and its building blocks: morphological feature types (aliased
to Universal Dependencies), the `Features` bundle, and the `Word` structure.

## Provenance

Lifted from `Core/Lexical/Word.lean` in the cleanup that dissolved
`Core/Lexical/`. Every layer (Fragments, Phenomena, Theories, Features,
Typology) consumes `Word`; the broad consumer base is the strongest case
for keeping it in `Core/`.

## Universal Dependencies Integration

Morphological features are aliased to UD types:
- `Number` = `UD.Number` (with compatibility constructors `sg`, `pl`)
- `Person` = `UD.Person` (with compatibility constructors `first`, `second`, `third`)
- `Voice` = `UD.Voice` (with compatibility constructors `active`, `passive`)
- `VForm` = `UD.VerbForm` (with compatibility constructors)

The grammatical-case substrate lives separately at `Linglib/Features/Case.lean`.

Syntactic categories use `UD.UPOS` directly (the 17 universal POS tags).

Types without UD equivalents remain defined here:
- `Valence` (argument structure)
- `HeadDirection` (word-order typology)
-/

-- ============================================================================
-- Aliased Types (backed by UD)
-- ============================================================================

/-- Grammatical number. Aliased to UD.Number for cross-linguistic compatibility. -/
abbrev Number := UD.Number

namespace Number
/-- Singular (compatibility alias for UD.Number.Sing) -/
@[match_pattern] abbrev sg : Number := .Sing
/-- Plural (compatibility alias for UD.Number.Plur) -/
@[match_pattern] abbrev pl : Number := .Plur
/-- Dual (compatibility alias for UD.Number.Dual). Used for lexical
items that morphologically restrict to two-atom domains
(e.g. English `both`/`neither`, Slovenian dual, Icelandic `hvor`). -/
@[match_pattern] abbrev du : Number := .Dual
end Number

/-- Grammatical person. Aliased to UD.Person for cross-linguistic compatibility.

    Constructors are: `.first`, `.second`, `.third`, `.zero`
    (no compatibility aliases needed - names match) -/
abbrev Person := UD.Person

/-- Voice: active vs passive. Aliased to UD.Voice. -/
abbrev Voice := UD.Voice

namespace Voice
/-- Active voice (compatibility alias) -/
abbrev active : Voice := .Act
/-- Passive voice (compatibility alias) -/
abbrev passive : Voice := .Pass
end Voice

/-- Verb form. Aliased to UD.VerbForm. -/
abbrev VForm := UD.VerbForm

namespace VForm
/-- Finite (compatibility alias) -/
abbrev finite : VForm := .Fin
/-- Infinitive (compatibility alias) -/
abbrev infinitive : VForm := .Inf
/-- Past participle (compatibility alias - maps to Part) -/
abbrev pastParticiple : VForm := .Part
/-- Present participle (compatibility alias - maps to Part) -/
abbrev presParticiple : VForm := .Part
end VForm

/-- Tense. Aliased to UD.Tense. -/
abbrev Tense := UD.Tense

namespace Tense
/-- Past tense (compatibility alias) -/
abbrev past : Tense := .Past
/-- Present tense (compatibility alias) -/
abbrev present : Tense := .Pres
/-- Future tense (compatibility alias) -/
abbrev future : Tense := .Fut
end Tense

-- ============================================================================
-- Types Without UD Equivalents
-- ============================================================================

/-- Morphosyntactic mass/count feature. No direct UD equivalent.

    A formal feature parallel to grammatical gender — not an ontological
    distinction. Determines kind-anaphor morphology: [MASS] → *it*,
    [COUNT] → *they*. Evidence: *pollen*[MASS] → *it* vs
    *pollen grains*[COUNT] → *they* for the same referent
    ([krifka-2026] §2). -/
inductive MassCount where
  | mass   -- mass nouns: *mold*, *pollen*, *milk*, *gold*
  | count  -- count nouns: *spider*, *pollen grain*, *dog*, *cup*
  deriving Repr, DecidableEq, Hashable

/-- Head direction of a syntactic construction.
    Used for word-order typology and
    constraints like FOFC. -/
inductive HeadDirection where
  | headInitial  -- head precedes complement (VO, preposition, head-initial FocP, ...)
  | headFinal    -- head follows complement (OV, postposition, head-final FocP, ...)
  deriving Repr, DecidableEq

-- ============================================================================
-- Feature Bundle and Word
-- ============================================================================

/-- Feature bundle for words. Uses aliased UD types. -/
structure Features where
  wh : Bool := false
  finite : Bool := true
  number : Option Number := none
  person : Option Person := none
  case_ : Option UD.Case := none
  /-- Grammatical gender (UD.Gender). Carried on the word so φ-agreement is
      feature-based, not recovered from surface form. -/
  gender : Option UD.Gender := none
  valence : Option Valence := none
  voice : Option Voice := none
  vform : Option VForm := none
  tense : Option Tense := none
  countable : Option MassCount := none  -- for count vs mass nouns
  /-- Pronoun type (UD `PronType`: personal, reciprocal, interrogative, …). Carried
      so a pro-form's binding class is read off its own morphology, not its surface form. -/
  pronType : Option UD.PronType := none
  /-- Reflexive morphology (UD `Reflex=Yes`). The one binding-relevant feature `PronType`
      does not encode; distinguishes a reflexive anaphor from a plain personal pronoun. -/
  reflex : Bool := false
  deriving Repr, DecidableEq

/-- A word: form + category + features. -/
structure Word where
  form : String
  cat : UD.UPOS
  features : Features := {}
  deriving Repr

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := ⟨form, cat, {}⟩

/-- The φ-feature subset (person, number, gender) of a word, as a
    `UD.MorphFeatures` bundle. -/
def Word.phi (w : Word) : UD.MorphFeatures :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

/-- φ-agreement between two words: their person/number/gender features are
    compatible (an unspecified feature is a wildcard). A reflexive, symmetric
    *tolerance* relation on `Word` (not transitive), decided by the shared
    `UD.MorphFeatures.compatible`. This is the feature-based agreement primitive
    binding and concord consumers share — no surface-form gender lookup. -/
def Word.Agree (w1 w2 : Word) : Prop := w1.phi.compatible w2.phi

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Word.Agree; infer_instance

@[refl] theorem Word.Agree.refl (w : Word) : Word.Agree w w :=
  UD.MorphFeatures.compatible_self w.phi


/-- Derive a passive variant: sets voice to passive, valence to intransitive.
    Used to compose with `VerbEntry.toWordPastPart` for passive constructions. -/
def Word.asPassive (w : Word) : Word :=
  { w with features := { w.features with
      valence := some .intransitive, voice := some Voice.passive } }

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string. -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))
