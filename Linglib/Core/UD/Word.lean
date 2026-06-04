import Linglib.Core.UD.Basic

/-!
# Word
[biberauer-roberts-2014] [dryer-1992]

The lexical unit and its building blocks: morphological feature types (aliased
to Universal Dependencies) and the `Word` structure. A word's morphology is one
`UD.MorphFeatures` bundle — there is no separate word-level feature record.

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
- `HeadDirection` (word-order typology)
-/

-- ============================================================================
-- Aliased Types (backed by UD)
-- ============================================================================

/-- Grammatical number. Aliased to UD.Number; constructors are UD's own
(`.Sing`, `.Plur`, `.Dual`, …) — there are no lowercase value aliases. -/
abbrev Number := UD.Number

/-- Grammatical person. Aliased to UD.Person; constructors are UD's own
(`.first`, `.second`, `.third`, `.zero`). -/
abbrev Person := UD.Person

/-- Voice. Aliased to UD.Voice; constructors are UD's own (`.Act`, `.Pass`, …). -/
abbrev Voice := UD.Voice

/-- Verb form. Aliased to UD.VerbForm; constructors are UD's own
(`.Fin`, `.Inf`, `.Part`, …). -/
abbrev VForm := UD.VerbForm

/-- Tense. Aliased to UD.Tense; constructors are UD's own (`.Past`, `.Pres`, `.Fut`, …). -/
abbrev Tense := UD.Tense

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
-- Word
-- ============================================================================

/-- A word: the pure CoNLL-U surface token — surface form, UD category, and UD morphology
    (one `UD.MorphFeatures` bundle; there is no separate word-level feature record).

    **Admission rule**: a property belongs on `Word` iff a Fragment-free token-level engine
    reads it off the token's *own* data; otherwise it lives on the typed lexical carrier
    (`Pronoun`, `NounEntry`, `Verb`, …) or on the consuming framework's own structures
    (e.g. DG subcategorization premises live on `DepTree.frames`, not here). Identity
    caveat: `BEq` is form + category, so homographs collapse; a CoNLL-U `lemma` field is
    the known fix, deferred until a consumer needs it. -/
structure Word where
  form : String
  cat : UD.UPOS
  features : UD.MorphFeatures := {}
  deriving Repr

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := { form := form, cat := cat }

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


/-- Derive a passive variant: sets voice to passive. The valence change
    (detransitivization) is a frame-level fact carried by the passive analysis on
    `DepTree.frames`, not token data. Composes with `VerbEntry.toWordPastPart`. -/
def Word.asPassive (w : Word) : Word :=
  { w with features := { w.features with voice := some .Pass } }

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string. -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))
