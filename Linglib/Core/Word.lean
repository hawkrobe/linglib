import Linglib.Core.UD

/-!
# Word

The lexical unit and its building blocks: morphological feature types (aliased
to Universal Dependencies), the `Features` bundle, and the `Word` structure.

## Universal Dependencies Integration

Morphological features are aliased to UD types:
- `Number` = `UD.Number` (with compatibility constructors `sg`, `pl`)
- `Person` = `UD.Person` (with compatibility constructors `first`, `second`, `third`)
- `Case` = `UD.Case` (with compatibility constructors `nom`, `acc`, `gen`)
- `Voice` = `UD.Voice` (with compatibility constructors `active`, `passive`)
- `VForm` = `UD.VerbForm` (with compatibility constructors)

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
abbrev sg : Number := .Sing
/-- Plural (compatibility alias for UD.Number.Plur) -/
abbrev pl : Number := .Plur
end Number

/-- Grammatical person. Aliased to UD.Person for cross-linguistic compatibility.

    Constructors are: `.first`, `.second`, `.third`, `.zero`
    (no compatibility aliases needed - names match) -/
abbrev Person := UD.Person

/-- Grammatical case. Aliased to UD.Case for cross-linguistic compatibility. -/
abbrev Case := UD.Case

namespace Case
/-- Nominative (compatibility alias) -/
abbrev nom : Case := .Nom
/-- Accusative (compatibility alias) -/
abbrev acc : Case := .Acc
/-- Genitive (compatibility alias) -/
abbrev gen : Case := .Gen
end Case

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

/-- Transitivity / argument structure. No direct UD equivalent. -/
inductive Valence where
  | intransitive  -- sleep, arrive
  | transitive    -- see, eat
  | ditransitive  -- give, send (double object)
  | dative        -- give X to Y (prepositional dative)
  | locative      -- put X on Y
  | copular       -- be (takes predicate)
  | clausal       -- manage to VP, believe that S (xcomp/ccomp complement)
  deriving Repr, DecidableEq, Inhabited

/-- Head direction of a syntactic construction.
    Used for word-order typology (Dryer 1992, Greenberg 1963) and
    constraints like FOFC (Biberauer, Holmberg & Roberts 2014). -/
inductive HeadDirection where
  | headInitial  -- head precedes complement (VO, preposition, head-initial FocP, ...)
  | headFinal    -- head follows complement (OV, postposition, head-final FocP, ...)
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Feature Bundle and Word
-- ============================================================================

/-- Feature bundle for words. Uses aliased UD types. -/
structure Features where
  wh : Bool := false
  finite : Bool := true
  number : Option Number := none
  person : Option Person := none
  case_ : Option Case := none
  valence : Option Valence := none
  voice : Option Voice := none
  vform : Option VForm := none
  tense : Option Tense := none
  countable : Option Bool := none  -- for count vs mass nouns
  deriving Repr, DecidableEq

/-- A word: form + category + features. -/
structure Word where
  form : String
  cat : UD.UPOS
  features : Features := {}
  deriving Repr

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := ⟨form, cat, {}⟩

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
