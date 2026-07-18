import Linglib.Data.UD.Basic
import Linglib.Features.Complementation
import Linglib.Morphology.RelevanceHierarchy

/-!
# Compositional realization rules
[bybee-1985] [dixon-aikhenvald-2000]

A morphological realization rule pairs a form operation with the feature,
valence, and semantic effects it induces, and a stem carries the paradigm
of such rules that generate its inflected forms.

## Main definitions

- `MorphRule σ`: a rule carrying formal and semantic effects at once.
- `Stem σ`: a lexical stem with its inflectional paradigm.
- `Stem.inflect`, `Stem.allForms`: applying the paradigm.

A `MorphRule σ` transforms a stem's surface form, morphosyntactic features,
and meaning of type `σ` simultaneously. Rules where the word-level semantic
contribution is delegated to a higher composition layer (e.g., tense rules
that delegate to `Semantics/Tense/`, agreement rules that contribute no
truth-conditional meaning) carry `delegatedSemantics := true`. The Bool flag
is **not** a claim that the morpheme is meaningless — [bybee-1985] Ch 1 §3
explicitly argues against the vacuity-of-inflection position. It tracks
*where* the meaning is computed (delegate to Theory layer vs. compute at the
morphological word level), not whether meaning exists.
-/

namespace Morphology

/-- A morphological rule: carries formal AND semantic effects.

    The type parameter `σ` is the meaning type, so this works uniformly
    across `Bool`/`Frac`/`Float` semantic backends.

    Design principle: `semEffect` can be `id` for rules whose word-level
    semantic contribution is delegated to a higher composition layer
    (verb agreement `-s` carries no truth-conditional meaning at the word
    level; tense rules delegate to the intensional layer), making it
    explicit which inflections compute meaning at the word level and
    which delegate. -/
structure MorphRule (σ : Type) where
  /-- Which morphological category this rule realizes -/
  category : MorphCategory
  /-- The feature value this rule realizes -/
  value : String
  /-- How the surface form changes -/
  formRule : String → String
  /-- How morphosyntactic features change -/
  featureRule : UD.MorphFeatures → UD.MorphFeatures
  /-- How the lexical frame changes — `id` except for valency-changing
      morphology (reciprocal, passive, causative affixes; [dixon-aikhenvald-2000]),
      where the frame change is the rule's whole point. The frame is lexical,
      not UD morphology, so it is its own effect channel rather than a
      `featureRule` component. -/
  valenceRule : Option ComplementType → Option ComplementType := fun v => v
  /-- Semantic effect (`id` when meaning is delegated to a higher layer) -/
  semEffect : σ → σ
  /-- Is the word-level semantic contribution delegated to a higher
      composition layer? (Set `true` for agreement, tense, etc., where
      `Semantics/{Tense,Aspect,Modality,Agreement}/` handle
      the meaning. NOT a claim that the morpheme is meaningless —
      see file docstring.) -/
  delegatedSemantics : Bool := false

/-- A lexical stem: a root meaning plus its morphological paradigm.

    `Stem` also plays the lexeme role — the abstract lexical unit standing
    over a word's set of inflected forms (its `paradigm`), realized here as
    a lemma-plus-paradigm bundle rather than a separate `Lexeme` type. -/
structure Stem (σ : Type) where
  /-- Base form (lemma) -/
  lemma_ : String
  /-- Syntactic category -/
  cat : UD.UPOS
  /-- Base morphosyntactic features -/
  baseFeatures : UD.MorphFeatures := {}
  /-- Base lexical frame (complement selection) — lexical, beside the morphology. -/
  baseFrame : Option ComplementType := none
  /-- Available inflectional rules -/
  paradigm : List (MorphRule σ)

variable {σ : Type}

/-- Apply a morphological rule to generate an inflected form + meaning. Threads
    morphology only; a rule's `valenceRule` acts on `Stem.baseFrame` at the consumer
    that builds `Word`s. -/
def Stem.inflect (s : Stem σ) (rule : MorphRule σ) (baseMeaning : σ) :
    String × UD.MorphFeatures × σ :=
  ( rule.formRule s.lemma_
  , rule.featureRule s.baseFeatures
  , rule.semEffect baseMeaning )

/-- Generate all forms in the paradigm (base + inflected). -/
def Stem.allForms (s : Stem σ) (baseMeaning : σ) :
    List (String × UD.MorphFeatures × σ) :=
  (s.lemma_, s.baseFeatures, baseMeaning) ::
    s.paradigm.map (s.inflect · baseMeaning)

end Morphology
