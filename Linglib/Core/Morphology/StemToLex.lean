import Linglib.Core.Morphology.MorphRule
import Linglib.Theories.Semantics.Compositional.Core.Lexicon

/-!
# Stem-to-Lexicon Bridge

Connects morphological stems (`Core.Morphology.Stem`) to semantic lexical
entries (`TruthConditional.Core.SemLexEntry`). A `SemStem` pairs a
morphological paradigm with a Montague-style type and base denotation;
`SemStem.allEntries` auto-generates one `SemLexEntry` per paradigm cell.

This replaces the pattern of manually duplicating `SemLexEntry` values
for each inflected form (e.g., `student_entry` and `students_entry`
sharing `student_sem`).
-/

namespace Core.Morphology

open TruthConditional.Core (SemLexEntry ScaleMembership)
open TruthConditional (Model Ty)

/-- A semantic stem: pairs morphological structure with Montague-style
    type and denotation. This is what researchers define in fragments.

    The semantic type `ty` determines the meaning type via `m.interpTy ty`;
    `morph.paradigm` lists the morphological rules whose `semEffect`
    operates on values of that type. -/
structure SemStem (m : Model) where
  /-- Semantic type -/
  ty : Ty
  /-- Morphological structure -/
  morph : Stem (m.interpTy ty)
  /-- Base denotation -/
  baseDenot : m.interpTy ty
  /-- Scale membership (inherited by all inflected forms) -/
  scaleMembership : Option ScaleMembership := none

/-- Generate a `SemLexEntry` from a `SemStem` by applying a `MorphRule`.

    This is the key function: it takes a stem and a morphological rule
    and produces a fully specified lexical entry with the correct
    surface form, features, type, AND denotation. -/
def SemStem.inflect {m : Model} (s : SemStem m) (rule : MorphRule (m.interpTy s.ty)) :
    SemLexEntry m :=
  { word := { form := rule.formRule s.morph.lemma_
            , cat := s.morph.cat
            , features := rule.featureRule s.morph.baseFeatures }
  , ty := s.ty
  , denot := rule.semEffect s.baseDenot
  , scaleMembership := s.scaleMembership }

/-- Generate the base (uninflected) `SemLexEntry`. -/
def SemStem.base {m : Model} (s : SemStem m) : SemLexEntry m :=
  { word := { form := s.morph.lemma_
            , cat := s.morph.cat
            , features := s.morph.baseFeatures }
  , ty := s.ty
  , denot := s.baseDenot
  , scaleMembership := s.scaleMembership }

/-- Generate all `SemLexEntry` values in the paradigm. -/
def SemStem.allEntries {m : Model} (s : SemStem m) : List (SemLexEntry m) :=
  s.base :: s.morph.paradigm.map s.inflect

/-- Build a `SemLexicon` from a list of `SemStem`s (auto-expanding paradigms). -/
def buildLexicon (m : Model) (stems : List (SemStem m)) : TruthConditional.Core.SemLexicon m :=
  λ form =>
    stems.findSome? λ stem =>
      (stem.allEntries).find? λ entry => entry.word.form == form

end Core.Morphology
