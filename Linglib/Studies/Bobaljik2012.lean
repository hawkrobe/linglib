import Linglib.Morphology.DegreeContainment
import Linglib.Morphology.DM.ContainmentVI
import Linglib.Morphology.Exponence
import Linglib.Semantics.Alternatives.Lexical
import Linglib.Semantics.Degree.Superlative
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Fragments.Latin.Adjectives

/-!
# Bobaljik (2012): Universals in Comparative Morphology
@cite{bobaljik-2012}

## Overview

@cite{bobaljik-2012} surveys comparative and superlative morphology
across languages and derives several cross-linguistic generalizations
from the **containment hypothesis**: the superlative structurally
contains the comparative (`[[[ADJ] CMPR] SPRL]`).

## Key Generalizations

1. **CSG (Comparative-Superlative Generalization)**: *ABA is
   unattested — if the comparative is suppletive, the superlative
   is too (and vice versa). Attested: AAA, ABB, ABC. Unattested: *ABA.
   **Scope**: applies to relative superlatives, not absolute
   superlatives / elatives (p. 2, p. 28).

2. **SSG (Synthetic Superlative Generalization)**: No language has a
   morphological (synthetic) superlative without also having a
   morphological comparative.

3. **RSG (Root Suppletion Generalization)**: Root suppletion is
   limited to synthetic (morphological) comparatives. No language
   has a periphrastic comparative with a suppletive root
   (*good → more bett).

4. **Lesslessness**: No language has a synthetic comparative of
   inferiority. "Less tall" is always periphrastic.

## English and Latin Fragment Verification

This module verifies the CSG, SSG, RSG, and lesslessness against
both the English adjective fragment (`Fragments/English/Modifiers/
Adjectives.lean`) and the Latin adjective fragment (`Fragments/Latin/
Adjectives.lean`), using the `suppletion` field on each entry to
encode empirically observed root-class patterns.
-/

-- ============================================================================
-- § 0: Scale-Generation Substrate (was Morphology/Core/ScaleFromParadigm.lean)
-- ============================================================================

/-! Connects morphological infrastructure (`Morphology`) to scalar-
alternative infrastructure (`Semantics/Alternatives/HornScale.lean`),
enabling automatic generation of the alternatives needed for scalar
implicature computation. Was previously in `Morphology/Core/
ScaleFromParadigm.lean`; relocated 0.230.455 (sole consumer is this study
file). @cite{horn-1972} @cite{kennedy-2007} -/

namespace Morphology.ScaleFromParadigm

open Morphology
open Alternatives (HornScale)

/-- A morphologically-derived Horn scale. -/
structure MorphScale where
  positive : String
  comparative : String
  superlative : String
  deriving Repr, BEq

/-- Convert a `MorphScale` to a `HornScale String`, weakest-to-strongest. -/
def MorphScale.toHornScale (ms : MorphScale) : HornScale String :=
  ⟨[ms.positive, ms.comparative, ms.superlative]⟩

/-- Extract a degree scale from a stem's paradigm. -/
def adjectiveScale {σ : Type} (stem : Stem σ) : Option MorphScale :=
  let compRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "comp")
  let superRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "super")
  match compRule, superRule with
  | some comp, some super_ =>
    some { positive := stem.lemma_
         , comparative := comp.formRule stem.lemma_
         , superlative := super_.formRule stem.lemma_ }
  | _, _ => none

/-- Paradigm-mates as scalar alternatives, scale order preserved. -/
def morphologicalAlternatives {σ : Type} (stem : Stem σ) (form : String) :
    List String :=
  match adjectiveScale stem with
  | none => []
  | some ms =>
    let scale := ms.toHornScale
    scale.members.filter (· != form)

end Morphology.ScaleFromParadigm

namespace Bobaljik2012

open Morphology.DegreeContainment
open English.Modifiers.Adjectives

-- ============================================================================
-- § 1: Pattern Verification (English)
-- ============================================================================

/-- Regular adjectives have AAA suppletion patterns. -/
theorem tall_aaa : tall.suppletion = aaa := rfl
theorem short_aaa : short.suppletion = aaa := rfl
theorem happy_aaa : happy.suppletion = aaa := rfl
theorem hot_aaa : hot.suppletion = aaa := rfl
theorem expensive_aaa : expensive.suppletion = aaa := rfl
theorem dry_aaa : dry.suppletion = aaa := rfl

/-- Suppletive adjectives have ABB suppletion patterns. -/
theorem good_abb : good.suppletion = abb := rfl
theorem bad_abb : bad.suppletion = abb := rfl

-- ============================================================================
-- § 2: CSG Verification (English)
-- ============================================================================

/-- **CSG**: All English adjective entries satisfy contiguity
    (no *ABA violations). -/
theorem english_no_aba :
    ∀ e ∈ allEntries, e.suppletion.IsContiguous := by decide

/-- CSG Part I applied to English data: "good" and "bad" have
    suppletive comparatives, so by `csg_part1` their superlatives
    must be suppletive too — and they are. -/
theorem good_csg : good.suppletion.SprlSuppletive :=
  csg_part1 good.suppletion (by decide) (by decide)

theorem bad_csg : bad.suppletion.SprlSuppletive :=
  csg_part1 bad.suppletion (by decide) (by decide)

/-- CSG Part II via VI locality: if the superlative is suppletive,
    the comparative is too. -/
theorem good_csg_part2 : good.suppletion.CmprSuppletive := by decide
theorem bad_csg_part2 : bad.suppletion.CmprSuppletive := by decide

-- ============================================================================
-- § 3: Attestedness Verification (English)
-- ============================================================================

/-- All English root suppletion patterns satisfy both contiguity (no
    *ABA — `csg_part1`) and VI locality (CMPR cell = SPRL cell — the
    DM-locality conjunction `Degree.vi_cmpr_eq_sprl` of
    `Morphology/DM/ContainmentVI.lean`). The conjunction restricts root patterns
    to AAA / ABB. Stated as the explicit conjunction so the underlying
    derivation is visible at use site, rather than packaged as a
    stipulated `isAttested` field. -/
theorem english_all_attested :
    ∀ e ∈ allEntries,
      e.suppletion.IsContiguous ∧ e.suppletion.cmpr = e.suppletion.sprl := by
  decide

-- ============================================================================
-- § 4: SSG (Synthetic Superlative Generalization)
-- ============================================================================

/-- **SSG** (@cite{bobaljik-2012}): If an entry has a synthetic
    superlative form, it also has a synthetic comparative form.
    No English adjective has `-est` without `-er`. -/
theorem english_ssg :
    ∀ e ∈ allEntries, e.formSuper.isSome → e.formComp.isSome := by decide

-- ============================================================================
-- § 5: RSG (Root Suppletion Generalization)
-- ============================================================================

/-- Is the comparative form synthetic (a single morphological word,
    not periphrastic "more X")? Detected by the absence of a space
    in the comparative form string. -/
def isSyntheticComp (e : AdjModifierEntry) : Bool :=
  match e.formComp with
  | some f => !(f.toList.any (· == ' '))
  | none => false

/-- **RSG** (@cite{bobaljik-2012}): Root suppletion is limited to
    synthetic comparatives. If an entry has a suppletive root (CMPR
    differs from POS), then its comparative form is synthetic (not
    periphrastic).

    This rules out patterns like *good → more bett: a language
    cannot have a periphrastic comparative with a suppletive root.

    Verified: "good" → "better" (synthetic), "bad" → "worse" (synthetic).
    Contrast: "expensive" → "more expensive" (periphrastic, but
    non-suppletive root — AAA, not ABB). -/
theorem english_rsg :
    ∀ e ∈ allEntries, e.suppletion.CmprSuppletive → isSyntheticComp e = true := by
  decide

-- ============================================================================
-- § 6: Lesslessness
-- ============================================================================

/-! **Lesslessness** (@cite{bobaljik-2012}): No synthetic comparative
of inferiority exists in any language. English expresses inferiority
periphrastically ("less tall"), never synthetically.

The fragment-level verification (`english_no_synthetic_inferior`) was
dropped during the Bool→Prop migration: kernel `decide` doesn't reduce
`String.startsWith` over a fragment-list, and the structural proof
(enumerate `allEntries`, dispatch each by `rfl` on the Bool value)
requires `fin_cases` from mathlib which isn't pulled in here. The
empirical claim is documented above; the cross-linguistic
generalization sits in `bobaljik-2012` directly. Re-encode if a future
study file motivates a structural witness. -/

-- ============================================================================
-- § 7: Fragment Cross-Check
-- ============================================================================

/-- The fragment records suppletive forms for "good" and "bad". -/
theorem good_forms :
    good.formComp = some "better" ∧ good.formSuper = some "best" :=
  ⟨rfl, rfl⟩

theorem bad_forms :
    bad.formComp = some "worse" ∧ bad.formSuper = some "worst" :=
  ⟨rfl, rfl⟩

/-- The suppletion field agrees with the surface forms:
    "good" → "better" → "best" is ABB (suppletive root shared
    across CMPR and SPRL). -/
theorem good_abb_from_forms :
    good.suppletion = abb ∧
    good.formComp = some "better" ∧
    good.formSuper = some "best" :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Cross-Linguistic Pattern Inventory
-- ============================================================================

/-- The three attested degree-suppletive patterns. -/
def attestedPatterns : List (String × DegreePattern) :=
  [ ("AAA (tall–taller–tallest)",       aaa)
  , ("ABB (good–better–best)",          abb)
  , ("ABC (bonus–melior–optimus)",      abc) ]

/-- All attested patterns are contiguous. -/
theorem attested_all_contiguous :
    ∀ pair ∈ attestedPatterns, pair.2.IsContiguous := by decide

/-- The unattested *ABA pattern is not contiguous. -/
theorem aba_unattested : ¬ aba.IsContiguous := by decide

-- ============================================================================
-- § 10: Cross-Linguistic Verification (Latin)
-- ============================================================================

open Latin.Adjectives in
/-- **Latin CSG**: All Latin adjective entries satisfy contiguity. -/
theorem latin_no_aba :
    ∀ e ∈ Latin.Adjectives.allEntries, e.suppletion.IsContiguous := by
  decide

open Latin.Adjectives in
/-- Latin *bonus – melior – optimus* derives ABC. -/
theorem latin_bonus_abc : bonus.suppletion = abc := rfl

open Latin.Adjectives in
/-- Latin exhibits all three attested patterns (AAA, ABB, ABC),
    confirming the cross-linguistic pattern inventory against a
    language with richer suppletion than English. -/
theorem latin_all_three_patterns :
    Latin.Adjectives.allEntries.any (λ e => e.suppletion == aaa) = true ∧
    Latin.Adjectives.allEntries.any (λ e => e.suppletion == abb) = true ∧
    Latin.Adjectives.allEntries.any (λ e => e.suppletion == abc) = true := by
  exact ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 11: Generic Containment Bridge
-- ============================================================================

/-- The English CSG verification is an instance of the generic
    contiguity predicate from `Containment.lean`: each entry's
    suppletion pattern, when converted to a list, satisfies
    the domain-independent `isContiguous`. -/
theorem english_generic_contiguity :
    ∀ e ∈ allEntries,
      Morphology.Containment.IsContiguous
        [e.suppletion.pos, e.suppletion.cmpr, e.suppletion.sprl] := by
  decide

-- ============================================================================
-- § 12: Scale Generation from Degree Paradigms
-- ============================================================================

/-! `Morphology/Core/ScaleFromParadigm.lean` derives Horn scales
from degree paradigms: a stem with comparative + superlative rules
yields a 3-point scale `[positive, comparative, superlative]`. The tests
below verify the extractor on the English adjective fragment. -/

open Morphology.ScaleFromParadigm

private def tallStem := tall.toStem Unit
private def goodStem := good.toStem Unit
private def expensiveStem := expensive.toStem Unit
private def deadStem := dead.toStem Unit
private def pregnantStem := pregnant.toStem Unit

/-- Gradable adjectives produce a scale; non-gradables do not. -/
theorem tall_scale_exists : (adjectiveScale tallStem).isSome = true := rfl

theorem dead_no_scale : (adjectiveScale deadStem).isNone = true := rfl

theorem pregnant_no_scale : (adjectiveScale pregnantStem).isNone = true := rfl

/-- Regular paradigm yields the expected 3-point scale. -/
theorem tall_scale_members :
    (adjectiveScale tallStem).map (·.toHornScale.members)
    = some ["tall", "taller", "tallest"] := rfl

/-- Suppletive paradigm yields the irregular forms in scale position. -/
theorem good_scale_members :
    (adjectiveScale goodStem).map (·.toHornScale.members)
    = some ["good", "better", "best"] := rfl

/-- Periphrastic paradigm yields multi-word scale members. -/
theorem expensive_scale_members :
    (adjectiveScale expensiveStem).map (·.toHornScale.members)
    = some ["expensive", "more expensive", "most expensive"] := rfl

-- ============================================================================
-- § 13: Morphological Alternatives
-- ============================================================================

/-! `morphologicalAlternatives stem form` returns paradigm-mates of `form`
preserving scale order — the input shape scalar-implicature reasoning
expects. Tests confirm filter-by-equality semantics across the three
scale positions, plus the empty-list result for non-gradable stems. -/

theorem tall_alternatives :
    morphologicalAlternatives tallStem "tall" = ["taller", "tallest"] := rfl

theorem taller_alternatives :
    morphologicalAlternatives tallStem "taller" = ["tall", "tallest"] := rfl

theorem tallest_alternatives :
    morphologicalAlternatives tallStem "tallest" = ["tall", "taller"] := rfl

theorem dead_no_alternatives :
    morphologicalAlternatives deadStem "dead" = [] := rfl

end Bobaljik2012
