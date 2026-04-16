import Linglib.Theories.Morphology.DegreeContainment
import Linglib.Theories.Morphology.Core.Exponence
import Linglib.Theories.Semantics.Degree.Superlative
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

namespace Phenomena.Comparison.Studies.Bobaljik2012

open Morphology.DegreeContainment
open Fragments.English.Modifiers.Adjectives

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
    allEntries.all (λ e => e.suppletion.isContiguous) = true := by native_decide

/-- CSG Part I applied to English data: "good" and "bad" have
    suppletive comparatives, so by `csg_part1` their superlatives
    must be suppletive too — and they are. -/
theorem good_csg : good.suppletion.sprlSuppletive = true :=
  csg_part1 good.suppletion (by native_decide) (by native_decide)

theorem bad_csg : bad.suppletion.sprlSuppletive = true :=
  csg_part1 bad.suppletion (by native_decide) (by native_decide)

/-- CSG Part II via VI locality: if the superlative is suppletive,
    the comparative is too. -/
theorem good_csg_part2 : good.suppletion.cmprSuppletive = true := by native_decide
theorem bad_csg_part2 : bad.suppletion.cmprSuppletive = true := by native_decide

-- ============================================================================
-- § 3: Attestedness Verification (English)
-- ============================================================================

/-- All English entries have attested root suppletion patterns
    (AAA or ABB — satisfying both contiguity and VI consistency). -/
theorem english_all_attested :
    allEntries.all (λ e => e.suppletion.isAttested) = true := by native_decide

-- ============================================================================
-- § 4: SSG (Synthetic Superlative Generalization)
-- ============================================================================

/-- **SSG** (@cite{bobaljik-2012}): If an entry has a synthetic
    superlative form, it also has a synthetic comparative form.
    No English adjective has `-est` without `-er`. -/
theorem english_ssg :
    allEntries.all (λ e =>
      !e.formSuper.isSome || e.formComp.isSome) = true := by
  native_decide

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
    allEntries.all (λ e =>
      !e.suppletion.cmprSuppletive || isSyntheticComp e) = true := by
  native_decide

-- ============================================================================
-- § 6: Lesslessness
-- ============================================================================

/-- **Lesslessness** (@cite{bobaljik-2012}): No synthetic comparative
    of inferiority exists in any language. English expresses inferiority
    periphrastically ("less tall"), never synthetically.

    We verify that no entry in the English fragment encodes a synthetic
    inferior form. -/
theorem english_no_synthetic_inferior :
    allEntries.all (λ e =>
      match e.formComp with
      | some f => !f.startsWith "less "
      | none => true) = true := by native_decide

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
-- § 8: Morphological Vacuity (DM Connection)
-- ============================================================================

/-- @cite{bobaljik-2012}'s containment analysis treats CMPR and SPRL
    as structural heads that trigger VI, not as semantic operators.
    Consistent with this, both degree rules in our morphology are
    semantically vacuous — compositional degree semantics is handled
    in `Semantics/Degree/`. -/
theorem comp_rule_vacuous (σ : Type) (irr : Option String) :
    (Core.Morphology.Degree.comparativeRule σ irr).isVacuous = true := rfl

theorem super_rule_vacuous (σ : Type) (irr : Option String) :
    (Core.Morphology.Degree.superlativeRule σ irr).isVacuous = true := rfl

-- ============================================================================
-- § 9: Cross-Linguistic Pattern Inventory
-- ============================================================================

/-- The three attested degree-suppletive patterns. -/
def attestedPatterns : List (String × DegreePattern) :=
  [ ("AAA (tall–taller–tallest)",       aaa)
  , ("ABB (good–better–best)",          abb)
  , ("ABC (bonus–melior–optimus)",      abc) ]

/-- All attested patterns are contiguous. -/
theorem attested_all_contiguous :
    attestedPatterns.all (λ ⟨_, p⟩ => p.isContiguous) = true := by native_decide

/-- The unattested *ABA pattern is not contiguous. -/
theorem aba_unattested :
    aba.isContiguous = false := by native_decide

-- ============================================================================
-- § 10: Cross-Linguistic Verification (Latin)
-- ============================================================================

open Fragments.Latin.Adjectives in
/-- **Latin CSG**: All Latin adjective entries satisfy contiguity. -/
theorem latin_no_aba :
    Fragments.Latin.Adjectives.allEntries.all
      (λ e => e.suppletion.isContiguous) = true := by native_decide

open Fragments.Latin.Adjectives in
/-- Latin *bonus – melior – optimus* derives ABC. -/
theorem latin_bonus_abc : bonus.suppletion = abc := rfl

open Fragments.Latin.Adjectives in
/-- Latin exhibits all three attested patterns (AAA, ABB, ABC),
    confirming the cross-linguistic pattern inventory against a
    language with richer suppletion than English. -/
theorem latin_all_three_patterns :
    Fragments.Latin.Adjectives.allEntries.any (λ e => e.suppletion == aaa) = true ∧
    Fragments.Latin.Adjectives.allEntries.any (λ e => e.suppletion == abb) = true ∧
    Fragments.Latin.Adjectives.allEntries.any (λ e => e.suppletion == abc) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § 11: Generic Containment Bridge
-- ============================================================================

/-- The English CSG verification is an instance of the generic
    contiguity predicate from `Containment.lean`: each entry's
    suppletion pattern, when converted to a list, satisfies
    the domain-independent `isContiguous`. -/
theorem english_generic_contiguity :
    allEntries.all (λ e =>
      Morphology.Containment.isContiguous
        [e.suppletion.pos, e.suppletion.cmpr, e.suppletion.sprl]) = true := by
  native_decide

end Phenomena.Comparison.Studies.Bobaljik2012
