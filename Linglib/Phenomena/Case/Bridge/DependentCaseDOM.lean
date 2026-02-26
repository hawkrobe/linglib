import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Core.Prominence
import Linglib.Phenomena.Case.Typology
import Linglib.Phenomena.Case.Studies.Aissen2003

/-!
# Bridge: Dependent Case → DOM → OT Factorial Typology @cite{aissen-2003}

Connects the three layers of the case pipeline end-to-end:

1. **Dependent Case** (Marantz 1991, Baker 2015) assigns abstract Case to NPs
   by structural configuration: in accusative transitives, the object gets ACC.
2. **DOM** (Aissen 2003) determines which ACC-bearing objects receive overt
   morphological marking, conditioned by animacy and definiteness.
3. **OT Factorial Typology** (Aissen 2003, §4) constrains which DOM patterns
   are possible: only monotone (staircase) patterns survive harmonic alignment.

The end-to-end theorem: in accusative transitives, the object receives
abstract ACC regardless of its prominence (`object_always_acc`). Overt
realization then reduces entirely to the DOM filter (`overt_reduces_to_dom`).
And the OT analysis guarantees that overt marking is monotone in prominence
(`ot_pipeline_monotone`).

## The Pipeline

```
  Structural Configuration     Prominence Properties     OT Constraint Ranking
        (syntax)                  (semantics)               (morphology)
           │                          │                          │
           ▼                          ▼                          ▼
     assignCases ──►  ACC   ──►  DOMProfile.marks  ──►  only monotone
     (all objects)              (some objects overt)     patterns possible
```

## References

- Marantz, A. (1991). Case and licensing. ESCOL 1991: 234–253.
- Baker, M. (2015). Case: Its Principles and Its Parameters. CUP.
- Aissen, J. (2003). Differential Object Marking. NLLT 21(3): 435–483.
-/

namespace Phenomena.Case.Bridge.DependentCaseDOM

open Core.Prominence
open Minimalism
open Phenomena.Case.Typology
open Phenomena.Case.Studies.Aissen2003

-- ============================================================================
-- § 1: Prominence-Annotated NPs
-- ============================================================================

/-- An NP enriched with referential prominence properties.

    Structural case assignment (dependent case) is blind to these properties —
    it cares only about c-command and lexical case. DOM then consults prominence
    to decide overt realization. -/
structure ProminentNP where
  label : String
  lexicalCase : Option CaseVal
  animacy : AnimacyLevel
  definiteness : DefinitenessLevel
  deriving DecidableEq, BEq, Repr

/-- Strip prominence, yielding the NP that the case algorithm sees. -/
def ProminentNP.toNP (pnp : ProminentNP) : NPInDomain :=
  ⟨pnp.label, pnp.lexicalCase⟩

-- ============================================================================
-- § 2: Transitive Pipeline
-- ============================================================================

/-- A transitive clause: subject c-commands object. -/
structure TransClause where
  subject : ProminentNP
  object  : ProminentNP
  deriving DecidableEq, BEq, Repr

/-- Run the dependent case algorithm on a transitive clause. -/
def derivation (lang : CaseLanguageType) (tc : TransClause) : List CasedNP :=
  assignCases lang [tc.subject.toNP, tc.object.toNP]

/-- Abstract case assigned to the object. -/
def objectCase (lang : CaseLanguageType) (tc : TransClause) : Option CaseVal :=
  getCaseOf tc.object.label (derivation lang tc)

/-- Whether the object receives overt case morphology.

    Two conditions:
    1. The dependent case algorithm assigns ACC (syntax).
    2. The DOM profile marks this prominence cell (morphology). -/
def objectOvert (lang : CaseLanguageType) (dom : DOMProfile)
    (tc : TransClause) : Bool :=
  objectCase lang tc == some .acc &&
  dom.marks tc.object.animacy tc.object.definiteness

-- ============================================================================
-- § 3: Standard Transitive Template
-- ============================================================================

/-- A standard transitive clause with a fixed subject (human pronoun)
    and a variable-prominence object. Both lack lexical case. -/
def mkTrans (a : AnimacyLevel) (d : DefinitenessLevel) : TransClause :=
  { subject := ⟨"subj", none, .human, .personalPronoun⟩
    object  := ⟨"obj",  none, a, d⟩ }

-- ============================================================================
-- § 4: Layer 1 — Object Always Gets ACC
-- ============================================================================

/-- In accusative transitives, the object receives abstract ACC regardless
    of its animacy or definiteness. Dependent case is prominence-blind. -/
theorem object_always_acc :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectCase .accusative (mkTrans a d) == some CaseVal.acc)) = true := by
  native_decide

/-- The subject always gets NOM (unmarked case). -/
theorem subject_always_nom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        getCaseOf "subj" (derivation .accusative (mkTrans a d)) == some CaseVal.nom)) = true := by
  native_decide

-- ============================================================================
-- § 5: Layer 2 — Overt Marking = DOM Filter
-- ============================================================================

/-! Since the object always gets ACC, overt marking reduces entirely to the
    DOM filter. We verify this per attested language. -/

/-- Spanish: overt marking matches DOMProfile exactly. -/
theorem spanish_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative spanishDOM (mkTrans a d) =
        spanishDOM.marks a d)) = true := by native_decide

/-- Russian: overt marking matches DOMProfile exactly. -/
theorem russian_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative russianDOM (mkTrans a d) =
        russianDOM.marks a d)) = true := by native_decide

/-- Turkish: overt marking matches DOMProfile exactly. -/
theorem turkish_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative turkishDOM (mkTrans a d) =
        turkishDOM.marks a d)) = true := by native_decide

/-- Hebrew: overt marking matches DOMProfile exactly. -/
theorem hebrew_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative hebrewDOM (mkTrans a d) =
        hebrewDOM.marks a d)) = true := by native_decide

/-- Persian: overt marking matches DOMProfile exactly. -/
theorem persian_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative persianDOM (mkTrans a d) =
        persianDOM.marks a d)) = true := by native_decide

/-- Catalan: overt marking matches DOMProfile exactly. -/
theorem catalan_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative catalanDOM (mkTrans a d) =
        catalanDOM.marks a d)) = true := by native_decide

/-- Hindi: overt marking matches DOMProfile exactly. -/
theorem hindi_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative hindiDOM (mkTrans a d) =
        hindiDOM.marks a d)) = true := by native_decide

/-- No-DOM baseline: nothing overtly marked. -/
theorem nodom_overt_eq_dom :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        objectOvert .accusative noDOMProfile (mkTrans a d) =
        noDOMProfile.marks a d)) = true := by native_decide

-- ============================================================================
-- § 6: Layer 3 — OT Constrains the Pipeline
-- ============================================================================

/-- The overt marking profile produced by running the full pipeline
    (dependent case + DOM filter). -/
def overtProfile (lang : CaseLanguageType) (dom : DOMProfile) : DOMProfile :=
  { name := dom.name ++ " (pipeline)"
    marks := λ a d => objectOvert lang dom (mkTrans a d) }

/-- Every OT-predicted animacy type, run through the full pipeline,
    produces a monotone overt marking profile. -/
theorem ot_pipeline_monotone :
    animOptima.all (λ opts =>
      opts.all (λ c =>
        (overtProfile .accusative (animCandToDOM c)).isMonotone)) = true := by
  native_decide

/-- The pipeline preserves monotonicity for all attested DOM languages. -/
theorem attested_pipeline_monotone :
    allDOMProfiles.all (λ dom =>
      (overtProfile .accusative dom).isMonotone) = true := by native_decide

-- ============================================================================
-- § 7: Cross-Layer Agreement
-- ============================================================================

/-! The three layers produce consistent results: the overt marking profile
    from the pipeline agrees with the DOMProfile input, and the OT-generated
    types match the attested language profiles. -/

/-- Spanish pipeline profile agrees with the directly-defined DOMProfile. -/
theorem spanish_pipeline_agrees :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        (overtProfile .accusative spanishDOM).marks a d =
        spanishDOM.marks a d)) = true := by native_decide

/-- Russian pipeline profile agrees with the directly-defined DOMProfile. -/
theorem russian_pipeline_agrees :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        (overtProfile .accusative russianDOM).marks a d =
        russianDOM.marks a d)) = true := by native_decide

/-- Turkish pipeline profile agrees with the directly-defined DOMProfile. -/
theorem turkish_pipeline_agrees :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        (overtProfile .accusative turkishDOM).marks a d =
        turkishDOM.marks a d)) = true := by native_decide

/-- Hindi pipeline profile agrees with the directly-defined DOMProfile. -/
theorem hindi_pipeline_agrees :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        (overtProfile .accusative hindiDOM).marks a d =
        hindiDOM.marks a d)) = true := by native_decide

-- ============================================================================
-- § 8: End-to-End Summary
-- ============================================================================

/-! Summary of the end-to-end chain:

    1. `object_always_acc`:
       Dependent case assigns ACC to all objects in accusative transitives.
       Prominence is irrelevant at this layer.

    2. `*_overt_eq_dom` (7 languages):
       Since all objects get ACC, overt realization reduces to the DOM filter.
       `objectOvert = dom.marks` for every attested language.

    3. `ot_pipeline_monotone`:
       OT factorial typology generates only monotone DOMProfiles. The full
       pipeline (dependent case → DOM) inherits this monotonicity.

    4. `*_pipeline_agrees` (4 languages):
       The pipeline output exactly matches the input DOMProfile, confirming
       that the case algorithm introduces no distortion.

    Changing any component — the case algorithm, the DOM profile, or the
    OT constraint families — breaks theorems at every layer downstream. -/

/-- All 8 attested DOM profiles, run through the accusative case pipeline,
    produce overt marking that is faithful to the DOM input AND monotone. -/
theorem full_pipeline_faithful_and_monotone :
    allDOMProfiles.all (λ dom =>
      -- Faithful: pipeline output = DOM input
      AnimacyLevel.all.all (λ a =>
        DefinitenessLevel.all.all (λ d =>
          (overtProfile .accusative dom).marks a d = dom.marks a d)) &&
      -- Monotone: overt marking pattern is an upper set
      (overtProfile .accusative dom).isMonotone) = true := by native_decide

end Phenomena.Case.Bridge.DependentCaseDOM
