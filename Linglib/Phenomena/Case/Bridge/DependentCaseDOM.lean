import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Core.Prominence
import Linglib.Phenomena.Case.Typology
import Linglib.Phenomena.Case.Studies.Aissen2003

/-!
# Bridge: Dependent Case → DOM → OT Factorial Typology @cite{aissen-2003}
@cite{baker-2015} @cite{marantz-1991}

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
    DOM filter. The universal theorem `full_pipeline_faithful_and_monotone`
    (§ 8) proves this for all 8 attested DOM profiles at once. -/

-- ============================================================================
-- § 6: Layer 3 — OT Constrains the Pipeline
-- ============================================================================

/-- The overt marking profile produced by running the full pipeline
    (dependent case + DOM filter). -/
def overtProfile (lang : CaseLanguageType) (dom : DOMProfile) : DOMProfile :=
  { name := dom.name ++ " (pipeline)", role := .P, channel := .flagging
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
-- § 7: End-to-End Summary
-- ============================================================================

/-! Summary of the end-to-end chain:

    1. `object_always_acc`:
       Dependent case assigns ACC to all objects in accusative transitives.
       Prominence is irrelevant at this layer.

    2. `full_pipeline_faithful_and_monotone`:
       For all 8 attested DOM profiles: the pipeline output exactly matches
       the DOM input (faithful) AND the overt marking pattern is monotone.
       Subsumes the per-language `*_overt_eq_dom` and `*_pipeline_agrees`
       theorems.

    3. `ot_pipeline_monotone`:
       OT factorial typology generates only monotone DOMProfiles. The full
       pipeline (dependent case → DOM) inherits this monotonicity.

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
