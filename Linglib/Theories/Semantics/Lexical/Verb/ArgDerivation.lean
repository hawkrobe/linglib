import Linglib.Theories.Semantics.Lexical.Verb.EventStructure
import Linglib.Theories.Semantics.Lexical.Verb.LevinClassProfiles

/-!
# Argument Structure Derivation Pipeline

@cite{beavers-koontz-garboden-2020} @cite{rappaport-hovav-levin-1998}
@cite{rappaport-hovav-levin-2024} @cite{dowty-1991}

The derivational chain from root content to argument structure, made
explicit as composed functions:

    RootEntailments → Template → ArgTemplate → ThetaRole

Each step exists in the literature: @cite{beavers-koontz-garboden-2020}
define root entailments; @cite{rappaport-hovav-levin-1998} define event
structure templates; @cite{dowty-1991} defines proto-role entailment
profiles. But nobody has written down the full pipeline as a single
computable derivation. This file does so.

## Key insight (Beavers SAG 2023, Lecture 3 §8)

Root and template meanings are not ontologically distinct — both are
sets of lexical entailments about events and participants. They differ
in degree of specificity: templates have general meanings shared across
many roots; roots have specific meanings that can include templatic
content (contra the Bifurcation Thesis, @cite{embick-2009}).

The template determines structural argument positions (subject, object).
The root determines WHICH template the verb fills, and class membership
can further refine the entailment profiles within those positions.

## Overrides

Three classes of systematic override exist where class membership
adds information beyond what root entailments + template predict:

- **Psych-causal** (amuse): stimulus subject instead of agent — the
  nature of causation (volitional vs. non-volitional) is not encoded
  in root entailments or template structure
- **Creation** (build): object has dependent existence + incremental
  theme — these are additional entailments about the object's
  ontological status
- **Consumption** (eat): object has incremental theme without dependent
  existence — the object pre-exists but measures the event
-/

namespace Semantics.Lexical.Verb.ArgDerivation

open EventStructure (Template)
open LevinClassProfiles
open Semantics.Lexical.Verb.EntailmentProfile

-- ════════════════════════════════════════════════════
-- § 1. Root-Template Compatibility
-- ════════════════════════════════════════════════════

/-- Can a root fill this template?

    A root licenses a template when it provides content for the
    template's structural positions. Templates provide operators
    (ACT, CAUSE, BECOME); roots fill the content slots (STATE,
    MANNER).

    @cite{beavers-koontz-garboden-2020} (SAG Lectures 2023 §6): roots
    fall into types based on how much templatic meaning they entail,
    and these types predict which templates they can fill.

    Licensing conditions:
    - **state** `[x STATE]`: root must describe a state
    - **activity** `[x ACT]`: root must describe an action manner
    - **achievement** `[BECOME [x STATE]]`: root provides state for
      BECOME to apply to (template adds the change)
    - **accomplishment** `[[x ACT] CAUSE [BECOME [y STATE]]]`: root
      provides state for the caused result
    - **motionContact** `[x MOVE y] WHILE [x CONTACT y]`: root must
      describe manner (motion + contact are manner-based) -/
def rootLicensesTemplate (re : RootEntailments) : Template → Bool
  | .state         => re.state
  | .activity      => re.manner
  | .achievement   => re.state
  | .accomplishment => re.state
  | .motionContact => re.manner

/-- All templates licensed by a root (captures alternation). -/
def licensedTemplates (re : RootEntailments) : List Template :=
  [.state, .activity, .achievement, .accomplishment, .motionContact].filter
    (rootLicensesTemplate re)

-- § 1a. Licensing verification for canonical root types

/-- PC roots (FLAT) license state, achievement, accomplishment —
    the three state-based templates. Not activity (no manner). -/
theorem pc_licenses :
    rootLicensesTemplate .propertyConcept .state = true ∧
    rootLicensesTemplate .propertyConcept .achievement = true ∧
    rootLicensesTemplate .propertyConcept .accomplishment = true ∧
    rootLicensesTemplate .propertyConcept .activity = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Pure manner roots (JOG) license activity and motionContact only.
    Not state-based templates (no state entailment). -/
theorem pureManner_licenses :
    rootLicensesTemplate .pureManner .activity = true ∧
    rootLicensesTemplate .pureManner .motionContact = true ∧
    rootLicensesTemplate .pureManner .state = false ∧
    rootLicensesTemplate .pureManner .achievement = false ∧
    rootLicensesTemplate .pureManner .accomplishment = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Pure result roots (BLOSSOM) license state, achievement,
    accomplishment — same as PC roots, since both have state. -/
theorem pureResult_licenses :
    rootLicensesTemplate .pureResult .state = true ∧
    rootLicensesTemplate .pureResult .achievement = true ∧
    rootLicensesTemplate .pureResult .accomplishment = true ∧
    rootLicensesTemplate .pureResult .activity = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Causative result roots (BREAK) license state-based templates. -/
theorem causativeResult_licenses :
    rootLicensesTemplate .causativeResult .state = true ∧
    rootLicensesTemplate .causativeResult .achievement = true ∧
    rootLicensesTemplate .causativeResult .accomplishment = true ∧
    rootLicensesTemplate .causativeResult .activity = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Full-spec roots (CUT) license ALL five templates — they have
    both state and manner, so they can fill any structural position. -/
theorem fullSpec_licenses :
    rootLicensesTemplate .fullSpec .state = true ∧
    rootLicensesTemplate .fullSpec .activity = true ∧
    rootLicensesTemplate .fullSpec .achievement = true ∧
    rootLicensesTemplate .fullSpec .accomplishment = true ∧
    rootLicensesTemplate .fullSpec .motionContact = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- § 1b. Alternation predictions

/-- PC roots license 3 templates → predict causative alternation.
    "The rug is flat" (state) / "The rug flattened" (achievement) /
    "Kim flattened the rug" (accomplishment). -/
theorem pc_alternation_count :
    (licensedTemplates .propertyConcept).length = 3 := by native_decide

/-- Pure manner roots license 2 templates — no alternation into
    state-based frames (*"Kim jogged the ball broken"). -/
theorem pureManner_alternation_count :
    (licensedTemplates .pureManner).length = 2 := by native_decide

/-- Full-spec roots license all 5 templates — maximal flexibility
    (conative, causative/inchoative, locative, etc.). -/
theorem fullSpec_alternation_count :
    (licensedTemplates .fullSpec).length = 5 := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. Template → ArgTemplate
-- ════════════════════════════════════════════════════

/-- Default ArgTemplate from an event structure template.

    Wraps `Template.subjectProfile`/`Template.objectProfile` into
    an `ArgTemplate`. This is the TEMPLATE-LEVEL prediction, before
    any class-level refinement.

    Known divergences from class-level named templates:
    - Activity subject gets C=true (assumes transitive activity like
      "hit"); intransitive activities (selfMotion) override to C=false
    - Accomplishment object gets IT=true (incremental theme);
      resultChange object overrides to IT=false (not all CoS objects
      are incremental themes)
    - State template has no object; perception verbs add one at the
      class level -/
def templateArgTemplate (t : Template) : ArgTemplate where
  subjectProfile := t.subjectProfile
  objectProfile := t.objectProfile

-- ════════════════════════════════════════════════════
-- § 3. Primary Template Selection
-- ════════════════════════════════════════════════════

/-- A root's primary (natural) template — the template whose structural
    complexity matches the root's entailment level.

    This is the template the root "wants" to fill by default:
    - cause → accomplishment (inherently causative verb)
    - result without cause → achievement (entails change, no external cause)
    - manner without result → activity (specifies action manner)
    - state only → state (names a property/state)

    @cite{beavers-koontz-garboden-2020} (SAG Lectures 2023 §6, table 32):
    the root typology mirrors the template typology.

    | Root type | Primary template |
    |---|---|
    | propertyConcept (FLAT) | state |
    | pureResult (CRACK) | achievement |
    | causativeResult (BREAK) | accomplishment |
    | pureManner (JOG) | activity |
    | fullSpec (CUT) | accomplishment | -/
def primaryTemplate (re : RootEntailments) : Option Template :=
  if re.cause then some .accomplishment
  else if re.result then some .achievement
  else if re.manner then some .activity
  else if re.state then some .state
  else none

-- § 3a. Root typology → primary template

theorem pc_primary :
    primaryTemplate .propertyConcept = some .state := rfl

theorem pureResult_primary :
    primaryTemplate .pureResult = some .achievement := rfl

theorem causativeResult_primary :
    primaryTemplate .causativeResult = some .accomplishment := rfl

theorem pureManner_primary :
    primaryTemplate .pureManner = some .activity := rfl

theorem fullSpec_primary :
    primaryTemplate .fullSpec = some .accomplishment := rfl

-- § 3b. Primary template is always licensed

/-- For canonical root types, the primary template is licensed. -/
theorem primary_licensed_canonical :
    (primaryTemplate .propertyConcept).any (rootLicensesTemplate .propertyConcept) = true ∧
    (primaryTemplate .pureResult).any (rootLicensesTemplate .pureResult) = true ∧
    (primaryTemplate .causativeResult).any (rootLicensesTemplate .causativeResult) = true ∧
    (primaryTemplate .pureManner).any (rootLicensesTemplate .pureManner) = true ∧
    (primaryTemplate .fullSpec).any (rootLicensesTemplate .fullSpec) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Full Pipeline
-- ════════════════════════════════════════════════════

/-- The full derivational pipeline: root entailments → primary
    template → template-level ArgTemplate. -/
def derivePrimary (re : RootEntailments) : Option ArgTemplate :=
  (primaryTemplate re).map templateArgTemplate

/-- All ArgTemplates derivable from a root (one per licensed template).
    Multiple entries represent alternation possibilities:
    e.g., a causativeResult root derives both an accomplishment
    ArgTemplate (transitive) and a state ArgTemplate (bare stative). -/
def deriveAll (re : RootEntailments) : List ArgTemplate :=
  (licensedTemplates re).map templateArgTemplate

-- § 4a. Pipeline produces non-trivial results

/-- causativeResult roots derive 3 ArgTemplates (state, achievement,
    accomplishment variants). -/
theorem causativeResult_derives_three :
    (deriveAll .causativeResult).length = 3 := by native_decide

/-- fullSpec roots derive 5 ArgTemplates (all templates). -/
theorem fullSpec_derives_five :
    (deriveAll .fullSpec).length = 5 := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Consistency: Pipeline vs Shortcut (toArgTemplate)
-- ════════════════════════════════════════════════════

/-! The `toArgTemplate` shortcut (§7 of LevinClassProfiles) maps
root entailments directly to named ArgTemplates. The pipeline goes
through an intermediate Template step. These agree on SUBJECT profiles
for causative roots but diverge for manner and state roots.

The divergences are informative — they reveal where template-level
defaults and class-level refinements differ:

| Root type | Pipeline subject | Shortcut subject | Agree? |
|---|---|---|---|
| causativeResult | V+S+C+M+IE | V+S+C+M+IE | yes |
| fullSpec | V+S+C+M+IE | V+S+C+M+IE | yes |
| pureManner | V+S+C+M+IE | V+S+M+IE | **no** (C) |
| propertyConcept | S+IE | S+IE | yes |
| pureResult | M+IE+CoS | CoS+CA | **no** |

The pureManner divergence: the template says "activity subjects cause
things" (C=true, assuming transitive activity like "hit"); the shortcut
says "manner-only activities don't cause anything" (C=false, selfMotion
pattern). The shortcut is more refined.

The pureResult divergence: the template says "achievement subjects move
and change" (M+IE+CoS); the shortcut says "unaccusative subjects are
changed and affected" (CoS+CA). These reflect different emphases in
what unaccusativity means. -/

/-- causativeResult: pipeline and shortcut AGREE on subject profile.
    Both give the accomplishment subject = full agent (V+S+C+M+IE). -/
theorem causativeResult_subject_agrees :
    (derivePrimary .causativeResult).map (·.subjectProfile) =
    (toArgTemplate .causativeResult).map (·.subjectProfile) := rfl

/-- fullSpec: pipeline and shortcut AGREE on subject profile. -/
theorem fullSpec_subject_agrees :
    (derivePrimary .fullSpec).map (·.subjectProfile) =
    (toArgTemplate .fullSpec).map (·.subjectProfile) := rfl

/-- propertyConcept: pipeline and shortcut AGREE on subject profile
    (both S+IE). -/
theorem propertyConcept_subject_agrees :
    (derivePrimary .propertyConcept).map (·.subjectProfile) =
    (toArgTemplate .propertyConcept).map (·.subjectProfile) := rfl

/-- pureManner: pipeline and shortcut DISAGREE on subject.
    Pipeline gives C=true (template-level: transitive activity default).
    Shortcut gives C=false (class-level: intransitive manner activity).
    The shortcut is correct for self-propelled motion verbs (run, jog)
    that don't cause changes in other participants. -/
theorem pureManner_subject_diverges :
    (derivePrimary .pureManner).map (·.subjectProfile) ≠
    (toArgTemplate .pureManner).map (·.subjectProfile) := by decide

/-- pureResult: pipeline and shortcut DISAGREE on subject.
    Pipeline: achievement subject = M+IE+CoS (moves, changes).
    Shortcut: unaccusativeCoS subject = CoS+CA (changed, affected).
    Different theoretical emphases on what characterizes unaccusatives. -/
theorem pureResult_subject_diverges :
    (derivePrimary .pureResult).map (·.subjectProfile) ≠
    (toArgTemplate .pureResult).map (·.subjectProfile) := by decide

/-- causativeResult: pipeline and shortcut DISAGREE on object.
    Pipeline: accomplishment object has IT=true (incremental theme).
    Shortcut: resultChange object has IT=false.
    Not all caused-change objects are incremental themes (break isn't;
    eat is). The template overpredicts IT; the class refines it. -/
theorem causativeResult_object_diverges :
    (derivePrimary .causativeResult).bind (·.objectProfile) ≠
    (toArgTemplate .causativeResult).bind (·.objectProfile) := by decide

-- ════════════════════════════════════════════════════
-- § 6. Consistency: Pipeline vs LevinClass.argTemplate
-- ════════════════════════════════════════════════════

/-! The LevinClass.argTemplate mapping hand-specifies ArgTemplates
for each class. The pipeline derives them from root entailments
through a template intermediate. Where do they agree? -/

/-- For break-class, the pipeline's PRIMARY subject matches the
    hand-specified subject. Both are full agent (V+S+C+M+IE). -/
theorem break_subject_pipeline_matches :
    (derivePrimary (LevinClass.rootEntailments .break_)).map (·.subjectProfile) =
    (LevinClass.argTemplate .break_).map (·.subjectProfile) := rfl

/-- For cut-class, same agreement on subject. -/
theorem cut_subject_pipeline_matches :
    (derivePrimary (LevinClass.rootEntailments .cut)).map (·.subjectProfile) =
    (LevinClass.argTemplate .cut).map (·.subjectProfile) := rfl

/-- Pipeline's primary template for break matches the
    event-structure-predicted template. The two independent
    derivations (root entailments → primaryTemplate, and
    meaningComponents → predictedTemplate) agree. -/
theorem break_template_derivations_agree :
    primaryTemplate (LevinClass.rootEntailments .break_) =
    some (LevinClass.eventTemplate .break_) := rfl

/-- Same for cut. -/
theorem cut_template_derivations_agree :
    primaryTemplate (LevinClass.rootEntailments .cut) =
    some (LevinClass.eventTemplate .cut) := rfl

/-- Same for mannerOfMotion. -/
theorem mannerOfMotion_template_derivations_agree :
    primaryTemplate (LevinClass.rootEntailments .mannerOfMotion) =
    some (LevinClass.eventTemplate .mannerOfMotion) := rfl

-- § 6a. Documented divergences

/-- Amuse-class: pipeline gives full agent subject (V+S+C+M+IE),
    but hand-specified gives stimulus subject (C+IE).
    The nature of causation (volitional vs. non-volitional) is
    not encoded in root entailments or template structure —
    it's a class-level semantic property. -/
theorem amuse_subject_override :
    (derivePrimary (LevinClass.rootEntailments .amuse)).map (·.subjectProfile) ≠
    (LevinClass.argTemplate .amuse).map (·.subjectProfile) := by decide

/-- Build-class: pipeline and hand-specified agree on subject
    (both full agent), but diverge on object (creation object
    has dependent existence). -/
theorem build_subject_agrees_object_diverges :
    (derivePrimary (LevinClass.rootEntailments .build)).map (·.subjectProfile) =
    (LevinClass.argTemplate .build).map (·.subjectProfile) ∧
    (derivePrimary (LevinClass.rootEntailments .build)).bind (·.objectProfile) ≠
    (LevinClass.argTemplate .build).bind (·.objectProfile) := ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 7. Root Typology Predictions
-- ════════════════════════════════════════════════════

/-! @cite{beavers-koontz-garboden-2020} (SAG Lectures 2023 §6):
roots fall into three types based on how much templatic meaning they
entail. This predicts morphological and semantic properties
cross-linguistically (validated across 88 languages).

| Type | Entails | Morphology | Simple stative |
|---|---|---|---|
| PC (FLAT) | state only | marked verbs (-en) | yes |
| Result (CRACK) | state + change | unmarked verbs | no |
| Caused result (FRY) | state + change + cause | unmarked verbs | no |
-/

/-- PC roots entail state but NOT result — they name properties
    without inherent change. "Flat" is a simple state. -/
theorem pc_no_result :
    RootEntailments.propertyConcept.state = true ∧
    RootEntailments.propertyConcept.result = false := ⟨rfl, rfl⟩

/-- Result roots entail both state AND result — the state is
    inseparable from prior change. "Cracked" entails having
    been cracked. -/
theorem result_has_change :
    RootEntailments.pureResult.state = true ∧
    RootEntailments.pureResult.result = true ∧
    RootEntailments.pureResult.cause = false := ⟨rfl, rfl, rfl⟩

/-- Caused-result roots entail state + result + cause — the
    change must have been externally caused. "Break" entails
    external causation. -/
theorem caused_result_full :
    RootEntailments.causativeResult.state = true ∧
    RootEntailments.causativeResult.result = true ∧
    RootEntailments.causativeResult.cause = true := ⟨rfl, rfl, rfl⟩

/-- The root typology forms an implicational hierarchy:
    cause → result → state.
    Each type INCLUDES the entailments of simpler types. -/
theorem root_typology_hierarchy :
    -- cause implies result
    RootEntailments.causativeResult.result = true ∧
    -- result implies state
    RootEntailments.pureResult.state = true ∧
    -- well-formedness enforces the hierarchy
    RootEntailments.causativeResult.wellFormed = true ∧
    RootEntailments.pureResult.wellFormed = true ∧
    RootEntailments.propertyConcept.wellFormed = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- PC and result roots differ in licensing predictions:
    PC roots can fill stative templates (simple statives exist);
    result roots also license stative BUT the root itself entails
    change, so the "stative" use still presupposes prior change. -/
theorem pc_result_stative_difference :
    -- Both license the state template
    rootLicensesTemplate .propertyConcept .state = true ∧
    rootLicensesTemplate .pureResult .state = true ∧
    -- But result roots entail change (root-level, not template-level)
    RootEntailments.propertyConcept.result = false ∧
    RootEntailments.pureResult.result = true := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Summary: Where the Pipeline is Informative
-- ════════════════════════════════════════════════════

/-! Making the pipeline explicit reveals three kinds of relationships:

1. **Agreement**: template-level and class-level predictions align.
   Break/cut subjects are full agents in both derivations.
   This is the DEFAULT and covers the majority of verbs.

2. **Refinement**: template-level gives a broader profile; class-level
   narrows it. Activity subjects lose C for intransitive manner verbs.
   Accomplishment objects lose IT for non-incremental-theme verbs.
   The template gives the MAXIMAL entailment set; the class removes
   inapplicable ones.

3. **Override**: class-level assigns a fundamentally different profile.
   Amuse-class replaces the full agent subject with a stimulus subject.
   This is irreducible to template structure — it requires knowing
   that the causer is non-volitional, which is a lexical property
   of the class.

The derivational chain:

    Root content → Template selection → Default ArgTemplate → Class refinement
    (RootEntailments)  (primaryTemplate)   (templateArgTemplate)  (LevinClass.argTemplate)

Each step is explicit and independently verifiable. -/

end Semantics.Lexical.Verb.ArgDerivation
