import Linglib.Semantics.Lexical.EventStructure
import Linglib.Semantics.Lexical.LevinClassProfiles

/-!
# Argument Structure Derivation Pipeline

[beavers-koontz-garboden-2020] [rappaport-hovav-levin-1998]
[dowty-1991]

The derivational chain from root content to argument structure, made
explicit as composed functions:

    Root.Kinds → Template → ArgTemplate → ThetaRole

Each step exists in the literature: [beavers-koontz-garboden-2020]
define root entailments; [rappaport-hovav-levin-1998] define event
structure templates; [dowty-1991] defines proto-role entailment
profiles. But nobody has written down the full pipeline as a single
computable derivation. This file does so.

## Key insight (Beavers SAG 2023, Lecture 3 §8)

Root and template meanings are not ontologically distinct — both are
sets of lexical entailments about events and participants. They differ
in degree of specificity: templates have general meanings shared across
many roots; roots have specific meanings that can include templatic
content (contra the Bifurcation Thesis, [embick-2009]).

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

namespace ArgumentStructure.ArgDerivation

open Verb
open Semantics.Lexical
open Semantics.Lexical.EventStructure (Template)
open Features.LevinClassProfiles
open _root_.ArgumentStructure (EntailmentProfile)
open _root_.ArgumentStructure
open Root.Kinds

-- ════════════════════════════════════════════════════
-- § 1. Root-Template Compatibility
-- ════════════════════════════════════════════════════

/-- Can a root fill this template?

    A root licenses a template when it provides content for the
    template's structural positions. Templates provide operators
    (ACT, CAUSE, BECOME); roots fill the content slots (STATE,
    MANNER).

    [beavers-koontz-garboden-2020] (SAG Lectures 2023 §6): roots
    fall into types based on how much templatic meaning they entail,
    and these types predict which templates they can fill.

    Licensing conditions:
    - **state** `[x STATE]`: root must describe a state
    - **activity** `[x ACT]`: root must describe an action manner
    - **achievement** `[BECOME [x STATE]]`: root provides state for
      BECOME to apply to (template adds the change)
    - **accomplishment** `[[x ACT] CAUSE [BECOME [y STATE]]]`: root
      provides state for the caused result -/
def RootLicensesTemplate (re : Root.Kinds) : Template → Prop
  | .state         => .state ∈ re
  | .activity      => .manner ∈ re
  | .achievement   => .state ∈ re
  | .accomplishment => .state ∈ re

instance (re : Root.Kinds) (t : Template) :
    Decidable (RootLicensesTemplate re t) := by
  cases t <;> unfold RootLicensesTemplate <;> infer_instance

/-- All templates licensed by a root (captures alternation). -/
def licensedTemplates (re : Root.Kinds) : List Template :=
  [.state, .activity, .achievement, .accomplishment].filter
    (λ t => decide (RootLicensesTemplate re t))

-- § 1a. Licensing verification for canonical root types

/-- PC roots (FLAT) license state, achievement, accomplishment —
    the three state-based templates. Not activity (no manner). -/
theorem pc_licenses :
    RootLicensesTemplate propertyConcept .state ∧
    RootLicensesTemplate propertyConcept .achievement ∧
    RootLicensesTemplate propertyConcept .accomplishment ∧
    ¬ RootLicensesTemplate propertyConcept .activity := by decide

/-- Pure manner roots (JOG) license activity only.
    Not state-based templates (no state entailment). -/
theorem pureManner_licenses :
    RootLicensesTemplate pureManner .activity ∧
    ¬ RootLicensesTemplate pureManner .state ∧
    ¬ RootLicensesTemplate pureManner .achievement ∧
    ¬ RootLicensesTemplate pureManner .accomplishment := by decide

/-- Pure result roots (BLOSSOM) license state, achievement,
    accomplishment — same as PC roots, since both have state. -/
theorem pureResult_licenses :
    RootLicensesTemplate pureResult .state ∧
    RootLicensesTemplate pureResult .achievement ∧
    RootLicensesTemplate pureResult .accomplishment ∧
    ¬ RootLicensesTemplate pureResult .activity := by decide

/-- Causative result roots (BREAK) license state-based templates. -/
theorem causativeResult_licenses :
    RootLicensesTemplate causativeResult .state ∧
    RootLicensesTemplate causativeResult .achievement ∧
    RootLicensesTemplate causativeResult .accomplishment ∧
    ¬ RootLicensesTemplate causativeResult .activity := by decide

/-- Full-spec roots (CUT) license all four templates — they have
    both state and manner, so they can fill any structural position. -/
theorem fullSpec_licenses :
    RootLicensesTemplate fullSpec .state ∧
    RootLicensesTemplate fullSpec .activity ∧
    RootLicensesTemplate fullSpec .achievement ∧
    RootLicensesTemplate fullSpec .accomplishment := by decide

-- § 1b. Alternation predictions

/-- PC roots license 3 templates → predict causative alternation.
    "The rug is flat" (state) / "The rug flattened" (achievement) /
    "Kim flattened the rug" (accomplishment). -/
theorem pc_alternation_count :
    (licensedTemplates propertyConcept).length = 3 := by decide

/-- Pure manner roots license 1 template — no alternation into
    state-based frames (*"Kim jogged the ball broken"). -/
theorem pureManner_alternation_count :
    (licensedTemplates pureManner).length = 1 := by decide

/-- Full-spec roots license all 4 templates — maximal flexibility
    (conative, causative/inchoative, locative, etc.). -/
theorem fullSpec_alternation_count :
    (licensedTemplates fullSpec).length = 4 := by decide

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

    [beavers-koontz-garboden-2020] (SAG Lectures 2023 §6, table 32):
    the root typology mirrors the template typology.

    | Root type | Primary template |
    |---|---|
    | propertyConcept (FLAT) | state |
    | pureResult (CRACK) | achievement |
    | causativeResult (BREAK) | accomplishment |
    | pureManner (JOG) | activity |
    | fullSpec (CUT) | accomplishment | -/
def primaryTemplate (re : Root.Kinds) : Option Template :=
  if .cause ∈ re then some .accomplishment
  else if .result ∈ re then some .achievement
  else if .manner ∈ re then some .activity
  else if .state ∈ re then some .state
  else none

-- § 3a. Root typology → primary template

theorem pc_primary :
    primaryTemplate propertyConcept = some .state := rfl

theorem pureResult_primary :
    primaryTemplate pureResult = some .achievement := rfl

theorem causativeResult_primary :
    primaryTemplate causativeResult = some .accomplishment := rfl

theorem pureManner_primary :
    primaryTemplate pureManner = some .activity := rfl

theorem fullSpec_primary :
    primaryTemplate fullSpec = some .accomplishment := rfl

-- § 3b. Primary template is always licensed

/-- For canonical root types, the primary template is licensed. -/
theorem primary_licensed_canonical :
    RootLicensesTemplate propertyConcept .state ∧
    RootLicensesTemplate pureResult .achievement ∧
    RootLicensesTemplate causativeResult .accomplishment ∧
    RootLicensesTemplate pureManner .activity ∧
    RootLicensesTemplate fullSpec .accomplishment := by decide

-- ════════════════════════════════════════════════════
-- § 4. Full Pipeline
-- ════════════════════════════════════════════════════

/-- The full derivational pipeline: root entailments → primary
    template → template-level ArgTemplate. -/
def derivePrimary (re : Root.Kinds) : Option ArgTemplate :=
  (primaryTemplate re).map templateArgTemplate

/-- All ArgTemplates derivable from a root (one per licensed template).
    Multiple entries represent alternation possibilities:
    e.g., a causativeResult root derives both an accomplishment
    ArgTemplate (transitive) and a state ArgTemplate (bare stative). -/
def deriveAll (re : Root.Kinds) : List ArgTemplate :=
  (licensedTemplates re).map templateArgTemplate

-- § 4a. Pipeline produces non-trivial results

/-- causativeResult roots derive 3 ArgTemplates (state, achievement,
    accomplishment variants). -/
theorem causativeResult_derives_three :
    (deriveAll causativeResult).length = 3 := by decide

/-- fullSpec roots derive 4 ArgTemplates (all templates). -/
theorem fullSpec_derives_four :
    (deriveAll fullSpec).length = 4 := by decide

-- ════════════════════════════════════════════════════
-- § 5. Root-Enriched Derivation
-- ════════════════════════════════════════════════════

/-! The template determines structural argument positions, but for
activity verbs, the ROOT contributes the object. In R&HL's notation,
`[x ACT<HIT> y]` — the `y` is an argument of the root (HIT), not of
the template (ACT).

This means activity objects come from meaning components (contact,
motion), not from template structure. When a root involves contact
with another entity, the activity becomes transitive, and the subject
gains causation (C) from the causal interaction with the object. -/

/-- Root-contributed object profile for activity verbs.
    Contact in meaning components → transitive activity with a
    contacted, stationary object (CA+St). No contact → intransitive. -/
def activityObjectProfile (mc : MeaningComponents) : Option EntailmentProfile :=
  if mc.contact then
    some ⟨false, false, false, false, false, false, false, true, true, false⟩
  else
    none

/-- Root-enriched derivation: combines template-level profiles with
    root-contributed objects.

    For activity templates, the root's meaning components determine
    whether there's a contacted object. When there is one, the subject
    also gains C (causation) — causal interaction with the object is
    a Dowty P-Agent entailment that comes from having an affected
    participant, not from the template.

    For other templates, the template's own profiles are used directly.

    Returns `none` for roots with no structural entailments (minimal). -/
def deriveEnriched (re : Root.Kinds) (mc : MeaningComponents) : Option ArgTemplate :=
  match primaryTemplate re with
  | none => none
  | some t =>
    let base := templateArgTemplate t
    match t with
    | .activity =>
      if mc.contact then
        -- Transitive activity: subject gets C from causal interaction
        some { subjectProfile := ArgumentStructure.accomplishmentSubjectProfile,
               objectProfile := some Features.LevinClassProfiles.contactObject }
      else
        some base
    | _ => some base

-- § 5a. Enriched derivation matches named templates

/-- Hit-class: enriched derivation gives mannerContact (full agent +
    contacted object). The root's contact meaning component contributes
    the object and adds C to the subject. -/
theorem hit_enriched_matches :
    deriveEnriched pureManner .hit = some mannerContact := rfl

/-- MannerOfMotion: enriched derivation gives selfMotion (no contact,
    no object). The root contributes no object. -/
theorem run_enriched_matches :
    deriveEnriched pureManner ⟨false, false, true, false, false, false⟩ = some selfMotion := rfl

/-- Break: enriched derivation gives resultChange (full agent +
    CoS+CA object). Accomplishment template used directly — the
    root doesn't modify it for non-activity templates. -/
theorem break_enriched_matches :
    deriveEnriched causativeResult .break_ = some resultChange := rfl

/-- Cut: enriched derivation gives resultChange (same as break).
    The manner component doesn't affect the accomplishment template. -/
theorem cut_enriched_matches :
    deriveEnriched fullSpec .cut = some resultChange := rfl

-- § 5b. Enriched derivation vs hand-specified LevinClass.argTemplate

/-- For hit-class, the enriched derivation matches the hand-specified
    argTemplate exactly — no override needed. -/
theorem hit_enriched_matches_class :
    deriveEnriched
      (LevinClass.rootEntailments .hit)
      (LevinClass.meaningComponents .hit) =
    LevinClass.argTemplate .hit := rfl

/-- For break-class, same exact match. -/
theorem break_enriched_matches_class :
    deriveEnriched
      (LevinClass.rootEntailments .break_)
      (LevinClass.meaningComponents .break_) =
    LevinClass.argTemplate .break_ := rfl

/-- For cut-class, same exact match. -/
theorem cut_enriched_matches_class :
    deriveEnriched
      (LevinClass.rootEntailments .cut)
      (LevinClass.meaningComponents .cut) =
    LevinClass.argTemplate .cut := rfl

/-- For mannerOfMotion, same exact match. -/
theorem mannerOfMotion_enriched_matches_class :
    deriveEnriched
      (LevinClass.rootEntailments .mannerOfMotion)
      (LevinClass.meaningComponents .mannerOfMotion) =
    LevinClass.argTemplate .mannerOfMotion := rfl

-- ════════════════════════════════════════════════════
-- § 6. Consistency: Pipeline vs Shortcut (toArgTemplate)
-- ════════════════════════════════════════════════════

/-! The `toArgTemplate` shortcut (§7 of LevinClassProfiles) maps
root entailments directly to named ArgTemplates. The pipeline goes
through an intermediate Template step.

After fixing the template defaults (activity subject C=false,
accomplishment object IT=false), the pipeline and shortcut now
AGREE on 4 of 5 canonical root types:

| Root type | Pipeline subject | Shortcut subject | Agree? |
|---|---|---|---|
| causativeResult | V+S+C+M+IE | V+S+C+M+IE | yes |
| fullSpec | V+S+C+M+IE | V+S+C+M+IE | yes |
| pureManner | V+S+M+IE | V+S+M+IE | yes |
| propertyConcept | S+IE | S+IE | yes |
| pureResult | M+IE+CoS | CoS+CA | **no** |

The pureResult divergence reflects genuinely different theoretical
emphases on what characterizes unaccusatives: the template emphasizes
movement and change (M+IE+CoS), while the shortcut emphasizes being
affected (CoS+CA). -/

/-- causativeResult: pipeline and shortcut AGREE on subject profile.
    Both give the accomplishment subject = full agent (V+S+C+M+IE). -/
theorem causativeResult_subject_agrees :
    (derivePrimary causativeResult).map (·.subjectProfile) =
    (toArgTemplate causativeResult).map (·.subjectProfile) := rfl

/-- fullSpec: pipeline and shortcut AGREE on subject profile. -/
theorem fullSpec_subject_agrees :
    (derivePrimary fullSpec).map (·.subjectProfile) =
    (toArgTemplate fullSpec).map (·.subjectProfile) := rfl

/-- propertyConcept: pipeline and shortcut AGREE on subject profile
    (both S+IE). -/
theorem propertyConcept_subject_agrees :
    (derivePrimary propertyConcept).map (·.subjectProfile) =
    (toArgTemplate propertyConcept).map (·.subjectProfile) := rfl

/-- pureManner: pipeline and shortcut AGREE on subject profile.
    Both give V+S+M+IE (no causation): the activity template does not
    entail causal interaction with another participant, matching
    selfMotion verbs like run and jog. -/
theorem pureManner_subject_agrees :
    (derivePrimary pureManner).map (·.subjectProfile) =
    (toArgTemplate pureManner).map (·.subjectProfile) := rfl

/-- pureResult: pipeline and shortcut DISAGREE on subject.
    Pipeline: achievement subject = M+IE+CoS (moves, changes).
    Shortcut: unaccusativeCoS subject = CoS+CA (changed, affected).
    Different theoretical emphases on what characterizes unaccusatives. -/
theorem pureResult_subject_diverges :
    (derivePrimary pureResult).map (·.subjectProfile) ≠
    (toArgTemplate pureResult).map (·.subjectProfile) := by decide

/-- causativeResult: pipeline and shortcut AGREE on object profile.
    Both give CoS+CA (change of state, causally affected). The
    template default correctly excludes IT (incremental theme) —
    not all caused-change objects measure the event. -/
theorem causativeResult_object_agrees :
    (derivePrimary causativeResult).bind (·.objectProfile) =
    (toArgTemplate causativeResult).bind (·.objectProfile) := rfl

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

/-! [beavers-koontz-garboden-2020] (SAG Lectures 2023 §6):
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
    LexKind.state ∈ propertyConcept ∧
    LexKind.result ∉ propertyConcept := by decide

/-- Result roots entail both state AND result — the state is
    inseparable from prior change. "Cracked" entails having
    been cracked. -/
theorem result_has_change :
    LexKind.state ∈ pureResult ∧
    LexKind.result ∈ pureResult ∧
    LexKind.cause ∉ pureResult := by decide

/-- Caused-result roots entail state + result + cause — the
    change must have been externally caused. "Break" entails
    external causation. -/
theorem caused_result_full :
    LexKind.state ∈ causativeResult ∧
    LexKind.result ∈ causativeResult ∧
    LexKind.cause ∈ causativeResult := by decide

/-- The root typology forms an implicational hierarchy:
    cause → result → state. For well-formed signatures this is a
    consequence of downward closure under the collocational order —
    not a per-signature stipulation. -/
theorem root_typology_hierarchy :
    ∀ s : Root.Kinds, s.WellFormed →
      (.cause ∈ s → .result ∈ s) ∧ (.result ∈ s → .state ∈ s) := by decide

/-- PC and result roots differ in licensing predictions:
    PC roots can fill stative templates (simple statives exist);
    result roots also license stative BUT the root itself entails
    change, so the "stative" use still presupposes prior change. -/
theorem pc_result_stative_difference :
    -- Both license the state template
    RootLicensesTemplate propertyConcept .state ∧
    RootLicensesTemplate pureResult .state ∧
    -- But result roots entail change (root-level, not template-level)
    LexKind.result ∉ propertyConcept ∧
    LexKind.result ∈ pureResult := by decide

-- ════════════════════════════════════════════════════
-- § 8. Summary: Where the Pipeline is Informative
-- ════════════════════════════════════════════════════

/-! The enriched pipeline (`deriveEnriched`) captures the field consensus:

1. **Template determines structural positions**: CAUSE introduces an
   external argument; BECOME introduces an internal argument.
   The template-level `templateArgTemplate` gives DEFAULT profiles.

2. **Root contributes additional participants**: for activity verbs,
   the root's meaning components (contact, motion) determine whether
   there's a contacted object. This adds transitivity and causation
   to the subject — effects that come from the ROOT, not the template.

3. **Class overrides remain for irreducible properties**: psych-causal
   (amuse), creation (build), consumption (eat) require class-level
   information not in root entailments or meaning components.

The enriched pipeline covers hit, break, cut, mannerOfMotion classes
exactly — `deriveEnriched` matches `LevinClass.argTemplate` with no
override needed. Only amuse, build/create, eat/devour, perception,
directedMotion, and minimal-rootEntailments classes need overrides.

The full derivational chain:

    Root entailments → Template → Template profiles → Root enrichment → Class override
    (Root.Kinds)  (primary)  (templateArg)     (deriveEnriched)   (LevinClass.argTemplate)
-/

end ArgumentStructure.ArgDerivation
