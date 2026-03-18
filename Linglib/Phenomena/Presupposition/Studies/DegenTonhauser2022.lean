import Linglib.Phenomena.Presupposition.Studies.DegenTonhauser2021

/-!
# @cite{degen-tonhauser-2022}: Are There Factive Predicates?
@cite{heim-1983} @cite{schlenker-2009} @cite{van-der-sandt-1992}

Empirical data from "Are there factive predicates? An empirical investigation"
by Judith Degen and Judith Tonhauser (Language 98(3):552–591, 2022).

## Finding

**Projection is gradient across predicates, with no categorical gap between
traditional factive and nonfactive classes.**

The gradient patterns observed in inference judgments do not, on their own,
settle whether factivity is fundamentally discrete or gradient. As Degen &
Tonhauser note, "the observed gradience in projection [is] compatible
with a binary factivity category" under the assumption that predicates are
ambiguous between factive and nonfactive readings. @cite{grove-white-2025}
subsequently show that models implementing discrete factivity fit these data
better than models implementing gradient factivity.

## Predicates

This paper reuses the 20 clause-embedding predicates from
@cite{degen-tonhauser-2021} and adds a four-way traditional classification.

## Experiments

### Experiment 1: Projection (Certain That Diagnostic)
- Presented polar questions with clause-embedding predicates
- Asked: "Is [speaker] certain that [CC]?"
- Found gradient projection, no categorical distinction

### Experiments 2-3: Entailment
- Inference diagnostic: "Does it follow that [CC]?"
- Contradictoriness diagnostic: "[Matrix] but [not CC]" contradictory?
- Found only prove/be right pattern with entailed controls

## Theoretical Implications

1. Definition 3a (CC is presupposed) not supported:
   - Canonically factive CCs not categorically more projective

2. Definition 3b (CC is presupposed AND entailed) not supported:
   - Set of "factive" predicates is either empty or heterogeneous

3. For projection analyses:
   - Unclear which predicates the analyses apply to
   - Need to account for gradient projection

## Connection to @cite{tonhauser-beaver-roberts-simons-2013}

This paper extends and empirically tests the Tonhauser taxonomy:
- SCF (Strong Contextual Felicity) relates to whether content must be established
- OLE (Obligatory Local Effect) relates to attribution under embedding
- The gradient projection patterns challenge simple binary classification
-/

namespace Phenomena.Presupposition.Studies.DegenTonhauser2022

open Phenomena.Presupposition.Studies.DegenTonhauser2021

/-- Traditional classification of clause-embedding predicates.
    This classification is challenged by the experimental results. -/
inductive TraditionalClass where
  /-- Canonically factive: CC traditionally assumed presupposed + entailed -/
  | factive
  /-- Nonveridical nonfactive: CC neither presupposed nor entailed -/
  | nonveridicalNonfactive
  /-- Veridical nonfactive: CC entailed but not presupposed -/
  | veridicalNonfactive
  /-- Optionally factive: CC may or may not be presupposed -/
  | optionallyFactive
  deriving DecidableEq, Repr

/-- Traditional classification of each predicate. -/
def traditionalClass : Predicate → TraditionalClass
  | .beAnnoyed => .factive
  | .discover => .factive
  | .know => .factive
  | .reveal => .factive
  | .see => .factive
  | .pretend => .nonveridicalNonfactive
  | .suggest => .nonveridicalNonfactive
  | .say => .nonveridicalNonfactive
  | .think => .nonveridicalNonfactive
  | .beRight => .veridicalNonfactive
  | .demonstrate => .veridicalNonfactive
  | .acknowledge => .optionallyFactive
  | .admit => .optionallyFactive
  | .announce => .optionallyFactive
  | .confess => .optionallyFactive
  | .confirm => .optionallyFactive
  | .establish => .optionallyFactive
  | .hear => .optionallyFactive
  | .inform => .optionallyFactive
  | .prove => .optionallyFactive


/--
Mean certainty ratings from Experiment 1a (gradient scale 0-1).
Higher = more projective (speaker more certain of CC).

Values computed from the data at
github.com/judith-tonhauser/projective-probability (results/5-projectivity-no-fact),
rounded to 2 decimal places. The gradient nature and ordering show no
categorical factive/nonfactive gap.
-/
def projectionRating_Exp1a : Predicate → Float
  -- Canonically factive - not clustered at top
  | .beAnnoyed => 0.88
  | .know => 0.86
  | .see => 0.81
  | .reveal => 0.70
  | .discover => 0.78
  -- Nonveridical nonfactive
  | .pretend => 0.15
  | .think => 0.20
  | .suggest => 0.22
  | .say => 0.24
  -- Veridical nonfactive
  | .beRight => 0.18
  | .demonstrate => 0.49
  -- Optionally factive - spans wide range
  | .inform => 0.81
  | .hear => 0.75
  | .acknowledge => 0.72
  | .admit => 0.66
  | .confess => 0.64
  | .announce => 0.58
  | .establish => 0.36
  | .confirm => 0.34
  | .prove => 0.30

/--
Proportion of 'yes' responses from Experiment 1b (binary choice).

Values computed from the data at
github.com/judith-tonhauser/projective-probability (results/8-projectivity-no-fact-binary),
rounded to 2 decimal places.
-/
def projectionRating_Exp1b : Predicate → Float
  | .know => 0.93
  | .beAnnoyed => 0.92
  | .inform => 0.90
  | .see => 0.86
  | .discover => 0.84
  | .hear => 0.81
  | .acknowledge => 0.78
  | .reveal => 0.70
  | .admit => 0.67
  | .confess => 0.58
  | .announce => 0.57
  | .demonstrate => 0.31
  | .establish => 0.19
  | .confirm => 0.16
  | .prove => 0.13
  | .suggest => 0.07
  | .pretend => 0.07
  | .say => 0.07
  | .think => 0.04
  | .beRight => 0.03


/--
Mean inference ratings from Experiment 2a (gradient scale 0-1).
Higher = inference to CC more strongly supported.

Values computed from the data at
github.com/judith-tonhauser/projective-probability (results/4-veridicality3),
rounded to 2 decimal places.
-/
def inferenceRating_Exp2a : Predicate → Float
  | .prove => 0.96
  | .beRight => 0.96
  | .see => 0.95
  | .discover => 0.94
  | .confirm => 0.94
  | .know => 0.93
  | .beAnnoyed => 0.92
  | .admit => 0.91
  | .acknowledge => 0.90
  | .establish => 0.90
  | .reveal => 0.90
  | .confess => 0.89
  | .demonstrate => 0.85
  | .inform => 0.83
  | .announce => 0.81
  | .say => 0.68
  | .hear => 0.50
  | .suggest => 0.34
  | .think => 0.32
  | .pretend => 0.12


/--
Optionally factive predicates can be as projective as canonically factive ones.

Inform projects more strongly than reveal (a canonical factive):
inform=0.81 vs reveal=0.70 (Exp 1a).
-/
theorem optionally_factive_as_projective_as_factive :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal ∧
    projectionRating_Exp1a .acknowledge > projectionRating_Exp1a .reveal :=
  ⟨by native_decide, by native_decide⟩

/--
There is no categorical gap between factive and optionally factive
predicates in projection.

The mean projection rating of the least projective factive (reveal: 0.70)
is lower than the most projective optionally factive (inform: 0.81).
-/
theorem no_categorical_projection_gap :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal := by
  native_decide

/--
Predicates with highest entailment have lowest projection.

be_right: inference=0.96, projection=0.18
know: inference=0.93, projection=0.86

This dissociation between inference (entailment) strength and projection
strength is one of the key empirical observations of the paper,
undermining Definition 3b. -/
theorem entailment_projection_dissociation :
    inferenceRating_Exp2a .beRight > inferenceRating_Exp2a .know ∧
    projectionRating_Exp1a .know > projectionRating_Exp1a .beRight :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §5. Cross-Diagnostic Consistency
-- ============================================================================

/-- The two projection diagnostics (Exp 1a continuous, Exp 1b binary) agree
    on the two most projective predicates: be_annoyed and know. -/
theorem top_two_agree :
    projectionRating_Exp1a .beAnnoyed > projectionRating_Exp1a .know ∧
    projectionRating_Exp1b .beAnnoyed < projectionRating_Exp1b .know ∧
    (∀ p : Predicate, p ≠ .beAnnoyed → p ≠ .know →
      projectionRating_Exp1a p < projectionRating_Exp1a .know) ∧
    (∀ p : Predicate, p ≠ .beAnnoyed → p ≠ .know →
      projectionRating_Exp1b p < projectionRating_Exp1b .know) := by
  refine ⟨by native_decide, by native_decide, fun p h1 h2 => ?_, fun p h1 h2 => ?_⟩ <;>
    cases p <;> simp_all [projectionRating_Exp1a, projectionRating_Exp1b] <;> native_decide

/-- The binary diagnostic produces sharper separation: nonfactive predicates
    cluster near 0 in binary (< 0.10) but are above 0.15 in continuous. -/
theorem binary_sharper_separation :
    projectionRating_Exp1b .pretend < 0.10 ∧
    projectionRating_Exp1b .think < 0.10 ∧
    projectionRating_Exp1b .say < 0.10 ∧
    projectionRating_Exp1b .suggest < 0.10 ∧
    projectionRating_Exp1b .beRight < 0.10 ∧
    projectionRating_Exp1a .pretend > 0.10 ∧
    projectionRating_Exp1a .think > 0.10 ∧
    projectionRating_Exp1a .say > 0.10 ∧
    projectionRating_Exp1a .suggest > 0.10 ∧
    projectionRating_Exp1a .beRight > 0.10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §6. Fragment Factivity Bridge
-- ============================================================================

open Fragments.English.Predicates.Verbal in
/-- Canonically factive *verbs* have `factivePresup = true` in the
    Fragment, matching D&T 2022's traditional classification. "be annoyed"
    is copular and emotive — its presupposition derives from emotive
    semantics, not doxastic veridicality, so `factivePresup = false`. -/
theorem factive_entries_have_factivePresup :
    know.factivePresup = true ∧
    discover.factivePresup = true ∧
    see.factivePresup = true ∧
    reveal.factivePresup = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.Predicates.Verbal in
/-- Nonveridical nonfactive predicates have `factivePresup = false` in the
    Fragment, matching D&T 2022's traditional classification. -/
theorem nonfactive_entries_lack_factivePresup :
    pretend.factivePresup = false ∧
    suggest.factivePresup = false ∧
    say.factivePresup = false ∧
    think.factivePresup = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

open Phenomena.Presupposition.Studies.DegenTonhauser2021 in
open Fragments.English.Predicates.Verbal in
/-- The traditional classification is consistent with Fragment factivity
    for verbal entries: every verb classified as factive has
    `factivePresup = true`, every nonfactive has `false`. -/
theorem traditionalClass_consistent_with_fragment (p : Predicate)
    (v : VerbEntry) (h : toVerbEntry p = some v) :
    (traditionalClass p = .factive → v.factivePresup = true) ∧
    (traditionalClass p = .nonveridicalNonfactive → v.factivePresup = false) := by
  cases p <;> (unfold toVerbEntry at h; cases h) <;>
    refine ⟨fun hc => ?_, fun hc => ?_⟩ <;> first | rfl | simp [traditionalClass] at hc

open Phenomena.Presupposition.Studies.DegenTonhauser2021 in
open Fragments.English.Predicates.Copular in
/-- "be annoyed" is a presupposition trigger (emotive factive), while
    "be right" is not. This matches D&T 2022's traditional classification:
    factive predicates trigger presuppositions, veridical nonfactives do not. -/
theorem copular_presup_matches_classification :
    (toPredicateCore .beAnnoyed).isPresupTrigger = true ∧
    (toPredicateCore .beRight).isPresupTrigger = false := by
  exact ⟨rfl, rfl⟩

end Phenomena.Presupposition.Studies.DegenTonhauser2022
