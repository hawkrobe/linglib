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
Tonhauser note (p. 583), "the observed gradience in projection [is] compatible
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

Values read from Figure 2 of the paper. The gradient nature and
ordering show no categorical factive/nonfactive gap.
-/
def projectionRating_Exp1a : Predicate → Float
  -- Canonically factive (purple diamonds) - not clustered at top
  | .beAnnoyed => 0.89
  | .know => 0.84
  | .see => 0.81
  | .reveal => 0.71
  | .discover => 0.77
  -- Nonveridical nonfactive (grey squares)
  | .pretend => 0.17
  | .think => 0.20
  | .suggest => 0.24
  | .say => 0.25
  -- Veridical nonfactive (blue triangles down)
  | .beRight => 0.19
  | .demonstrate => 0.49
  -- Optionally factive (orange triangles up) - spans wide range
  | .inform => 0.79
  | .hear => 0.75
  | .acknowledge => 0.73
  | .admit => 0.67
  | .confess => 0.64
  | .announce => 0.59
  | .establish => 0.37
  | .confirm => 0.35
  | .prove => 0.31

/--
Proportion of 'yes' responses from Experiment 1b (categorical).
Approximate values from Figure 4.
-/
def projectionRating_Exp1b : Predicate → Float
  | .know => 0.88
  | .beAnnoyed => 0.87
  | .inform => 0.85
  | .see => 0.84
  | .discover => 0.82
  | .hear => 0.80
  | .acknowledge => 0.78
  | .reveal => 0.74
  | .admit => 0.72
  | .confess => 0.68
  | .announce => 0.58
  | .demonstrate => 0.54
  | .establish => 0.50
  | .confirm => 0.48
  | .prove => 0.42
  | .suggest => 0.32
  | .pretend => 0.30
  | .say => 0.28
  | .think => 0.24
  | .beRight => 0.18


/--
Mean inference ratings from Experiment 2a (gradient scale 0-1).
Higher = inference to CC more strongly supported.

Approximate values from Figure 9.
-/
def inferenceRating_Exp2a : Predicate → Float
  | .prove => 0.97
  | .beRight => 0.96
  | .see => 0.93
  | .discover => 0.92
  | .confirm => 0.91
  | .know => 0.90
  | .beAnnoyed => 0.89
  | .admit => 0.88
  | .acknowledge => 0.87
  | .establish => 0.85
  | .reveal => 0.84
  | .confess => 0.80
  | .demonstrate => 0.75
  | .inform => 0.68
  | .announce => 0.60
  | .say => 0.55
  | .hear => 0.45
  | .suggest => 0.35
  | .think => 0.30
  | .pretend => 0.15


/--
Optionally factive predicates can be as projective as canonically factive ones.

Inform projects more strongly than reveal (a canonical factive):
inform=0.79 vs reveal=0.71 (Exp 1a).
-/
theorem optionally_factive_as_projective_as_factive :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal ∧
    projectionRating_Exp1a .acknowledge > projectionRating_Exp1a .reveal :=
  ⟨by native_decide, by native_decide⟩

/--
There is no categorical gap between factive and optionally factive
predicates in projection.

The mean projection rating of the least projective factive (reveal: 0.71)
is lower than the most projective optionally factive (inform: 0.79).
-/
theorem no_categorical_projection_gap :
    projectionRating_Exp1a .inform > projectionRating_Exp1a .reveal := by
  native_decide

/--
Predicates with highest entailment have lowest projection.

be_right: inference=0.96, projection=0.19
know: inference=0.90, projection=0.84

This dissociation between inference (entailment) strength and projection
strength is one of the key empirical observations of the paper,
undermining Definition 3b. -/
theorem entailment_projection_dissociation :
    inferenceRating_Exp2a .beRight > inferenceRating_Exp2a .know ∧
    projectionRating_Exp1a .know > projectionRating_Exp1a .beRight :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §5. Fragment Factivity Bridge
-- ============================================================================

open Fragments.English.Predicates.Verbal in
/-- Canonically factive predicates have `factivePresup = true` in the
    Fragment, matching D&T 2022's traditional classification. "be annoyed"
    has no Fragment entry (copular construction). -/
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
    for all predicates that have entries: every predicate classified as
    factive has `factivePresup = true`, every nonfactive has `false`. -/
theorem traditionalClass_consistent_with_fragment (p : Predicate)
    (v : VerbEntry) (h : toVerbEntry p = some v) :
    (traditionalClass p = .factive → v.factivePresup = true) ∧
    (traditionalClass p = .nonveridicalNonfactive → v.factivePresup = false) := by
  cases p <;> (unfold toVerbEntry at h; cases h) <;>
    refine ⟨fun hc => ?_, fun hc => ?_⟩ <;> first | rfl | simp [traditionalClass] at hc

end Phenomena.Presupposition.Studies.DegenTonhauser2022
