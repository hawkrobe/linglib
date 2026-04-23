import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype
import Linglib.Features.PropertyDomain
import Linglib.Paradigms.VisualWorld

/-!
# @cite{sedivy-etal-1999}

Achieving incremental semantic interpretation through contextual representation.
*Cognition* 71(2), 109–147.

## Empirical Phenomenon

Visual-world eye-tracking with prenominal adjective instructions. Listeners
hearing "the tall glass" in a display containing both a tall glass and a
short glass identify the target faster — and consider an unrelated tall
pitcher less — than in a display lacking the same-category contrast pair.

The paper reports three experiments. Experiment 1 (subexperiments 1A and 1B,
intersective adjectives, N = 12) replicates @cite{eberhard-etal-1995}'s
incremental processing finding and shows contrastive interpretation of
color/material/shape adjectives. Experiments 2 (N = 24) and 3 (N = 22)
probe the mechanism for vague scalar adjectives such as "tall" that lack a
stable denotation, contrasting a definite-NP instruction task with an
indefinite-NP verification task.

## Paradigm

Built on `Paradigms.VisualWorld` (@cite{huettig-rommers-meyer-2011}). The
display contains four objects (`ObjectRole`):

- `target`: the intended referent (e.g. tall glass).
- `contrastingObject`: same category, opposite scale pole (short glass).
  Present only in the *contrast* condition.
- `crossCategoryCompetitor`: different category but further along the
  scale (pitcher, taller than the target glasses). Always present.
- `distractor`: unrelated object (key). Always present.

In the *no-contrast* condition the contrasting object is replaced by a
second distractor. Three within-subjects manipulations are crossed:

- **Contrast** (`ContrastCondition`): contrasting object present vs. replaced.
- **Typicality**: target is a good vs. poor exemplar of the modified NP.
- **Task** (`Task`): instruction with definite NP (Exp 2,
  `directAction`) vs. verification with indefinite NP (Exp 3,
  `verification`).

## Architectural Role

This file is an **empirical anchor**: it defines the experimental cells and
qualitative predicates that downstream theoretical models must satisfy. A
theory of incremental adjective processing predicts a numeric response for
each `Cell`; the predicates `PredictsContrastSpeedsTarget`,
`PredictsContrastReducesCompetitorLooks`, and
`PredictsContrastAttenuatesTypicality` constrain those predictions to match
the qualitative empirical patterns. F-statistics from the paper are
documented in prose at each predicate; numeric means are reproduced only
for the norming study (Table 5), which is itself an empirical baseline that
operationally defines the typicality manipulation.

## Theoretical Significance

The paper's central theoretical contrast pits two accounts of the contrast
effect:

1. **Referential / presupposition account** (@cite{altmann-steedman-1988}):
   the contrast effect derives from definiteness presuppositions on the
   modified NP.
2. **Lexical comparison-class account** (@cite{bierwisch-1989}): scalar
   adjectives carry a free comparison-class variable in their lexical entry,
   bound by the contextually salient set.

Experiment 3's indefinite verification task removes the definiteness
presupposition while preserving the contrast effect, supporting the lexical
account. The qualitative patterns universally quantify over `Task`, so any
theory satisfying the patterns is committed to a task-invariant mechanism.
-/

namespace SedivyEtAl1999

open Paradigms.VisualWorld

-- ============================================================================
-- §1. Study-Specific Manipulations
-- ============================================================================

/-- Typicality of the target with respect to the modifying adjective,
    determined empirically by the norming study (Table 5). -/
inductive Typicality where
  /-- Target is a clear exemplar of the modified NP. -/
  | goodToken
  /-- Target is a marginal exemplar of the modified NP. -/
  | poorToken
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A condition cell in Sedivy's 2 × 2 × 2 design. -/
structure Cell where
  contrast : ContrastCondition
  typicality : Typicality
  task : Task
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : HasContrastCondition Cell where
  contrastOf c := c.contrast
  setContrast k c := { c with contrast := k }
  contrastOf_setContrast _ _ := rfl
  setContrast_contrastOf _ := rfl
  setContrast_setContrast _ _ _ := rfl

instance : HasTask Cell where
  taskOf c := c.task
  setTask k c := { c with task := k }
  taskOf_setTask _ _ := rfl
  setTask_taskOf _ := rfl
  setTask_setTask _ _ _ := rfl

/-- Sedivy's displays are object arrays (four-object workspace) throughout
    Exps 1–3, per the paper's Methods sections. Display kind is a
    between-study constant, not a within-study manipulation, so this
    instance has no lens. -/
instance : HasDisplayKind Cell where
  displayKindOf _ := .objectArray

/-- The perceptual domain targeted by Exps 2 and 3 (scalar size adjectives:
    "tall", "short", "long"). Cross-study bridges use this to connect
    Sedivy's findings to the comparison-class typology in
    `Features.PropertyDomain`. Exp 1's intersective adjectives (color,
    material, shape) live in different domains and are not summarised
    here — see the docstring for the per-experiment breakdown. -/
def adjDomain : Features.PropertyDomain := .size

/-- The size domain requires comparison-class binding, which is the
    structural prerequisite for Bierwisch's lexical account of the
    contrast effect (§5 of @cite{sedivy-etal-1999}). This is not a
    stipulation: it follows from `Features.PropertyDomain.requiresComparisonClass`
    by reduction. -/
theorem adjDomain_requires_comparison_class :
    Features.PropertyDomain.requiresComparisonClass adjDomain = true := rfl

-- ============================================================================
-- §2. Norming Data (Table 5)
-- ============================================================================

/-! Table 5 of @cite{sedivy-etal-1999} reports a rating study used to
classify objects as good/poor tokens or contrasting objects. Subjects chose
which of {target adjective, no adjective, opposite adjective, other}
described each object best. Percentages reproduced here as exact rationals.
These data are the operational definition of the typicality manipulation:
any theory referring to "good" vs. "poor" tokens of a scalar adjective
inherits this empirical baseline. -/

/-- Good tokens: 92.5% of subjects chose the target-adjective description. -/
def normTargetAdjForGoodToken : ℚ := 925 / 1000

/-- Good tokens: 3.3% chose the bare-noun description. -/
def normNoAdjForGoodToken : ℚ := 33 / 1000

/-- Poor tokens: 19.4% chose the target-adjective description. -/
def normTargetAdjForPoorToken : ℚ := 194 / 1000

/-- Poor tokens: 69.3% chose the bare-noun description. -/
def normNoAdjForPoorToken : ℚ := 693 / 1000

/-- Contrasting objects: 75.2% chose the opposite-adjective description. -/
def normOppositeAdjForContrastObject : ℚ := 752 / 1000

/-- Norming verification: good tokens overwhelmingly receive target-adjective
    descriptions; poor tokens are predominantly bare-noun. This justifies
    the typicality manipulation across Exps 2–3. -/
theorem norming_distinguishes_token_types :
    9 / 10 < normTargetAdjForGoodToken ∧
    1 / 2 < normNoAdjForPoorToken := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [normTargetAdjForGoodToken, normNoAdjForPoorToken]

/-- Norming verification: contrasting objects are reliably described by the
    opposite-pole adjective. This is the operational definition of "scale
    contrast" in the visual paradigm. -/
theorem contrasting_object_evokes_opposite :
    7 / 10 < normOppositeAdjForContrastObject := by
  norm_num [normOppositeAdjForContrastObject]

-- ============================================================================
-- §3. Empirical Predicates
-- ============================================================================

/-! Patterns 1 and 2 are stated at the paradigm level
(`Paradigms.VisualWorld.ContrastSpeedsResponse`,
`ContrastReducesCompetitorLooks`); they consume Sedivy's
`HasContrastCondition Cell` instance to swap the contrast factor while
holding typicality and task fixed. Pattern 3 (typicality interaction)
is study-specific because typicality is not a paradigm primitive — it
is Sedivy's operationalisation of "exemplar goodness" via the norming
study. -/

/-- **Pattern 3** (Tables 6, 8, 9): contrast attenuates typicality effects.

    The typicality slowdown (poor-token RTs longer than good-token RTs) is
    smaller in the contrast condition than in the no-contrast condition.
    Mechanism: when a visual contrast pair is present, the comparison
    class is fixed by visual context rather than by stored norms about
    typical exemplars; stored typicality matters less.

    Empirical support:
    - Exp 2 latency contrast × typicality: F₁(1,21) = 3.3, P = 0.08
      (marginal). Latency typicality gap (combined): contrast 16 ms
      (554 − 538) vs. no-contrast 134 ms (690 − 556).
    - Exp 3 yes-rate contrast × typicality: F₁(1,21) = 17.13, P < 0.001;
      F₂(1,19) = 19.45, P < 0.001. The interaction is most visible in
      yes-rate (Table 8): no-contrast-poor 35% yes vs. contrast-poor 8.3%
      (good token: 1.9% vs. 4.4%).
    - Exp 3 yes-response latency contrast × typicality: F₁(1,21) = 8.77,
      P < 0.01; F₂(1,13) = 22.95, P < 0.001. -/
def ContrastAttenuatesTypicality {R : Type} [LT R] [Sub R]
    (rt : Latency Cell R) : Prop :=
  ∀ ta,
    rt ⟨.contrast, .poorToken, ta⟩ - rt ⟨.contrast, .goodToken, ta⟩ <
    rt ⟨.noContrast, .poorToken, ta⟩ - rt ⟨.noContrast, .goodToken, ta⟩

/-- A theory **satisfies the Sedivy pattern** if it predicts all three
    qualitative findings.

    - `contrast_speeds_target`: paradigm-level
      `ContrastSpeedsResponse` (Sedivy Tables 6, 9). Exp 2 latency main
      effect of contrast: F₁(1,21) = 11.62, P < 0.01. Exp 3
      yes-response latency: F₁(1,21) = 20.00, P < 0.001.
    - `contrast_reduces_competitor_looks`: paradigm-level
      `ContrastReducesCompetitorLooks` (Sedivy Tables 7, 11). Exp 2
      F₁(1,22) = 32.66, P < 0.001. Exp 3 F₁(1,19) = 12.83, P < 0.01.
    - `contrast_attenuates_typicality`: study-specific Pattern 3 above.

    Task invariance is enforced by the lens-based paradigm predicates:
    `setContrast k c` swaps the contrast condition while preserving
    `c.task`, so the predicate quantifies uniformly over Exp 2
    (`directAction`) and Exp 3 (`verification`) cells. This is the
    empirical discriminator between presupposition-based and lexical
    accounts of the contrast effect (the former predicts a task-by-
    contrast interaction; the data show task invariance). -/
structure SatisfiesSedivyPattern {R : Type} [LT R] [Sub R]
    (rt : Latency Cell R) (looks : LookProportion Cell R) : Prop where
  contrast_speeds_target : ContrastSpeedsResponse rt
  contrast_reduces_competitor_looks : ContrastReducesCompetitorLooks looks
  contrast_attenuates_typicality : ContrastAttenuatesTypicality rt

-- ============================================================================
-- §4. Non-Vacuity Witness
-- ============================================================================

/-- A trivial RT model: contrast cells get RT 0, no-contrast cells get RT 2,
    with poor tokens adding 1 in no-contrast (so the typicality gap is
    larger there). Constructed only to witness that `SatisfiesSedivyPattern`
    is satisfiable; carries no theoretical content. -/
def trivialRT : Latency Cell ℚ := fun c =>
  match c.contrast, c.typicality with
  | .contrast, _ => 0
  | .noContrast, .goodToken => 2
  | .noContrast, .poorToken => 3

/-- A trivial look model: competitor looks are 1 in contrast cells and 2 in
    no-contrast cells; other roles get 0. Witness only. -/
def trivialLooks : LookProportion Cell ℚ := fun role c =>
  match role, c.contrast with
  | .crossCategoryCompetitor, .contrast => 1
  | .crossCategoryCompetitor, .noContrast => 2
  | _, _ => 0

/-- The Sedivy pattern is satisfiable: `trivialRT` and `trivialLooks`
    jointly satisfy all three predicates. Without this witness the
    structure could in principle be uninhabited. -/
theorem trivial_satisfies_pattern :
    SatisfiesSedivyPattern trivialRT trivialLooks where
  contrast_speeds_target := by
    intro c
    obtain ⟨_, ty, _⟩ := c
    cases ty <;> simp [trivialRT]
  contrast_reduces_competitor_looks := by
    intro c
    obtain ⟨_, _, _⟩ := c
    simp [trivialLooks]
  contrast_attenuates_typicality := by
    intro ta; simp [trivialRT]; norm_num

-- ============================================================================
-- §5. Connection to Comparison-Class Semantics
-- ============================================================================

/-! The lexical-semantic account of the contrast effect (@cite{bierwisch-1989},
adopted in §5 of @cite{sedivy-etal-1999}) places a free comparison-class
variable in the lexical entry of every scalar adjective. The
`Features.PropertyDomain` infrastructure flags this with
`requiresComparisonClass`; the connection is made formal by
`adjDomain_requires_comparison_class` above.

Note: Exp 1B nonetheless found contrast effects with intersective adjectives,
attributed to *referential narrowing* rather than comparison-class binding.
The two mechanisms are theoretically distinct; `requiresComparisonClass`
captures only the comparison-class route. -/

end SedivyEtAl1999
