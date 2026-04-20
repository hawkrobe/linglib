import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Visual-World Paradigm

@cite{huettig-rommers-meyer-2011}

Shared vocabulary for the visual-world eye-tracking paradigm. A subject
sees a display of objects and hears a sentence; their eye movements reveal
incremental processing decisions before the referent is unambiguous from
the speech signal.

## Architectural role

`Paradigms/` is the contract layer between `Theories/` and
`Phenomena/Studies/`. Theories produce predictions in their native
types; bridge theorems in `Studies/` translate those predictions into
paradigm-typed predictions and prove they satisfy the empirical patterns
documented in the study file. The paradigm itself is theory-agnostic:
it specifies *what kind of input the experiment provides* and *what
shape of output a theory must produce*.

## Anchoring on a methodological review

This file's type structure follows the data-field ontology of
@cite{huettig-rommers-meyer-2011}'s methodological review of the
paradigm. Each paradigm-level type cites the section of the review it
comes from, so the lineage stays auditable. New paradigm primitives
should not be added without a corresponding review section motivating
them — the discipline is to follow existing methodological consensus
rather than invent categories.

## Lens-shaped manipulation classes

`HasContrastCondition` and `HasTask` are not projection-only — they
also carry a `set*` lens with three lens laws (`get_set`, `set_get`,
`set_set`). This is what makes them load-bearing: the paradigm-level
predicates `ContrastSpeedsResponse` and `ContrastReducesRoleLooks`
universally quantify over a base cell and apply the lens to swap the
manipulated factor, so any study whose `Cell` type instances the class
inherits the predicates without re-deriving them per design. A study
whose `Cell` type cannot provide a lawful lens for a factor should not
claim the typeclass for that factor.

`HasDisplayKind` is intentionally projection-only: display kind is
typically a *between-study* constant rather than a within-study
manipulation, so a lens would have no consumer.

## Out of scope (per `CLAUDE.md` Processing scope)

- Stimulus timing details (preview duration, display offset) — typically
  constant within a study, not a typed manipulation
- Participant population (adult/child/bilingual/patient) — study metadata
- Data analysis pipeline (regions of interest, time windows, ANOVA vs.
  growth curves) — analysis decisions, not paradigm contract
- Eye-tracker apparatus (saccade detection thresholds, sampling rate) —
  measurement modality
-/

namespace Paradigms.VisualWorld

-- ============================================================================
-- §1. Display
-- ============================================================================

/-- Display kind, per @cite{huettig-rommers-meyer-2011} §2.1.1.

    Different display kinds tap different representations:

    - `semiRealisticScene`: line drawings of scenes; activates world
      knowledge about scenes/events. Used by Altmann & Kamide (1999).
    - `objectArray`: separate objects laid out on a workspace or screen.
      Minimises scene-level world knowledge. Used by Tanenhaus et al.
      (1995), Sedivy et al. (1999), and most adjective studies.
    - `printedWord`: written words instead of pictures. Taps orthographic
      processing. Introduced by Huettig & McQueen (2007). -/
inductive DisplayKind where
  | semiRealisticScene
  | objectArray
  | printedWord
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Role an object plays in the visual display, per
    @cite{huettig-rommers-meyer-2011} §2.1.2.

    The four-way split is the standard vocabulary for studies that
    cross a same-category-contrast manipulation (Sedivy 1999, Engelhardt
    2006, Ronderos 2024). Studies without a contrast manipulation
    typically use only `target` and `distractor`. Cohort/phonological
    paradigms (Allopenna 1998, Huettig & Altmann 2005) use additional
    role distinctions (cohort competitor, rhyme competitor) that are
    not yet enumerated here — extend this type rather than encoding them
    in study-local enums. -/
inductive ObjectRole where
  /-- Intended referent of the spoken expression. -/
  | target
  /-- Same category as target, opposite pole on the relevant scale.
      Present only in *contrast* trials. -/
  | contrastingObject
  /-- Different category from target, but further along the relevant
      scale. Always present. -/
  | crossCategoryCompetitor
  /-- Phonological cohort competitor (shares onset with target word).
      Used in Allopenna et al. (1998), Huettig & Altmann (2005). -/
  | cohortCompetitor
  /-- Rhyme competitor (shares offset/rhyme with target word).
      Used in Allopenna et al. (1998). -/
  | rhymeCompetitor
  /-- Semantic competitor (semantically related to target, no
      phonological/visual overlap). Used in Huettig & Altmann (2005). -/
  | semanticCompetitor
  /-- Unrelated object. Always present. -/
  | distractor
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Whether the display contains a same-category contrasting object.

    The canonical between-condition manipulation in adjective-driven
    contrastive-inference paradigms. -/
inductive ContrastCondition where
  | contrast
  | noContrast
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Task
-- ============================================================================

/-- Communicative task, per @cite{huettig-rommers-meyer-2011} §2.1.3.

    Task choice affects which competition effects appear:
    look-and-listen tasks reveal general language–vision interactions,
    while direct-action tasks may impose specific task demands.

    - `directAction`: "Pick up the candy" (Allopenna et al. 1998,
      Sedivy et al. 1999 Exp 2 instruction).
    - `lookAndListen`: "The boy will eat the cake" (Altmann & Kamide
      1999, Huettig & Altmann 2005).
    - `verification`: "Is there a tall glass?" (Sedivy et al. 1999
      Exp 3).
    - `description`: "Tell me what you see" (production studies; Griffin
      & Bock 2000, Meyer et al. 1998). -/
inductive Task where
  | directAction
  | lookAndListen
  | verification
  | description
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §3. Observable shapes
-- ============================================================================

/-! These are *observable* shapes — the form data takes when the
eye-tracker reports it (or when a theory's predictions have been
projected through a linking hypothesis to that form). They are
deliberately polymorphic over the codomain `R`: empirical data tables
naturally live in `ℚ` (proportions, mean ms), while theory predictions
ride along `ℝ` (RSA posteriors, surprisal in nats). The qualitative
predicates in §5 only use `<` (and `Sub` for difference scores), so
they apply uniformly across codomains.

**Linking-hypothesis caveat (deferred refactor)**: a theory like
incremental RSA produces a *posterior* `Word → Referent → ℝ`, not
fixation proportions. Mapping a posterior to a `LookProportion`
requires an explicit linking hypothesis (e.g. Allopenna-Magnuson-
Tanenhaus 1998 Luce-choice over activations; or a Bayesian "looks
proportional to L1 posterior" assumption). Today studies bridge that
gap inline with a docstring naming the linking hypothesis. If/when a
second linking hypothesis enters the codebase, extract them into a
typed `LinkingHypothesis` module and make the bridge theorem statement
mention the linking hypothesis by name. -/

/-- Latency observable: per-cell response time (ms in empirical
    tables; an arbitrary `R` for theory predictions that ride along a
    different numeric type). -/
abbrev Latency (Cell : Type) (R : Type) := Cell → R

/-- Fixation-proportion observable: per-cell proportion of fixations on
    each `ObjectRole`. The role argument lets predicates make role-
    specific claims ("contrast reduces *competitor* looks") at the type
    level. Codomain `R` is polymorphic; see the §3 docstring. -/
abbrev LookProportion (Cell : Type) (R : Type) := ObjectRole → Cell → R

-- ============================================================================
-- §4. Cell typeclasses
-- ============================================================================

/-! Studies' `Cell` types vary in what manipulations they cross
(typicality, task, prime, frequency, …). The shared minimum is that
every visual-world cell with a contrast manipulation has a contrast
condition AND a way to swap that condition while holding the rest of
the cell constant. The lens laws (`get_set`, `set_get`, `set_set`)
make `setContrast` a proper lens; the paradigm-level predicates in §5
rely on them to express "swapping the contrast condition slows RT" as
a statement that quantifies over the rest of the cell uniformly. -/

/-- `Cell` has a contrast condition that can be swapped without touching
    other factors. Lens laws are stated as fields so that the paradigm
    predicates can rewrite with them when discharging concrete proofs. -/
class HasContrastCondition (Cell : Type) where
  contrastOf : Cell → ContrastCondition
  setContrast : ContrastCondition → Cell → Cell
  contrastOf_setContrast : ∀ k c, contrastOf (setContrast k c) = k
  setContrast_contrastOf : ∀ c, setContrast (contrastOf c) c = c
  setContrast_setContrast :
      ∀ k₁ k₂ c, setContrast k₁ (setContrast k₂ c) = setContrast k₁ c

/-- `Cell` has a task that can be swapped without touching other factors.
    Same lens-law shape as `HasContrastCondition`. -/
class HasTask (Cell : Type) where
  taskOf : Cell → Task
  setTask : Task → Cell → Cell
  taskOf_setTask : ∀ k c, taskOf (setTask k c) = k
  setTask_taskOf : ∀ c, setTask (taskOf c) c = c
  setTask_setTask :
      ∀ k₁ k₂ c, setTask k₁ (setTask k₂ c) = setTask k₁ c

/-- `Cell` has a display kind. Projection-only: display kind is a
    between-study constant in essentially all visual-world studies, so
    no lens is required. Studies that *do* manipulate display kind
    within-subjects should add their own lens API rather than inflating
    this class. -/
class HasDisplayKind (Cell : Type) where
  displayKindOf : Cell → DisplayKind

-- ============================================================================
-- §5. Paradigm-level qualitative predicates
-- ============================================================================

/-! These predicates state empirical patterns at the paradigm level —
they are written in terms of `setContrast` (the lens), so any `Cell`
type with a `HasContrastCondition` instance can claim them without
re-deriving the universal-quantification machinery per study. The
predicates are *abstract*; they express a shape ("swapping the contrast
condition reduces RT") that empirical studies and theoretical models
may or may not satisfy. -/

variable {Cell : Type} {R : Type}

/-- A latency observable satisfies the *contrast-speeds-response*
    pattern if swapping any cell's contrast condition from `contrast`
    to `noContrast` strictly increases the latency. The lens laws
    guarantee that "swapping" only changes the contrast factor. -/
def ContrastSpeedsResponse [HasContrastCondition Cell] [LT R]
    (rt : Latency Cell R) : Prop :=
  ∀ c : Cell,
    rt (HasContrastCondition.setContrast .contrast c) <
    rt (HasContrastCondition.setContrast .noContrast c)

/-- A look-proportion observable satisfies the
    *contrast-reduces-role-looks* pattern at `role` if swapping any
    cell's contrast condition from `contrast` to `noContrast` strictly
    increases the proportion of looks to `role`. The role argument
    lets a study scope the claim to a particular competitor type. -/
def ContrastReducesRoleLooks [HasContrastCondition Cell] [LT R]
    (role : ObjectRole) (looks : LookProportion Cell R) : Prop :=
  ∀ c : Cell,
    looks role (HasContrastCondition.setContrast .contrast c) <
    looks role (HasContrastCondition.setContrast .noContrast c)

/-- Specialisation of `ContrastReducesRoleLooks` to the
    cross-category-competitor role — the canonical effect in
    same-category contrast paradigms (Sedivy 1999, etc.). -/
abbrev ContrastReducesCompetitorLooks [HasContrastCondition Cell] [LT R]
    (looks : LookProportion Cell R) : Prop :=
  ContrastReducesRoleLooks (Cell := Cell) (R := R) .crossCategoryCompetitor looks

/-- A look-proportion observable satisfies the
    *contrast-speeds-target-looks* pattern if swapping any cell's
    contrast condition from `contrast` to `noContrast` strictly
    *decreases* the proportion of looks to the target. (Sedivy 1999
    Tables 7, 11 also show target-look acceleration; this is the dual
    of `ContrastReducesCompetitorLooks`.) -/
def ContrastSpeedsTargetLooks [HasContrastCondition Cell] [LT R]
    (looks : LookProportion Cell R) : Prop :=
  ∀ c : Cell,
    looks .target (HasContrastCondition.setContrast .noContrast c) <
    looks .target (HasContrastCondition.setContrast .contrast c)

-- ============================================================================
-- §6. Stratified and effect-size predicates
-- ============================================================================

/-! Studies that cross *multiple* within-subject factors (e.g.
@cite{ronderos-etal-2024}'s 2 × 3 contrast × adjective-type design)
need to express the contrast-effect predicates *per stratum* rather
than universally over all cells — Ronderos finds a contrast effect for
color and scalar adjectives but *not* for material adjectives, so a
universal claim over the cell type is empirically false.

The `When` variants below take a sub-cell predicate `P : Cell → Prop`
and restrict the contrast-effect claim to cells satisfying `P`. The
universal-form predicates of §5 are the special case `P := fun _ =>
True` (made explicit in `ContrastReducesRoleLooks_iff_when_True`).

The `contrastEffect` accessor projects out the difference between the
no-contrast and contrast values at a given cell — the paradigm-level
shape of the "target advantage" or "competitor reduction" measure that
downstream studies report. With `[Sub R]` we can quantitatively
compare effects across strata via `ContrastEffectLargerFor`, which is
the qualitative shape of an "X × condition" interaction. The
predicates here only constrain *qualitative* relationships (strict
inequality between matched cells); statistical readings ("the mean
β is larger for color than material") need a real-valued aggregator
and are out of scope for the paradigm contract. -/

/-- Effect size of the contrast manipulation on `role` looks at cell
    `c`: the difference between the no-contrast and contrast values.
    Positive when contrast strictly reduces `role` looks (the canonical
    direction in same-category contrast paradigms). The lens laws on
    `setContrast` ensure this depends only on the non-contrast factors
    of `c`. -/
def contrastEffect [HasContrastCondition Cell] [Sub R]
    (role : ObjectRole) (looks : LookProportion Cell R) (c : Cell) : R :=
  looks role (HasContrastCondition.setContrast .noContrast c) -
  looks role (HasContrastCondition.setContrast .contrast c)

/-- Stratified `ContrastReducesRoleLooks`: the role-look reduction holds
    for every cell satisfying `P`. The original universal-form
    predicate is `ContrastReducesRoleLooksWhen (fun _ => True)`. -/
def ContrastReducesRoleLooksWhen [HasContrastCondition Cell] [LT R]
    (P : Cell → Prop) (role : ObjectRole) (looks : LookProportion Cell R) :
    Prop :=
  ∀ c : Cell, P c →
    looks role (HasContrastCondition.setContrast .contrast c) <
    looks role (HasContrastCondition.setContrast .noContrast c)

/-- Specialisation of `ContrastReducesRoleLooksWhen` to the
    cross-category-competitor role. -/
abbrev ContrastReducesCompetitorLooksWhen [HasContrastCondition Cell] [LT R]
    (P : Cell → Prop) (looks : LookProportion Cell R) : Prop :=
  ContrastReducesRoleLooksWhen (Cell := Cell) (R := R)
    P .crossCategoryCompetitor looks

/-- Interaction predicate: the contrast effect on `role` looks is
    strictly larger in the `P` stratum than in the `Q` stratum. The
    paradigm-level shape of an "X × condition" interaction — e.g.
    @cite{ronderos-etal-2024}'s adjective-type × contrast interaction,
    where color/scalar cells show a contrast effect that material cells
    lack. Universal quantification over both strata is the strongest
    qualitative reading: every `P`-cell's effect strictly exceeds every
    `Q`-cell's effect. Mean-over-mean readings need a real-valued
    aggregator; the paradigm only commits to the strict-pairwise
    qualitative shape. -/
def ContrastEffectLargerFor [HasContrastCondition Cell] [Sub R] [LT R]
    (role : ObjectRole) (P Q : Cell → Prop) (looks : LookProportion Cell R) :
    Prop :=
  ∀ cP cQ : Cell, P cP → Q cQ →
    contrastEffect role looks cQ < contrastEffect role looks cP

/-- The original universal-form `ContrastReducesRoleLooks` is the
    `True`-stratum case of `ContrastReducesRoleLooksWhen`. Studies that
    move to the stratified API can recover their existing universal
    claims by passing the trivial filter. -/
theorem ContrastReducesRoleLooks_iff_when_True
    [HasContrastCondition Cell] [LT R]
    (role : ObjectRole) (looks : LookProportion Cell R) :
    ContrastReducesRoleLooks role looks ↔
    ContrastReducesRoleLooksWhen (fun _ => True) role looks := by
  unfold ContrastReducesRoleLooks ContrastReducesRoleLooksWhen
  exact ⟨fun h c _ => h c, fun h c => h c trivial⟩

-- ============================================================================
-- §7. Baseline-condition role-sum predicates
-- ============================================================================

/-! Several visual-world studies report a *baseline* analysis comparing
overall fixations on a *subset of roles* in the no-contrast (or other
designated baseline) condition across strata. Examples:

- @cite{aparicio-xiang-kennedy-2015} / @cite{aparicio-2017}: in the
  No-Contrast baseline, fixations on target + cross-category competitor
  are lower for scalar adjectives than for color adjectives, attributed
  to scalar adjectives requiring more comparison-class processing time
  (more distributed gaze across all four display objects).
- @cite{ronderos-etal-2024}: extends the same finding to the
  scalar-vs-material comparison and treats it as evidence for an
  Aparicio-style semantic factor distinct from the contrast effect
  itself.

The pattern is: pick a baseline value of the contrast factor, sum
`looks` across a designated subset of roles (target + competitor in the
papers above), and compare the sums between strata. The predicate
below packages this. The role-sum is computed via `List.sum` so it
generalises to any subset; the baseline is the contrast condition the
sum is computed in. -/

/-- Sum of `looks` across a list of roles at cell `c`. Generalises the
    "looks at target + competitor" projection used in baseline analyses. -/
def roleSum [Add R] [Zero R] (roles : List ObjectRole)
    (looks : LookProportion Cell R) (c : Cell) : R :=
  (roles.map (fun r => looks r c)).sum

/-- In the `baseline` contrast condition, the role-sum for `roles` is
    strictly smaller for cells satisfying `P` than for cells satisfying
    `Q`. Captures Aparicio-style "stratum X requires more processing"
    findings expressed as reduced fixations on the critical-role subset.
    The lens fixes the contrast factor to `baseline` so the comparison
    isolates the stratum effect from any contrast effect. -/
def RoleSumLowerInBaselineWhen [HasContrastCondition Cell] [Add R] [Zero R]
    [LT R] (baseline : ContrastCondition) (roles : List ObjectRole)
    (P Q : Cell → Prop) (looks : LookProportion Cell R) : Prop :=
  ∀ cP cQ : Cell, P cP → Q cQ →
    roleSum roles looks (HasContrastCondition.setContrast baseline cP) <
    roleSum roles looks (HasContrastCondition.setContrast baseline cQ)

end Paradigms.VisualWorld
