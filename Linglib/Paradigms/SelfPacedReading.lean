/-!
# Self-Paced Reading Paradigm

@cite{jegerski-2014}

Shared vocabulary for the self-paced reading (SPR) experimental paradigm —
a sentence-level on-line method in which participants advance through a
segmented stimulus one segment at a time and per-segment reading times
are taken as indices of processing cost.

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
@cite{jegerski-2014}'s methodological review of SPR. Each paradigm-level
type cites the section of the chapter it comes from, so the lineage
stays auditable. New paradigm primitives should not be added without a
corresponding review section motivating them — the discipline is to
follow existing methodological consensus rather than invent categories.

The chapter predates the bidirectional masked SPR (BSPR) variant
(@cite{paape-vasishth-2026}); that constructor of `Presentation` is
flagged as post-Jegerski.

## Out of scope (per `CLAUDE.md` Processing scope)

- Statistical-model specifications (mixed-effects formulae, Bayes-factor
  thresholds, Bonferroni corrections, log/inverse transformations) —
  analysis pipeline, not paradigm contract
- Trial structure (cue + stimulus + distractor sequencing) — constant
  within a study, not a typed manipulation
- Stimulus phenomenon classes (ambiguities, anomalies, dependencies) —
  about content of stimuli, not paradigm contract
- Counterbalancing details, filler ratios, pseudo-randomization
  procedures — study-internal design choices
- Participant population (L1, age, dialect, L2 proficiency) — study
  metadata, not paradigm contract
-/

namespace Paradigms.SelfPacedReading

-- ============================================================================
-- §1. Region — offset from a designated critical region
-- ============================================================================

/-! Per @cite{jegerski-2014} ("What is Looked at and Measured"), an SPR
stimulus is broken into *regions of interest*, each contributing a
single reading-time data point. The chapter uses absolute 1-indexed
region numbering ("Region 1 is a subject NP") for stimulus design;
theorem statements about reading-time effects more naturally use
*offset from a designated critical region* ("the effect appeared at
verb+1"). This file encodes the latter, since the paradigm's downstream
qualitative predicates speak about effect locations relative to a
manipulation's critical region.

`Region` is `Int` rather than an enum: integers admit precritical
regions for free (negative offsets), arithmetic for free, and follow
the mathlib convention of using a structured numeric type when one
suffices. The named convenience constructors `critical`, `spillover n`,
`precritical n` keep call sites readable. -/

/-- Offset from a designated critical region. `0` is the critical region;
    positive offsets are spillover regions; negative offsets are
    precritical regions. -/
abbrev Region := Int

namespace Region

/-- The designated critical region of the stimulus. -/
def critical : Region := 0

/-- The `n`-th spillover region (post-critical). -/
def spillover (n : Nat) : Region := (n : Int)

/-- The `n`-th precritical region (pre-critical). -/
def precritical (n : Nat) : Region := -(n : Int)

/-- A region is in the spillover window if it lies strictly after the
    critical region. -/
def IsSpillover (r : Region) : Prop := r > 0

/-- A region is precritical if it lies strictly before the critical region. -/
def IsPrecritical (r : Region) : Prop := r < 0

instance (r : Region) : Decidable r.IsSpillover := by
  unfold IsSpillover; infer_instance

instance (r : Region) : Decidable r.IsPrecritical := by
  unfold IsPrecritical; infer_instance

end Region

-- ============================================================================
-- §2. Presentation
-- ============================================================================

/-! Per @cite{jegerski-2014} (Figs 2.1–2.3), historical SPR displays vary
along two orthogonal axes: cumulative-vs-noncumulative (whether previous
segments stay visible) and centered-vs-linear (where on the screen each
segment appears). Three of the four combinations have been used in
practice. The chapter establishes the modern default (noncumulative +
linear, "moving window") and notes the others are deprecated:

- Cumulative is "problematic because most participants develop a reading
  strategy in which they reveal several segments of a stimulus at a time
  before reading them all at once" (Ferreira & Henderson 1990; Just et
  al. 1982, both cited in @cite{jegerski-2014}).
- Centered display is "avoided with SPR because it is less like normal
  reading" (@cite{jegerski-2014}).

This enum names the historically-attested displays as flat alternatives
rather than encoding the two axes separately, matching how SPR studies
actually describe their methods. -/

inductive Presentation where
  /-- Noncumulative + linear; the modern de facto standard. Each segment
      is unmasked one at a time in normal left-to-right (or right-to-left)
      succession. Same as "moving window." Per @cite{jegerski-2014}. -/
  | movingWindow
  /-- Cumulative + linear; previous segments stay visible as the next
      segment is unmasked. Deprecated (multi-segment-reveal strategy).
      Per @cite{jegerski-2014} citing Ferreira & Henderson 1990;
      Just et al. 1982. -/
  | cumulative
  /-- Noncumulative + centered; segments overwrite at screen center.
      Avoided in SPR (less like normal reading). Per @cite{jegerski-2014}. -/
  | centered
  /-- Bidirectional masked SPR (BSPR): segments can be re-read by pressing
      the back button, with masking. A post-@cite{jegerski-2014} variant
      used by @cite{paape-vasishth-2026}. -/
  | bidirectional
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- §3. Segmentation
-- ============================================================================

/-! Per @cite{jegerski-2014} ("Issues in the Development and Presentation
of Stimuli", ex. (5)–(6)), regions of interest can be either single words
or multi-word phrases. The choice is "typically a compromise between the
conflicting goals of maximizing the level of detail in the reading time
data and maximizing the ecological validity of the experimental task."
Word-by-word data can be summed to phrase-by-phrase post-hoc; the reverse
is not possible. -/

inductive Segmentation where
  /-- Word-by-word: each region is a single word. Higher data resolution;
      may induce overly-incremental processing. Per @cite{jegerski-2014}
      ex. (5). -/
  | wordByWord
  /-- Phrase-by-phrase: each region is a meaningful phrase. Lower data
      resolution; closer to normal reading. Per @cite{jegerski-2014}
      ex. (6). -/
  | phraseByPhrase
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- §4. Distractor task
-- ============================================================================

/-! Per @cite{jegerski-2014} ("Issues in the Development..."), most SPR
studies follow each stimulus with a distractor task to maintain
attention. Two main types are attested. The chapter expresses a strong
methodological preference for comprehension questions over acceptability
judgments in SLA research, citing the demonstrated effect of distractor
type on processing strategy (Aaronson & Scarborough 1976; Havik et al.
2009; Leeser, Brandl & Weissglass 2011, all cited in @cite{jegerski-2014}). -/

inductive DistractorTask where
  /-- Meaning-based comprehension question. Preferred per
      @cite{jegerski-2014}; avoids inducing metalinguistic processing
      strategy on the SPR task itself. -/
  | comprehensionQuestion
  /-- Off-line acceptability judgment. Used in some psycholinguistic
      studies but has known cross-contamination effects on RT data
      (Luka & Barsalou 2005, cited in @cite{jegerski-2014}). -/
  | acceptabilityJudgment
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- §5. Observable shapes
-- ============================================================================

/-! These are *observable* shapes — the form data takes when the SPR
apparatus reports it (or when a theory's predictions have been projected
through a linking hypothesis to that form). They are deliberately
polymorphic over the codomain `R`: empirical data tables naturally live
in `ℚ` (mean ms, log-RT coefficients), while theory predictions ride
along `ℝ` (surprisal in nats, retrieval-cost expectations). The
qualitative predicates in §6 only use `<` and so apply uniformly across
codomains.

**Linking-hypothesis caveat (deferred refactor)**: a theory like
surprisal produces a per-word information-theoretic value, not a reading
time. Mapping surprisal to a `ReadingTime` requires an explicit linking
hypothesis (e.g. a logarithmic link function with empirically-fit
coefficients). Today studies bridge that gap inline with a docstring
naming the linking hypothesis. If/when a second linking hypothesis
enters the codebase, extract them into a typed `LinkingHypothesis`
module and make bridge theorem statements mention the linking
hypothesis by name. -/

/-- Per-cell, per-region reading time. Polymorphic codomain `R`
    (typically `ℚ` for empirical ms data, `ℝ` for theory predictions). -/
abbrev ReadingTime (Cell : Type) (R : Type) := Cell → Region → R

-- ============================================================================
-- §6. Paradigm-level qualitative predicates
-- ============================================================================

/-! These predicates state empirical patterns at the paradigm level,
quantifying over arbitrary cell pairs. SPR studies vary in what
manipulations they cross (garden-path vs unambiguous, coercion vs
control, congruous vs incongruous, agreement-violating vs grammatical),
so the paradigm cannot provide a single canonical lens-based class for
"the manipulated factor" the way `Paradigms/VisualWorld.lean` does for
the contrast manipulation. Studies provide cell pairs explicitly; the
paradigm provides the qualitative shapes that empirical patterns and
theoretical predictions may inhabit. -/

variable {Cell : Type} {R : Type}

/-- A reading-time observable satisfies the *region-RT-higher* pattern
    at `region` for the pair `(slowCell, fastCell)` if the slow cell's
    RT at that region strictly exceeds the fast cell's. The canonical
    qualitative shape of a per-region SPR effect. -/
def RegionRTHigher [LT R] (rt : ReadingTime Cell R)
    (slowCell fastCell : Cell) (region : Region) : Prop :=
  rt fastCell region < rt slowCell region

/-- A reading-time observable satisfies the *spillover* pattern for the
    pair `(slowCell, fastCell)` if the slow cell's RT strictly exceeds
    the fast cell's at *some* spillover region. The canonical
    qualitative shape of a delayed processing effect surfacing
    post-critical (e.g., garden-path reanalysis cost at verb+1). -/
def Spillover [LT R] (rt : ReadingTime Cell R)
    (slowCell fastCell : Cell) : Prop :=
  ∃ r : Region, r.IsSpillover ∧ rt fastCell r < rt slowCell r

/-- A reading-time observable satisfies the *critical-region effect*
    pattern if the slow cell's RT strictly exceeds the fast cell's at
    the critical region itself (no spillover delay). -/
def CriticalEffect [LT R] (rt : ReadingTime Cell R)
    (slowCell fastCell : Cell) : Prop :=
  rt fastCell .critical < rt slowCell .critical

-- ============================================================================
-- §7. Stratified predicates
-- ============================================================================

/-! Studies that report effects in some strata only (e.g., AlstottAravind
2026's coercion effects in completive but not inchoative conditions)
need stratified versions of the §6 predicates. The `When P` family
restricts the effect claim to cells satisfying `P`. The unrestricted
predicates of §6 are recoverable by passing `fun _ => True`. -/

/-- Stratified `RegionRTHigher`: at `region`, every `P`-cell pair shows
    higher RT than every `P`-cell pair. The unrestricted form quantifies
    over arbitrary pairs and recovers the §6 shape via `True`. -/
def RegionRTHigherWhen [LT R] (rt : ReadingTime Cell R)
    (P : Cell → Prop) (region : Region) : Prop :=
  ∀ slow fast : Cell, P slow → P fast → rt fast region < rt slow region

/-- Stratified `Spillover`: a spillover region exists at which `P`-cells
    show strictly higher RT than `P`-cells. -/
def SpilloverWhen [LT R] (rt : ReadingTime Cell R)
    (P : Cell → Prop) : Prop :=
  ∃ r : Region, r.IsSpillover ∧
    ∀ slow fast : Cell, P slow → P fast → rt fast r < rt slow r

end Paradigms.SelfPacedReading
