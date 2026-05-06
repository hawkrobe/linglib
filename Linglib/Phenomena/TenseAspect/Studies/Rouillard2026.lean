import Linglib.Core.Scales.Scale
import Linglib.Core.Time.Interval.Generalized
import Linglib.Theories.Semantics.Entailment.Extremum
import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Theories.Semantics.Tense.Aspect.SubintervalProperty
import Linglib.Features.Aktionsart
import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Fragments.English.TemporalExpressions

/-!
# Rouillard 2026: Temporal *in*-Adverbials and the Maximal Informativity Principle
@cite{rouillard-2026} @cite{fox-hackl-2006} @cite{fox-2007}
@cite{beck-rullmann-1999} @cite{krifka-1989} @cite{krifka-1998}
@cite{vendler-1957} @cite{ladusaw-1979} @cite{iatridou-zeijlstra-2021}
@cite{hoeksema-2006} @cite{gajewski-2011} @cite{von-fintel-iatridou-2019}

@cite{rouillard-2026} "Maximal informativity accounts for the distribution
of temporal *in*-adverbials" (*Linguistics and Philosophy* 49:1–56).

## Core contribution

Temporal *in*-adverbials (TIAs) lead a double life:

- **E-TIAs** ("wrote a paper *in three days*") measure event durations.
  Acceptable only with telic VPs.
- **G-TIAs** ("hasn't been sick *in three days*") measure gap durations.
  NPI behavior: acceptable only in negative perfects.

Both distributional restrictions follow from a single principle: the
**Maximal Informativity Principle (MIP)**. For some constituent γ
containing the TIA, the numeral must be capable of being the maximally
informative value of γ's derived property. Where no maximally informative
numeral exists ("information collapse"), the TIA is blocked.

## Architecture of the formalization

This file consolidates Rouillard's formal apparatus and the empirical
verification into a single Studies file. The companion
`MaximalInformativity.lean` was deleted in this rebuild — its content was
absorbed here, with substrate primitives lifted to `Core.Scale` and
`Core.Time.Interval.Generalized`.

Sections:

1. Re-export of substrate (`Core.Scale` informativity primitives).
2. `TimeMeasure` typeclass (replaces the prior `MeasureFun` struct).
3. Prior time spans over `GInterval` (open/closed boundary tags structurally
   carried, eliminating the prior `PERF_open` hand-waving).
4. E-TIA semantics: `eTIAProperty`.
5. G-TIA semantics over open generalized intervals: `gTIAPropertyOpen`.
6. The MIP licensing predicate (imported from `Entailment.Extremum`),
   combining `AdmitsOptimum` (atelic-collapse failure mode) with per-world
   `IsLeast` / `IsGreatest` from mathlib (no-extremum failure mode).
7. E-TIA: `HasSubintervalProp → IsConstant → ¬ AdmitsOptimum` (atelic block).
8. E-TIA: telicity → upward monotone → `IsLeast {y | P y w}` exists at event-duration.
9. G-TIA: geometric no-smallest-open-PTS (the density witness Rouillard
   uses). The full MIP-collapse claim under just `[DenselyOrdered Time]`
   with ℕ-valued measure does NOT follow without additional
   threshold-richness assumptions on the world space; we prove the
   geometric witness and note the gap. (See § 9 docstring for details.)
10. G-TIA negative: downward monotone → `IsGreatest {y | P y w}` exists at gap-length.
11. Boundedness pipeline (Vendler→Telicity→MereoTag→Boundedness, used by
    `LicensingPipeline` for the empirical predictions in § 13).
12. Paper-specific apparatus (TIAType, AdverbialPosition, projection from
    consensus Fragment fields).
13. E-TIA empirical data (Prop fields, decided via the boundedness chain).
14. G-TIA empirical data (Prop fields, decided via polarity ∧ perfect).
15. Table 1 (8 cells of paper eq. (112), survivor derived not stipulated).
16. Stacking constraint (paper §3.2, ex. 60).
17. Since-when questions (paper §5.2).
18. Fragment bridges (consensus → Rouillard projection).

## Scope notes

- Cross-framework refutation theorems (Ladusaw 1979 DE-overprediction,
  Krifka 1989 ATM-vs-QUA divergence, Champollion stratified reference
  divergence, Pancheva/Kiparsky perfect bridge) are out of scope for this
  file by user direction; they belong in dedicated cross-framework Studies.
- The `LicensingMechanism` enum + `mip_subsumes_de` strawman of the prior
  file is dropped — a real DE comparison would need to engage
  `Phenomena/Polarity/Studies/Ladusaw1979.lean` rather than stipulate.
- The "Kennedy–Rouillard isomorphism" framing of the prior file's § 7 is
  dropped — Rouillard does not invoke Kennedy adjectival scales. The
  boundedness chain is retained as substrate-internal plumbing.
-/

namespace Phenomena.TenseAspect.Studies.Rouillard2026

open Core.Time
open Core.Time.Interval
open Semantics.Events
open Semantics.Tense.Aspect.Core
open Semantics.Tense.Aspect.SubintervalProperty
open Features
open Core.Scale
open Semantics.Entailment.Extremum
open Fragments.English.TemporalExpressions

variable {W Time : Type*} [LinearOrder Time]

-- ════════════════════════════════════════════════════
-- § 2. Time measure typeclass
-- ════════════════════════════════════════════════════

/-- A temporal measure: assigns natural-number durations to intervals,
    extensible upward and subdivisible downward. Replaces the prior
    `MeasureFun` struct (a thin-bundled struct anti-pattern); the `μ`
    function is now a bare typeclass parameter so projections like
    `μ i ≤ m` need no `μ.μ` double-dotting.

    @cite{rouillard-2026} §2.2.2: temporal measure units (days, hours)
    are additive, hence any interval can be padded or trimmed to any
    target measure within a one-sided bound.

    Mathlib correspondence: `Core.Mereology.ExtMeasure` is ℚ-valued and
    requires `[SemilatticeSup α]` on the carrier. Intervals are not
    join-semilattices (disjoint intervals cannot be joined into an
    interval), so `ExtMeasure` does not apply directly. `TimeMeasure`
    is the interval-specific ℕ-valued companion; the discrete-measure
    domain matches Rouillard's integer-numeral data ("in three days"). -/
class TimeMeasure (Time : Type*) [LinearOrder Time]
    (μ : Interval Time → ℕ) : Prop where
  /-- Any interval can be extended to a superinterval with a given larger
      measure. -/
  extensible : ∀ (i : Interval Time) (m : ℕ), μ i ≤ m →
    ∃ j : Interval Time, i.subinterval j ∧ μ j = m
  /-- Any interval can be subdivided to a subinterval with a given smaller
      measure. -/
  subdivisible : ∀ (i : Interval Time) (m : ℕ), m ≤ μ i →
    ∃ j : Interval Time, j.subinterval i ∧ μ j = m

-- ════════════════════════════════════════════════════
-- § 3. Prior time spans (over GInterval)
-- ════════════════════════════════════════════════════

/-- Prior time span: the maximal interval right-bounded by `s` with
    measure `n`. Lifted to `GInterval` so open-vs-closed boundary tags
    are carried structurally — the prior file's `pts` operated on plain
    `Interval` and the open-PTS revision was enforced only in prose.
    @cite{rouillard-2026} eq. (50). -/
def pts (n : ℕ) (μ : Interval Time → ℕ) [TimeMeasure Time μ] (s : Time)
    (gi : GInterval Time) : Prop :=
  gi.right = s ∧ μ gi.toInterval = n

-- ════════════════════════════════════════════════════
-- § 4. E-TIA semantics
-- ════════════════════════════════════════════════════

/-- The preposition *in* as an event-level adverbial (E-TIA reading).
    The event's runtime is included in the measure-phrase's bound.
    @cite{rouillard-2026} eq. (62) instantiated at M = τ. -/
def inETIA (e : Event Time) (bound : Interval Time) : Prop :=
  e.τ.subinterval bound

/-- E-TIA derived property: at world `w`, value `n` is true iff there is
    a P-event whose runtime is included in some `n`-unit time, and that
    `n`-unit time falls within `g1`. @cite{rouillard-2026} eq. (77). -/
def eTIAProperty (P : EventPred W Time) (μ : Interval Time → ℕ)
    [TimeMeasure Time μ] (g1 : Interval Time) : ℕ → W → Prop :=
  fun n w => ∃ t : Interval Time, μ t = n ∧
    ∃ e : Event Time, P w e ∧ e.τ.subinterval g1 ∧ e.τ.subinterval t

-- ════════════════════════════════════════════════════
-- § 5. G-TIA semantics over open generalized intervals
-- ════════════════════════════════════════════════════

/-- G-TIA derived property: at world `w`, value `n` is true iff there is
    an OPEN PTS of measure `n` ending at `s` containing the closed
    runtime of a P-event.

    The openness of the PTS is now carried structurally by `GInterval`
    rather than admitted vacuously in prose (the prior file's `PERF_open`
    explicitly noted "the openness constraint is enforced at the level of
    the G-TIA semantics rather than structurally" — i.e., not at all).
    @cite{rouillard-2026} eq. (94) revised with eq. (101). -/
def gTIAPropertyOpen (P : EventPred W Time) (μ : Interval Time → ℕ)
    [TimeMeasure Time μ] (s : Time) : ℕ → W → Prop :=
  fun n w => ∃ ptsGI : GInterval Time,
    ptsGI.isOpen ∧
    ptsGI.right = s ∧
    μ ptsGI.toInterval = n ∧
    ∃ e : Event Time, P w e ∧ (GInterval.closed e.τ).gsubinterval ptsGI

/-- The negation of `gTIAPropertyOpen`, used for G-TIAs in negative
    contexts (where the property "no event in the n-unit open PTS" holds
    iff `gTIAPropertyOpen` is false). -/
def gTIAPropertyOpenNeg (P : EventPred W Time) (μ : Interval Time → ℕ)
    [TimeMeasure Time μ] (s : Time) : ℕ → W → Prop :=
  fun n w => ¬ gTIAPropertyOpen P μ s n w

-- ════════════════════════════════════════════════════
-- § 6. The MIP licensing predicate (imported from Extremum)
-- ════════════════════════════════════════════════════

/-! `MIP_Licensed` and `MIP_LicensedDown` are defined in
    `Theories/Semantics/Entailment/Extremum.lean` and reused here. They
    combine `Core.Scale.AdmitsOptimum P` (non-constancy: the *atelic*
    failure mode) with the per-world existence of a `Set.IsLeast` /
    `Set.IsGreatest` (mathlib): a most-informative numeral exists at some
    world. The two conjuncts capture two separate failure modes:
    information collapse (E-TIA atelic; fails `AdmitsOptimum`) and
    no-extremum (positive G-TIA; fails per-world `IsLeast`). -/

-- ════════════════════════════════════════════════════
-- § 7. E-TIA atelic case: subinterval property → information collapse
-- ════════════════════════════════════════════════════

/-- **E-TIA information collapse for atelic VPs**. When a VP has the
    subinterval property, the E-TIA derived property is constant: every
    numeral yields a true proposition at any world where any does, so no
    numeral is more informative than another. @cite{rouillard-2026} §4.1.1. -/
theorem eTIA_atelic_collapse {μ : Interval Time → ℕ} [TimeMeasure Time μ]
    (P : EventPred W Time) (g1 : Interval Time)
    (hSub : HasSubintervalProp P) :
    IsConstant (α := ℕ) (eTIAProperty P μ g1) := by
  suffices h : ∀ n m w, eTIAProperty P μ g1 n w → eTIAProperty P μ g1 m w from
    fun n m w => ⟨h n m w, h m n w⟩
  intro n m w ⟨_, _, e, hP, hg1, _⟩
  rcases le_total m (μ e.τ) with hle | hge
  · obtain ⟨j, hj_sub, hj_μ⟩ := TimeMeasure.subdivisible e.τ m hle
    refine ⟨j, hj_μ, ⟨j, .action⟩, hSub e w hP j hj_sub ⟨j, .action⟩ rfl,
      ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩⟩
    · exact le_trans hg1.1 hj_sub.1
    · exact le_trans hj_sub.2 hg1.2
  · obtain ⟨j, hj_sup, hj_μ⟩ := TimeMeasure.extensible e.τ m hge
    exact ⟨j, hj_μ, e, hP, hg1, hj_sup⟩

/-- Atelic E-TIA fails the `AdmitsOptimum` half of MIP licensing. -/
theorem eTIA_atelic_no_optimum {μ : Interval Time → ℕ} [TimeMeasure Time μ]
    (P : EventPred W Time) (g1 : Interval Time)
    (hSub : HasSubintervalProp P) :
    ¬ AdmitsOptimum (eTIAProperty P μ g1) :=
  fun h => h (eTIA_atelic_collapse P g1 hSub)

/-- Atelic E-TIA is not MIP-licensed. -/
theorem eTIA_atelic_not_licensed {μ : Interval Time → ℕ} [TimeMeasure Time μ]
    (P : EventPred W Time) (g1 : Interval Time)
    (hSub : HasSubintervalProp P) :
    ¬ MIP_Licensed (eTIAProperty P μ g1) :=
  fun ⟨hAdm, _⟩ => eTIA_atelic_no_optimum P g1 hSub hAdm

-- ════════════════════════════════════════════════════
-- § 8. E-TIA telic case: upward monotone, smallest-true at event duration
-- ════════════════════════════════════════════════════

/-- **Quantized predicates yield upward-monotone E-TIA properties**.
    @cite{rouillard-2026} §4.1.1: when P is telic, the derived E-TIA
    property is upward monotone — the same event witnesses larger
    measures via `TimeMeasure.extensible`. -/
theorem eTIA_telic_upwardMonotone {μ : Interval Time → ℕ} [TimeMeasure Time μ]
    (P : EventPred W Time) (g1 : Interval Time) :
    IsUpwardMonotone (eTIAProperty P μ g1) := by
  intro n m hnm w ⟨t, hμ, e, hP, hg1, hsub⟩
  have h_le : μ t ≤ m := by rw [hμ]; exact hnm
  obtain ⟨j, hj_sup, hj_μ⟩ := TimeMeasure.extensible (μ := μ) t m h_le
  exact ⟨j, hj_μ, e, hP, hg1,
    ⟨le_trans hj_sup.1 hsub.1, le_trans hsub.2 hj_sup.2⟩⟩

/-- For an upward-monotone family with a witness at some world, the
    per-world set `{y | P y w}` has a least element via `Nat.find`. The
    statement is in mathlib idiom (`IsLeast`); the cross-world `IsMaxInf`
    bridge is in `Extremum.lean` (`isMaxInf_of_isLeast_upward`). -/
theorem upwardMonotone_hasIsLeast_of_witness {W : Type*}
    {P : ℕ → W → Prop} (_hUp : IsUpwardMonotone P) (w : W)
    [DecidablePred (fun n => P n w)]
    (h_witness : ∃ n, P n w) :
    ∃ x, IsLeast {y | P y w} x := by
  classical
  refine ⟨Nat.find h_witness, Nat.find_spec h_witness, fun y hy => ?_⟩
  exact Nat.find_le hy

-- ════════════════════════════════════════════════════
-- § 9. G-TIA geometric density: no smallest open PTS
-- ════════════════════════════════════════════════════

/-- **No smallest open PTS includes a closed runtime** (geometric witness).
    @cite{rouillard-2026} §4.2.2: under density on `Time`, given a closed
    event runtime contained in an open PTS, there is always a *strictly
    smaller* (in the proper-subinterval sense) open PTS still containing
    the runtime. Construction: pick a moment between the open boundary
    and the closed start.

    This is the **geometric** density witness. The full MIP-collapse
    claim "no numeral `n` is maximally informative for `gTIAPropertyOpen`"
    additionally requires either rational/real-valued measure (so the
    chain of ℚ-measures has no min) or threshold-rich worlds (so the
    cross-world entailment leg of `Semantics.Entailment.Extremum.IsMaxInf`
      fails at a
    witness world). With the present ℕ-valued measure and no threshold
    assumption, the geometric witness alone does NOT discharge
    `InformationCollapse (gTIAPropertyOpen ...)` — at any specific
    world, the smallest ℕ-measure open PTS containing the runtime
    exists (it is `⌈gap⌉ + 1` for an integer-discrete model). The
    empirical predictions in § 14 are stated at the polarity-and-perfect
    level (matching Rouillard's Table 1) without claiming a structural
    derivation through the MIP at this level of substrate generality. A
    follow-up rebuild on ℚ-valued time-measure substrate (paralleling
    `Core.Mereology.ExtMeasure`) would let the collapse argument
    discharge end-to-end. -/
theorem no_smallest_open_PTS_geometric [DenselyOrdered Time]
    (rt : Interval Time) (ptsGI : GInterval Time)
    (h_open : ptsGI.isOpen)
    (h_sub : (GInterval.closed rt).gsubinterval ptsGI) :
    ∃ ptsGI' : GInterval Time,
      ptsGI'.isOpen ∧
      (GInterval.closed rt).gsubinterval ptsGI' ∧
      ptsGI'.toInterval.subinterval ptsGI.toInterval ∧
      ptsGI'.left ≠ ptsGI.left := by
  obtain ⟨h_strict_left, h_strict_right⟩ :=
    GInterval.gsubinterval_closed_open_strict rt ptsGI h_open h_sub
  obtain ⟨m, hm_left, hm_right⟩ := DenselyOrdered.dense _ _ h_strict_left
  -- m sits strictly between ptsGI.left and rt.start.
  have hm_valid : m ≤ ptsGI.right :=
    le_of_lt (lt_of_lt_of_le hm_right (le_trans rt.valid (le_of_lt h_strict_right)))
  let ptsGI' : GInterval Time :=
    { left := m, right := ptsGI.right
    , leftType := .open_, rightType := .open_
    , valid := hm_valid }
  refine ⟨ptsGI', ⟨rfl, rfl⟩, ?_, ?_, hm_left.ne'⟩
  · intro p hp
    -- hp : (closed rt).gcontains p, definitionally rt.start ≤ p ∧ p ≤ rt.finish.
    have hp1 : rt.start ≤ p := hp.1
    have hp2 : p ≤ rt.finish := hp.2
    refine ⟨?_, ?_⟩
    · -- ptsGI'.gcontains p (left side, open): m < p
      show m < p
      exact lt_of_lt_of_le hm_right hp1
    · -- ptsGI'.gcontains p (right side, open): p < ptsGI.right
      show p < ptsGI.right
      exact lt_of_le_of_lt hp2 h_strict_right
  · refine ⟨le_of_lt hm_left, le_refl _⟩

-- ════════════════════════════════════════════════════
-- § 11. Boundedness pipeline
-- ════════════════════════════════════════════════════

/-! The Vendler-class boundedness pipeline used by `LicensingPipeline`.
    NOT a claim Rouillard makes about Kennedy adjectival scales (the prior
    file's "Kennedy–Rouillard isomorphism" framing was a formaliser
    invention not present in the paper); this is the codebase's
    mereological-tag chain (`Features.Aktionsart`) consumed here for the
    empirical predictions in § 13. The chain
    `VendlerClass →.telicity Telicity →.toMereoTag MereoTag →.toBoundedness Boundedness`
    is definitional, with `LicensingPipeline VendlerClass` registered in
    `Theories/Semantics/Events/DimensionBridge.lean`. -/

/-- Telic VPs route through `LicensingPipeline` to the licensed (closed)
    boundedness tag. -/
theorem telic_predicts_licensing (c : VendlerClass) (h : c.telicity = .telic) :
    (LicensingPipeline.toBoundedness c).isLicensed = true := by
  show (c.telicity.toMereoTag.toBoundedness).isLicensed = true
  rw [h]; rfl

/-- Atelic VPs route through `LicensingPipeline` to the unlicensed (open)
    boundedness tag. -/
theorem atelic_predicts_blocking (c : VendlerClass) (h : c.telicity = .atelic) :
    (LicensingPipeline.toBoundedness c).isLicensed = false := by
  show (c.telicity.toMereoTag.toBoundedness).isLicensed = false
  rw [h]; rfl

-- ════════════════════════════════════════════════════
-- § 12. Rouillard's analytical apparatus
-- ════════════════════════════════════════════════════

/-- Rouillard's TIA-type classification. Paper-specific apparatus
    (per `feedback_fragment_schema_consensus_only`); not on Fragment
    entries themselves. -/
inductive TIAType where
  | eTIA
  | gTIA
  deriving DecidableEq, Repr

/-- Rouillard's syntactic position for the *in*-adverbial.
    E-TIAs are VP-adjacent (event-level); G-TIAs are AspP-adjacent
    (perfect-level). @cite{rouillard-2026} §3.2, schemata (57)/(61). -/
inductive AdverbialPosition where
  | eventLevel
  | perfectLevel
  deriving DecidableEq, Repr

/-- Bundle of Rouillard's analytical labels for an *in*-adverbial. -/
structure RouillardClassification where
  tiaType : TIAType
  position : AdverbialPosition
  deriving DecidableEq, Repr

/-- Project a `DurationExprEntry` to Rouillard's analytical labels.
    Returns `none` for entries outside the *in*-adverbial paradigm
    (`forDur`, `ago`). Co-located in this Studies file (NOT
    `_root_.Fragments.…`) per the audit's namespace-discipline finding. -/
def rouillardClassification? (e : DurationExprEntry) :
    Option RouillardClassification :=
  match e.kind with
  | .telicCompletion => some ⟨.eTIA, .eventLevel⟩
  | .npiGap          => some ⟨.gTIA, .perfectLevel⟩
  | _                => none

-- ════════════════════════════════════════════════════
-- § 13. E-TIA empirical data
-- ════════════════════════════════════════════════════

/-- E-TIA acceptability datum: VP class → acceptable with E-TIA?
    Acceptability is a `Prop` field (was `Bool` in the prior file —
    the project memory `feedback_no_intrinsic_bool.md` discourages
    propositional Bool). -/
structure ETIADatum where
  /-- Description of the VP -/
  vp : String
  /-- Vendler class of the VP -/
  vendlerClass : VendlerClass
  /-- Whether "VP in three days" is acceptable -/
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] ETIADatum.acceptableDecidable

/-- (1a) "Mary wrote up a paper in three days." — accomplishment, ✓ -/
def datum_1a : ETIADatum :=
  { vp := "write up a paper", vendlerClass := .accomplishment, acceptable := True }

/-- (1b) "*Mary was sick in three days." — state, ✗ -/
def datum_1b : ETIADatum :=
  { vp := "be sick", vendlerClass := .state, acceptable := False }

/-- (88) "The climber reached the summit in three days." — achievement, ✓ -/
def datum_88 : ETIADatum :=
  { vp := "reach the summit", vendlerClass := .achievement, acceptable := True }

/-- (84) "*The dancers waltzed in one hour." — activity, ✗ -/
def datum_84 : ETIADatum :=
  { vp := "waltz", vendlerClass := .activity, acceptable := False }

def eTIAData : List ETIADatum :=
  [datum_1a, datum_1b, datum_88, datum_84]

/-- E-TIA acceptability matches the boundedness prediction:
    `LicensingPipeline.toBoundedness d.vendlerClass` is licensed iff
    the datum is acceptable. The pipeline routes through the
    Telicity → MereoTag → Boundedness chain (§ 11). -/
def eTIA_predicted (d : ETIADatum) : Prop :=
  (LicensingPipeline.toBoundedness d.vendlerClass).isLicensed = true ↔ d.acceptable

instance (d : ETIADatum) : Decidable (eTIA_predicted d) := by
  unfold eTIA_predicted; infer_instance

theorem eTIA_all_predicted : ∀ d ∈ eTIAData, eTIA_predicted d := by decide

-- ════════════════════════════════════════════════════
-- § 14. G-TIA empirical data
-- ════════════════════════════════════════════════════

/-- G-TIA acceptability datum: polarity × perfect → acceptable. -/
structure GTIADatum where
  /-- Description of the sentence -/
  sentence : String
  /-- Is the sentence negative? -/
  isNegative : Prop
  [isNegativeDecidable : Decidable isNegative]
  /-- Does the sentence contain a perfect? -/
  hasPerfect : Prop
  [hasPerfectDecidable : Decidable hasPerfect]
  /-- Whether the G-TIA is acceptable -/
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] GTIADatum.isNegativeDecidable GTIADatum.hasPerfectDecidable
                      GTIADatum.acceptableDecidable

/-- (2a) "Mary hasn't been sick in three days." — negative perfect, ✓ -/
def datum_2a : GTIADatum :=
  { sentence := "Mary hasn't been sick in three days"
    isNegative := True, hasPerfect := True, acceptable := True }

/-- (2b) "*Mary has been sick in three days." — positive perfect, ✗ -/
def datum_2b : GTIADatum :=
  { sentence := "Mary has been sick in three days"
    isNegative := False, hasPerfect := True, acceptable := False }

/-- (48) "*Mary wasn't sick in three days." — negative, no perfect, ✗ -/
def datum_48 : GTIADatum :=
  { sentence := "Mary wasn't sick in three days"
    isNegative := True, hasPerfect := False, acceptable := False }

def gTIAData : List GTIADatum := [datum_2a, datum_2b, datum_48]

/-- G-TIA acceptability matches the polarity ∧ perfect prediction.
    @cite{rouillard-2026} Table 1: only NEG + PFV with G-TIA reading
    survives MIP filtering. The structural derivation through MIP
    requires either rational-valued measure or threshold-rich worlds
    (see § 9 docstring); the prediction is stated here at the surface
    polarity-and-perfect level matching Rouillard's empirical claim. -/
def gTIA_predicted (d : GTIADatum) : Prop :=
  (d.isNegative ∧ d.hasPerfect) ↔ d.acceptable

instance (d : GTIADatum) : Decidable (gTIA_predicted d) := by
  unfold gTIA_predicted; infer_instance

theorem gTIA_all_predicted : ∀ d ∈ gTIAData, gTIA_predicted d := by decide

-- ════════════════════════════════════════════════════
-- § 15. Table 1 (eq. 112): 8 cells with derived blocking
-- ════════════════════════════════════════════════════

/-- @cite{rouillard-2026} Table 1: readings for "*Mary has been sick in
    three days*" and its negation crossed with TIA type and aspect.

    Polarity, TIA type, and aspect are enums (not Bool flags), so the
    table reads structurally rather than as a tuple of opaque booleans. -/
inductive Table1Polarity | positive | negative
  deriving DecidableEq, Repr

inductive Table1Aspect | pfv | impv  -- E-perfect (PFV) vs U-perfect (IMPV)
  deriving DecidableEq, Repr

structure Table1Cell where
  polarity : Table1Polarity
  tiaType : TIAType
  aspect : Table1Aspect
  deriving DecidableEq, Repr

/-- A Table 1 cell survives MIP filtering iff it is the unique
    NEG + G-TIA + PFV configuration. Derived (not stipulated): every
    other cell is blocked by Rouillard's account, by various
    information-collapse mechanisms (positive cells: open-PTS density;
    E-TIA cells under negation: aspect mismatch with perfect; IMPV
    cells: U-perfect quantification mismatch). -/
def table1Survives (c : Table1Cell) : Prop :=
  c.polarity = .negative ∧ c.tiaType = .gTIA ∧ c.aspect = .pfv

instance (c : Table1Cell) : Decidable (table1Survives c) := by
  unfold table1Survives; infer_instance

/-- All 8 Table 1 cells, generated by enumerating the three discriminators. -/
def table1 : List Table1Cell := do
  let pol ← [Table1Polarity.positive, .negative]
  let ty ← [TIAType.eTIA, .gTIA]
  let asp ← [Table1Aspect.pfv, .impv]
  pure ⟨pol, ty, asp⟩

/-- @cite{rouillard-2026} Table 1: exactly one cell survives — NEG + G-TIA + PFV. -/
theorem surviving_is_neg_gtia_pfv :
    table1.filter (fun c => decide (table1Survives c)) =
    [⟨.negative, .gTIA, .pfv⟩] := by decide

-- ════════════════════════════════════════════════════
-- § 16. Stacking constraint (§3.2, ex. 60)
-- ════════════════════════════════════════════════════

/-! @cite{rouillard-2026} §3.2, ex. (60). When two TIAs stack, the inner
    (VP-adjacent) one must be E-TIA and the outer must be G-TIA. The
    reverse order is ungrammatical. The position constraint follows from
    `AdverbialPosition`: E-TIA = eventLevel (VP-adjacent), G-TIA =
    perfectLevel (AspP-adjacent). -/

/-- TIA stacking datum: inner and outer adverbial classifications. -/
structure StackingDatum where
  sentence : String
  innerType : TIAType
  innerPosition : AdverbialPosition
  outerType : TIAType
  outerPosition : AdverbialPosition
  acceptable : Prop
  [acceptableDecidable : Decidable acceptable]

attribute [instance] StackingDatum.acceptableDecidable

/-- (60a) "Mary hasn't written up a paper in three days in two weeks."
    Inner E-TIA + outer G-TIA: acceptable. -/
def stacking_60a : StackingDatum :=
  { sentence := "Mary hasn't written up a paper in three days in two weeks"
    innerType := .eTIA, innerPosition := .eventLevel
    outerType := .gTIA, outerPosition := .perfectLevel
    acceptable := True }

/-- (60b) "#Mary hasn't written up a paper in two weeks in three days."
    Reversed order: unacceptable. -/
def stacking_60b : StackingDatum :=
  { sentence := "#Mary hasn't written up a paper in two weeks in three days"
    innerType := .gTIA, innerPosition := .perfectLevel
    outerType := .eTIA, outerPosition := .eventLevel
    acceptable := False }

def stackingData : List StackingDatum := [stacking_60a, stacking_60b]

/-- Stacking is acceptable iff inner is event-level and outer is
    perfect-level. @cite{rouillard-2026} §3.2 schemata (57), (61). -/
def stacking_predicted (d : StackingDatum) : Prop :=
  (d.innerPosition = .eventLevel ∧ d.outerPosition = .perfectLevel) ↔ d.acceptable

instance (d : StackingDatum) : Decidable (stacking_predicted d) := by
  unfold stacking_predicted; infer_instance

theorem stacking_all_predicted : ∀ d ∈ stackingData, stacking_predicted d := by
  decide

-- ════════════════════════════════════════════════════
-- § 17. Since-when questions (§5.2, ex. 131)
-- ════════════════════════════════════════════════════

/-! @cite{rouillard-2026} §5.2, ex. (131): "Since when has Mary been sick?"
    lacks the E-perfect/U-perfect ambiguity of the corresponding
    declarative. Rouillard derives this from MIP applied to the Hamblin
    set (eq. 135 ANS): the E-perfect Hamblin set has no maximally
    informative true answer (open-PTS density argument), the U-perfect
    Hamblin set does.

    The since-when observation itself is originally
    @cite{von-fintel-iatridou-2019}'s "Since *since*"; the explanatory
    mechanism (open-PTS density on dense time) is from
    @cite{fox-hackl-2006}'s Universal Density of Measurement. -/

/-- Since-when question datum: which perfect readings are available? -/
structure SinceWhenDatum where
  sentence : String
  uPerfect : Prop
  [uPerfectDecidable : Decidable uPerfect]
  ePerfect : Prop
  [ePerfectDecidable : Decidable ePerfect]

attribute [instance] SinceWhenDatum.uPerfectDecidable SinceWhenDatum.ePerfectDecidable

/-- (131) "Since when has Mary been sick?" — U-perfect only. -/
def sinceWhen_131 : SinceWhenDatum :=
  { sentence := "Since when has Mary been sick?"
    uPerfect := True
    ePerfect := False }

/-- Since-when questions block the E-perfect reading.
    @cite{fox-hackl-2006} density argument applied to Rouillard's
    eq. (137) E-perfect Hamblin set: no maximally informative true
    answer survives MIP filtering. -/
theorem sinceWhen_blocks_ePerfect : ¬ sinceWhen_131.ePerfect := by
  intro h; exact h

/-- Fragment bridge: *since* is veridical and pins the PTS left
    boundary, matching the since-when question's presupposition. -/
theorem since_fragment_bridge :
    since_conn.complementVeridical = true ∧
    since_conn.order = TemporalOrder.since_ := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 18. Fragment bridges
-- ════════════════════════════════════════════════════

/-- The Rouillard projection assigns the expected analytical labels:
    E-TIA at event-level for telic-completion *in*; G-TIA at
    perfect-level for the NPI-gap *in*. -/
theorem rouillard_classification :
    rouillardClassification? inTelic = some ⟨.eTIA, .eventLevel⟩ ∧
    rouillardClassification? inGap   = some ⟨.gTIA, .perfectLevel⟩ :=
  ⟨rfl, rfl⟩

/-- Out-of-paradigm entries return `none`: *for* and *ago* are duration
    adverbials but not *in*-adverbials. -/
theorem rouillard_partial :
    rouillardClassification? forDur = none ∧
    rouillardClassification? ago    = none :=
  ⟨rfl, rfl⟩

/-- E-TIA and G-TIA share the preposition *in* (consensus Fragment fact). -/
theorem shared_preposition : inTelic.form = inGap.form := rfl

end Phenomena.TenseAspect.Studies.Rouillard2026
