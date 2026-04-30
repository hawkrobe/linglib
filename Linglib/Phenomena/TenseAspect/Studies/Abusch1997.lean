import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.DeRe
import Linglib.Theories.Semantics.Dynamic.PLA.Belief

/-!
# @cite{abusch-1997}: Sequence of Tense and Temporal de re
@cite{abusch-1997} @cite{sharvit-2003} @cite{heim-1994-comments}
@cite{lewis-1979-attitudes} @cite{cresswell-vonstechow-1982}

@cite{abusch-1997}'s theory: tense morphemes are temporal pronouns
(variables with presupposed constraints and binding modes). The key
innovation is **temporal de re**: tense can take wide scope over
attitude operators via res movement, just as DPs can scope out of
attitude complements.

Two derivation styles coexist in this file:

1. **Value-level shadow** (`abusch_derives_*` against `TensePronoun.fullPresupposition`):
   tense pronoun + `GramTense.constrains` + temporal assignment.
   Captures Abusch's predictions at the value level without committing
   to the centered-world architecture. Cheap, presupposition-free.

2. **Centered-world substrate** (`abusch_derives_*_via_acquaintance` /
   `_full` / `_full_metaphysical` against
   `Semantics.Tense.DeRe.TemporalDeReReading`): `Intension (KContext)
   Time` time-concept + holder-context base anchor + modal-alternative
   quantification over a `Set (WorldTimeIndex W Time)`. The Abusch §3 +
   def. 13 architecture, faithful to the @cite{lewis-1979-attitudes} /
   @cite{cresswell-vonstechow-1982} centered-world reduction of de re.
   The two styles are bridged by
   `Semantics.Tense.DeRe.TemporalDeReReading.isFelicitousWith_iff_tensePronoun_fullPresupposition`.

The substrate is now (PR-B, 0.230.554) modal-base-agnostic and
holder-now-honest: `holderContext.time` is the holder's now (per §7
ULC), and `IsRigidAcrossAlternatives` takes a `Set (WorldTimeIndex)`
parameter (with `metaphysicalAlternatives` / `doxasticAlternatives`
convenience constructors).

What's still deferred — see `Tense/DeRe.lean` docstring for the LF
rewrite, contrastive theorems against Schlenker 2004, and the
Anand-Nevins entity-concept bridge (PR-C target).

## Core Mechanisms

1. **Tense as pronoun**: `TensePronoun` (in `Core.Time.Tense`) with
   variable index, constraint, and binding mode.
2. **Upper Limit Constraint (ULC)**: stated by @cite{abusch-1997} §7
   ("the now of an epistemic alternative is an upper limit for the
   denotation of tenses"); presuppositional construal due to
   @cite{heim-1994-comments}, endorsed by Abusch 1997 fn 20. Lives in
   `Theories/Semantics/Tense/Basic.lean` as `upperLimitConstraint`,
   formalized at the value level as `embeddedR ≤ matrixE`. **Note:**
   this value-level reduction strips the modal-alternative
   quantification the original formulation carries; making the modal
   layer explicit (over `WorldHistory W Time` à la @cite{klecha-2016})
   is deferred.
3. **Temporal de re**: tense variable in the res position of an
   attitude. The value-level shadow uses `TensePronoun.fullPresupposition`:
   constraint applied to (resolved time, eval time). The LF rewrite +
   acquaintance-relation machinery (Lewis 1979 / Cresswell-von Stechow
   1982) is not formalized here.
4. **Eval-time shift via attitude embedding**: the substrate primitives
   are `Core.Time.Tense.evalTime_shifts_under_embedding` and
   `updateTemporal`. Abusch's "relation transmission" (feature passing
   of relation variables PAST/PRES across embedding) is *not* what this
   file currently captures — we only model the value-level eval-time
   update.

## Derivation Theorems

- Shifted reading: free past variable with presupposition against eval time
- Simultaneous reading: bound variable receives matrix event time
- Double-access: indexical present + attitude binding (placeholder; the
  full Abusch derivation involves doxastic alternatives + acquaintance
  relations + the rigid-present presupposition, not formalized here)
- Temporal de re: res movement for wide-scope tense

## Limitations

- Relative clause tense: @cite{sharvit-2003}'s challenge (the mechanism
  doesn't extend straightforwardly to relative clauses where the tense
  takes the perspective of a participant)
- Modal-tense interaction: not addressed in @cite{abusch-1997}'s
  framework (see @cite{klecha-2016} for a successor)
- Counterfactual tense: not addressed
- Counterpart-relation isomorphism @cite{abusch-1997} §12 invokes for
  the double-access reading derivation (the constraint that actual
  and belief worlds be temporally isomorphic, eliminating most of the
  4 cells in the DAR diagram on p. 43): not formalized
- Modal-layer ULC formulation: see Core Mechanism 2 above

-/

namespace Phenomena.TenseAspect.Studies.Abusch1997

open Core.Time.Tense
open Core.Time.Reichenbach
open Core.Time
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- @cite{abusch-1997} derives the shifted reading: a free past
    variable with presupposition checked against the (shifted) eval
    time. The past constraint gives R < evalTime = matrixE.

    Note: the proof closes via `embeddedFrame.isPast`'s definition,
    which only requires `tp.resolve g < matrixFrame.eventTime`. The
    `tp.constraint = .past` condition is what *Abusch's theory* says
    licenses this reading, but it isn't load-bearing in this proof —
    the conclusion follows for any tense pronoun whose resolution is
    below the matrix event time. A full Abusch derivation would
    project through `tp.constraint.constrains` from the binding mode. -/
theorem abusch_derives_shifted {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hPresup : tp.resolve g < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPresup

/-- @cite{abusch-1997} derives the simultaneous reading: a bound
    variable receives the matrix event time via lambda abstraction. -/
theorem abusch_derives_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hBind : tp.resolve g = matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent, hBind]

/-- @cite{abusch-1997} derives the simultaneous reading via the bound
    variable mechanism: updating the temporal assignment so the tense
    variable receives matrix E. -/
theorem abusch_derives_simultaneous_via_binding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time) :
    tp.resolve (updateTemporal g tp.varIndex matrixFrame.eventTime) =
    matrixFrame.eventTime :=
  tp.bound_resolve_eq_binder g matrixFrame.eventTime

/-- @cite{abusch-1997}'s double-access *placeholder*: indexical present
    requires truth at BOTH speech time (indexical rigidity) AND matrix
    event time (attitude accessibility). The full Abusch derivation
    involves doxastic alternatives + acquaintance relations + the
    rigid-present presupposition; this theorem only states the surface
    conjunction. -/
theorem abusch_derives_double_access {Time : Type*}
    (p : Time → Prop) (speechTime matrixEventTime : Time)
    (h_speech : p speechTime) (h_matrix : p matrixEventTime) :
    doubleAccess p speechTime matrixEventTime :=
  ⟨h_speech, h_matrix⟩

/-- @cite{abusch-1997} derives temporal de re: the tense variable in
    res position is evaluated in the matrix context, giving wide-scope
    temporal reference. When the resolved referent satisfies the past
    constraint against the (matrix-shifted) eval time, the de re reading
    is felicitous.

    Value-level shadow: this theorem checks `TensePronoun.fullPresupposition`,
    not Abusch's actual centered-proposition rule (paper def. 13). The
    `g` here would, in the full account, be a temporal assignment shifted
    by the attitude verb to put the matrix event time at `tp.evalTimeIndex`. -/
theorem abusch_derives_temporal_de_re {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (hPast : tp.constraint = .past)
    (hBefore : tp.resolve g < tp.evalTime g) :
    tp.fullPresupposition g := by
  simp only [TensePronoun.fullPresupposition, GramTense.constrains, hPast]
  exact hBefore


-- ════════════════════════════════════════════════════════════════
-- § Centered-World Substrate Derivations
-- ════════════════════════════════════════════════════════════════

/-- @cite{abusch-1997}'s temporal de re via the centered-world substrate
    (`Theories/Semantics/Tense/DeRe.lean`). The time-concept is the
    rigid intension at the actual past time (`Intension.rigid pastTime`);
    the base-world condition (Abusch §3 p. 9) is satisfied by
    construction (the rigid concept evaluates to `pastTime` at the
    holder's centered context, so the actual res-time is `pastTime`
    and the past constraint holds against `holderContext.time` per the
    §7 ULC). -/
theorem abusch_derives_temporal_de_re_via_acquaintance
    {W E P Time : Type*} [LinearOrder Time]
    (holderContext : Core.Context.KContext W E P Time)
    (pastTime : Time)
    (hBefore : pastTime < holderContext.time) :
    let dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time :=
      ⟨Core.Intension.rigid pastTime, holderContext⟩
    dr.isFelicitousWith .past := by
  simp only [Semantics.Tense.DeRe.TemporalDeReReading.isFelicitousWith,
    Semantics.Tense.DeRe.TemporalDeReReading.actualRes,
    Core.Intension.rigid, GramTense.constrains]
  exact hBefore

/-- @cite{abusch-1997}'s temporal de re with **modal-alternative
    quantification** (Abusch §3 p. 9): the time-concept identifies the
    same time across an `alternatives : Set (WorldTimeIndex W Time)`.
    The substrate is modal-base-agnostic; this theorem holds for any
    alternative-set the consumer supplies (doxastic, metaphysical, or
    other). The full `isAbuschFelicitous` predicate combines the
    value-level past constraint with this modal rigidity.

    A rigid time-concept (constant intension) discharges the modal
    rigidity automatically — Abusch's de re reading is satisfied "for
    free" when the res is identified by a name-like rigid concept. -/
theorem abusch_derives_temporal_de_re_full
    {W E P Time : Type*} [LinearOrder Time]
    (holderContext : Core.Context.KContext W E P Time)
    (alternatives : Set (Core.WorldTimeIndex W Time))
    (pastTime : Time)
    (hBefore : pastTime < holderContext.time) :
    let dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time :=
      ⟨Core.Intension.rigid pastTime, holderContext⟩
    dr.isAbuschFelicitous alternatives .past := by
  refine ⟨?_, ?_⟩
  · simp only [Semantics.Tense.DeRe.TemporalDeReReading.isFelicitousWith,
      Semantics.Tense.DeRe.TemporalDeReReading.actualRes,
      Core.Intension.rigid, GramTense.constrains]
    exact hBefore
  · exact Semantics.Tense.DeRe.TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
      _ (Core.Intension.rigid_isRigid pastTime) alternatives

/-- **Metaphysical-instantiation specialization** of
    `abusch_derives_temporal_de_re_full`. Recovers the legacy
    `WorldHistory`-based formulation as a corollary at the
    `metaphysicalAlternatives` instance, demonstrating backward
    compatibility with Klecha 2016 DOX-shaped reasoning. -/
theorem abusch_derives_temporal_de_re_full_metaphysical
    {W E P Time : Type*} [LinearOrder Time]
    (holderContext : Core.Context.KContext W E P Time)
    (history : Core.Modality.HistoricalAlternatives.WorldHistory W Time)
    (pastTime : Time)
    (hBefore : pastTime < holderContext.time) :
    let dr : Semantics.Tense.DeRe.TemporalDeReReading W E P Time :=
      ⟨Core.Intension.rigid pastTime, holderContext⟩
    dr.isAbuschFelicitous (dr.metaphysicalAlternatives history) .past :=
  abusch_derives_temporal_de_re_full holderContext _ pastTime hBefore

/-- **PLA ↔ Abusch substrate unification**: PLA's `isAcquaintedWith`
    (entity-side, individual de re) and the polymorphic
    `Reference.Acquaintance.isAcquaintedWith` are the same predicate at
    the PLA index `Idx := Assignment E × WitnessSeq E`, modulo PLA's
    discarded `agent` parameter.

    Provable by `Iff.rfl` because the PLA wrapper delegates to the
    polymorphic version. The *content* of the theorem is structural —
    it shows the de re reading PLA proves about *individuals* and the
    de re reading `TemporalDeReReading` exposes for *times* are
    instantiations of the same acquaintance substrate, making true the
    individual ↔ temporal de re parallel @cite{abusch-1997} asserts in
    prose at p. 6 ("To apply the same machinery to de re belief, a
    further constraint is required..."). -/
theorem pla_isAcquaintedWith_unifies_with_polymorphic
    {E : Type*} (a individual : E)
    (C : Semantics.Dynamic.PLA.Cover E)
    (p : Semantics.Dynamic.PLA.Poss E) :
    Semantics.Dynamic.PLA.isAcquaintedWith a individual C p ↔
    Semantics.Reference.Acquaintance.isAcquaintedWith individual C p :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Stress Tests: §§1-7 grounding
-- ════════════════════════════════════════════════════════════════

/-! These declarations stress-test the substrate against canonical
    examples from @cite{abusch-1997-attitudes} centered worlds and
    @cite{abusch-1997}'s temporal application. Four classes:

    - **Positive consistency**: build a concrete `TemporalDeReReading`
      from an Abusch §§1-4 example and prove `isAbuschFelicitous`.
    - **Negative rejection**: construct cases that should fail and
      prove they do (filter check — confirms operators don't vacuously
      accept).
    - **Structural sanity**: verify intermediate primitives
      (`actualHistoryBase` non-empty, `shiftWorldTime` round-trip,
      `IsRigidOn` monotonicity) do real work.
    - **Bug-exposing**: named theorems documenting false-positive
      cases the current substrate accepts but @cite{abusch-1997} §7 ULC
      would reject. PR-B's modal-base + holder-now refactor will turn
      these into negative tests; for now they're regression witnesses.

    Concrete instance: `W := Bool` (2-world domain — enough to
    distinguish rigid from non-rigid concepts), `E := Unit`,
    `P := Unit`, `T := ℤ`. -/

namespace StressTests

open Core (Intension WorldTimeIndex)
open Core.Context (KContext)
open Core.Modality.HistoricalAlternatives (WorldHistory actualHistoryBase)
open Semantics.Tense.DeRe (TimeConcept TemporalDeReReading)

private abbrev W := Bool
private abbrev E := Unit
private abbrev P := Unit

/-- The attitude holder's centered Kaplanian context: agent (=Unit),
    in world `true`, with the holder's "now" = `now`. Per
    @cite{abusch-1997} §7 ULC, this `now` is the relevant evaluation
    time for embedded tenses (NOT the outer speaker's speech time). -/
private def holderCtx (now : ℤ) : KContext W E P ℤ :=
  ⟨(), (), true, now, ()⟩

/-- All-permissive alternative set: every world-time pair is an
    alternative. Models maximal epistemic uncertainty. -/
private def trivialAlts : Set (WorldTimeIndex W ℤ) := Set.univ

/-- Restrictive alternative set: only world `true` is included.
    Models a relation that excludes the counterfactual world (could
    be metaphysical-like or a tightly-knowing doxastic agent). -/
private def restrictiveAlts : Set (WorldTimeIndex W ℤ) :=
  { s | s.world = true }

/-- A non-rigid time-concept: 50 in world `true`, 60 in world `false`.
    Discriminates worlds — the wrong shape for an Abusch-faithful
    de re reading. -/
private def nonRigidConcept : TimeConcept W E P ℤ :=
  fun c => if c.world then 50 else 60

/-- Rigid de re reading: rigid concept at time `t`, holder's now = `now`. -/
private def rigidReading (t now : ℤ) : TemporalDeReReading W E P ℤ :=
  ⟨Intension.rigid t, holderCtx now⟩

/-- Non-rigid reading: non-rigid concept, holder's now = `now`. -/
private def nonRigidReading (now : ℤ) : TemporalDeReReading W E P ℤ :=
  ⟨nonRigidConcept, holderCtx now⟩

/-- All-permissive `WorldHistory`, used to demonstrate the
    `metaphysicalAlternatives` constructor at the substrate boundary. -/
private def trivialHistory : WorldHistory W ℤ := fun _ => Set.univ


-- ───────────────────────────────────────────────────────
-- Class 1: Positive consistency
-- ───────────────────────────────────────────────────────

/-- @cite{abusch-1997} example (1) (p. 2-3) backward-shifted reading:
    "the jurors Past₃ believed that he Past₂ was in the laboratory
    building." Holder = jurors, holder's now (jurors' believing time)
    tb=90, crime time tc=50. Rigid time-concept at 50; past constraint
    discharged (50 < 90, **relative to holder's now NOT to outer speech
    time**, per @cite{abusch-1997} §7 ULC); modal rigidity automatic
    from concept-rigidity. -/
example : (rigidReading 50 90).isAbuschFelicitous trivialAlts .past := by
  refine ⟨?_, ?_⟩
  · show (50 : ℤ) < 90; decide
  · exact TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
      (rigidReading 50 90) (Intension.rigid_isRigid 50) trivialAlts

/-- Round-trip via the shadow lemma: the substrate's value-level felicity
    matches `TensePronoun.fullPresupposition` for any `TensePronoun`
    whose resolve and evalTime align with the de re reading. -/
example
    (tp : Core.Time.Tense.TensePronoun) (g : Core.Time.Tense.TemporalAssignment ℤ)
    (hRes : tp.resolve g = 50) (hEval : tp.evalTime g = 90) :
    (rigidReading 50 90).isFelicitousWith tp.constraint ↔ tp.fullPresupposition g :=
  TemporalDeReReading.isFelicitousWith_iff_tensePronoun_fullPresupposition
    (rigidReading 50 90) tp g hRes hEval

/-- **Metaphysical-instantiation demo**: the substrate's
    `metaphysicalAlternatives` constructor recovers the legacy
    `WorldHistory`-based behavior as a special case. The de re reading
    is felicitous against the metaphysical alternative set derived
    from `trivialHistory` (max-permissive). -/
example : (rigidReading 50 90).isAbuschFelicitous
    ((rigidReading 50 90).metaphysicalAlternatives trivialHistory) .past := by
  refine ⟨?_, ?_⟩
  · show (50 : ℤ) < 90; decide
  · exact TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
      _ (Intension.rigid_isRigid 50) _


-- ───────────────────────────────────────────────────────
-- Class 2: Negative rejection (filter check)
-- ───────────────────────────────────────────────────────

/-- Future-from-holder-now actualRes (200 > 90) fails the past
    constraint. The substrate now correctly rejects per
    @cite{abusch-1997} §7 ULC. -/
example : ¬ (rigidReading 200 90).isFelicitousWith .past := by
  show ¬ ((200 : ℤ) < 90)
  decide

/-- A non-rigid time-concept (different value at each world) fails
    `IsRigidAcrossAlternatives` over the trivial alternative set.
    This is the **non-vacuity** check: the modal layer genuinely
    discriminates rigid from non-rigid, not vacuously accepting. -/
example : ¬ (nonRigidReading 90).IsRigidAcrossAlternatives trivialAlts := by
  intro hRig
  -- ⟨true, 0⟩ and ⟨false, 0⟩ are both trivially in `Set.univ`.
  have h := hRig (⟨true, 0⟩ : WorldTimeIndex W ℤ) trivial
                 (⟨false, 0⟩ : WorldTimeIndex W ℤ) trivial
  simp only [nonRigidReading, nonRigidConcept,
    KContext.shiftWorldTime_world] at h
  exact absurd h (by decide)


-- ───────────────────────────────────────────────────────
-- Class 3: Structural sanity
-- ───────────────────────────────────────────────────────

/-- The holder's situation is in its own `actualHistoryBase` under the
    trivial history — non-vacuity baseline. -/
example : (holderCtx 90).toSituation ∈
    actualHistoryBase trivialHistory (holderCtx 90).toSituation := by
  refine ⟨trivial, ?_⟩
  show (90 : ℤ) ≤ 90; decide

/-- `KContext.shiftWorldTime` preserves agent (load-bearing for
    centered-world identity: the believer is held fixed across
    alternatives) and round-trips through `toSituation`. -/
example (c : KContext W E P ℤ) (s : WorldTimeIndex W ℤ) :
    (c.shiftWorldTime s).agent = c.agent ∧
    (c.shiftWorldTime s).toSituation = s := ⟨rfl, rfl⟩

/-- `Intension.IsRigidOn` is monotone in the set: rigidity on a larger
    set implies rigidity on any subset. -/
example (f : Intension W ℤ) (S S' : Set W) (hSub : S' ⊆ S)
    (h : Intension.IsRigidOn f S) : Intension.IsRigidOn f S' :=
  fun _ hw₁ _ hw₂ => h _ (hSub hw₁) _ (hSub hw₂)


-- ───────────────────────────────────────────────────────
-- Class 4: PR-B fix witnesses (formerly bug-exposing)
-- ───────────────────────────────────────────────────────

/-- **PR-B fix for Bug 3 (speech vs holder now)**. Pre-PR-B the
    substrate's context field was named `matrixContext` and the
    felicity predicate checked the constraint against
    `matrixContext.time`, which test code treated as speech time —
    `(rigidReading 75 100).isFelicitousWith .past` passed (75 < 100,
    speech-time-relative) — a false positive per @cite{abusch-1997}
    §7 ULC, which requires the past constraint to be against the
    *holder's now* (NOT speech).

    Post-PR-B the field is `holderContext.time` and represents the
    holder's now by construction. With holder's now = 50 and
    actualRes = 75, the substrate now correctly REJECTS the case
    (75 ≥ 50). What was a bug-witnessing positive theorem is now a
    fix-witnessing negative theorem. -/
theorem pr_b_substrate_rejects_actualRes_after_holderNow :
    ¬ (rigidReading 75 50).isFelicitousWith .past := by
  show ¬ ((75 : ℤ) < 50)
  decide

/-- **PR-B fix for Bug 1 (modal base — metaphysical vs doxastic)**.
    Pre-PR-B `IsRigidAcrossAlternatives` took a `WorldHistory W T`
    parameter and quantified over the (metaphysical) `actualHistoryBase`.
    The substrate was agent-blind by construction; the doxastic vs
    metaphysical distinction lived only in the docstring.

    Post-PR-B the parameter is `Set (WorldTimeIndex W T)` directly.
    The substrate is **modal-base-agnostic**; the consumer chooses
    doxastic or metaphysical (via the `doxasticAlternatives` /
    `metaphysicalAlternatives` constructors) at the call site. The
    same concept correctly varies its verdict by alternative-set —
    but this is now the consumer's *explicit, type-level* choice, not
    an opaque consequence of `WorldHistory`-shape. -/
theorem pr_b_substrate_correctly_distinguishes_alternative_sets :
    (nonRigidReading 90).IsRigidAcrossAlternatives restrictiveAlts ∧
    ¬ (nonRigidReading 90).IsRigidAcrossAlternatives trivialAlts := by
  refine ⟨?_, ?_⟩
  · intro s₁ hs₁ s₂ hs₂
    -- restrictiveAlts membership unfolds to s.world = true
    have hw₁ : s₁.world = true := hs₁
    have hw₂ : s₂.world = true := hs₂
    simp only [nonRigidReading, nonRigidConcept,
      KContext.shiftWorldTime_world, hw₁, hw₂]
  · intro hRig
    have h := hRig (⟨true, 0⟩ : WorldTimeIndex W ℤ) trivial
                   (⟨false, 0⟩ : WorldTimeIndex W ℤ) trivial
    simp only [nonRigidReading, nonRigidConcept,
      KContext.shiftWorldTime_world] at h
    exact absurd h (by decide)

/-- **PR-B doxastic-instantiation demo** (new). The substrate accepts
    a `doxasticAlternatives`-derived alternative set just as readily
    as the metaphysical one. The doxastic relation here is the
    "anything goes" max-permissive `dox` — every (world, time) pair
    is doxastically possible from the holder's perspective. The rigid
    concept passes regardless. -/
example
    (dox : E → W → WorldTimeIndex W ℤ → Prop := fun _ _ _ => True) :
    (rigidReading 50 90).isAbuschFelicitous
      ((rigidReading 50 90).doxasticAlternatives dox) .past := by
  refine ⟨?_, ?_⟩
  · show (50 : ℤ) < 90; decide
  · exact TemporalDeReReading.IsRigidAcrossAlternatives_of_concept_isRigid
      _ (Intension.rigid_isRigid 50) _


end StressTests


end Phenomena.TenseAspect.Studies.Abusch1997
