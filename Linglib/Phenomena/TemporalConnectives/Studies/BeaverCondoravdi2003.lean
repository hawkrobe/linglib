import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Tense.BranchingTime
import Linglib.Core.Scales.Scale

/-!
# @cite{beaver-condoravdi-2003}: Uniform Analysis with `earliest`
@cite{beaver-condoravdi-2003} @cite{thomason-1984}

A **uniform** semantics for *before* and *after*: both connectives use the
same `earliest` operator, with the veridicality asymmetry derived from
**branching time** and historical alternatives rather than quantificational
asymmetry.

## Core Architecture

B&C define temporal connective truth conditions over **world–time pairs**
(situations) with access to historical alternatives:

- `A after B` true at w iff ∃t : ⟨w,t⟩ ∈ A, t > earliest_{alt(w,t)}(B)
- `A before B` true at w iff ∃t : ⟨w,t⟩ ∈ A, t < earliest_{alt(w,t)}(B)

Where `alt(w,t)` is the set of worlds historically accessible from w at t
(worlds sharing w's history up to t).

## Veridicality from Branching

The veridicality asymmetry falls out from the initial branch point condition:

- **After**: A happens after the earliest B. Since B is in the past of A and
  `alt(w,t)` only branches in the future of t, B must be on the actual branch.
  So *after* is always veridical.

- **Before**: A happens before the earliest B. B could be on a different branch
  (a historical alternative), so B might not be instantiated in w. Three readings
  arise from context: veridical (all context worlds have B), counterfactual
  (no context world has B), non-committal (some do, some don't).

## Level

**Level 4 (intensional)**: operates on sets of world–time pairs. The
`earliest` operator is MAX on the < scale (same as Rett's MAX₍<₎), applied
across historical alternatives.

-/

namespace Semantics.Tense.TemporalConnectives.BeaverCondoravdi

open Core.Scale (maxOnScale)

variable {W T : Type*} [LinearOrder T]

-- ============================================================================
-- § 1: Historical Alternatives
-- ============================================================================

/-- Historical alternatives: for each world w and time t, the set of worlds
    sharing w's history up to t but potentially diverging afterwards.

    `alt(w,t)` satisfies the initial branch point condition: all worlds in
    `alt(w,t)` agree with w on all events at times ≤ t. -/
abbrev HistAlt (W T : Type*) := W → T → Set W

/-- Initial branch point condition: worlds in `alt(w,t)` agree with w
    on all events at times before t.

    `agree t' w w'` means "w and w' are indistinguishable at time t'". -/
def initialBranchPoint (alt : HistAlt W T) (agree : T → W → W → Prop) : Prop :=
  ∀ w t, ∀ w' ∈ alt w t, ∀ t', t' < t → agree t' w w'

/-- The actual world is always a historical alternative of itself. -/
def altReflexive (alt : HistAlt W T) : Prop :=
  ∀ w t, w ∈ alt w t

/-- Monotonicity of alternatives: later times have fewer alternatives,
    since more shared history constrains the set of compatible worlds.
    `alt(w,t') ⊆ alt(w,t)` when `t ≤ t'`.

    Intuitively: if w' shares w's history up to t', it also shares w's
    history up to any earlier t ≤ t'. -/
def altMonotone (alt : HistAlt W T) : Prop :=
  ∀ w t t', t ≤ t' → alt w t' ⊆ alt w t

-- ============================================================================
-- § 1b: Bridge to BranchingTime.WorldHistory
-- ============================================================================

/-- Convert a `WorldHistory` (situation-indexed) to curried `HistAlt` form. -/
def histAltOfWorldHistory (h : Semantics.Tense.BranchingTime.WorldHistory W T) :
    HistAlt W T :=
  fun w t => h ⟨w, t⟩

/-- Convert curried `HistAlt` to `WorldHistory` (situation-indexed) form. -/
def worldHistoryOfHistAlt (a : HistAlt W T) :
    Semantics.Tense.BranchingTime.WorldHistory W T :=
  fun s => a s.world s.time

omit [LinearOrder T] in
/-- Round-trip: `WorldHistory → HistAlt → WorldHistory` is identity. -/
theorem histAlt_worldHistory_roundtrip
    (h : Semantics.Tense.BranchingTime.WorldHistory W T) :
    worldHistoryOfHistAlt (histAltOfWorldHistory h) = h := rfl

omit [LinearOrder T] in
/-- Round-trip: `HistAlt → WorldHistory → HistAlt` is identity. -/
theorem worldHistory_histAlt_roundtrip (a : HistAlt W T) :
    histAltOfWorldHistory (worldHistoryOfHistAlt a) = a := rfl

omit [LinearOrder T] in
/-- `altReflexive` is equivalent to `WorldHistory.reflexive`. -/
theorem altReflexive_iff_reflexive (a : HistAlt W T) :
    altReflexive a ↔ (worldHistoryOfHistAlt a).reflexive := by
  unfold altReflexive Semantics.Tense.BranchingTime.WorldHistory.reflexive
         worldHistoryOfHistAlt
  constructor
  · intro h s; exact h s.world s.time
  · intro h w t; exact h ⟨w, t⟩

/-- `altMonotone` is equivalent to `WorldHistory.backwardsClosed`. -/
theorem altMonotone_iff_backwardsClosed (a : HistAlt W T) :
    altMonotone a ↔ (worldHistoryOfHistAlt a).backwardsClosed := by
  unfold altMonotone Semantics.Tense.BranchingTime.WorldHistory.backwardsClosed
         worldHistoryOfHistAlt
  constructor
  · intro h w w' t t' hle hw'
    exact h w t' t hle hw'
  · intro h w t t' hle w' hw'
    exact h w w' t' t hle hw'

-- ============================================================================
-- § 2: Earliest Across Alternatives
-- ============================================================================

/-- The set of times at which B is instantiated in some world of a world set.
    `instTimes worlds B` = { t | ∃ w ∈ worlds, ⟨w,t⟩ ∈ B }. -/
def instTimes (worlds : Set W) (B : Set (W × T)) : Set T :=
  { t | ∃ w ∈ worlds, (w, t) ∈ B }

/-- `earliest` across alternatives: the earliest time at which B is
    instantiated in any world of `alt(w,t)`.

    Uses `maxOnScale (· < ·)` which selects elements dominated by all others
    on the < ordering — i.e., the minimum / GLB. This is the same operator
    @cite{rett-2020} uses for her MAX₍<₎. -/
def earliestAlt (alt : HistAlt W T) (B : Set (W × T)) (w : W) (t : T) : Set T :=
  maxOnScale (· < ·) (instTimes (alt w t) B)

-- ============================================================================
-- § 3: B&C's Truth Conditions
-- ============================================================================

/-- B&C's *after*: ∃t : ⟨w,t⟩ ∈ A, t > earliest_{alt(w,t)}(B).

    "There is a time at which A is true in w, and that time is later than
    the earliest time at which B is true in any historical alternative." -/
def BC.after (A B : Set (W × T)) (alt : HistAlt W T) (w : W) : Prop :=
  ∃ t, (w, t) ∈ A ∧ ∃ te ∈ earliestAlt alt B w t, t > te

/-- B&C's *before*: ∃t : ⟨w,t⟩ ∈ A, t < earliest_{alt(w,t)}(B).

    "There is a time at which A is true in w, and that time is earlier than
    the earliest time at which B is true in any historical alternative." -/
def BC.before (A B : Set (W × T)) (alt : HistAlt W T) (w : W) : Prop :=
  ∃ t, (w, t) ∈ A ∧ ∃ te ∈ earliestAlt alt B w t, t < te

-- ============================================================================
-- § 4: Instantiation and the Three Readings of *Before*
-- ============================================================================

/-- B is instantiated in world w: ∃t, ⟨w,t⟩ ∈ B. -/
def Inst (B : Set (W × T)) (w : W) : Prop :=
  ∃ t, (w, t) ∈ B

/-- B is instantiated in some alternative of w at t. -/
def InstAlt (B : Set (W × T)) (alt : HistAlt W T) (w : W) (t : T) : Prop :=
  ∃ w' ∈ alt w t, Inst B w'

/-- The three contextual readings of *before* (B&C §5).

    Since *before* quantifies over historical alternatives, the reading
    depends on whether B is instantiated in the actual world:
    - **Veridical**: B happens in the actual world and in alternatives
    - **Counterfactual**: B doesn't happen in the actual world but does
      in some alternative (the "barely prevented" reading)
    - **NonCommittal**: context is compatible with both -/
inductive BeforeReading where
  | veridical
  | counterfactual
  | nonCommittal
  deriving DecidableEq, Repr

/-- Classify a *before* sentence into its reading based on whether B
    is instantiated in the actual world w.

    Uses classical decidability since the underlying propositions involve
    arbitrary set membership. -/
noncomputable def classifyBeforeReading [∀ p : Prop, Decidable p]
    (B : Set (W × T)) (_w : W)
    (contextWorlds : Set W) : BeforeReading :=
  if (∀ w' ∈ contextWorlds, Inst B w') then .veridical
  else if (∀ w' ∈ contextWorlds, ¬Inst B w') then .counterfactual
  else .nonCommittal

-- ============================================================================
-- § 5: Veridicality of *After*
-- ============================================================================

/-- *After* is veridical under the initial branch point condition: if
    `after(A,B)` holds at w, then B is instantiated in w.

    The key reasoning (B&C §4): A is at ⟨w,t_A⟩ and B is at ⟨w',t_B⟩ for
    some w' ∈ alt(w,t_A). Since t_B < t_A (earliest before A), and
    alt(w,t_A) branches only after t_A, w and w' agree at t_B. So if
    ⟨w',t_B⟩ ∈ B, the "same event" exists at ⟨w,t_B⟩.

    We formalize this with `eventLocal`: if w' agrees with w at t_B
    and ⟨w',t_B⟩ ∈ B, then ⟨w,t_B⟩ ∈ B. -/
theorem BC.after_veridical
    (A B : Set (W × T)) (alt : HistAlt W T)
    (agree : T → W → W → Prop)
    (hIBP : initialBranchPoint alt agree)
    (eventLocal : ∀ w w' t, agree t w w' → (w', t) ∈ B → (w, t) ∈ B)
    (w : W) :
    BC.after A B alt w → Inst B w := by
  rintro ⟨t_A, _, t_B, ⟨⟨w', hw'_alt, hw'_B⟩, _⟩, ht_lt⟩
  -- w' ∈ alt(w, t_A) and (w', t_B) ∈ B, with t_B < t_A
  -- By IBP: agree t_B w w'. By eventLocal: (w, t_B) ∈ B.
  exact ⟨t_B, eventLocal w w' t_B (hIBP w t_A w' hw'_alt t_B ht_lt) hw'_B⟩

-- ============================================================================
-- § 6: Uniformity
-- ============================================================================

/-- B&C's key claim: *before* and *after* use the same `earliestAlt` operator.
    The only difference is the comparison direction (< vs >). This is the
    "uniform analysis" — the veridicality asymmetry is not lexical but
    structural, following from branching time. -/
theorem BC.uniform_structure (A B : Set (W × T)) (alt : HistAlt W T) (w : W) :
    (BC.before A B alt w ↔ ∃ t, (w, t) ∈ A ∧ ∃ te ∈ earliestAlt alt B w t, t < te) ∧
    (BC.after A B alt w ↔ ∃ t, (w, t) ∈ A ∧ ∃ te ∈ earliestAlt alt B w t, t > te) :=
  ⟨Iff.rfl, Iff.rfl⟩

-- ============================================================================
-- § 7: O&ST Eventuality-Relative Equivalence (def 17)
-- ============================================================================

/-! @cite{ogihara-steinert-threlkeld-2024} §4 propose revising B&C's equivalence
    relation to be sensitive to both an interval I and an eventuality e. The key
    idea: alternative worlds must contain a counterpart of e that co-occurs with
    e throughout the interval [START_w(e₁), START(I)), and worlds must be
    identical at all earlier intervals.

    This allows w₂ to become distinct from w₁ before I as long as they contain
    events that start simultaneously, share the same set of participants, and
    run up until I (not necessarily including I). -/

/-- Counterpart relation on eventualities across worlds
    (@cite{ogihara-steinert-threlkeld-2024}, fn. 18): counterpart eventualities
    share essential properties such as starting time and thematic participants. -/
abbrev Counterpart (W T : Type*) := W → T → W → T → Prop

/-- **Eventuality-relative equivalence** ≃_{I,e₁}
    (@cite{ogihara-steinert-threlkeld-2024}, def 17).

    For worlds w₁, w₂ ∈ W, interval I, and eventuality e₁ in w₁,
    w₁ ≃_{I,e₁} w₂ iff:

    (i) there is an eventuality e₂ in w₂ understood as e₁'s counterpart;
    (ii) e₁ and e₂ co-occur throughout [START_{w₁}(e₁), START(I));
    (iii) at all intervals I₁ < START_{w₁}(e₁), w₁ and w₂ are identical.

    The `coOccur` parameter models condition (ii): both eventualities occur
    throughout the interval [start_e, start_I). The `agree` parameter
    models condition (iii): world identity at earlier intervals. -/
def equivIE
    (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI : T) (e₁_start : T) : Prop :=
  -- (i) counterpart exists
  counterpart w₁ e₁_start w₂ e₁_start ∧
  -- (ii) co-occurrence throughout [start_e, start_I)
  coOccur w₁ e₁_start w₂ e₁_start e₁_start startI ∧
  -- (iii) identical at all earlier times
  (∀ t', t' < e₁_start → agree t' w₁ w₂)

-- ============================================================================
-- § 8: Revamped Alternative Set (def 18)
-- ============================================================================

/-! The revised alt(w, I, e) uses the eventuality-relative equivalence
    (@cite{ogihara-steinert-threlkeld-2024}, def 18a). -/

/-- **Eventuality-relative alternatives** alt(w, I, e)
    (@cite{ogihara-steinert-threlkeld-2024}, def 18a):
    alt(w, I, e) ⊆ {w' : w ≃_{I,e} w'}. -/
def altIE
    (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w : W) (startI : T) (e_start : T) : Set W :=
  { w' | equivIE counterpart coOccur agree w w' startI e_start }

/-- **Event continuation condition** (@cite{ogihara-steinert-threlkeld-2024}, def 18b):
    alt(w, I, e) contains only those worlds w' in which the counterpart
    eventuality of e develops beyond I, as long as this is reasonable.
    Modeled as a predicate on the alternative set. -/
def eventContinuation (alt : Set W) (continues : W → Prop) : Set W :=
  { w' ∈ alt | continues w' }

/-- **Downward closure** (@cite{ogihara-steinert-threlkeld-2024}, def 18c):
    If w ≃_{I,e} w' and I' < I, then w ≃_{I',e} w'.
    Earlier equivalence classes are supersets. -/
theorem equivIE_downward_closed
    (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (coOccur_mono : ∀ w₁ e₁ w₂ e₂ s₁ s₂ s₂',
      s₂' ≤ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂')
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI startI' : T) (e_start : T)
    (hle : startI' ≤ startI)
    (h : equivIE counterpart coOccur agree w₁ w₂ startI e_start) :
    equivIE counterpart coOccur agree w₁ w₂ startI' e_start :=
  ⟨h.1, coOccur_mono w₁ e_start w₂ e_start e_start startI startI' hle h.2.1, h.2.2⟩

-- ============================================================================
-- § 9: equivIE Generalizes initialBranchPoint
-- ============================================================================

/-! O&ST's eventuality-relative equivalence ≃_{I,e} is a strict generalization
    of B&C's initial branch point condition. Under trivial counterpart and
    co-occurrence relations (always true), `equivIE` reduces to condition (iii)
    alone: identity at all times before the eventuality's start — which is
    exactly B&C's `initialBranchPoint` restricted to a single world pair.

    This shows that the O&ST framework subsumes B&C: any `HistAlt` satisfying
    `initialBranchPoint` can be recovered as an `altIE` with trivial parameters. -/

/-- Under trivial counterpart (always holds) and trivial co-occurrence (always
    holds), `equivIE` reduces to B&C's condition (iii): agreement at all
    earlier times. This is the per-world-pair content of `initialBranchPoint`. -/
theorem equivIE_trivial_iff_agree
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI e_start : T) :
    equivIE (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True) agree w₁ w₂ startI e_start ↔
    (∀ t', t' < e_start → agree t' w₁ w₂) := by
  simp [equivIE]

/-- B&C's `alt(w,t)` under `initialBranchPoint` is a subset of `altIE` with
    trivial counterpart/co-occurrence, when the eventuality starts at t.
    That is: any world sharing w's history up to t (B&C-style) also satisfies
    the trivial ≃_{I,e} (O&ST-style). -/
theorem histAlt_subset_altIE_trivial
    (alt : HistAlt W T) (agree : T → W → W → Prop)
    (hIBP : initialBranchPoint alt agree)
    (w : W) (t : T) :
    alt w t ⊆ altIE (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True) agree w t t := by
  intro w' hw'
  rw [altIE, Set.mem_setOf_eq, equivIE_trivial_iff_agree]
  exact hIBP w t w' hw'

end Semantics.Tense.TemporalConnectives.BeaverCondoravdi
