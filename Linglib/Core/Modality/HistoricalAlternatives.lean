import Linglib.Core.WorldTimeIndex
import Linglib.Theories.Semantics.Modality.TemporalConstraint

/-!
# Historical Alternatives
@cite{condoravdi-2002} @cite{thomason-1984} @cite{cariani-santorio-2018}

Framework-agnostic relational structure on worlds: the **historical
alternatives** of a world at a time are the worlds that perfectly match
it in matters of particular fact up to that time
(@cite{lewis-1979}, @cite{cariani-santorio-2018}). This is the substrate
of the historical modal base used by metaphysical and future-oriented
modality.

## Key Concepts

1. **World history function** — the relation between a ⟨world, time⟩
   point and the worlds that share its history up to that time.
2. **Historical/actual/future bases** — the three temporal slices of
   the historical modal base, indexed by time predicates from
   `Theories/Semantics/Modality/TemporalConstraint`.
3. **Historical equivalence** — the equivalence relation `≃_t` of
   @cite{condoravdi-2002} §4.1.
4. **Metaphysical modal base** — the equivalence class of the
   evaluation world under `≃_t`.

## What's not here

This file is foundational: it commits to no specific modal theory
(Kratzer, Stalnaker selection, etc.). It defines the relational
substrate that any modal theory referring to "historical
alternatives" can use. The selectional semantics for *will*
(@cite{cariani-santorio-2018}) lives in
`Theories/Semantics/Modality/Selectional.lean`.
-/

namespace Core.Modality.HistoricalAlternatives

open _root_.Core.Time

/--
World history function: given a world and time, returns worlds that
agree with that world up to that time.

This is the basis for the "historical" or "open future" modal base
used in future-oriented modality.

Intuition: At time t in world w, multiple futures are possible.
The historical alternatives are all worlds that share the same
past with w up to t.
-/
def WorldHistory (W Time : Type*) := WorldTimeIndex W Time → Set W

/--
Historical modal base: situations whose worlds agree with s up to τ(s),
and whose times are at or after τ(s).

Following @cite{thomason-1984} and @cite{condoravdi-2002}:
- Past is fixed (determined)
- Future branches (open)

hist(s) = {s' : w_{s'} ∈ H(wₛ, τ(s)) ∧ τ(s') ≥ τ(s)}
-/
def historicalBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ s'.time ≥ s.time }

/--
Actual history base (@cite{klecha-2016} DOX): situations whose worlds
agree with `s` and whose times are at or before τ(s).

This is the temporal mirror of `historicalBase` (which uses ≥).
DOX returns actual histories — world-time pairs where the temporal
component ends at the evaluation time: 𝒜_t = {i : τ(i) = (-∞, t]}.
-/
def actualHistoryBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ s'.time ≤ s.time }

/--
Future history base (@cite{klecha-2016} CIR): situations whose worlds
agree with `s` and whose times are strictly after τ(s).

CIR returns future histories — world-time pairs where the temporal
component departs from the evaluation time: ℱ_t = {j : τ(j) = (t, ∞)}.
-/
def futureHistoryBase {W Time : Type*} [LT Time]
    (history : WorldHistory W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ s'.time > s.time }

/--
A world history is reflexive if every world agrees with itself.
-/
def WorldHistory.reflexive {W Time : Type*} (h : WorldHistory W Time) : Prop :=
  ∀ s : WorldTimeIndex W Time, s.world ∈ h s

/--
A world history is symmetric: if w' agrees with w up to t,
then w agrees with w' up to t.

@cite{condoravdi-2002} §4.1, condition (i): ≃_t is an equivalence
relation for all t. Symmetry ensures historical equivalence is
bidirectional — "sharing a history" is a mutual relationship.
-/
def WorldHistory.symmetric {W Time : Type*}
    (h : WorldHistory W Time) : Prop :=
  ∀ (w w' : W) (t : Time), w' ∈ h ⟨w, t⟩ → w ∈ h ⟨w', t⟩

/--
A world history is transitive: if w' agrees with w up to t
and w'' agrees with w' up to t, then w'' agrees with w up to t.
-/
def WorldHistory.transitive {W Time : Type*}
    (h : WorldHistory W Time) : Prop :=
  ∀ (w w' w'' : W) (t : Time), w' ∈ h ⟨w, t⟩ → w'' ∈ h ⟨w', t⟩ → w'' ∈ h ⟨w, t⟩

/--
A world history is backwards-closed: if w' agrees with w up to t,
and t' ≤ t, then w' agrees with w up to t'.

"If two worlds agree up to time t, they also agree up to any earlier time."
@cite{condoravdi-2002} §4.1, condition (ii).
-/
def WorldHistory.backwardsClosed {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop :=
  ∀ (w w' : W) (t t' : Time), t' ≤ t → w' ∈ h ⟨w, t⟩ → w' ∈ h ⟨w, t'⟩

/--
Standard historical modal base properties.
@cite{condoravdi-2002} §4.1: ≃_t is an equivalence relation (i) that
is monotone in time (ii).
-/
structure HistoricalProperties {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop where
  /-- Every world agrees with itself -/
  refl : h.reflexive
  /-- Historical agreement is symmetric -/
  symm : h.symmetric
  /-- Historical agreement is transitive -/
  trans : h.transitive
  /-- Agreement is preserved for earlier times -/
  backwards : h.backwardsClosed


/--
A temporal proposition: true or false at each situation.

This is the situation-semantic analog of Prop' W.
-/
abbrev TProp (W Time : Type*) := WorldTimeIndex W Time → Prop

/--
Lift a world proposition to a temporal proposition.

The lifted proposition is true at situation s iff the original
proposition is true at s.world.
-/
def liftProp {W Time : Type*} (p : W → Prop) : TProp W Time :=
  λ s => p s.world

/--
A proposition holds at time t in world w.
-/
def holdsAt {W Time : Type*} (p : TProp W Time) (w : W) (t : Time) : Prop :=
  p ⟨w, t⟩


/-! ## Bridge: BranchingTime ↔ TemporalConstraint

`TemporalConstraint` defines abstract time predicates (actual: ≤, future: >,
prospective: ≥) on bare time values. `BranchingTime` defines concrete sets of
*situations* (world-time pairs) using the same inequalities on the time
component. The theorems below make the connection structural: membership in a
history base implies (and is implied by) the corresponding time predicate,
modulo the world-agreement condition. -/

open Semantics.Modality.TemporalConstraint

/-- A situation in `historicalBase` has prospective time:
    `s' ∈ historicalBase h s → isProspectiveHistory s.time s'.time`. -/
theorem historicalBase_time_prospective {W Time : Type*} [LE Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ historicalBase history s) :
    isProspectiveHistory s.time s'.time :=
  h.2

/-- A situation in `actualHistoryBase` has actual time:
    `s' ∈ actualHistoryBase h s → isActualHistory s.time s'.time`. -/
theorem actualHistoryBase_time_actual {W Time : Type*} [LE Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ actualHistoryBase history s) :
    isActualHistory s.time s'.time :=
  h.2

/-- A situation in `futureHistoryBase` has future time:
    `s' ∈ futureHistoryBase h s → isFutureHistory s.time s'.time`. -/
theorem futureHistoryBase_time_future {W Time : Type*} [LT Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ futureHistoryBase history s) :
    isFutureHistory s.time s'.time :=
  h.2

/-- `futureHistoryBase ⊆ historicalBase`: future situations are prospective.
    This is the situation-semantic instantiation of `future_implies_prospective`. -/
theorem futureHistoryBase_subset_historicalBase {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time) (s : WorldTimeIndex W Time) :
    futureHistoryBase history s ⊆ historicalBase history s :=
  λ _ ⟨hw, ht⟩ => ⟨hw, le_of_lt ht⟩

/-- `actualHistoryBase ∩ historicalBase` contains only simultaneous situations:
    if `s'.time ≤ s.time` and `s'.time ≥ s.time`, then `s'.time = s.time`.
    This is the situation-semantic instantiation of
    `actual_and_prospective_iff_simultaneous`. -/
theorem actualBase_inter_historicalBase_simultaneous {W Time : Type*} [PartialOrder Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (hActual : s' ∈ actualHistoryBase history s)
    (hHist : s' ∈ historicalBase history s) :
    s'.time = s.time :=
  le_antisymm hActual.2 hHist.2

/-- Actual and future history bases are disjoint on the time component:
    no situation can have time both ≤ t and > t.
    This is the situation-semantic instantiation of `past_future_disjoint`
    (actual ∩ future = ∅ since actual ⊃ past). -/
theorem actualBase_futureBase_disjoint {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time) :
    ¬(s' ∈ actualHistoryBase history s ∧ s' ∈ futureHistoryBase history s) := by
  intro ⟨⟨_, hle⟩, ⟨_, hgt⟩⟩
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

/-- Every situation is in `actualHistoryBase ∪ futureHistoryBase` (on the time
    component): for any `s'`, either `s'.time ≤ s.time` or `s'.time > s.time`.
    This is the situation-semantic instantiation of
    `actual_future_complementary`. -/
theorem actualBase_futureBase_complementary {W Time : Type*} [LinearOrder Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s) :
    s' ∈ actualHistoryBase history s ∨ s' ∈ futureHistoryBase history s :=
  (le_or_gt s'.time s.time).elim
    (λ h => Or.inl ⟨hw, h⟩)
    (λ h => Or.inr ⟨hw, h⟩)

/-- Converse: prospective time + world agreement → membership in
    `historicalBase`. The time predicate fully characterizes the temporal
    component of the base. -/
theorem prospective_time_mem_historicalBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isProspectiveHistory s.time s'.time) :
    s' ∈ historicalBase history s :=
  ⟨hw, ht⟩

/-- Converse: actual time + world agreement → membership in
    `actualHistoryBase`. -/
theorem actual_time_mem_actualHistoryBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isActualHistory s.time s'.time) :
    s' ∈ actualHistoryBase history s :=
  ⟨hw, ht⟩

/-- Converse: future time + world agreement → membership in
    `futureHistoryBase`. -/
theorem future_time_mem_futureHistoryBase {W Time : Type*} [LT Time]
    (history : WorldHistory W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isFutureHistory s.time s'.time) :
    s' ∈ futureHistoryBase history s :=
  ⟨hw, ht⟩

/-! ## Historical Equivalence

@cite{condoravdi-2002} §4.1: historical equivalence ≃_t groups worlds
that share the same history up to time t. The equivalence classes are
the "ways things might have gone" — worlds that agree on the past but
may diverge in the future. -/

variable {W Time : Type*}

/-- Historical equivalence: `w'` agrees with `w` up to time `t`.
    `w ≃_t w'` iff `w' ∈ history(w, t)`. -/
def histEquiv (history : WorldHistory W Time) (t : Time)
    (w w' : W) : Prop :=
  w' ∈ history ⟨w, t⟩

/-- `histEquiv history t` is an equivalence relation when `history`
    satisfies the standard properties. This is the content of
    @cite{condoravdi-2002} §4.1, condition (i). -/
def histEquiv_equivalence {history : WorldHistory W Time}
    (hRefl : history.reflexive) (hSymm : history.symmetric)
    (hTrans : history.transitive) (t : Time) :
    Equivalence (histEquiv history t) where
  refl w := hRefl ⟨w, t⟩
  symm h := hSymm _ _ t h
  trans h₁ h₂ := hTrans _ _ _ t h₁ h₂

/-- The `Setoid` induced by historical equivalence at time `t`. -/
def histSetoid {history : WorldHistory W Time}
    (hRefl : history.reflexive) (hSymm : history.symmetric)
    (hTrans : history.transitive) (t : Time) : Setoid W where
  r := histEquiv history t
  iseqv := histEquiv_equivalence hRefl hSymm hTrans t

/-- `histEquiv_equivalence` from bundled `HistoricalProperties`. -/
def histEquiv_equivalence' {history : WorldHistory W Time} [LE Time]
    (hp : HistoricalProperties history) (t : Time) :
    Equivalence (histEquiv history t) :=
  histEquiv_equivalence hp.refl hp.symm hp.trans t

/-- `histSetoid` from bundled `HistoricalProperties`. -/
def histSetoid' {history : WorldHistory W Time} [LE Time]
    (hp : HistoricalProperties history) (t : Time) : Setoid W :=
  histSetoid hp.refl hp.symm hp.trans t

/-- Historical equivalence is reflexive (from `WorldHistory.reflexive`). -/
theorem histEquiv_refl {history : WorldHistory W Time}
    (hRefl : history.reflexive) (t : Time) (w : W) :
    histEquiv history t w w :=
  hRefl ⟨w, t⟩

/-- Historical equivalence is symmetric (from `WorldHistory.symmetric`). -/
theorem histEquiv_symm {history : WorldHistory W Time}
    (hSymm : history.symmetric) (t : Time) {w w' : W}
    (h : histEquiv history t w w') :
    histEquiv history t w' w :=
  hSymm w w' t h

/-- Historical equivalence is transitive (from `WorldHistory.transitive`). -/
theorem histEquiv_trans {history : WorldHistory W Time}
    (hTrans : history.transitive) (t : Time) {w w' w'' : W}
    (h₁ : histEquiv history t w w')
    (h₂ : histEquiv history t w' w'') :
    histEquiv history t w w'' :=
  hTrans w w' w'' t h₁ h₂

variable [LE Time] in
/-- Historical equivalence is monotone in time: agreement up to a later
    time implies agreement up to an earlier time
    (from `WorldHistory.backwardsClosed`). -/
theorem histEquiv_mono {history : WorldHistory W Time}
    (hBC : history.backwardsClosed) {t t' : Time} (w w' : W)
    (hle : t' ≤ t) (h : histEquiv history t w w') :
    histEquiv history t' w w' :=
  hBC w w' t t' hle h

variable [LE Time] in
/-- @cite{condoravdi-2002} §4.1: "as time advances the set of
    metaphysical alternatives to any given world decreases."

    The function `t ↦ { w' | w ≃_t w' }` is antitone: later times
    yield smaller (or equal) equivalence classes. -/
theorem alternatives_antitone {history : WorldHistory W Time}
    (hBC : history.backwardsClosed) (w : W) {t t' : Time}
    (hle : t ≤ t') :
    { w' | histEquiv history t' w w' } ⊆
    { w' | histEquiv history t w w' } :=
  λ _ h => histEquiv_mono hBC w _ hle h

/-! ## Metaphysical Modal Base

@cite{condoravdi-2002} §4.1: for modals expressing metaphysical modality,
the modal base consists of historical alternatives: `MB(w,t) = {w' | w ≃_t w'}`.
This is the maximal modal base compatible with the world's history up to `t`. -/

/-- The metaphysical modal base: at world `w` and time `t`, the set of
    all worlds sharing `w`'s history up to `t`. -/
def metaphysicalBase (history : WorldHistory W Time) :
    W → Time → Set W :=
  λ w t => { w' | histEquiv history t w w' }

variable [LE Time] in
/-- The metaphysical modal base is antitone in time: later times yield
    smaller accessible sets. -/
theorem metaphysicalBase_antitone {history : WorldHistory W Time}
    (hBC : history.backwardsClosed) (w : W) {t t' : Time}
    (hle : t ≤ t') :
    metaphysicalBase history w t' ⊆ metaphysicalBase history w t :=
  alternatives_antitone hBC w hle

/-! ## Settledness and Diversity

@cite{condoravdi-2002} §4.1: an issue is **settled** at time t₀ when
    all historically equivalent worlds agree on its resolution.
    Past and present issues are always settled; future issues may not be.

    The **diversity condition** [45] is the felicity condition for
    associating a metaphysical modal base with a possibility modal:
    the modal base must contain worlds that disagree on the property. -/

/-- Settledness [44]: within each equivalence class of the common ground,
    the property `P` is resolved uniformly — all historically equivalent
    worlds agree on whether `P` holds.

    @cite{condoravdi-2002}: "the past and the present are settled." -/
def settled (history : WorldHistory W Time) (cg : Set W)
    (t₀ : Time) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ w', histEquiv history t₀ w w' → (P w ↔ P w')

/-- Diversity Condition [45]: there exists a world in the common ground
    whose modal base contains worlds that disagree on `P`.

    This is the felicity condition for associating a metaphysical modal
    base with a possibility modal applying to property `P`. Without
    diversity, the modal assertion would be equivalent to a non-modal
    assertion, violating the distinctness requirement. -/
def diverse (MB : W → Time → Set W) (cg : Set W)
    (t : Time) (P : W → Prop) : Prop :=
  ∃ w ∈ cg, ∃ w' ∈ MB w t, ∃ w'' ∈ MB w t, P w' ∧ ¬ P w''

/-- When `MB(w,t) ⊆ {w' | w ≃_t w'}` (the metaphysical case) and `P` is
    settled, diversity fails: all worlds in the modal base agree on `P`,
    so no pair can witness disagreement.

    This is the key theorem blocking metaphysical readings for settled
    properties. -/
theorem settled_not_diverse
    (history : WorldHistory W Time) (MB : W → Time → Set W)
    (cg : Set W) (t : Time) (P : W → Prop)
    (hMB : ∀ w ∈ cg, ∀ w' ∈ MB w t, histEquiv history t w w')
    (hSettled : settled history cg t P) :
    ¬ diverse MB cg t P := by
  intro ⟨w, hwcg, w', hw'MB, w'', hw''MB, hPw', hnPw''⟩
  have heq' := hSettled w hwcg w' (hMB w hwcg w' hw'MB)
  have heq'' := hSettled w hwcg w'' (hMB w hwcg w'' hw''MB)
  exact hnPw'' (heq''.mp (heq'.mpr hPw'))

/-- Diversity is witnessed by the common ground: if `P` holds for some
    world in `cg` and fails for another, and both are accessible from
    some `w` via `MB`, then diversity holds. -/
theorem diverse_of_witnesses
    (MB : W → Time → Set W) (cg : Set W) (t : Time) (P : W → Prop)
    (w : W) (hwcg : w ∈ cg)
    (w' w'' : W) (hw' : w' ∈ MB w t) (hw'' : w'' ∈ MB w t)
    (hP : P w') (hnP : ¬ P w'') :
    diverse MB cg t P :=
  ⟨w, hwcg, w', hw', w'', hw'', hP, hnP⟩

end Core.Modality.HistoricalAlternatives
