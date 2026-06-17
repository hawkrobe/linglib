import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.LinearOrder
import Linglib.Core.Logic.Intensional.WorldTimeIndex
import Linglib.Core.Logic.Temporal.Basic

/-!
# Historical Alternatives

The **historical alternatives** of a world at a time are the worlds that
perfectly match it in matters of particular fact up to that time
([lewis-1979], [cariani-santorio-2018]).

## Main definitions

* `HistoricalAlternatives` : the relation between a ⟨world, time⟩ index and the
  worlds that share its history up to that time;
* `isActualHistory`, `isFutureHistory`, `isPastHistory`, `isProspectiveHistory`,
  `isMaximalHistory` : interval predicates indexing the situation-base slices;
* `historicalBase`, `actualHistoryBase`, `futureHistoryBase` : the temporal
  slices of the historical modal base;
* `histEquiv` : historical equivalence `≃_t` of [condoravdi-2002];
* `metaphysicalBase` : the equivalence class of the evaluation world under `≃_t`;
* `toTWFrame` : a relation with `HistoricalProperties`, viewed as a
  `Core.Logic.Temporal.TWFrame` ([thomason-1984], [von-kutschera-1997]).

## Main results

* `upperLimitConstraintModal_implies_value` : the Upper Limit Constraint
  ([abusch-1997]) is derived from `actualHistoryBase` membership;
* `alternatives_antitone`, `metaphysicalBase_antitone` : the metaphysical base
  shrinks as time advances;
* `settled_not_diverse` : settled properties block metaphysical readings;
* `toTWFrame_sat_N_atom` : the object logic's historical necessity `N` reduces to
  truth throughout the `metaphysicalBase`.
-/

open Core (WorldTimeIndex)

/-- Historical-alternatives relation: given a ⟨world, time⟩ index, returns the
    worlds that agree with that world up to that time. This is the basis for the
    "historical" or "open future" modal base used in future-oriented modality. -/
def HistoricalAlternatives (W Time : Type*) := WorldTimeIndex W Time → Set W

namespace HistoricalAlternatives

variable {W Time : Type*}

/-! ## Partial History Taxonomy

[klecha-2016] distinguishes five kinds of partial history by the temporal
component of the world-time pair relative to a reference time `t`. We formalize
all five as predicates on time pairs. Only actual and future drive the core
DOX/CIR mechanism, but the full taxonomy is needed for extensions (prospective
is the temporal component of `historicalBase` below).

These are framework-neutral interval predicates over `LE Time` / `LT Time`; the
[klecha-2016] citation is for the terminology, not the mathematical content
(which is just `≤`, `<`, `>`, `≥`). -/

/-- Maximal history: unrestricted temporal extent (Ω_t = all histories). -/
def isMaximalHistory (_evalTime _historyTime : Time) : Prop :=
  True

/-- Actual history: temporal component ends at or before `t` (𝒜_t). -/
def isActualHistory [LE Time] (evalTime historyTime : Time) : Prop :=
  historyTime ≤ evalTime

/-- Past history: temporal component ends strictly before `t` (𝒫_t).
    Distinct from actual: past excludes `t` itself. -/
def isPastHistory [LT Time] (evalTime historyTime : Time) : Prop :=
  historyTime < evalTime

/-- Future history: temporal component starts strictly after `t` (ℱ_t). -/
def isFutureHistory [LT Time] (evalTime historyTime : Time) : Prop :=
  historyTime > evalTime

/-- Prospective history: temporal component starts at or after `t` (ℙ_t).
    This is exactly the temporal component of `historicalBase`. -/
def isProspectiveHistory [LE Time] (evalTime historyTime : Time) : Prop :=
  historyTime ≥ evalTime

/-- Actual and future histories are complementary: every time is
    either ≤ t (actual) or > t (future). -/
theorem actual_future_complementary [LinearOrder Time]
    (evalTime historyTime : Time) :
    isActualHistory evalTime historyTime ∨ isFutureHistory evalTime historyTime :=
  (lt_or_ge evalTime historyTime).elim Or.inr Or.inl

/-- Past and prospective histories are complementary: every time is
    either < t (past) or ≥ t (prospective). -/
theorem past_prospective_complementary [LinearOrder Time]
    (evalTime historyTime : Time) :
    isPastHistory evalTime historyTime ∨ isProspectiveHistory evalTime historyTime :=
  (lt_or_ge historyTime evalTime).elim Or.inl Or.inr

/-- Past ⊂ actual: strict past implies actual. -/
theorem past_implies_actual [Preorder Time]
    (evalTime historyTime : Time) (h : isPastHistory evalTime historyTime) :
    isActualHistory evalTime historyTime :=
  le_of_lt h

/-- Future ⊂ prospective: strict future implies prospective. -/
theorem future_implies_prospective [Preorder Time]
    (evalTime historyTime : Time) (h : isFutureHistory evalTime historyTime) :
    isProspectiveHistory evalTime historyTime :=
  le_of_lt h

/-- Actual ∩ prospective = simultaneous: a time that is both actual
    and prospective is exactly the evaluation time. -/
theorem actual_and_prospective_iff_simultaneous [PartialOrder Time]
    (evalTime historyTime : Time) :
    isActualHistory evalTime historyTime ∧ isProspectiveHistory evalTime historyTime ↔
    historyTime = evalTime :=
  ⟨λ ⟨hle, hge⟩ => le_antisymm hle hge, λ h => ⟨le_of_eq h, ge_of_eq h⟩⟩

/-- Past and future are disjoint: no time is both < t and > t. -/
theorem past_future_disjoint [Preorder Time]
    (evalTime historyTime : Time) :
    ¬(isPastHistory evalTime historyTime ∧ isFutureHistory evalTime historyTime) := by
  intro ⟨h1, h2⟩
  exact lt_asymm h1 h2

/-! ## Situation Bases -/

/-- Historical modal base: situations whose worlds agree with `s` up to τ(s),
    and whose times are at or after τ(s). Past is fixed, the future branches
    ([thomason-1984], [condoravdi-2002]). -/
def historicalBase [LE Time]
    (history : HistoricalAlternatives W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ isProspectiveHistory s.time s'.time }

/-- Actual history base ([klecha-2016] DOX): situations whose worlds agree
    with `s` and whose times are at or before τ(s) — the temporal mirror of
    `historicalBase`. -/
def actualHistoryBase [LE Time]
    (history : HistoricalAlternatives W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ isActualHistory s.time s'.time }

/-- Future history base ([klecha-2016] CIR): situations whose worlds agree
    with `s` and whose times are strictly after τ(s). -/
def futureHistoryBase [LT Time]
    (history : HistoricalAlternatives W Time)
    (s : WorldTimeIndex W Time) : Set (WorldTimeIndex W Time) :=
  { s' | s'.world ∈ history s ∧ isFutureHistory s.time s'.time }

/-- A historical-alternatives relation is reflexive if every world agrees with
    itself. -/
def reflexive (h : HistoricalAlternatives W Time) : Prop :=
  ∀ s : WorldTimeIndex W Time, s.world ∈ h s

/-- A historical-alternatives relation is symmetric: if `w'` agrees with `w` up
    to `t`, then `w` agrees with `w'` up to `t`. Part of `≃_t` being an
    equivalence relation ([condoravdi-2002]). -/
def symmetric (h : HistoricalAlternatives W Time) : Prop :=
  ∀ (w w' : W) (t : Time), w' ∈ h ⟨w, t⟩ → w ∈ h ⟨w', t⟩

/-- A historical-alternatives relation is transitive: if `w'` agrees with `w` up
    to `t` and `w''` agrees with `w'` up to `t`, then `w''` agrees with `w` up
    to `t`. -/
def transitive (h : HistoricalAlternatives W Time) : Prop :=
  ∀ (w w' w'' : W) (t : Time), w' ∈ h ⟨w, t⟩ → w'' ∈ h ⟨w', t⟩ → w'' ∈ h ⟨w, t⟩

/-- A historical-alternatives relation is backwards-closed: if `w'` agrees with
    `w` up to `t` and `t' ≤ t`, then `w'` agrees with `w` up to `t'`
    ([condoravdi-2002]). -/
def backwardsClosed [LE Time] (h : HistoricalAlternatives W Time) : Prop :=
  ∀ (w w' : W) (t t' : Time), t' ≤ t → w' ∈ h ⟨w, t⟩ → w' ∈ h ⟨w, t'⟩

/-- Standard historical modal base properties: `≃_t` is an equivalence relation
    that is monotone in time ([condoravdi-2002]). -/
structure HistoricalProperties [LE Time]
    (h : HistoricalAlternatives W Time) : Prop where
  /-- Every world agrees with itself -/
  refl : h.reflexive
  /-- Historical agreement is symmetric -/
  symm : h.symmetric
  /-- Historical agreement is transitive -/
  trans : h.transitive
  /-- Agreement is preserved for earlier times -/
  backwards : h.backwardsClosed

/-- A temporal proposition: true or false at each situation. The
    situation-semantic analog of `Prop' W`. -/
abbrev TProp (W Time : Type*) := WorldTimeIndex W Time → Prop

/-- Lift a world proposition to a temporal proposition, true at situation `s`
    iff the original holds at `s.world`. -/
def liftProp (p : W → Prop) : TProp W Time :=
  λ s => p s.world

/-- A proposition holds at time `t` in world `w`. -/
def holdsAt (p : TProp W Time) (w : W) (t : Time) : Prop :=
  p ⟨w, t⟩

/-! ## Klecha 2016: ULC derived from history structure

The Upper Limit Constraint — embedded RT under a doxastic attitude must be
≤ matrix EvalT — was stated by [abusch-1997] ("the now of an epistemic
alternative is an upper limit for the denotation of tenses"), with the
presuppositional construal due to [heim-1994-comments].
[klecha-2016] *derives* the same constraint from the temporal character of
the doxastic modal base: DOX returns actual histories 𝒜_t, and membership
entails RT ≤ t by `.2` projection through the situation-base definition.
Symmetrically, CIR returns ℱ_t and membership entails RT > t. The theorems
below make the projection kernel-checked.

This is what distinguishes [klecha-2016]'s account from
[abusch-1997]'s: both rely on the branching-futures motivation, but Klecha
derives ULC from history structure while Abusch states it as a constraint on
tense-node denotation. The Klecha-namespace dispatch on `ModalBaseKind` lives in
`Semantics/Modality/TemporalConstraint.lean`. The modal-alternative
quantification in Abusch's formulation is captured here at the substrate level
by `HistoricalAlternatives` membership; the value-level projection
`s'.time ≤ s.time` recovers Abusch's bare-`≤` form. -/

/-- A situation in `historicalBase` has prospective time. -/
theorem historicalBase_time_prospective [LE Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ historicalBase history s) :
    isProspectiveHistory s.time s'.time :=
  h.2

/-- A situation in `actualHistoryBase` has actual time. -/
theorem actualHistoryBase_time_actual [LE Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ actualHistoryBase history s) :
    isActualHistory s.time s'.time :=
  h.2

/-- Modal-layer Upper Limit Constraint: an embedded situation `s'` satisfies it
    relative to a matrix situation `s` and doxastic accessibility `history` iff
    `s'` lies in `s`'s actual-history base. See the section note for how this
    recovers [abusch-1997]'s alternative-quantifying formulation. -/
def upperLimitConstraintModal [LE Time]
    (history : HistoricalAlternatives W Time)
    (matrixSituation embeddedSituation : WorldTimeIndex W Time) : Prop :=
  embeddedSituation ∈ actualHistoryBase history matrixSituation

/-- The modal-layer Upper Limit Constraint implies the value-level one
    (`embeddedSituation.time ≤ matrixSituation.time`), by `.2` projection
    through `actualHistoryBase`. -/
theorem upperLimitConstraintModal_implies_value [LE Time]
    (history : HistoricalAlternatives W Time)
    (s s' : WorldTimeIndex W Time)
    (h : upperLimitConstraintModal history s s') :
    s'.time ≤ s.time :=
  h.2

/-- A situation in `futureHistoryBase` has future time. -/
theorem futureHistoryBase_time_future [LT Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (h : s' ∈ futureHistoryBase history s) :
    isFutureHistory s.time s'.time :=
  h.2

/-- `futureHistoryBase ⊆ historicalBase`: future situations are prospective.
    The situation-semantic instantiation of `future_implies_prospective`. -/
theorem futureHistoryBase_subset_historicalBase [Preorder Time]
    (history : HistoricalAlternatives W Time) (s : WorldTimeIndex W Time) :
    futureHistoryBase history s ⊆ historicalBase history s :=
  λ _ ⟨hw, ht⟩ => ⟨hw, le_of_lt ht⟩

/-- `actualHistoryBase ∩ historicalBase` contains only simultaneous situations.
    The situation-semantic instantiation of
    `actual_and_prospective_iff_simultaneous`. -/
theorem actualBase_inter_historicalBase_simultaneous [PartialOrder Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (hActual : s' ∈ actualHistoryBase history s)
    (hHist : s' ∈ historicalBase history s) :
    s'.time = s.time :=
  le_antisymm hActual.2 hHist.2

/-- Actual and future history bases are disjoint on the time component.
    The situation-semantic instantiation of `past_future_disjoint`. -/
theorem actualBase_futureBase_disjoint [Preorder Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time) :
    ¬(s' ∈ actualHistoryBase history s ∧ s' ∈ futureHistoryBase history s) := by
  intro ⟨⟨_, hle⟩, ⟨_, hgt⟩⟩
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

/-- Every situation is in `actualHistoryBase ∪ futureHistoryBase` on the time
    component. The situation-semantic instantiation of
    `actual_future_complementary`. -/
theorem actualBase_futureBase_complementary [LinearOrder Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s) :
    s' ∈ actualHistoryBase history s ∨ s' ∈ futureHistoryBase history s :=
  (le_or_gt s'.time s.time).elim
    (λ h => Or.inl ⟨hw, h⟩)
    (λ h => Or.inr ⟨hw, h⟩)

/-- Converse: prospective time + world agreement → membership in
    `historicalBase`. -/
theorem prospective_time_mem_historicalBase [LE Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isProspectiveHistory s.time s'.time) :
    s' ∈ historicalBase history s :=
  ⟨hw, ht⟩

/-- Converse: actual time + world agreement → membership in
    `actualHistoryBase`. -/
theorem actual_time_mem_actualHistoryBase [LE Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isActualHistory s.time s'.time) :
    s' ∈ actualHistoryBase history s :=
  ⟨hw, ht⟩

/-- Converse: future time + world agreement → membership in
    `futureHistoryBase`. -/
theorem future_time_mem_futureHistoryBase [LT Time]
    (history : HistoricalAlternatives W Time) (s s' : WorldTimeIndex W Time)
    (hw : s'.world ∈ history s)
    (ht : isFutureHistory s.time s'.time) :
    s' ∈ futureHistoryBase history s :=
  ⟨hw, ht⟩

/-! ## Historical Equivalence

[condoravdi-2002]: historical equivalence `≃_t` groups worlds that share
the same history up to time `t`. The equivalence classes are the "ways things
might have gone" — worlds that agree on the past but may diverge in the future. -/

/-- Historical equivalence: `w'` agrees with `w` up to time `t`.
    `w ≃_t w'` iff `w' ∈ history(w, t)`. -/
def histEquiv (history : HistoricalAlternatives W Time) (t : Time)
    (w w' : W) : Prop :=
  w' ∈ history ⟨w, t⟩

/-- `histEquiv history t` is an equivalence relation when `history` satisfies the
    standard properties ([condoravdi-2002]). -/
def histEquiv_equivalence {history : HistoricalAlternatives W Time}
    (hRefl : history.reflexive) (hSymm : history.symmetric)
    (hTrans : history.transitive) (t : Time) :
    Equivalence (histEquiv history t) where
  refl w := hRefl ⟨w, t⟩
  symm h := hSymm _ _ t h
  trans h₁ h₂ := hTrans _ _ _ t h₁ h₂

/-- The `Setoid` induced by historical equivalence at time `t`. -/
def histSetoid {history : HistoricalAlternatives W Time}
    (hRefl : history.reflexive) (hSymm : history.symmetric)
    (hTrans : history.transitive) (t : Time) : Setoid W where
  r := histEquiv history t
  iseqv := histEquiv_equivalence hRefl hSymm hTrans t

/-- `histEquiv_equivalence` from bundled `HistoricalProperties`. -/
def histEquiv_equivalence' {history : HistoricalAlternatives W Time} [LE Time]
    (hp : HistoricalProperties history) (t : Time) :
    Equivalence (histEquiv history t) :=
  histEquiv_equivalence hp.refl hp.symm hp.trans t

/-- `histSetoid` from bundled `HistoricalProperties`. -/
def histSetoid' {history : HistoricalAlternatives W Time} [LE Time]
    (hp : HistoricalProperties history) (t : Time) : Setoid W :=
  histSetoid hp.refl hp.symm hp.trans t

/-- Historical equivalence is reflexive (from `reflexive`). -/
theorem histEquiv_refl {history : HistoricalAlternatives W Time}
    (hRefl : history.reflexive) (t : Time) (w : W) :
    histEquiv history t w w :=
  hRefl ⟨w, t⟩

/-- Historical equivalence is symmetric (from `symmetric`). -/
theorem histEquiv_symm {history : HistoricalAlternatives W Time}
    (hSymm : history.symmetric) (t : Time) {w w' : W}
    (h : histEquiv history t w w') :
    histEquiv history t w' w :=
  hSymm w w' t h

/-- Historical equivalence is transitive (from `transitive`). -/
theorem histEquiv_trans {history : HistoricalAlternatives W Time}
    (hTrans : history.transitive) (t : Time) {w w' w'' : W}
    (h₁ : histEquiv history t w w')
    (h₂ : histEquiv history t w' w'') :
    histEquiv history t w w'' :=
  hTrans w w' w'' t h₁ h₂

variable [LE Time] in
/-- Historical equivalence is monotone in time: agreement up to a later time
    implies agreement up to an earlier time (from `backwardsClosed`). -/
theorem histEquiv_mono {history : HistoricalAlternatives W Time}
    (hBC : history.backwardsClosed) {t t' : Time} (w w' : W)
    (hle : t' ≤ t) (h : histEquiv history t w w') :
    histEquiv history t' w w' :=
  hBC w w' t t' hle h

variable [LE Time] in
/-- The set of metaphysical alternatives shrinks as time advances
    ([condoravdi-2002]): `t ↦ { w' | w ≃_t w' }` is antitone. -/
theorem alternatives_antitone {history : HistoricalAlternatives W Time}
    (hBC : history.backwardsClosed) (w : W) {t t' : Time}
    (hle : t ≤ t') :
    { w' | histEquiv history t' w w' } ⊆
    { w' | histEquiv history t w w' } :=
  λ _ h => histEquiv_mono hBC w _ hle h

/-! ## Metaphysical Modal Base

[condoravdi-2002]: for modals expressing metaphysical modality, the modal
base consists of historical alternatives `MB(w,t) = {w' | w ≃_t w'}` — the
maximal modal base compatible with the world's history up to `t`. -/

/-- The metaphysical modal base: at world `w` and time `t`, the set of all worlds
    sharing `w`'s history up to `t`. -/
def metaphysicalBase (history : HistoricalAlternatives W Time) :
    W → Time → Set W :=
  λ w t => { w' | histEquiv history t w w' }

variable [LE Time] in
/-- The metaphysical modal base is antitone in time: later times yield smaller
    accessible sets. -/
theorem metaphysicalBase_antitone {history : HistoricalAlternatives W Time}
    (hBC : history.backwardsClosed) (w : W) {t t' : Time}
    (hle : t ≤ t') :
    metaphysicalBase history w t' ⊆ metaphysicalBase history w t :=
  alternatives_antitone hBC w hle

/-! ## Settledness and Diversity

[condoravdi-2002]: an issue is **settled** at time `t₀` when all historically
equivalent worlds agree on its resolution; past and present issues are always
settled, future issues may not be. The **diversity condition** is the felicity
condition for associating a metaphysical modal base with a possibility modal: the
base must contain worlds that disagree on the property. -/

/-- Settledness: within each common-ground equivalence class, the property `P` is
    resolved uniformly — all historically equivalent worlds agree on `P`. -/
def settled (history : HistoricalAlternatives W Time) (cg : Set W)
    (t₀ : Time) (P : W → Prop) : Prop :=
  ∀ w ∈ cg, ∀ w', histEquiv history t₀ w w' → (P w ↔ P w')

/-- Diversity condition: there is a common-ground world whose modal base contains
    worlds disagreeing on `P`. The felicity condition for pairing a metaphysical
    modal base with a possibility modal ([condoravdi-2002]). -/
def diverse (MB : W → Time → Set W) (cg : Set W)
    (t : Time) (P : W → Prop) : Prop :=
  ∃ w ∈ cg, ∃ w' ∈ MB w t, ∃ w'' ∈ MB w t, P w' ∧ ¬ P w''

/-- When `MB(w,t) ⊆ {w' | w ≃_t w'}` (the metaphysical case) and `P` is settled,
    diversity fails: all worlds in the modal base agree on `P`, so no pair can
    witness disagreement. The key theorem blocking metaphysical readings for
    settled properties. -/
theorem settled_not_diverse
    (history : HistoricalAlternatives W Time) (MB : W → Time → Set W)
    (cg : Set W) (t : Time) (P : W → Prop)
    (hMB : ∀ w ∈ cg, ∀ w' ∈ MB w t, histEquiv history t w w')
    (hSettled : settled history cg t P) :
    ¬ diverse MB cg t P := by
  intro ⟨w, hwcg, w', hw'MB, w'', hw''MB, hPw', hnPw''⟩
  have heq' := hSettled w hwcg w' (hMB w hwcg w' hw'MB)
  have heq'' := hSettled w hwcg w'' (hMB w hwcg w'' hw''MB)
  exact hnPw'' (heq''.mp (heq'.mpr hPw'))

/-- Diversity is witnessed by the common ground: if `P` holds for some world in
    `cg` and fails for another, both accessible from some `w` via `MB`, then
    diversity holds. -/
theorem diverse_of_witnesses
    (MB : W → Time → Set W) (cg : Set W) (t : Time) (P : W → Prop)
    (w : W) (hwcg : w ∈ cg)
    (w' w'' : W) (hw' : w' ∈ MB w t) (hw'' : w'' ∈ MB w t)
    (hP : P w') (hnP : ¬ P w'') :
    diverse MB cg t P :=
  ⟨w, hwcg, w', hw', w'', hw'', hP, hnP⟩

/-! ## Grounding in the T × W object logic

A historical-alternatives relation with `HistoricalProperties` satisfies exactly
the axioms of a `Core.Logic.Temporal.TWFrame` — per-time equivalence (via
`histEquiv_equivalence'`) and backward closure — so it *is* a T × W frame. The
object logic's historical necessity `N` then reduces to quantification over
`metaphysicalBase`, making the denotational base and the object-language modality
the same operator ([thomason-1984], [von-kutschera-1997]). -/

section TWFrame
open Core.Logic.Temporal

variable [LinearOrder Time] {Atom : Type*}
  (history : HistoricalAlternatives W Time) (hp : HistoricalProperties history)

/-- A historical-alternatives relation with `HistoricalProperties`, viewed as a
    `TWFrame`: `sim` is `histEquiv`, reusing `histEquiv_equivalence'` for the
    equivalence axiom and `backwards` for backward closure. -/
def toTWFrame : TWFrame Time W where
  sim := histEquiv history
  sim_equiv t := histEquiv_equivalence' hp t
  sim_backward w w' hle h := hp.backwards w w' _ _ hle h

@[simp] theorem toTWFrame_sim (t : Time) (w w' : W) :
    (toTWFrame history hp).sim t w w' ↔ w' ∈ metaphysicalBase history w t := Iff.rfl

/-- Historical necessity `N` in the object logic = truth throughout the
    metaphysical base. -/
theorem toTWFrame_sat_N_atom (V : Atom → Time → W → Prop) (p : Atom) (t : Time) (w : W) :
    (toTWFrame history hp).sat V (.N (.atom p)) t w ↔
      ∀ w' ∈ metaphysicalBase history w t, V p t w' := by
  simp only [TWFrame.sat_N, TWFrame.sat_atom, toTWFrame_sim]

/-- The all-worlds modality `box` = truth in every world (the unrestricted base). -/
theorem toTWFrame_sat_box_atom (V : Atom → Time → W → Prop) (p : Atom) (t : Time) (w : W) :
    (toTWFrame history hp).sat V (.box (.atom p)) t w ↔ ∀ w', V p t w' := by
  simp only [TWFrame.sat_box, TWFrame.sat_atom]

end TWFrame

end HistoricalAlternatives
