import Linglib.Semantics.Tense.Embedding
import Linglib.Semantics.Tense.Pronoun
import Linglib.Semantics.Reference.Context.Tower
import Linglib.Semantics.Reference.Context.Shifts
import Linglib.Semantics.Attitudes.Doxastic

/-!
# von Stechow 2009: tenses in compositional semantics

[von-stechow-2009]'s theory: tense features are checked against a
local evaluation time that shifts under attitude embedding. The key
mechanism is **feature checking**: tense morphology bears a feature
([PAST], [PRES]) that must be checked against the local temporal
anchor.

## Core Mechanisms

1. **Feature checking** = `Core.Order.holds` (substrate primitive
   in `Core/Time/Tense.lean`). The "checking" terminology is von
   Stechow's; the underlying predicate is the framework-neutral
   `Core.Order.holds feature refTime evalTime`.
2. **Perspective shift** = `embeddedFrame` (substrate primitive in
   `Semantics/Tense/Embedding.lean`). The attitude verb sets the
   embedded eval time = matrix E. von Stechow calls this "perspective
   shift"; the operation is the framework-neutral `embeddedFrame
   matrixFrame embeddedR embeddedE`.
3. **SOT as feature checking**: simultaneous reading = [PRES] checked
   against matrix E (no deletion, no ambiguity).

The paper's second contribution is the situation-indexed attitude
semantics it synthesizes from [lewis-1979-attitudes],
[heim-kratzer-1998], and [ogihara-1989]: *believe*'s complement type
shifts from propositions to situation-dependent propositions
(`SitProp`), and the doxastic alternatives become world–time pairs.
`sitBoxAt` is the universal modal over situations, with Hintikka
world-only semantics the time-invariant special case
(`sitBoxAt_lift_eq_BoxAt`); genuinely temporal accessibility
constraints (`temporallyBound`, `futureOriented`) are what tie
embedded tense to the matrix event time in sequence of tense.

## Advantages Over Abusch

- Handles relative clause tense: feature checking works in relative
  clauses where the perspective time is the modified NP's temporal
  coordinate, not the matrix event time.
- Cleaner compositional architecture: no res movement needed.

-/

open Time

namespace VonStechow2009

open Tense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- [von-stechow-2009] derives the shifted reading: [PAST] feature
    checked against matrix E. The embedded reference time is before
    the matrix event time. -/
theorem vonStechow_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : Core.Order.holds Tense.past embeddedR matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

/-- [von-stechow-2009] derives the simultaneous reading: [PRES]
    feature checked against matrix E. The embedded reference time
    equals the matrix event time — no deletion rule needed. -/
theorem vonStechow_derives_simultaneous {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (embeddedFrame matrixFrame matrixFrame.eventTime embeddedE).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent]

/-- [von-stechow-2009] derives double-access: [PRES] feature under
    past attitude verb. The present tense is checked against matrix E,
    but its indexical nature also requires truth at speech time. -/
theorem vonStechow_derives_double_access {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (p : Time → Prop)
    (h_matrix : p matrixFrame.eventTime)
    (h_speech : p matrixFrame.speechTime) :
    p matrixFrame.eventTime ∧ p matrixFrame.speechTime :=
  ⟨h_matrix, h_speech⟩

/-- [von-stechow-2009] derives relative clause tense: the
    perspective time in a relative clause is the modified NP's
    temporal coordinate, not necessarily the matrix event time.
    Feature checking works uniformly regardless of the source of the
    eval time.

    This is where von Stechow has an advantage over [abusch-1997]:
    feature checking does not require attitude semantics or res
    movement — any eval time source works. -/
theorem vonStechow_derives_relative_clause {Time : Type*} [LinearOrder Time]
    (rcPerspective : Time) (rcRefTime : Time)
    (hPast : Core.Order.holds Tense.past rcRefTime rcPerspective) :
    rcRefTime < rcPerspective :=
  (Core.Order.holds_before _ _).mp hPast


-- ════════════════════════════════════════════════════════════════
-- § Bridge to TensePronoun
-- ════════════════════════════════════════════════════════════════

/-- [von-stechow-2009]'s feature checking is
    `TensePronoun.fullPresupposition` when the eval time resolves to
    the same value. -/
theorem feature_checking_is_fullPresupposition {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) :
    Core.Order.holds tp.constraint (tp.resolve g) (tp.evalTime g) ↔
    tp.fullPresupposition g :=
  Iff.rfl


/-! ### Situation-indexed attitudes

The complement type of *believe* shifts from `W → Prop` to
`SitProp W Time`, and doxastic alternatives become world–time pairs:
⟦x believes p⟧(w,t) = ∀(w',t') ∈ Dox_x(w,t). p(w',t'). -/

open Intensional (WorldTimeIndex SitProp)
open Doxastic (Veridicality DoxasticPredicate BoxAt VeridicalityHolds)

variable {W Time E : Type*}

/-- Universal modal over situations: `p` holds at every accessible
    world–time pair. -/
def sitBoxAt (R : E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (agent : E) (s : WorldTimeIndex W Time)
    (situations : List (WorldTimeIndex W Time)) (p : SitProp W Time) : Prop :=
  ∀ s' ∈ situations, R agent s s' → p s'

instance (R : E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    [∀ a s s', Decidable (R a s s')] (agent : E) (s : WorldTimeIndex W Time)
    (situations : List (WorldTimeIndex W Time)) (p : SitProp W Time)
    [DecidablePred p] : Decidable (sitBoxAt R agent s situations p) :=
  inferInstanceAs (Decidable (∀ s' ∈ situations, _))

/-- A world-proposition as a situation-proposition ignoring the
    temporal coordinate. -/
def liftProp (p : W → Prop) : SitProp W Time :=
  fun s => p s.world

/-- A world-accessibility relation as a situation-accessibility
    relation ignoring temporal coordinates — classic Hintikka
    behavior, where doxastic alternatives differ only in world. -/
def liftAccess (R : E → W → W → Prop) :
    E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop :=
  fun agent s₁ s₂ => R agent s₁.world s₂.world

/-- Hintikka semantics is the time-invariant special case: on lifted
    relations and propositions, the situation modal is `BoxAt` over
    the world projections. -/
theorem sitBoxAt_lift_eq_BoxAt (R : E → W → W → Prop) (agent : E)
    (s : WorldTimeIndex W Time) (sits : List (WorldTimeIndex W Time))
    (p : W → Prop) :
    sitBoxAt (liftAccess R) agent s sits (liftProp p) ↔
    BoxAt R agent s.world (sits.map (·.world)) p := by
  simp only [sitBoxAt, BoxAt, liftAccess, liftProp, List.mem_map]
  constructor
  · intro h w' ⟨s', hs', heq⟩ hR
    exact heq ▸ h s' hs' (heq ▸ hR)
  · intro h s' hs' hR
    exact h s'.world ⟨s', hs', rfl⟩ hR

/-- The veridicality check at a situation: veridical predicates
    require the complement at the evaluation situation. -/
def sitVeridicalityHolds (v : Veridicality) (p : SitProp W Time)
    (s : WorldTimeIndex W Time) : Prop :=
  match v with
  | .veridical => p s
  | .nonVeridical => True

instance (v : Veridicality) (p : SitProp W Time) [DecidablePred p]
    (s : WorldTimeIndex W Time) :
    Decidable (sitVeridicalityHolds v p s) := by
  cases v <;> simp [sitVeridicalityHolds] <;> infer_instance

/-- Lifted veridicality is world-level veridicality. -/
theorem sitVeridicalityHolds_lift (v : Veridicality) (p : W → Prop)
    (s : WorldTimeIndex W Time) :
    sitVeridicalityHolds v (liftProp p) s ↔ VeridicalityHolds v p s.world := by
  cases v <;> simp [sitVeridicalityHolds, VeridicalityHolds, liftProp]

/-- A doxastic predicate with situation-indexed accessibility:
    `Dox_y(w,t)` is a set of world–time pairs. -/
structure SitDoxasticPredicate (W Time E : Type*) where
  /-- Situation-indexed accessibility relation. -/
  access : E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop
  /-- Veridicality (veridical or not). -/
  veridicality : Veridicality

/-- ⟦x V that p⟧(s): the veridicality check at `s` plus the universal
    modal over accessible situations. -/
def SitDoxasticPredicate.HoldsAt (V : SitDoxasticPredicate W Time E)
    (agent : E) (p : SitProp W Time) (s : WorldTimeIndex W Time)
    (situations : List (WorldTimeIndex W Time)) : Prop :=
  sitVeridicalityHolds V.veridicality p s ∧ sitBoxAt V.access agent s situations p

/-- Veridical situation-indexed predicates entail their complement at
    the evaluation situation. -/
theorem sit_veridical_entails_complement (V : SitDoxasticPredicate W Time E)
    (hV : V.veridicality = .veridical) (agent : E) (p : SitProp W Time)
    (s : WorldTimeIndex W Time) (sits : List (WorldTimeIndex W Time))
    (holds : V.HoldsAt agent p s sits) : p s := by
  unfold SitDoxasticPredicate.HoldsAt at holds
  rw [hV] at holds
  exact holds.1

/-- A world-level `DoxasticPredicate` as a situation-indexed one, with
    time-invariant accessibility. -/
def liftDoxastic (V : DoxasticPredicate W E) (Time : Type*) :
    SitDoxasticPredicate W Time E where
  access := liftAccess V.access
  veridicality := V.veridicality

/-- The lifted predicate has exactly the world-level semantics — any
    `DoxasticPredicate` analysis replays unchanged in the
    situation-indexed framework. -/
theorem liftDoxastic_holdsAt_iff (V : DoxasticPredicate W E) (agent : E)
    (p : W → Prop) (s : WorldTimeIndex W Time)
    (sits : List (WorldTimeIndex W Time)) :
    (liftDoxastic V Time).HoldsAt agent (liftProp p) s sits ↔
    V.HoldsAt agent p s.world (sits.map (·.world)) := by
  simp only [SitDoxasticPredicate.HoldsAt, DoxasticPredicate.HoldsAt,
    liftDoxastic, sitVeridicalityHolds_lift, sitBoxAt_lift_eq_BoxAt]

/-! ### Temporal accessibility constraints

What makes the situation indexing do work beyond the lift: relations
that genuinely constrain the temporal coordinate, tying the embedded
clause's temporal interpretation to the matrix event time. -/

/-- Accessible situations share the evaluation time — the
    simultaneous reading in sequence of tense. -/
def temporallyBound (R : E → W → W → Prop) :
    E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop :=
  fun agent s₁ s₂ => R agent s₁.world s₂.world ∧ s₂.time = s₁.time

instance [DecidableEq Time] (R : E → W → W → Prop)
    [∀ a w w', Decidable (R a w w')] :
    ∀ a s₁ s₂, Decidable (temporallyBound (Time := Time) R a s₁ s₂) := by
  intro a s₁ s₂; unfold temporallyBound; infer_instance

/-- Accessible situations are at or after the evaluation time —
    forward-looking attitudes like *expect* and *intend*. -/
def futureOriented [LE Time] (R : E → W → W → Prop) :
    E → WorldTimeIndex W Time → WorldTimeIndex W Time → Prop :=
  fun agent s₁ s₂ => R agent s₁.world s₂.world ∧ s₁.time ≤ s₂.time

instance [LE Time] [DecidableRel (α := Time) (· ≤ ·)]
    (R : E → W → W → Prop) [∀ a w w', Decidable (R a w w')] :
    ∀ a s₁ s₂, Decidable (futureOriented (Time := Time) R a s₁ s₂) := by
  intro a s₁ s₂; unfold futureOriented; infer_instance

/-! ### Temporal tower bridge ([abusch-1997] ↔ `ContextTower`)

[abusch-1997]'s De Bruijn temporal indexing is tower-style depth access:
`TensePronoun.evalTimeIndex` is a depth-relative index into the tower —
when the temporal assignment encodes tower time coordinates
(`g k = (tower.contextAt k).time`), `interpTense` agrees with
`AccessPattern.resolve` — and the perspective shift of this paper is
pushing a `temporalShift` onto the tower. -/

section TemporalBridge

open Semantics.Context (KContext ContextTower ContextShift AccessPattern DepthSpec
  temporalShift)

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- Convert a `TensePronoun`'s eval-time index to an `AccessPattern` that reads
    the time coordinate at the corresponding tower depth: `evalTimeIndex = 0`
    is the origin (speech-act context time), `evalTimeIndex = k` the k-th
    embedding's time. Abusch's variable indices ARE tower depth indices for
    the temporal coordinate. -/
def tensePronounAccessPattern (tp : TensePronoun) :
    AccessPattern (KContext W E P T) T where
  depth := .relative tp.evalTimeIndex
  project := KContext.time

/-- A temporal assignment that faithfully represents a tower: `g k` returns
    the time coordinate at tower depth `k`. -/
def towerFaithful (g : TemporalAssignment T) (t : ContextTower (KContext W E P T)) : Prop :=
  ∀ (k : ℕ), g k = (t.contextAt k).time

/-- When the temporal assignment encodes tower time coordinates,
    `interpTense` at the eval-time index agrees with resolving
    the `tensePronounAccessPattern` against the tower. -/
theorem tense_tower_bridge
    (tp : TensePronoun) (g : TemporalAssignment T)
    (t : ContextTower (KContext W E P T))
    (hFaithful : towerFaithful (W := W) (E := E) (P := P) g t) :
    tp.evalTime g = (tensePronounAccessPattern (W := W) (E := E) (P := P) tp).resolve t := by
  simp only [TensePronoun.evalTime, interpTense,
             tensePronounAccessPattern, AccessPattern.resolve,
             DepthSpec.relative_resolve]
  exact hFaithful tp.evalTimeIndex

/-- In a root tower (no shifts), `evalTimeIndex = 0` accesses the origin
    time — root-clause temporal evaluation is origin access, Kaplan's
    thesis for time. -/
theorem tense_root_bridge
    (tp : TensePronoun) (c : KContext W E P T)
    (hEval : tp.evalTimeIndex = 0)
    (g : TemporalAssignment T)
    (hFaithful : towerFaithful (W := W) (E := E) (P := P) g (ContextTower.root c)) :
    tp.evalTime g = c.time := by
  have h1 := hFaithful 0
  simp only [ContextTower.root_contextAt] at h1
  simp only [TensePronoun.evalTime, interpTense, hEval]
  exact h1

/-- The access pattern for a root-clause tense pronoun (evalTimeIndex = 0)
    resolves to depth 0, the origin. -/
theorem tensePronounAccessPattern_root_resolves
    (tp : TensePronoun) (hEval : tp.evalTimeIndex = 0)
    (c : KContext W E P T) :
    (tensePronounAccessPattern (W := W) (E := E) (P := P) tp).resolve
      (ContextTower.root c) = c.time := by
  simp only [tensePronounAccessPattern, AccessPattern.resolve, hEval,
             DepthSpec.relative_resolve, ContextTower.root_contextAt]

/-- [von-stechow-2009]'s perspective shift — the attitude verb transmits
    its event time to the embedded clause — as pushing a `temporalShift`
    onto the tower: the updated assignment at the tower depth yields the
    new time. -/
theorem von_stechow_tower
    (g : TemporalAssignment T) (t : ContextTower (KContext W E P T))
    (newTime : T) :
    updateTemporal g t.depth newTime t.depth = newTime :=
  Function.update_self t.depth newTime g

/-- Under faithful encoding, layers below the push point are preserved. -/
theorem von_stechow_tower_preserves
    (g : TemporalAssignment T) (t : ContextTower (KContext W E P T))
    (newTime : T)
    (hFaithful : towerFaithful g t)
    (k : ℕ) (hk : k < t.depth) :
    updateTemporal g t.depth newTime k = (t.contextAt k).time := by
  simp only [updateTemporal]
  rw [Function.update_of_ne (Nat.ne_of_lt hk)]
  exact hFaithful k

/-- Pushing a temporal shift assigns `newTime` to the new depth in
    the extended tower, mirroring `von_stechow_tower` on the assignment side. -/
theorem von_stechow_tower_innermost
    (t : ContextTower (KContext W E P T)) (newTime : T) :
    (t.push (temporalShift newTime)).innermost.time = newTime := by
  rw [ContextTower.push_innermost]
  simp only [temporalShift]

end TemporalBridge

end VonStechow2009
