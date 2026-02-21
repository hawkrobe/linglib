import Linglib.Core.Intension
import Linglib.Core.Time
import Linglib.Core.Reichenbach
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Unified Tense Pronoun Architecture

Abusch's (1997) insight: a tense morpheme is a **temporal pronoun** — a variable
(Partee 1973) with a presupposed temporal constraint (Prior, reinterpreted) and
a binding mode (indexical/anaphoric/bound). This single concept projects onto
five representations of temporal reference in the codebase:

1. **Priorean operators** (PAST/PRES/FUT): `constraint.constrains`
2. **Reichenbach frames** (S, P, R, E): `TensePronoun.toFrame`
3. **Referential variables** (Partee 1973): `TensePronoun.resolve`
4. **Kaplan indexicals** (rigid to speech time): `mode = .indexical`
5. **Attitude binding** (zero tense, Ogihara 1989): `mode = .bound`

The existing ad-hoc bridge theorems (`referential_past_decomposition`,
`temporallyBound_gives_simultaneous`, `indexical_tense_matches_opNow`,
`ogihara_bound_tense_simultaneous`) become trivial projections from this
unified type.

## Architecture

This module lives in `Core/` because both `Theories/Semantics.Montague/Sentence/Tense/`
and `Theories/Semantics.Intensional/Attitude/` need the shared infrastructure
(`GramTense`, `SOTParameter`, `TemporalAssignment`, etc.) without a cross-tree
import.

## References

- Partee, B. (1973). Some structural analogies between tenses and pronouns.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope. Kluwer.
- Abusch, D. (1997). Sequence of tense and temporal de re.
- Von Stechow, A. (2009). Tenses in compositional semantics.
-/

namespace Core.Tense

open Core.Time
open Core.Reichenbach
open Core.ReferentialMode (ReferentialMode)
open Core.VarAssignment (VarAssignment updateVar lookupVar varLambdaAbs
  update_lookup_same)


-- ════════════════════════════════════════════════════════════════
-- § GramTense
-- ════════════════════════════════════════════════════════════════

/--
Grammatical tense: a temporal relation imposed by tense morphology.

Following the Reichenbach/Klein tradition:
- PAST: reference time before speech time
- PRESENT: reference time overlaps speech time
- FUTURE: reference time after speech time
-/
inductive GramTense where
  | past
  | present
  | future
  deriving DecidableEq, Repr, BEq, Inhabited

namespace GramTense

/-- Convert tense to its corresponding temporal relation -/
def toRelation : GramTense → TemporalRelation
  | .past => .before
  | .present => .overlapping
  | .future => .after

/-- The inverse relation (for "backwards" reference) -/
def inverseRelation : GramTense → TemporalRelation
  | .past => .after
  | .present => .overlapping
  | .future => .before

/-- The temporal constraint imposed by a grammatical tense.
    Past: ref < perspective. Present: ref = perspective. Future: ref > perspective.
    This is the core ordering that Priorean operators assert and
    Abusch's tense pronouns presuppose. -/
def constrains {Time : Type*} [LinearOrder Time]
    (t : GramTense) (refTime perspTime : Time) : Prop :=
  match t with
  | .past => refTime < perspTime
  | .present => refTime = perspTime
  | .future => refTime > perspTime

end GramTense


-- ════════════════════════════════════════════════════════════════
-- § SOTParameter
-- ════════════════════════════════════════════════════════════════

/--
Sequence of Tenses (SOT) parameter.

Languages differ in how embedded tense interacts with matrix tense:
- **SOT languages** (English): Embedded tense is relative to matrix
- **Non-SOT languages** (Japanese): Embedded tense is absolute
-/
inductive SOTParameter where
  | relative  -- English: embedded tense relative to matrix
  | absolute  -- Japanese: embedded tense absolute (to utterance time)
  deriving DecidableEq, Repr, BEq


-- ════════════════════════════════════════════════════════════════
-- § TenseInterpretation
-- ════════════════════════════════════════════════════════════════

/-- Tense interpretation modes (Partee 1973, Kratzer 1998).
    Tenses parallel pronouns: indexical (deictic), anaphoric
    (discourse-bound), and bound variable (zero tense).

    This is an alias for `Core.ReferentialMode.ReferentialMode`,
    which captures Partee's insight that the same three-way classification
    applies to both pronouns and tenses. -/
abbrev TenseInterpretation := Core.ReferentialMode.ReferentialMode

/-- Bound (zero) tense is the SOT mechanism: it must be locally bound,
    yielding the simultaneous reading without a deletion rule. -/
theorem bound_is_sot_mechanism :
    ReferentialMode.bound ≠ ReferentialMode.indexical ∧
    ReferentialMode.bound ≠ ReferentialMode.anaphoric := ⟨nofun, nofun⟩


-- ════════════════════════════════════════════════════════════════
-- § Temporal Variable Infrastructure (Partee 1973)
-- ════════════════════════════════════════════════════════════════

/-! Temporal assignment functions are the temporal instantiation of
`Core.VarAssignment` (`VarAssignment Time = ℕ → Time`). All algebraic
properties (update_lookup_same, update_lookup_other, update_update_same,
update_self) are inherited from the generic infrastructure. -/

/-- Temporal assignment function: maps variable indices to times.
    The temporal analogue of H&K's `Assignment` (`ℕ → Entity`).
    Defined as `VarAssignment Time` from `Core.VarAssignment`. -/
abbrev TemporalAssignment (Time : Type*) := VarAssignment Time

/-- Modified temporal assignment g[n ↦ t].
    Specializes `Core.VarAssignment.updateVar`. -/
abbrev updateTemporal {Time : Type*} (g : TemporalAssignment Time)
    (n : ℕ) (t : Time) : TemporalAssignment Time :=
  updateVar g n t

/-- Temporal variable denotation: ⟦tₙ⟧^g = g(n).
    Specializes `Core.VarAssignment.lookupVar`. -/
abbrev interpTense {Time : Type*} (n : ℕ) (g : TemporalAssignment Time) : Time :=
  lookupVar n g

/-- Temporal lambda abstraction: bind a time variable.
    Specializes `Core.VarAssignment.varLambdaAbs`.

    Partee's bound tense: "Whenever Mary phones, Sam *is* asleep" —
    present tense bound by "whenever", just as "Every farmer beats
    *his* donkey" has "his" bound by "every farmer". -/
abbrev temporalLambdaAbs {Time α : Type*} (n : ℕ)
    (body : TemporalAssignment Time → α) :
    TemporalAssignment Time → Time → α :=
  varLambdaAbs n body

/-- Project a situation assignment to a temporal assignment (Kratzer 1998).
    This is the formal bridge between situation semantics and tense semantics:
    the temporal coordinate of each situation is extracted. -/
def situationToTemporal {W Time : Type*}
    (g : ℕ → Situation W Time) : TemporalAssignment Time :=
  λ n => (g n).time

/-- Temporal interpretation via situation assignment commutes with
    time projection: `interpTense n (π g) = (g n).time`. -/
theorem situation_temporal_commutes {W Time : Type*}
    (g : ℕ → Situation W Time) (n : ℕ) :
    interpTense n (situationToTemporal g) = (g n).time := rfl

/-- Zero tense (Ogihara 1989): a bound tense variable contributes no independent
    temporal constraint. When an attitude verb binds it, the variable receives
    the matrix event time. This is the SOT mechanism: the "past" morphology on
    the embedded verb is agreement, not a semantic tense. -/
theorem zeroTense_receives_binder_time {Time : Type*}
    (g : TemporalAssignment Time) (n : ℕ) (binderTime : Time) :
    interpTense n (updateTemporal g n binderTime) = binderTime :=
  update_lookup_same g n binderTime


-- ════════════════════════════════════════════════════════════════
-- § SitProp (Prop-valued)
-- ════════════════════════════════════════════════════════════════

/--
Type of situation-level propositions (Prop-valued, for proof-level temporal reasoning).

A temporal predicate takes a situation and returns truth value.
This is what tense operators modify.

Note: a Bool-valued counterpart exists at
`Semantics.Attitudes.SituationDependent.SitProp` for
computational RSA evaluation. The split follows the `Prop'`/`BProp`
pattern in `Core/Proposition.lean`.
-/
abbrev SitProp (W Time : Type*) := Situation W Time → Prop


-- ════════════════════════════════════════════════════════════════
-- § TensePronoun (Abusch 1997)
-- ════════════════════════════════════════════════════════════════

/-- Abusch's (1997) unified tense denotation.

    A tense morpheme introduces a temporal variable (Partee 1973) with:
    - A variable index in the temporal assignment
    - A presupposed temporal constraint (past/present/future)
    - A binding mode (indexical, anaphoric, or bound)

    This unifies five views of tense:
    - **Priorean**: `constraint.constrains` (temporal ordering)
    - **Reichenbach**: `resolve g` = R, perspective time = P
    - **Referential**: `resolve g = interpTense varIndex g`
    - **Kaplan indexical**: `mode = .indexical` → rigid to speech time
    - **Attitude binding**: `mode = .bound` → zero tense -/
structure TensePronoun where
  varIndex : ℕ
  constraint : GramTense
  mode : TenseInterpretation
  /-- Index of the evaluation time variable in the temporal assignment.
      Default 0 = speech time slot. Under embedding, attitude verbs update
      this index to point at the matrix event time (Von Stechow 2009).
      Klecha (2016): modals can also shift the eval time index. -/
  evalTimeIndex : ℕ := 0
  deriving DecidableEq, Repr, BEq

namespace TensePronoun

/-- Resolve: look up the temporal variable. -/
def resolve {Time : Type*} (tp : TensePronoun)
    (g : TemporalAssignment Time) : Time :=
  interpTense tp.varIndex g

/-- Presupposition: the constraint applied to the resolved time. -/
def presupposition {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (resolvedTime perspectiveTime : Time) : Prop :=
  tp.constraint.constrains resolvedTime perspectiveTime

/-- Construct the Reichenbach frame. R = g(varIndex), P = perspectiveTime. -/
def toFrame {Time : Type*} (tp : TensePronoun)
    (g : TemporalAssignment Time)
    (speechTime perspectiveTime eventTime : Time) :
    ReichenbachFrame Time where
  speechTime := speechTime
  perspectiveTime := perspectiveTime
  referenceTime := tp.resolve g
  eventTime := eventTime

def isIndexical (tp : TensePronoun) : Bool := tp.mode == .indexical
def isBound (tp : TensePronoun) : Bool := tp.mode == .bound

end TensePronoun


-- ════════════════════════════════════════════════════════════════
-- § TensePronoun Bridge Theorems
-- ════════════════════════════════════════════════════════════════

/-- Resolve the evaluation time from the assignment.
    In root clauses (evalTimeIndex = 0, g(0) = speech time), this is speech time.
    Under embedding, the attitude verb updates the assignment so that
    g(evalTimeIndex) = matrix event time. -/
def TensePronoun.evalTime {Time : Type*} (tp : TensePronoun)
    (g : TemporalAssignment Time) : Time :=
  interpTense tp.evalTimeIndex g

/-- Full presupposition: the tense constraint checked against the resolved
    evaluation time (not just a bare perspective time parameter).
    This makes the eval time compositionally determined rather than stipulated. -/
def TensePronoun.fullPresupposition {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) : Prop :=
  tp.constraint.constrains (tp.resolve g) (tp.evalTime g)

/-- When evalTimeIndex = 0 and g(0) = speechTime, the evaluation time is speech time.
    This is the root-clause default: tense is checked against speech time. -/
theorem evalTime_root_is_speech {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time) (speechTime : Time)
    (hEval : tp.evalTimeIndex = 0) (hRoot : g 0 = speechTime) :
    tp.evalTime g = speechTime := by
  simp [TensePronoun.evalTime, interpTense, lookupVar, hEval, hRoot]

/-- Updating the eval time index gives Von Stechow's perspective shift:
    the embedded tense is now checked against a different time (the matrix
    event time). This is how attitude verbs "transmit" their event time. -/
theorem evalTime_shifts_under_embedding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time) (matrixEventTime : Time) :
    tp.evalTime (updateTemporal g tp.evalTimeIndex matrixEventTime) = matrixEventTime :=
  update_lookup_same g tp.evalTimeIndex matrixEventTime

/-- Resolving a bound tense under binding yields the binder time. -/
theorem TensePronoun.bound_resolve_eq_binder {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time) (binderTime : Time) :
    tp.resolve (updateTemporal g tp.varIndex binderTime) = binderTime :=
  zeroTense_receives_binder_time g tp.varIndex binderTime

/-- A present-constraint bound tense under binding gives R = P (simultaneous).
    The `hPres` hypothesis constrains the theorem to present tenses; the
    frame equality follows from `hBind` alone (R = resolve = perspTime). -/
theorem TensePronoun.bound_present_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (speechTime perspTime eventTime : Time)
    (hBind : tp.resolve g = perspTime)
    (_hPres : tp.constraint = .present) :
    (tp.toFrame g speechTime perspTime eventTime).isPresent := by
  simp only [TensePronoun.toFrame, ReichenbachFrame.isPresent]
  exact hBind

/-- Double-access (Abusch 1997): present-under-past requires the complement
    to hold at BOTH speech time (indexical rigidity) AND matrix event time
    (attitude accessibility). -/
def doubleAccess {Time : Type*} (p : Time → Prop)
    (speechTime matrixEventTime : Time) : Prop :=
  p speechTime ∧ p matrixEventTime

/-- An indexical present tense presupposes resolution to speech time. -/
theorem TensePronoun.indexical_present_at_speech {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (resolvedTime speechTime : Time)
    (hPres : tp.constraint = .present)
    (hPresup : tp.presupposition resolvedTime speechTime) :
    resolvedTime = speechTime := by
  simp [TensePronoun.presupposition, GramTense.constrains, hPres] at hPresup
  exact hPresup


-- ════════════════════════════════════════════════════════════════
-- § Overtness (Kratzer 1998)
-- ════════════════════════════════════════════════════════════════

/-- Phonological overtness of a referential expression (Kratzer 1998 §3).

    Applies uniformly to pronouns and tenses: English has zero tense
    under SOT (bound present surfaces as ∅); Japanese has zero pronouns
    in subject position (locally bound by Agr). Persian has zero pronouns
    but NOT zero tense (tense is in C, outside the local agreement domain).

    The distribution of overt vs. zero is governed by locality of agreement:
    a referential expression that is locally bound by an agreeing head
    surfaces as zero. -/
inductive Overtness where
  | overt  -- Phonologically realized (English "he", German Preterit -te)
  | zero   -- Phonologically empty (zero tense under SOT, pro-drop subjects)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Kratzer's locality generalization (1998, formula 26):

    A referential expression that is locally bound by an agreeing head
    surfaces as zero. Free (indexical or anaphoric) expressions surface
    as overt. This unifies:
    - Reflexives = locally bound entity pronouns → zero/reduced
    - Simultaneous tense = locally bound temporal pronoun → zero under SOT
    - Japanese subject pro = locally bound by Agr → zero
    - Persian pronouns = locally bound by Agr → zero, but tense is NOT
      local to Agr (tense is in C) → overt -/
def Overtness.fromBinding : ReferentialMode → (localDomain : Bool) → Overtness
  | .bound, true => .zero
  | _, _ => .overt

/-- Free (indexical or anaphoric) expressions are always overt. -/
theorem Overtness.free_always_overt (m : ReferentialMode) (l : Bool)
    (hFree : m.isFree = true) :
    Overtness.fromBinding m l = .overt := by
  cases m <;> simp_all [Overtness.fromBinding, ReferentialMode.isFree]

/-- Bound expressions in a local domain are zero. -/
theorem Overtness.bound_local_is_zero :
    Overtness.fromBinding .bound true = .zero := rfl

/-- Bound expressions outside the local domain remain overt.
    This is the Persian case: tense is bound but not in a local
    agreement domain (tense is in C, Agr is in Infl). -/
theorem Overtness.bound_nonlocal_is_overt :
    Overtness.fromBinding .bound false = .overt := rfl


-- ════════════════════════════════════════════════════════════════
-- § Temporal Tower Bridge (Abusch 1997 ↔ ContextTower)
-- ════════════════════════════════════════════════════════════════

/-! The key bridge showing that Abusch's (1997) De Bruijn temporal indexing is already
tower-style depth access. `TensePronoun.evalTimeIndex` is a depth-relative index
into the tower: when the temporal assignment encodes tower time coordinates
(`g k = (tower.contextAt k).time`), `interpTense` agrees with `AccessPattern.resolve`.

- `tensePronounAccessPattern` — converts `TensePronoun.evalTimeIndex` to an
  `AccessPattern` with `depth := .relative tp.evalTimeIndex`
- `tense_tower_bridge` — when `g` encodes tower time coordinates, `interpTense`
  agrees with `AccessPattern.resolve`
- `tense_root_bridge` — root clause: `evalTimeIndex = 0` means origin time
- `von_stechow_tower` — pushing a temporal shift = Von Stechow's perspective shift -/

section TemporalBridge

open Core.Context (KContext ContextTower ContextShift AccessPattern DepthSpec
  temporalShift)

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- Convert a `TensePronoun`'s eval-time index to an `AccessPattern` that reads
    the time coordinate at the corresponding tower depth.

    `evalTimeIndex = 0` → origin (speech-act context time)
    `evalTimeIndex = k` → depth k (the k-th embedding's time)

    This makes explicit the observation that Abusch's variable indices ARE
    tower depth indices for the temporal coordinate. -/
def tensePronounAccessPattern (tp : TensePronoun) :
    AccessPattern (KContext W E P T) T where
  depth := .relative tp.evalTimeIndex
  project := KContext.time

/-- A temporal assignment that faithfully represents a tower: `g k` returns
    the time coordinate at tower depth `k`. This is the bridge condition
    connecting the variable-assignment world to the tower world. -/
def towerFaithful (g : TemporalAssignment T) (t : ContextTower (KContext W E P T)) : Prop :=
  ∀ (k : ℕ), g k = (t.contextAt k).time

/-- When the temporal assignment encodes tower time coordinates,
    `interpTense` at the eval-time index agrees with resolving
    the `tensePronounAccessPattern` against the tower.

    This is the central result: Abusch's De Bruijn indexing IS
    tower-depth access for the temporal coordinate. -/
theorem tense_tower_bridge
    (tp : TensePronoun) (g : TemporalAssignment T)
    (t : ContextTower (KContext W E P T))
    (hFaithful : towerFaithful (W := W) (E := E) (P := P) g t) :
    tp.evalTime g = (tensePronounAccessPattern (W := W) (E := E) (P := P) tp).resolve t := by
  simp only [TensePronoun.evalTime, interpTense, Core.VarAssignment.lookupVar,
             tensePronounAccessPattern, AccessPattern.resolve,
             DepthSpec.relative_resolve]
  exact hFaithful tp.evalTimeIndex

/-- In a root tower (no shifts), `evalTimeIndex = 0` accesses the origin time.
    This is the root-clause default: tense is checked against speech time.

    Combined with `evalTime_root_is_speech`, this shows that root-clause
    temporal evaluation is origin access — exactly Kaplan's thesis for time. -/
theorem tense_root_bridge
    (tp : TensePronoun) (c : KContext W E P T)
    (hEval : tp.evalTimeIndex = 0)
    (g : TemporalAssignment T)
    (hFaithful : towerFaithful (W := W) (E := E) (P := P) g (ContextTower.root c)) :
    tp.evalTime g = c.time := by
  have h1 := hFaithful 0
  simp only [ContextTower.root_contextAt] at h1
  simp only [TensePronoun.evalTime, interpTense, Core.VarAssignment.lookupVar, hEval]
  exact h1

/-- The access pattern for a root-clause tense pronoun (evalTimeIndex = 0)
    resolves to depth 0, which is the origin. -/
theorem tensePronounAccessPattern_root_resolves
    (tp : TensePronoun) (hEval : tp.evalTimeIndex = 0)
    (c : KContext W E P T) :
    (tensePronounAccessPattern (W := W) (E := E) (P := P) tp).resolve
      (ContextTower.root c) = c.time := by
  simp only [tensePronounAccessPattern, AccessPattern.resolve, hEval,
             DepthSpec.relative_resolve, ContextTower.root_contextAt]

/-- Von Stechow's (2009) perspective shift — the attitude verb transmits
    its event time to the embedded clause — corresponds to pushing a
    `temporalShift` onto the tower.

    Concretely: the updated assignment at the tower depth yields the new time. -/
theorem von_stechow_tower
    (g : TemporalAssignment T) (t : ContextTower (KContext W E P T))
    (newTime : T) :
    updateTemporal g t.depth newTime t.depth = newTime :=
  Core.VarAssignment.update_lookup_same g t.depth newTime

/-- Under faithful encoding, layers below the push point are preserved. -/
theorem von_stechow_tower_preserves
    (g : TemporalAssignment T) (t : ContextTower (KContext W E P T))
    (newTime : T)
    (hFaithful : towerFaithful g t)
    (k : ℕ) (hk : k < t.depth) :
    updateTemporal g t.depth newTime k = (t.contextAt k).time := by
  simp only [updateTemporal, Core.VarAssignment.updateVar]
  rw [if_neg (Nat.ne_of_lt hk)]
  exact hFaithful k

/-- Pushing a temporal shift assigns `newTime` to the new depth in
    the extended tower, mirroring `von_stechow_tower` on the assignment side. -/
theorem von_stechow_tower_innermost
    (t : ContextTower (KContext W E P T)) (newTime : T) :
    (t.push (temporalShift newTime)).innermost.time = newTime := by
  rw [ContextTower.push_innermost]
  simp only [temporalShift]

end TemporalBridge

end Core.Tense
