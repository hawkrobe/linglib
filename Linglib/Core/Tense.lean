import Linglib.Core.Intension
import Linglib.Core.Time
import Linglib.Core.Reichenbach

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


end Core.Tense
