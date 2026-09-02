import Linglib.Semantics.Reference.Rigidity
import Linglib.Logic.Assignment
import Linglib.Semantics.Reference.Context.Index
import Linglib.Semantics.Tense.Defs

/-!
# Tense pronouns
[abusch-1997] [heim-1994-comments] [kratzer-1998] [partee-1973]

[partee-1973]'s insight: a tense morpheme is a **temporal pronoun** — a
variable with a temporal constraint and a binding mode
(indexical/anaphoric/bound). `TensePronoun` carries the four ingredients
(variable index, comparison-cell constraint, `ReferentialMode`, evaluation
index); the constraint-as-presupposition formulation
(`fullPresupposition`) follows [heim-1994-comments] (commenting on
[abusch-1997]) and [kratzer-1998]. The assignment infrastructure is the
temporal instantiation of `Assignment`; all update laws are mathlib's
`Function.update` lemmas.
-/

open Semantics.Context (Index)

namespace Tense

/-- [partee-1973]'s three-way interpretive classification of a referential expression,
uniform across pronouns (entity variables) and tenses (temporal variables): anchored to the
utterance context (*I*, the deictic present), resolved by discourse salience (*he*, the
narrative past), or bound by a c-commanding operator. -/
inductive ReferentialMode where
  | indexical
  | anaphoric
  | bound
  deriving DecidableEq, Repr

/-- Indexical and anaphoric expressions are both free; they differ only in how the free
variable is resolved. -/
def ReferentialMode.isFree : ReferentialMode → Bool
  | .indexical | .anaphoric => true
  | .bound => false

/-! ### Temporal variable infrastructure ([partee-1973]) -/

/-- Temporal assignment function: maps variable indices to times.
    The temporal analogue of H&K's `Assignment` (`ℕ → Entity`). -/
abbrev TemporalAssignment (T : Type*) := Assignment T

/-- Modified temporal assignment `g[n ↦ t]`. Specializes `Function.update`. -/
abbrev updateTemporal {T : Type*} (g : TemporalAssignment T)
    (n : ℕ) (t : T) : TemporalAssignment T :=
  Function.update g n t

/-- Temporal variable denotation: ⟦tₙ⟧^g = g(n). -/
abbrev interpTense {T : Type*} (n : ℕ) (g : TemporalAssignment T) : T :=
  g n

/-- Temporal lambda abstraction: bind a time variable.

    Partee's bound tense: "Whenever Mary phones, Sam *is* asleep" —
    present tense bound by "whenever", just as "Every farmer beats
    *his* donkey" has "his" bound by "every farmer". -/
abbrev temporalLambdaAbs {T α : Type*} (n : ℕ)
    (body : TemporalAssignment T → α) :
    TemporalAssignment T → T → α :=
  λ g t => body (Function.update g n t)

/-- Project a situation assignment to a temporal assignment: the temporal
    coordinate of each situation is extracted. -/
def situationToTemporal {W T : Type*}
    (g : ℕ → Index W T) : TemporalAssignment T :=
  λ n => (g n).time

/-- Temporal interpretation via situation assignment commutes with
    time projection: `interpTense n (π g) = (g n).time`. -/
theorem situation_temporal_commutes {W T : Type*}
    (g : ℕ → Index W T) (n : ℕ) :
    interpTense n (situationToTemporal g) = (g n).time := rfl

/-- Zero tense: a bound tense variable contributes no independent
    temporal constraint. When an attitude verb binds it, the variable receives
    the matrix event time. This is the SOT mechanism: the "past" morphology on
    the embedded verb is agreement, not a semantic tense. -/
theorem zeroTense_receives_binder_time {T : Type*}
    (g : TemporalAssignment T) (n : ℕ) (binderTime : T) :
    interpTense n (updateTemporal g n binderTime) = binderTime :=
  Function.update_self n binderTime g

/-! ### TensePronoun ([abusch-1997]) -/

/-- [abusch-1997]'s unified tense denotation: a temporal variable with a
    presupposed comparison-cell constraint and a [partee-1973] binding
    mode. Indexical mode is rigid to speech time; bound mode is the zero
    tense of attitude binding ([ogihara-1989]). -/
structure TensePronoun where
  varIndex : ℕ
  constraint : Finset Ordering
  mode : ReferentialMode
  /-- Index of the evaluation time variable in the temporal assignment.
      Default 0 = speech time slot. Under embedding, attitude verbs update
      this index to point at the matrix event time.
      [klecha-2016]: modals can also shift the eval time index. -/
  evalTimeIndex : ℕ := 0
  deriving DecidableEq

namespace TensePronoun

variable {T : Type*}

/-- Resolve: look up the temporal variable. -/
def resolve (tp : TensePronoun) (g : TemporalAssignment T) : T :=
  interpTense tp.varIndex g

/-- Presupposition: the constraint applied to the resolved time. -/
def presupposition [LinearOrder T]
    (tp : TensePronoun) (resolvedTime perspectiveTime : T) : Prop :=
  compare resolvedTime perspectiveTime ∈ tp.constraint

/-- Resolve the evaluation time from the assignment.
    In root clauses (evalTimeIndex = 0, g(0) = speech time), this is speech time.
    Under embedding, the attitude verb updates the assignment so that
    g(evalTimeIndex) = matrix event time. -/
def evalTime (tp : TensePronoun) (g : TemporalAssignment T) : T :=
  interpTense tp.evalTimeIndex g

/-- Full presupposition: the tense constraint checked against the resolved
    evaluation time (not just a bare perspective time parameter).
    This makes the eval time compositionally determined rather than stipulated. -/
def fullPresupposition [LinearOrder T]
    (tp : TensePronoun) (g : TemporalAssignment T) : Prop :=
  compare (tp.resolve g) (tp.evalTime g) ∈ tp.constraint

def isIndexical (tp : TensePronoun) : Prop := tp.mode = .indexical
instance (tp : TensePronoun) : Decidable tp.isIndexical :=
  inferInstanceAs (Decidable (tp.mode = .indexical))

def isBound (tp : TensePronoun) : Prop := tp.mode = .bound
instance (tp : TensePronoun) : Decidable tp.isBound :=
  inferInstanceAs (Decidable (tp.mode = .bound))

/-- When evalTimeIndex = 0 and g(0) = speechTime, the evaluation time is speech time.
    This is the root-clause default: tense is checked against speech time. -/
theorem evalTime_root_is_speech (tp : TensePronoun)
    (g : TemporalAssignment T) (speechTime : T)
    (hEval : tp.evalTimeIndex = 0) (hRoot : g 0 = speechTime) :
    tp.evalTime g = speechTime := by
  simp [evalTime, interpTense, hEval, hRoot]

/-- Updating the eval time index gives Von Stechow's perspective shift:
    the embedded tense is now checked against a different time (the matrix
    event time). This is how attitude verbs "transmit" their event time. -/
theorem evalTime_shifts_under_embedding (tp : TensePronoun)
    (g : TemporalAssignment T) (matrixEventTime : T) :
    tp.evalTime (updateTemporal g tp.evalTimeIndex matrixEventTime) = matrixEventTime :=
  zeroTense_receives_binder_time g tp.evalTimeIndex matrixEventTime

/-- Resolving a bound tense under binding yields the binder time. -/
theorem bound_resolve_eq_binder (tp : TensePronoun)
    (g : TemporalAssignment T) (binderTime : T) :
    tp.resolve (updateTemporal g tp.varIndex binderTime) = binderTime :=
  zeroTense_receives_binder_time g tp.varIndex binderTime

/-- An indexical present tense presupposes resolution to speech time. -/
theorem indexical_present_at_speech [LinearOrder T]
    (tp : TensePronoun) (resolvedTime speechTime : T)
    (hPres : tp.constraint = present)
    (hPresup : tp.presupposition resolvedTime speechTime) :
    resolvedTime = speechTime := by
  simp only [presupposition, hPres, compare_mem_present] at hPresup
  exact hPresup

end TensePronoun

end Tense
