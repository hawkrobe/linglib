module

public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Composition.Assignment
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Semantics.Tense.Defs

/-!
# Tense pronouns

Partee's insight is that a tense morpheme is a temporal pronoun, a variable with a temporal
constraint and a binding mode: indexical, anaphoric or bound. `TensePronoun` carries the variable
index, the comparison-cell constraint, the `ReferentialMode` and the evaluation index, and the
constraint is a presupposition on the resolved time, after Heim's comments on Abusch and after
Kratzer. Tense variables are read and bound by the same assignment API as entity pronouns,
`HeimKratzer.interpPronoun` and `HeimKratzer.lambdaAbsG` over `Assignment T`.

## References

* [partee-1973]
* [abusch-1997]
* [heim-1994-comments]
* [kratzer-1998]
-/

@[expose] public section

open Reference

namespace Tense

open HeimKratzer
open scoped Assignment

open Semantics

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

/-- The temporal assignment of a situation assignment sends each index to the time of its
situation. -/
def situationToTemporal {W T : Type*}
    (g : ℕ → Index W T) : Assignment T :=
  λ n => (g n).time

/-- Temporal interpretation via situation assignment commutes with
    time projection: `interpPronoun n (π g) = (g n).time`. -/
theorem situation_temporal_commutes {W T : Type*}
    (g : ℕ → Index W T) (n : ℕ) :
    interpPronoun n (situationToTemporal g) = (g n).time := rfl

/-- A bound tense variable, the zero tense, receives the time of its binder, so it contributes no
temporal constraint of its own: under an attitude verb it is the matrix event time, and the
embedded past morphology is agreement, not a semantic tense. -/
theorem zeroTense_receives_binder_time {T : Type*}
    (g : Assignment T) (n : ℕ) (binderTime : T) :
    interpPronoun n (g[n ↦ binderTime]) = binderTime := by
  simp

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

/-- A tense pronoun resolves to the time its variable is assigned. -/
def resolve (tp : TensePronoun) (g : Assignment T) : T :=
  interpPronoun tp.varIndex g

/-- The presupposition of a tense pronoun is that the resolved time stands to the perspective
time in a relation its constraint admits. -/
def presupposition [LinearOrder T]
    (tp : TensePronoun) (resolvedTime perspectiveTime : T) : Prop :=
  compare resolvedTime perspectiveTime ∈ tp.constraint

/-- Resolve the evaluation time from the assignment.
    In root clauses (evalTimeIndex = 0, g(0) = speech time), this is speech time.
    Under embedding, the attitude verb updates the assignment so that
    g(evalTimeIndex) = matrix event time. -/
def evalTime (tp : TensePronoun) (g : Assignment T) : T :=
  interpPronoun tp.evalTimeIndex g

/-- The full presupposition checks the constraint against the evaluation time the assignment
resolves, so the evaluation time is determined compositionally. -/
def fullPresupposition [LinearOrder T]
    (tp : TensePronoun) (g : Assignment T) : Prop :=
  compare (tp.resolve g) (tp.evalTime g) ∈ tp.constraint

instance [LinearOrder T] (tp : TensePronoun) (g : Assignment T) :
    Decidable (tp.fullPresupposition g) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- In a context with a single salient time, the assignment sending every variable there, a
tense pronoun is defined iff its cell admits coincidence with the evaluation time. -/
@[simp] theorem fullPresupposition_const [LinearOrder T] (tp : TensePronoun) (t₀ : T) :
    tp.fullPresupposition (Function.const ℕ t₀) ↔ .eq ∈ tp.constraint := by
  simp [fullPresupposition, resolve, evalTime, interpPronoun]

def isIndexical (tp : TensePronoun) : Prop := tp.mode = .indexical
instance (tp : TensePronoun) : Decidable tp.isIndexical :=
  inferInstanceAs (Decidable (tp.mode = .indexical))

def isBound (tp : TensePronoun) : Prop := tp.mode = .bound
instance (tp : TensePronoun) : Decidable tp.isBound :=
  inferInstanceAs (Decidable (tp.mode = .bound))

/-- When evalTimeIndex = 0 and g(0) = speechTime, the evaluation time is speech time.
    This is the root-clause default: tense is checked against speech time. -/
theorem evalTime_root_is_speech (tp : TensePronoun)
    (g : Assignment T) (speechTime : T)
    (hEval : tp.evalTimeIndex = 0) (hRoot : g 0 = speechTime) :
    tp.evalTime g = speechTime := by
  simp [evalTime, interpPronoun, hEval, hRoot]

/-- Updating the eval time index gives Von Stechow's perspective shift:
    the embedded tense is now checked against a different time (the matrix
    event time). This is how attitude verbs "transmit" their event time. -/
theorem evalTime_shifts_under_embedding (tp : TensePronoun)
    (g : Assignment T) (matrixEventTime : T) :
    tp.evalTime (g[tp.evalTimeIndex ↦ matrixEventTime]) = matrixEventTime :=
  zeroTense_receives_binder_time g tp.evalTimeIndex matrixEventTime

/-- Resolving a bound tense under binding yields the binder time. -/
theorem bound_resolve_eq_binder (tp : TensePronoun)
    (g : Assignment T) (binderTime : T) :
    tp.resolve (g[tp.varIndex ↦ binderTime]) = binderTime :=
  zeroTense_receives_binder_time g tp.varIndex binderTime

/-- An indexical present tense presupposes resolution to speech time. -/
theorem indexical_present_at_speech [LinearOrder T]
    (tp : TensePronoun) (resolvedTime speechTime : T)
    (hPres : tp.constraint = ⟦present⟧)
    (hPresup : tp.presupposition resolvedTime speechTime) :
    resolvedTime = speechTime := by
  simp only [presupposition, hPres, compare_mem_present] at hPresup
  exact hPresup

end TensePronoun

end Tense
