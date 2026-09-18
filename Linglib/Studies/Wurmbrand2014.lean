import Linglib.Core.Order.Interval
import Linglib.Semantics.Tense.Embedding
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Data.Examples.Wurmbrand2014

/-!
# Wurmbrand (2014): Tense and Aspect in English Infinitives

This file formalizes [wurmbrand-2014]'s account of the temporal composition of English
infinitival complements. Three classes are distinguished by whether a bare, nonprogressive
verb phrase can be episodic: future infinitives allow it, propositional attitude infinitives
never do, and tenseless simultaneous infinitives allow it depending on the matrix tense
(`InfinitivalTenseClass`). The distribution is derived from viewpoint aspect. Perfective
aspect includes the event time in the reference time and imperfective the reverse
(`Perfective`), and an episodic eventive predicate occupies an extended interval, so
perfective fails whenever the reference time is an instant (`not_perfective_of_isPoint`).
Each class fixes the embedded reference time (`ReferenceTime`): the future modal *woll* shifts
it to an unrestricted interval after the evaluation time, a propositional attitude imposes the
holder's NOW, an instant, and a tenseless simultaneous infinitive inherits the matrix reference
time, an instant under present tense and an extended interval under past. The three rows of
the paper's table follow (`Episodic`), and a verb ambiguous between classes, like *seem*, is
episodic exactly when one of its classes is (`Verb.Episodic`).

Future infinitives are tenseless: finite *will* is present tense plus *woll* and *would* is
past plus *woll* (`Composition`), so finite future is absolute while infinitival future is
relative to the matrix event (`infinitival_relative`), and infinitives are invisible to the
sequence-of-tense rule, whose local tense feature skips them (`localTense`): a past under an
infinitive under past deletes, a past under *will* does not, and a silent *would* in the
infinitive would wrongly license deletion under a *will* matrix (`silent_would_wrong`).

## Implementation notes

Times are the nonempty intervals of a linear order; an instant is an interval whose endpoints
coincide. The evaluation time of *woll* and the attitude holder's NOW are one instant
parameter, and adverbials that restrict a reference time to an instant fall under the same
lemma as the NOW. The obligatory deletion of *would*'s past is taken as the paper does, as a
lexical requirement.

## References

* [wurmbrand-2014]
* [ogihara-1996]
* [abusch-1988]
* [wurmbrand-2001]
* [landau-2000]
-/

namespace Wurmbrand2014

open Tense Minimalist

/-! ### Viewpoint aspect -/

section Aspect

variable {T : Type*} [LinearOrder T]

/-- Perfective aspect: the event time is included in the reference time. -/
def Perfective (e r : NonemptyInterval T) : Prop := e ≤ r

/-- Imperfective aspect: the reference time is included in the event time. -/
def Imperfective (e r : NonemptyInterval T) : Prop := r ≤ e

/-- An extended event time cannot be included in an instant: perfective aspect fails at a
point reference time, the present, an attitude holder's NOW, or a reference time an adverbial
restricts to an instant. -/
theorem not_perfective_of_isPoint {e r : NonemptyInterval T} (he : ¬ e.IsPoint)
    (hr : r.IsPoint) : ¬ Perfective e r := by
  intro h
  rw [Perfective, NonemptyInterval.le_def] at h
  exact he (le_antisymm e.fst_le_snd (h.2.trans (hr.symm.le.trans h.1)))

/-- Imperfective aspect, the progressive, is available at any instant within the event. -/
theorem imperfective_pure_of_mem {e : NonemptyInterval T} {t : T} (h : t ∈ e) :
    Imperfective e (NonemptyInterval.pure t) := by
  rw [Imperfective, NonemptyInterval.le_def]
  exact NonemptyInterval.mem_def.mp h

/-! ### The reference time of an infinitive -/

variable (matrixR : NonemptyInterval T) (now : T)

/-- The reference time each class assigns the embedded aspect, given the matrix reference
time and the evaluation instant: after *woll*, any interval after the evaluation time; under a
propositional attitude, the holder's NOW; in a tenseless simultaneous infinitive, the matrix
reference time. -/
def ReferenceTime : InfinitivalTenseClass → NonemptyInterval T → Prop
  | .futureIrrealis, r => now < r.fst
  | .propositional, r => r = NonemptyInterval.pure now
  | .restructuring, r => r = matrixR

/-- A bare episodic verb phrase is available when some reference time of the class includes
an extended event time. -/
def Episodic (c : InfinitivalTenseClass) : Prop :=
  ∃ r, ReferenceTime matrixR now c r ∧
    ∃ e : NonemptyInterval T, ¬ e.IsPoint ∧ Perfective e r

/-- A future infinitive always has an episodic reading: *woll* supplies an unrestricted
interval. -/
theorem episodic_futureIrrealis [NoMaxOrder T] : Episodic matrixR now .futureIrrealis := by
  obtain ⟨a, ha⟩ := exists_gt now
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨⟨(a, b), hb.le⟩, ha, ⟨(a, b), hb.le⟩, hb.ne, le_rfl⟩

/-- A propositional attitude infinitive never has one: the holder's NOW is an instant. -/
theorem not_episodic_propositional : ¬ Episodic matrixR now .propositional := by
  rintro ⟨r, rfl, e, he, h⟩
  exact not_perfective_of_isPoint he (show (NonemptyInterval.pure now).IsPoint from rfl) h

/-- A tenseless simultaneous infinitive has one exactly when the matrix reference time is
extended: under past tense, but not under present, nor under an adverbial restricting it to
an instant. -/
theorem episodic_restructuring_iff :
    Episodic matrixR now .restructuring ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨r, rfl, e, he, h⟩ hp
    exact not_perfective_of_isPoint he hp h
  · exact λ h => ⟨matrixR, rfl, matrixR, h, le_rfl⟩

/-! ### Verbs -/

/-- The infinitive-taking verbs of the paper's table. -/
inductive Verb where
  | decide
  | want
  | promise
  | expect
  | claim
  | believe
  | try_
  | begin_
  | manage
  | seem
  deriving DecidableEq, Repr

/-- The classes a verb's infinitive may belong to: *expect* is future or, as a belief,
propositional; *seem* is tenseless simultaneous or, with an attitude holder, propositional. -/
def Verb.classes : Verb → List InfinitivalTenseClass
  | .decide | .want | .promise => [.futureIrrealis]
  | .expect => [.futureIrrealis, .propositional]
  | .claim | .believe => [.propositional]
  | .try_ | .begin_ | .manage => [.restructuring]
  | .seem => [.restructuring, .propositional]

/-- A verb's infinitive has an episodic reading when one of its classes does. -/
def Verb.Episodic (v : Verb) : Prop :=
  ∃ c ∈ v.classes, Wurmbrand2014.Episodic matrixR now c

/-- *believe* never allows a bare episodic complement. -/
theorem believe_not_episodic : ¬ Verb.believe.Episodic matrixR now := by
  rintro ⟨c, hc, h⟩
  simp only [Verb.classes, List.mem_singleton] at hc
  exact not_episodic_propositional matrixR now (hc ▸ h)

/-- *seem* allows one exactly when the matrix reference time is extended: its propositional
option adds nothing. -/
theorem seem_episodic_iff : Verb.seem.Episodic matrixR now ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨c, hc, h⟩
    simp only [Verb.classes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (episodic_restructuring_iff matrixR now).mp h
    · exact absurd h (not_episodic_propositional matrixR now)
  · exact λ h => ⟨.restructuring, by simp [Verb.classes],
      (episodic_restructuring_iff matrixR now).mpr h⟩

/-- *decide* always allows one. -/
theorem decide_episodic [NoMaxOrder T] : Verb.decide.Episodic matrixR now :=
  ⟨.futureIrrealis, by simp [Verb.classes], episodic_futureIrrealis matrixR now⟩

end Aspect

/-! ### Temporal composition -/

/-- The temporal composition of a clause: an optional tense feature and whether the future
modal *woll* is present. -/
structure Composition where
  tense : Option (Finset Ordering)
  woll : Bool
  deriving DecidableEq

/-- Finite *will*: present tense plus *woll*. -/
def will : Composition := ⟨some present, true⟩

/-- Finite *would*: past tense plus *woll*. -/
def would : Composition := ⟨some past, true⟩

/-- An infinitive: no tense, with or without *woll*. -/
def infinitive (woll : Bool) : Composition := ⟨none, woll⟩

/-- The composition of each class: all tenseless, with *woll* in the future class only. -/
def composition : InfinitivalTenseClass → Composition
  | .futureIrrealis => infinitive true
  | .propositional | .restructuring => infinitive false

/-- *woll* projects the modal layer: a class has *woll* exactly when its complement is a
ModP. -/
theorem woll_iff_modP (c : InfinitivalTenseClass) :
    (composition c).woll = true ↔ c.toComplementSize = .modP := by
  cases c <;> decide

section Future

variable {T : Type*} [LinearOrder T]

/-- Where a composition with *woll* locates its event: after the utterance time when present
tense is present, after the evaluation time otherwise. -/
def Composition.Locates (c : Composition) (utterance eval e : T) : Prop :=
  c.woll = true ∧ if c.tense = some present then utterance < e else eval < e

/-- Finite future is absolute: the event follows the utterance time. -/
theorem will_absolute {utterance eval e : T} (h : will.Locates utterance eval e) :
    utterance < e := by
  simpa [will, Composition.Locates] using h.2

/-- Infinitival future is relative: the event may precede the utterance time so long as it
follows the matrix evaluation time. -/
theorem infinitival_relative [DenselyOrdered T] {utterance eval : T} (h : eval < utterance) :
    ∃ e, (infinitive true).Locates utterance eval e ∧ e < utterance := by
  obtain ⟨e, h₁, h₂⟩ := exists_between h
  exact ⟨e, ⟨rfl, by simpa [infinitive] using h₁⟩, h₂⟩

end Future

/-! ### Sequence of tense -/

/-- The local tense feature of an embedded tense: the nearest tense feature above it,
infinitives contributing none. -/
def localTense : List (Option (Finset Ordering)) → Option (Finset Ordering)
  | [] => none
  | some f :: _ => some f
  | none :: rest => localTense rest

/-- Ogihara's rule: an embedded tense may delete when its local tense feature is the same
feature. -/
def sotApplies (above : List (Option (Finset Ordering))) (embedded : Finset Ordering) : Bool :=
  match localTense above with
  | some m => decide (m = embedded)
  | none => false

/-- The present of *will* intervenes between two pasts, blocking deletion. -/
theorem sot_will_blocks : sotApplies [will.tense, some past] past = false := by decide

/-- A tenseless infinitive does not intervene, so the lower past deletes. -/
theorem sot_infinitive_transparent :
    sotApplies [(infinitive true).tense, some past] past = true := by
  decide

/-- The past of *would* licenses deletion below it. -/
theorem sot_would : sotApplies [would.tense, some past] past = true := by decide

/-- Under a *will* matrix, a past below an infinitive finds no past above it. -/
theorem sot_will_infinitive : sotApplies [(infinitive true).tense, will.tense] past = false := by
  decide

/-- A silent *would* in the infinitive would license deletion under a *will* matrix, contrary
to the judgment. -/
theorem silent_would_wrong : sotApplies [would.tense, will.tense] past = true := by decide

/-- *would*'s past must delete: it is licensed only below a past. -/
def WouldLicensed (above : List (Option (Finset Ordering))) : Prop := sotApplies above past = true

instance : DecidablePred WouldLicensed := λ _ => inferInstanceAs (Decidable (_ = true))

/-- Temporal *would* under *will* is out, under a past matrix in. -/
theorem would_licensing : ¬ WouldLicensed [will.tense] ∧ WouldLicensed [some past] := by decide

end Wurmbrand2014
