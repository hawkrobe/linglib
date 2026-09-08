import Linglib.Syntax.Voice.Alternation
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Chierchia (1984): Topics in the syntax and semantics of infinitives and gerunds

This file formalizes the control theory of [chierchia-1984]. Infinitival and gerundive
complements denote properties, not propositions, and control is not movement of PRO but
entailment: the Control Principle is a meaning postulate on a verb taking a property
complement, that it holds of the property and its arguments exactly when a designated argument
has the property throughout the situations the verb's conversational background selects
([kratzer-1981]), so the controller is fixed by the predicate's meaning rather than by syntactic
configuration. Visser's and Bach's generalizations follow: a subject-control verb cannot
passivize and an object-control verb cannot detransitivize, since either alternation removes
the argument the postulate needs. The control classes of chapter IV are cut by whether the
postulate applies and whether the controller must be expressed. The theorems derive the
controller's having the property from the postulate, the blocking of each valency alternation
from which argument controls, and check the Fragment's control verbs against both.

## Implementation notes

* The conversational background is the two-parameter one of [kratzer-1991], a modal base and an
  ordering source, and the entailment is necessity over it; the possibility that *allow*
  needs is not instantiated.

## References

* [chierchia-1984]
* [kratzer-1981]
* [kratzer-1991]
-/

namespace Chierchia1984

open Modality.Kratzer

variable {E W Args : Type*}

/-! ### The Control Principle (chapter IV) -/

/-- A verb taking a property complement, with the Control Principle as its meaning postulate:
the verb holds of a property and its arguments at a world exactly when the argument it controls
has the property throughout the situations its conversational background selects, what is aimed
at for *try*, what is imposed for *force*. -/
structure ControlVerb (E W Args : Type*) where
  sem : (E → W → Prop) → Args → W → Prop
  controller : Args → E
  accessible : Args → W → Set W
  control : ∀ P args w, sem P args w ↔ ∀ w' ∈ accessible args w, P (controller args) w'

/-- A subject-control verb's one argument is its controller. -/
abbrev SubjectControlVerb (E W : Type*) := ControlVerb E W E

/-- An object-control verb controls the first of its object and subject. -/
abbrev ObjectControlVerb (E W : Type*) := ControlVerb E W (E × E)

/-- A control verb from a modal base and an ordering source, [kratzer-1991]'s form of the
background: the controller has the property throughout the best accessible worlds. -/
def ControlVerb.ofKratzer (base : ModalBase W) (ordering : OrderingSource W)
    (controller : Args → E) : ControlVerb E W Args where
  sem P args w := necessity base ordering (P (controller args)) w
  controller := controller
  accessible _ w := bestWorlds base ordering w
  control _ _ _ := necessity_iff_all _ _ _ _

variable (v : ControlVerb E W Args)

/-- The controller has the property in every situation the background selects. -/
theorem ControlVerb.controller_has {P : E → W → Prop} {args : Args} {w : W}
    (h : v.sem P args w) : ∀ w' ∈ v.accessible args w, P (v.controller args) w' :=
  (v.control P args w).1 h

/-- Over a reflexive background the controller has the property at the world itself. -/
theorem ControlVerb.controller_has_self (hrefl : ∀ args w, w ∈ v.accessible args w)
    {P : E → W → Prop} {args : Args} {w : W} (h : v.sem P args w) : P (v.controller args) w :=
  v.controller_has h w (hrefl args w)

/-! ### Visser's and Bach's generalizations (chapter IV) -/

/-- Visser's generalization: a faithful passive of a subject-control verb, one whose truth
witnesses a truth of the active, can only guarantee that some entity has the property in the
selected situations; the argument the postulate would name is gone. -/
theorem visser (v : SubjectControlVerb E W) (pass : (E → W → Prop) → W → Prop)
    (faithful : ∀ P w, pass P w → ∃ x, v.sem P x w) {P : E → W → Prop} {w : W}
    (h : pass P w) : ∃ x, ∀ w' ∈ v.accessible x w, P (v.controller x) w' :=
  let ⟨x, hx⟩ := faithful P w h
  ⟨x, v.controller_has hx⟩

/-- Bach's generalization: the same for a faithful detransitive of an object-control verb. -/
theorem bach (v : ObjectControlVerb E W) (detrans : (E → W → Prop) → E → W → Prop)
    (faithful : ∀ P y w, detrans P y w → ∃ args, v.sem P args w) {P : E → W → Prop} {y : E}
    {w : W} (h : detrans P y w) : ∃ args, ∀ w' ∈ v.accessible args w, P (v.controller args) w' :=
  let ⟨args, hv⟩ := faithful P y w h
  ⟨args, v.controller_has hv⟩

/-! ### Control classes (chapter IV, section 1) -/

/-- The three control classes: obligatory control, where the Control Principle fixes a
controller that must be expressed, *try* and *persuade* alike; semi-obligatory control, where
the controller may stay implicit, *decide*, *recommend*; and prominence control, where discourse
rather than the postulate fixes it, *bother*, *be dangerous*. -/
inductive ControlClass where
  | obligatory
  | semiObligatory
  | prominence
  deriving DecidableEq, Repr

/-- The Control Principle governs the first two classes. -/
def ControlClass.HasControlPrinciple : ControlClass → Prop
  | .obligatory => True
  | .semiObligatory => True
  | .prominence => False

instance : DecidablePred ControlClass.HasControlPrinciple
  | .obligatory => inferInstanceAs (Decidable True)
  | .semiObligatory => inferInstanceAs (Decidable True)
  | .prominence => inferInstanceAs (Decidable False)

/-- The class of a Fragment verb: every verb the Fragment marks for control has a fixed
controller and is obligatory control, the Fragment recording neither an implicit controller nor
the prominence verbs. -/
def ControlClass.ofVerb (v : Verb) : Option ControlClass :=
  if v.controlType = .none ∧ v.altControlType = .none then none else some .obligatory

/-! ### Which alternations the postulate blocks -/

open Voice

/-- The argument the postulate needs: the agent-like term of a subject-control verb, the
patient-like term of an object-control verb, none for raising. -/
def controllerRole : ControlType → Option TermRole
  | .subjectControl => some .A
  | .objectControl => some .P
  | .raising => none
  | .none => none

/-- The Control Principle blocks a valency alternation that removes the controller from
core-term status. -/
def Blocks (ct : ControlType) (va : ValencyAlternation) : Prop :=
  ∃ role ∈ controllerRole ct, (va.fateOfRole role).removesFromCoreStatus = true

instance (ct : ControlType) (va : ValencyAlternation) : Decidable (Blocks ct va) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A control type passivizes when the postulate does not block passivization. -/
def Passivizable (ct : ControlType) : Prop := ¬ Blocks ct passivization

instance : DecidablePred Passivizable := λ ct => inferInstanceAs (Decidable (¬ Blocks ct _))

/-- Visser's generalization at the level of alternations: passivization demotes the agent-like
term, which subject control needs. -/
theorem subjectControl_blocks_passivization : Blocks .subjectControl passivization := by decide

/-- Passivization keeps the patient-like term, so object control survives it. -/
theorem objectControl_passivizable : Passivizable .objectControl := by decide

/-- Bach's generalization at the level of alternations: antipassivization demotes the
patient-like term, which object control needs. -/
theorem objectControl_blocks_antipassivization : Blocks .objectControl antipassivization := by
  decide

/-- Antipassivization keeps the agent-like term, so subject control survives it, *promise to
come* beside *promise Bill to come*. -/
theorem subjectControl_not_blocks_antipassivization :
    ¬ Blocks .subjectControl antipassivization := by
  decide

/-! ### The Fragment's control verbs -/

section Fragment

open English.Predicates.Verbal

/-- Every control verb of the Fragment, the attitude verbs *want*, *hope* and *promise* included,
is a control verb in the dissertation's sense, with a fixed controller whether subject or
object. -/
theorem fragment_control_verbs :
    ∀ v ∈ [try_.toVerb, manage.toVerb, begin_.toVerb, stop.toVerb, continue_.toVerb, fail.toVerb,
      persuade.toVerb, force.toVerb, want.toVerb, hope.toVerb, promise.toVerb],
      v.controlType ≠ .none ∨ v.altControlType ≠ .none := by
  intro v hv
  fin_cases hv <;> decide

/-- At each Fragment control verb the passivizability the postulate derives agrees with the
stored flag: subject control blocks passivization and object control does not. -/
theorem passivizable_iff :
    ∀ v ∈ [try_.toVerb, persuade.toVerb, force.toVerb],
      Passivizable v.controlType ↔ v.passivizable = true := by
  intro v hv
  fin_cases hv <;> decide

/-- Control verbs take property-denoting complements; *believe*, no control verb, takes a finite
clause denoting a proposition. -/
theorem control_complements_property :
    (∀ v ∈ [try_.toVerb, want.toVerb], v.complementType.denotation = some .property) ∧
      believe.toVerb.complementType.denotation = some .proposition ∧
      believe.toVerb.controlType = .none := by
  refine ⟨λ v hv => ?_, rfl, rfl⟩
  fin_cases hv <;> rfl

end Fragment

end Chierchia1984
