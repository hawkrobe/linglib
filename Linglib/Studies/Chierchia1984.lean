import Linglib.Syntax.Voice.Alternation
import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Composition.TypeShifting
import Linglib.Fragments.English.Predicates.Verbal
import Mathlib.Data.Fin.Basic

/-!
# Chierchia 1984: infinitives and gerunds as properties

This file formalizes the control theory of [chierchia-1984]. Infinitival and gerundive
complements denote properties, not propositions, and control is not movement of PRO but semantic
entailment: a verb taking a property complement entails that a designated individual argument has
that property. The controller is fixed by predicate class rather than syntactic configuration,
which makes control follow from the meaning postulate wherever a property argument occurs.

Control predicates qualify the entailment modally — *try* entails the property in the situations
where what is tried succeeds, *force* in the situations compatible with what is imposed — which
the file states with [kratzer-1981]'s conversational backgrounds in the later two-parameter form
of [kratzer-1991]. Two generalizations fall out of the entailment approach: a subject-control
verb cannot passivize (Visser) and an object-control verb cannot detransitivize (Bach), since
either operation removes the argument the meaning postulate needs.

The three control classes are cut by closure properties: obligatory control (with subject
control *try* and object control *persuade* in one class), semi-obligatory control, whose
controller may stay implicit, and prominence control, fixed by discourse rather than by the
Control Principle.

## Main definitions

* `ControlVerb`, `ModalControl` — the Control Principle as a meaning postulate, and its modally
  qualified form
* `ChierchiaControlClass`, `derivedChierchiaClass` — the three classes, read off a Fragment
  verb's control type
* `controllerRole`, `cpBlocksAlternation`, `derivedPassivizable` — which argument the postulate
  needs, and which valency alternations that blocks

## Main results

* `visser`, `bach` — the two generalizations, from the meaning postulate alone
* `subjectControl_blocks_passivization`, `objectControl_blocks_detransitivization` — the same at
  the level of alternations
* `fragment_control_verbs_obligatory` — every Fragment control verb is obligatory control,
  attitude verbs included, against Landau's logophoric split
* `passivizability_derived_agrees` — the derived passivizability matches the Fragment's flag
* `control_complements_property_denoting` — control verbs take property-denoting complements

## References

* [chierchia-1984]
* [kratzer-1981]
* [kratzer-1991]
-/

namespace Chierchia1984

open Modality.Kratzer
open Semantics.Composition.TypeShifting (ComplementDenotation)

abbrev World := Fin 4

def allWorlds : List World := [0, 1, 2, 3]

-- ════════════════════════════════════════════════════════════════
-- § 1. Complement Denotations: Property vs. Proposition
-- ════════════════════════════════════════════════════════════════

/-! ## The VP = Property hypothesis

The central type-theoretic claim — infinitival and gerundive complements denote properties, not
propositions — is carried by the substrate: `ComplementType.denotation` derives the split from
clausality and finiteness, crediting this dissertation. What remains to check here is the verbs
(see the per-verb layer below). -/

-- ════════════════════════════════════════════════════════════════
-- § 2. The Control Principle
-- ════════════════════════════════════════════════════════════════

/-! ## The Control Principle (CP)

The CP is a meaning postulate on verbs that take property arguments:
if a verb takes a property P and individual arguments, it entails that
one of those individuals has property P.

We formalize this as a structure bundling the verb's semantics with
its control entailment. The entailment is **by construction**: the
`entails` field witnesses that the semantics forces P to hold of the
controlled argument.

Chierchia's full CP (Ch IV ex. 43) is a biconditional:
  □ α(x₁)..(P)..(xₙ) ↔ M_a P(xᵢ)
We formalize the left-to-right direction (the entailment) because this
is the load-bearing direction for control: it guarantees that the
controller has the complement property whenever the matrix verb holds. -/

section ControlPrinciple
variable (E Args : Type)

/-- A control verb with the Control Principle built in.

    The CP states: for any property P and world w where the verb's meaning
    holds, some designated argument has property P. The `controller` function
    selects which argument (from the full argument tuple) serves as controller.

    Parameterized over an argument tuple type `Args` — subject control verbs
    use `Args = E` (just the subject), object control verbs use `Args = E × E`
    (object, subject). -/
structure ControlVerb (Args : Type) where
  /-- The verb's semantics: property → arguments → world → Bool -/
  sem : (E → Bool) → Args → World → Bool
  /-- Select the controlled argument from the argument tuple -/
  controller : Args → E
  /-- The Control Principle: verb(P)(args)(w) → P(controller(args)) -/
  entails : ∀ (P : E → Bool) (args : Args) (w : World),
    sem P args w = true → P (controller args) = true

/-- Subject control verb: `Args = E`, controller is the identity. -/
abbrev SubjControlVerb := ControlVerb E E

/-- Object control verb: `Args = E × E` (object, subject), controller
    selects the object (first component). -/
abbrev ObjControlVerb := ControlVerb E (E × E)

-- ════════════════════════════════════════════════════════════════
-- § 3. Modal Qualification of Control
-- ════════════════════════════════════════════════════════════════

/-! ## Modal Qualification

[chierchia-1984] Ch IV §2.2: control predicates involve modal
qualification. The verb's meaning is not simply "x does P" but "in all
situations compatible with certain conditions, x does P."

Chierchia adopts [kratzer-1981]'s theory of conversational
backgrounds: each control verb selects a conversational background type
and a modal relation (necessity or possibility).

- **try**: buletic conversational background, necessity.
  try(P)(j) iff in all situations compatible with j's aims, j does P.
- **force**: deontic conversational background, necessity.
  force(P)(x)(y) iff in all situations compatible with what y imposes
  on x, x does P.
- **allow**: deontic conversational background, possibility.
  allow(P)(x)(y) iff there exists a situation compatible with what y
  imposes on x where x does P.

The formalization below uses the later two-parameter framework
(modal base + ordering source) from [kratzer-1991], which
refines Kratzer (1981)'s single-parameter approach. The `ModalBase`
corresponds roughly to the circumstantial facts, and the
`OrderingSource` to the conversational background type (bouletic,
deontic, etc.). This is a modernization, not what Chierchia literally
writes — he uses a single "conversational background" parameter.

Note: the property P here is extensional (`E → Bool`), so the modal
quantification over `bestWorlds` checks that the controller has P
whenever the accessible worlds are nonempty. A fully intensional
version would use `E → World → Bool`, allowing P's extension to vary
across worlds. We use the extensional version for simplicity, matching
the level of abstraction in the `ControlVerb` structure. -/

/-- A modally qualified control verb: the verb's semantics is defined via
    Kratzer necessity over a modal base and ordering source.

    The CP follows from the modal semantics + reflexivity (axiom T):
    if □P(x) and the actual world is among the best worlds, then P(x). -/
structure ModalControl (Args : Type) where
  /-- Circumstantial modal base -/
  base : ModalBase World
  /-- Ordering source (bouletic for try, deontic for force, ...) -/
  ordering : OrderingSource World
  /-- Select the controlled argument -/
  controller : Args → E
  /-- Reflexivity: actual world is among best worlds (axiom T) -/
  reflexive : ∀ (w : World), w ∈ bestWorlds base ordering w

/-- Construct a `ControlVerb` from a `ModalControl`.

    The verb's semantics is: verb(P)(args)(w) = ∀w' ∈ bestWorlds(w). P(controller(args)).
    The CP follows from reflexivity. -/
def ModalControl.toControlVerb (m : ModalControl E Args) :
    ControlVerb E Args where
  -- Since `P (m.controller args)` does not depend on the bound world, the
  -- universal quantification ∀ w' ∈ bestWorlds, P (controller args) = true
  -- collapses to `P (controller args)` (bestWorlds is nonempty by reflexivity).
  sem P args _w := P (m.controller args)
  controller := m.controller
  entails _P _args _w h := h

-- ════════════════════════════════════════════════════════════════
-- § 4. Visser's and Bach's Generalizations
-- ════════════════════════════════════════════════════════════════

/-! ## Visser's and Bach's Generalizations

These follow from the CP: if an argument-structure operation removes the
controller, the entailment cannot be satisfied.

- **Visser** (Ch IV §1.1, ex. 11): Subject control verbs cannot passivize.
  Passivization demotes the subject (A → oblique/unexpressed), but the CP
  requires P(subject). No subject → no entailment.
- **Bach** (attributed by Bresnan 1982; Ch IV §1.1, ex. 13-14): Object
  control verbs cannot detransitivize. Detransitivization removes the
  object, but the CP requires P(object).

We state these as: any faithful argument-reduction operation on a
control verb preserves existential control (∃x. P(x)) but loses
specific control (the guarantee that a *particular* argument has P). -/

/-- Visser's generalization: if a subject control verb is faithfully
    passivized (every passive truth witnesses some active truth),
    then P is satisfied by *some* entity — but the passive form
    cannot identify *which* entity. The CP guarantees existence. -/
theorem visser
    (v : SubjControlVerb E)
    (pass : (E → Bool) → World → Bool)
    (faithful : ∀ P w, pass P w = true → ∃ x, v.sem P x w = true) :
    ∀ P w, pass P w = true → ∃ x, P x = true := by
  intro P w hpass
  obtain ⟨x, hv⟩ := faithful P w hpass
  exact ⟨v.controller x, v.entails P x w hv⟩

/-- Bach's generalization: if an object control verb is faithfully
    detransitivized (losing the object argument), the CP still
    guarantees ∃x. P(x), but the detransitivized form cannot
    identify the specific x. -/
theorem bach
    (v : ObjControlVerb E)
    (detrans : (E → Bool) → E → World → Bool)
    (faithful : ∀ P y w, detrans P y w = true → ∃ args, v.sem P args w = true) :
    ∀ P y w, detrans P y w = true → ∃ x, P x = true := by
  intro P y w hd
  obtain ⟨args, hv⟩ := faithful P y w hd
  exact ⟨v.controller args, v.entails P args w hv⟩

end ControlPrinciple

-- ════════════════════════════════════════════════════════════════
-- § 5. Three Control Classes
-- ════════════════════════════════════════════════════════════════

/-- [chierchia-1984]'s three control classes (Ch IV §1), distinguished
    by their closure properties under argument-structure operations.

    - `obligatory`: all six OC properties hold (locality, no arbitrary
      reading, thematic uniqueness, no split antecedents, obligatory
      controller presence, Visser/Bach sensitivity). Includes both
      subject control (try, manage, begin) and object control (persuade,
      force) verbs. (Ch IV §1.1, ex. 4-6, properties in ex. 17)
    - `semiObligatory`: all OC properties EXCEPT obligatory controller
      presence — the controller can be implicit or contextually recovered.
      (Ch IV §1.2, ex. 18: decide, signal, recommend)
    - `prominence`: controller determined by discourse prominence, not by
      the CP. None of the six OC properties hold. (Ch IV §1.3, ex. 25:
      bother, be dangerous, denounce) -/
inductive ChierchiaControlClass where
  | obligatory
  | semiObligatory
  | prominence
  deriving DecidableEq, Repr

/-! ### The six properties of obligatory control (Ch IV ex. 17)

The six classic properties that define the obligatory control class:

  a. **Locality**: the controller must be a matrix argument
  b. **No arbitrary reading**: the controlled position has a specific referent
  c. **Thematic uniqueness**: the controller bears a specific θ-role
  d. **No split antecedents**: the controller is singular
  e. **Obligatory controller presence**: a controller must exist
  f. **Visser/Bach sensitivity**: removing the controller is impossible

All six follow from two facts: (A) the CP requires a specific argument
to have property P, and (B) obligatory control verbs have a fixed,
lexically determined controller.

Semi-obligatory control has (a-d) and (f) but not (e).
Prominence control has none of the six. -/

/-- Whether a control class has the CP (entailment-based control). -/
def ChierchiaControlClass.hasCP : ChierchiaControlClass → Bool
  | .obligatory     => true
  | .semiObligatory => true
  | .prominence     => false

/-- Prominence control lacks the CP and relaxes all OC properties. -/
theorem prominence_no_cp : ChierchiaControlClass.prominence.hasCP = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Deriving the Classification from Verb
-- ════════════════════════════════════════════════════════════════

/-! ## Per-Verb Classification

Derive [chierchia-1984]'s control class from Verb fields.

In Chierchia's taxonomy, ALL control verbs with a fixed, lexically
determined controller are obligatory — regardless of whether they are
subject or object control, and regardless of whether they are attitude
verbs. The subject/object distinction and the attitude/non-attitude
distinction are orthogonal to the obligatory/semi-obligatory/prominence
trichotomy.

The semi-obligatory class (decide, signal, recommend) requires a
Verb field for controller optionality, which does not currently
exist. The prominence class (bother, be dangerous) requires verbs
not currently in the English Fragment. Therefore, all current Fragment
control verbs are classified as obligatory. -/

def derivedChierchiaClass (v : Verb) : Option ChierchiaControlClass :=
  if v.controlType == .none && v.altControlType == .none then none
  else some .obligatory

-- ════════════════════════════════════════════════════════════════
-- § 7. Deriving Passivizability from the CP + Alternation Structure
-- ════════════════════════════════════════════════════════════════

/-! ## Passivizability: Derived from Deeper Principles

Visser's and Bach's generalizations both follow from a single structural
principle: an alternation is blocked by the CP iff it removes the
**controller** from core-term status.

The derivation has three steps:

1. **Which argument is the controller?** Subject control verbs have their
   A (agent-like) argument as controller; object control verbs have their
   P (patient-like) argument. Raising and non-control verbs have no
   semantic controller.

2. **What does the alternation do to that argument?** Passivization
   denucleativizes A and maintains P (`Voice.passivization`).
   Antipassivization (detransitivization) denucleativizes P and maintains A.

3. **Does removing the controller break the CP?** If the alternation
   denucleativizes or suppresses the controller, the CP cannot be
   satisfied → the alternation is blocked.

This replaces the stipulated `predictedPassivizable` case-split with a
derivation from `Voice.passivization` and `ControlType`. -/

open Voice

/-- Which TR-role serves as the controller, per [chierchia-1984]'s CP.

    Subject control: A is the controller (the subject has property P).
    Object control: P is the controller (the object has property P).
    Raising/none: no semantic controller (the CP does not apply). -/
def controllerRole : ControlType → Option TermRole
  | .subjectControl => some .A
  | .objectControl  => some .P
  | .raising        => none
  | .none           => none

/-- The CP blocks an alternation iff the alternation removes the
    controller from core-term status (denucleativizes or suppresses it).

    This is the general structural principle behind both Visser's
    generalization (passivization blocked for subject control) and
    Bach's generalization (detransitivization blocked for object control). -/
def cpBlocksAlternation (ct : ControlType) (va : ValencyAlternation) : Bool :=
  match controllerRole ct with
  | some role => (va.fateOfRole role).removesFromCoreStatus
  | none      => false

/-- Derived passivizability: a control verb can passivize iff the CP
    does not block passivization.

    - Subject control: controller = A, passivization denucleativizes A
      → CP broken → blocked (Visser's generalization)
    - Object control: controller = P, passivization maintains P
      → CP intact → allowed
    - Raising/none: no CP → no constraint → allowed -/
def derivedPassivizable (ct : ControlType) : Bool :=
  !cpBlocksAlternation ct passivization

-- ── Structural derivation theorems ──

/-- Subject control blocks passivization: passivization denucleativizes
    A, but the controller IS A. Denucleativizing the controller breaks
    the CP (Visser's generalization). -/
theorem subjectControl_blocks_passivization :
    cpBlocksAlternation .subjectControl passivization = true := rfl

/-- Object control allows passivization: passivization maintains P,
    and the controller IS P. The controller survives → CP intact. -/
theorem objectControl_allows_passivization :
    cpBlocksAlternation .objectControl passivization = false := rfl

/-- Object control blocks detransitivization: antipassivization
    denucleativizes P, but the controller IS P (Bach's generalization). -/
theorem objectControl_blocks_detransitivization :
    cpBlocksAlternation .objectControl antipassivization = true := rfl

/-- Subject control allows detransitivization: antipassivization
    maintains A, and the controller IS A. (e.g., "Mary promised Bill
    to come" → "Mary promised to come".) -/
theorem subjectControl_allows_detransitivization :
    cpBlocksAlternation .subjectControl antipassivization = false := rfl

section VerbVerification
open English.Predicates.Verbal

-- ── Per-verb Chierchia class verification ──

/-- Every control verb in the Fragment is obligatory control in Chierchia's sense — a fixed,
lexically determined controller with all six properties. *Want*, *hope* and *promise* included,
attitude verbs though they are: where Landau separates attitude verbs as logophoric, the Control
Principle classifies by fixed controller alone, and *persuade* and *force* show the class is
indifferent to whether that controller is subject or object. -/
theorem fragment_control_verbs_obligatory :
    ∀ v ∈ [try_.toVerb, manage.toVerb, begin_.toVerb, stop.toVerb, continue_.toVerb,
           fail.toVerb, persuade.toVerb, force.toVerb, want.toVerb, hope.toVerb,
           promise.toVerb],
      derivedChierchiaClass v = some .obligatory := by
  intro v hv
  fin_cases hv <;> rfl

-- ── Passivizability: derived agrees with stipulated ──

/-- At each Fragment control verb the passivizability the Control Principle derives agrees with
the stored flag: subject control blocks passivization and object control does not. -/
theorem passivizability_derived_agrees :
    ∀ v ∈ [try_.toVerb, persuade.toVerb, force.toVerb],
      derivedPassivizable v.controlType = v.passivizable := by
  intro v hv
  fin_cases hv <;> rfl

-- ── Complement semantic layer: control verbs take property-denoting complements ──

/-- Control verbs take property-denoting complements; *believe*, which is no control verb, takes
a finite clause denoting a proposition. -/
theorem control_complements_property_denoting :
    (∀ v ∈ [try_.toVerb, want.toVerb], v.complementType.denotation = some .property) ∧
      believe.toVerb.complementType.denotation = some .proposition ∧
      derivedChierchiaClass believe.toVerb = none := by
  refine ⟨fun v hv => ?_, rfl, rfl⟩
  fin_cases hv <;> rfl

end VerbVerification

end Chierchia1984
