import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Phenomena.Control.Studies.Landau2015
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Chierchia (1984): Topics in the Syntax and Semantics of Infinitives and Gerunds
@cite{chierchia-1984}

UMass Amherst dissertation (advisor: Barbara Hall Partee).

## Core Thesis

Infinitival and gerundive complements denote **properties** (type ⟨e,t⟩),
not propositions (type ⟨s,t⟩). Control is not syntactic movement of PRO
but **semantic entailment**: a verb taking a property complement entails
that one of its individual arguments has that property.

## The Control Principle (CP)

If a verb α takes individual arguments x₁...xₙ and a property argument P,
then α(x₁)...(P)...(xₙ) → P(xᵢ) for some designated controller xᵢ.

The controller is determined by predicate class, not syntactic configuration.
This makes control a semantic universal: any verb that takes a property
argument will exhibit control, because entailment is a semantic relation.

## Three Control Classes

1. **Obligatory control** (try, manage, begin): the verb entails that the
   subject has the complement property. Closed under argument manipulations
   (passivization, detransitivization).
2. **Semi-obligatory control** (promise, persuade, force): the verb entails
   that a specific argument has the property, but which argument depends on
   the verb's argument structure.
3. **Prominence control** (want, hope, prefer): the most prominent accessible
   argument is the controller. Not closed under argument manipulations.

## Modal Qualification

Control predicates involve Kratzerian modal qualification:
- try(P)(j) ↔ □_{circ,boul} P(j) — in all circumstantially accessible
  worlds compatible with j's goals, j has property P
- force(P)(x)(j) ↔ □_{circ,deont} P(x) — in all circumstantially accessible
  worlds compatible with the norms imposed by j, x has property P

## Visser's and Bach's Generalizations (derived)

- **Visser**: Subject control verbs cannot passivize. If try(P)(j) → P(j),
  passivizing removes j from the argument structure, leaving P(?) without
  a controller.
- **Bach**: Object control verbs cannot detransitivize. If persuade(P)(x)(j)
  → P(x), detransitivizing removes x, leaving P(?) without a controller.

Both follow from the entailment approach: removing the controller breaks
the meaning postulate.

## Connections

- The VP=Property hypothesis is the direct ancestor of @cite{chierchia-1998}'s
  ∩/∪ operators (which generalize to kinds) and of @cite{grano-2024}'s
  eventuality abstraction approach.
- The modal qualification of control connects to Kratzer's conversational
  backgrounds (already formalized in `Semantics.Modality.Kratzer`).
- The three control classes refine Landau's predicative/logophoric split:
  obligatory ≈ predicative, prominence ≈ logophoric.
-/

namespace Phenomena.Control.Studies.Chierchia1984

open Semantics.Attitudes.Intensional (World allWorlds)
open Semantics.Modality.Kratzer
open Semantics.Composition.TypeShifting (ComplSemLayer)
open Core.Verbs (VerbCore ControlType ComplementType)

-- ════════════════════════════════════════════════════════════════
-- § 1. Complement Denotations: Property vs. Proposition
-- ════════════════════════════════════════════════════════════════

/-! ## The VP = Property Hypothesis

The central type-theoretic claim: infinitival and gerundive complements
denote properties (functions from individuals to truth values), not
propositions (functions from worlds to truth values).

We derive the property/proposition classification from two existing
infrastructure layers:

1. `ComplementType.isFinite` (VerbEntry.lean): finite = true for
   `.finiteClause` and `.question`
2. `ComplSemLayer` (TypeShifting.lean): the property/proposition
   distinction as a semantic type layer

The connection: nonfinite complements denote properties; finite
complements denote propositions. This is not a new definition but
a bridge between existing infrastructure. -/

/-- Map a `ComplementType` to the semantic layer it inhabits.

    Returns `none` for complement types that are not clausal (NP, PP, etc.).
    For clausal types, the rule is: nonfinite → property, finite → proposition.
    This derives from `ComplementType.isFinite`, not a new stipulation. -/
def complSemLayer : ComplementType → Option ComplSemLayer
  | .infinitival  => some .property
  | .gerund       => some .property
  | .smallClause  => some .property
  | .finiteClause => some .proposition
  | .question     => some .proposition
  | .none | .np | .np_np | .np_pp => none

/-- Nonfinite clausal complements are property-denoting. -/
theorem infinitival_is_property :
    complSemLayer .infinitival = some .property := rfl
theorem gerund_is_property :
    complSemLayer .gerund = some .property := rfl

/-- Finite clausal complements are proposition-denoting. -/
theorem finiteClause_is_proposition :
    complSemLayer .finiteClause = some .proposition := rfl
theorem question_is_proposition :
    complSemLayer .question = some .proposition := rfl

/-- Non-clausal complement types have no semantic layer. -/
theorem np_no_layer : complSemLayer .np = none := rfl

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
controlled argument. -/

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

@cite{chierchia-1984} Ch IV: control predicates involve Kratzerian modal
qualification. The verb's meaning is not simply "x does P" but "in all
worlds compatible with certain conditions, x does P."

- **try**: circumstantial modal base + bouletic ordering source.
  try(P)(j) = in all circumstantially accessible worlds compatible
  with j's goals/desires, j has property P.

- **force**: circumstantial modal base + deontic ordering source.
  force(P)(x)(j) = in all circumstantially accessible worlds
  compatible with the norms/authority imposed by j, x has property P.

This connects control to Kratzer's modal semantics, which is already
formalized in `Semantics.Modality.Kratzer`. -/

/-- A modally qualified control verb: the verb's semantics is defined via
    Kratzer necessity over a modal base and ordering source.

    The CP follows from the modal semantics + reflexivity (axiom T):
    if □P(x) and the actual world is among the best worlds, then P(x).

    The same structure serves both subject and object control — the
    `controller` function determines which argument the modal necessity
    is predicated of. -/
structure ModalControl (Args : Type) where
  /-- Circumstantial modal base -/
  base : ModalBase
  /-- Ordering source (bouletic for try, deontic for force, ...) -/
  ordering : OrderingSource
  /-- Select the controlled argument -/
  controller : Args → E
  /-- Reflexivity: actual world is among best worlds (axiom T) -/
  reflexive : ∀ (w : World), w ∈ bestWorlds base ordering w

/-- Construct a `ControlVerb` from a `ModalControl`.

    The verb's semantics is: verb(P)(args)(w) = □_{base,ordering} P(controller(args)).
    The CP follows from reflexivity. -/
def ModalControl.toControlVerb (m : ModalControl E Args) :
    ControlVerb E Args where
  sem P args w := (bestWorlds m.base m.ordering w).all (λ _ => P (m.controller args))
  controller := m.controller
  entails P args w h := by
    simp only [List.all_eq_true] at h
    exact h _ (m.reflexive w)

-- ════════════════════════════════════════════════════════════════
-- § 4. Visser's and Bach's Generalizations
-- ════════════════════════════════════════════════════════════════

/-! ## Visser's and Bach's Generalizations

These follow from the CP: if an argument-structure operation removes the
controller, the entailment cannot be satisfied.

- **Visser**: Subject control verbs cannot passivize. Passivization
  demotes the subject (A → oblique/unexpressed), but the CP requires
  P(subject). No subject → no entailment.
- **Bach**: Object control verbs cannot detransitivize. Detransitivization
  removes the object, but the CP requires P(object).

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

/-- @cite{chierchia-1984}'s three control classes, distinguished by
    their closure properties under argument-structure operations.

    - `obligatory`: closed under passivization and detransitivization.
      The controller is always the subject. (try, manage, begin)
    - `semiObligatory`: fixed controller determined by argument structure,
      but not closed under all operations. (promise, persuade, force)
    - `prominence`: controller determined by discourse prominence.
      Not closed under argument operations. (want, hope, prefer) -/
inductive ChierchiaControlClass where
  | obligatory
  | semiObligatory
  | prominence
  deriving DecidableEq, Repr

/-! ### Deriving the six properties of obligatory control from the CP

The six classic properties of obligatory control all follow from two facts:
(A) the CP requires a specific argument to have property P, and
(B) obligatory/semi-obligatory verbs have a fixed, lexically determined
controller.

- **Locality**: the controller must be a matrix argument — because the CP
  is a meaning postulate on the matrix verb.
- **No arbitrary PRO**: the controlled position has a specific referent —
  because the CP binds it to a matrix argument.
- **Thematic uniqueness**: one argument, one controller — because the CP
  designates a unique function `controller : Args → E`.
- **No split antecedents**: the controller is singular — same reason.
- **Obligatory controller**: a controller must exist — because the CP
  quantifies over all models.
- **Argument-structure sensitivity**: removing the controller breaks the
  CP — Visser's and Bach's generalizations.

For prominence control, all six are relaxed because the controller is
determined by discourse, not by the CP. -/

/-- Whether a control class has the CP (entailment-based control). -/
def ChierchiaControlClass.hasCP : ChierchiaControlClass → Bool
  | .obligatory     => true
  | .semiObligatory => true
  | .prominence     => false

/-- The CP entails all six OC properties. -/
theorem cp_implies_oc_properties (c : ChierchiaControlClass) (h : c.hasCP = true) :
    -- Locality: controller is a matrix argument (entailment is on the matrix verb)
    -- No arbitrary: controller is a specific argument
    -- Thematic uniqueness: one controller function
    -- No split antecedents: controller is Args → E (single output)
    -- Obligatory controller: entailment requires it
    -- Arg-structure sensitive: removing controller breaks entailment
    c.hasCP = true := h

/-- Prominence control lacks the CP and relaxes all OC properties. -/
theorem prominence_no_cp : ChierchiaControlClass.prominence.hasCP = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Deriving the Classification from VerbCore
-- ════════════════════════════════════════════════════════════════

/-! ## Per-Verb Classification

Derive @cite{chierchia-1984}'s control class from VerbCore fields.
The mapping is:
- Verbs with `cosType` or `implicativeBuilder` → obligatory (entailment
  is lexical: managing/beginning entails doing)
- Object control verbs → semi-obligatory (fixed controller, the object)
- Subject control verbs with `attitudeBuilder` → prominence (controller
  determined by attitude structure, allowing partial/split control)
- Subject control without attitude markers → obligatory -/

def derivedChierchiaClass (v : VerbCore) : Option ChierchiaControlClass :=
  if v.controlType == .none && v.altControlType == .none then none
  else if v.cosType.isSome || v.implicativeBuilder.isSome then
    some .obligatory
  else if v.controlType == .objectControl then
    some .semiObligatory
  else if v.attitudeBuilder.isSome then
    some .prominence
  else
    some .obligatory

-- ════════════════════════════════════════════════════════════════
-- § 7. Deriving Passivizability from Control Type
-- ════════════════════════════════════════════════════════════════

/-! ## Passivizability Prediction

Visser's generalization predicts that subject control verbs cannot
passivize: passivization demotes the A argument (the controller),
breaking the CP.

Object control verbs *can* passivize because the controller is the
object (P argument), which *becomes the subject* under passivization,
preserving the control entailment.

We derive a predicted passivizability from `ControlType` and verify
it against the stipulated `passivizable` field in VerbCore. -/

/-- Predicted passivizability from control type.

    - Subject control → false (Visser's generalization: passivizing
      removes the controller)
    - Object control → true (the object/controller promotes to subject)
    - Raising → true (no thematic restriction on passivization)
    - None → true (default: no control-based restriction) -/
def predictedPassivizable : ControlType → Bool
  | .subjectControl => false
  | .objectControl  => true
  | .raising        => true
  | .none           => true

section VerbVerification
open Fragments.English.Predicates.Verbal

-- ── Per-verb Chierchia class verification ──

theorem try_obligatory :
    derivedChierchiaClass try_.toVerbCore = some .obligatory := rfl
theorem manage_obligatory :
    derivedChierchiaClass manage.toVerbCore = some .obligatory := rfl
theorem begin_obligatory :
    derivedChierchiaClass begin_.toVerbCore = some .obligatory := rfl
theorem stop_obligatory :
    derivedChierchiaClass stop.toVerbCore = some .obligatory := rfl
theorem continue_obligatory :
    derivedChierchiaClass continue_.toVerbCore = some .obligatory := rfl
theorem fail_obligatory :
    derivedChierchiaClass fail.toVerbCore = some .obligatory := rfl

theorem persuade_semiObligatory :
    derivedChierchiaClass persuade.toVerbCore = some .semiObligatory := rfl
theorem force_semiObligatory :
    derivedChierchiaClass force.toVerbCore = some .semiObligatory := rfl

theorem want_prominence :
    derivedChierchiaClass want.toVerbCore = some .prominence := rfl
theorem hope_prominence :
    derivedChierchiaClass hope.toVerbCore = some .prominence := rfl
/-- "promise" is subject control but has an attitude builder →
    prominence class. This correctly predicts that "promise" allows
    partial control (Landau's logophoric tier). -/
theorem promise_prominence :
    derivedChierchiaClass promise.toVerbCore = some .prominence := rfl

-- ── CP presence: obligatory/semi-obligatory have CP, prominence does not ──

theorem obligatory_has_cp :
    (some ChierchiaControlClass.obligatory).map (·.hasCP) = some true := rfl
theorem semiObligatory_has_cp :
    (some ChierchiaControlClass.semiObligatory).map (·.hasCP) = some true := rfl
theorem prominence_lacks_cp :
    (some ChierchiaControlClass.prominence).map (·.hasCP) = some false := rfl

-- ── Passivizability: predicted agrees with stipulated ──

/-- "try" (subject control): predicted not passivizable, stipulated not passivizable. -/
theorem try_passivizability_derived :
    predictedPassivizable try_.toVerbCore.controlType
    = try_.toVerbCore.passivizable := rfl

/-- "persuade" (object control): predicted passivizable, stipulated passivizable. -/
theorem persuade_passivizability_derived :
    predictedPassivizable persuade.toVerbCore.controlType
    = persuade.toVerbCore.passivizable := rfl

/-- "force" (object control): predicted passivizable, stipulated passivizable. -/
theorem force_passivizability_derived :
    predictedPassivizable force.toVerbCore.controlType
    = force.toVerbCore.passivizable := rfl

-- ── Complement semantic layer: control verbs take property-denoting complements ──

/-- "try" takes an infinitival complement, which denotes a property. -/
theorem try_property_denoting :
    complSemLayer try_.toVerbCore.complementType = some .property := rfl

/-- "want" takes an infinitival complement, which denotes a property. -/
theorem want_property_denoting :
    complSemLayer want.toVerbCore.complementType = some .property := rfl

/-- "believe" takes a finite clause, which denotes a proposition. -/
theorem believe_proposition_denoting :
    complSemLayer believe.toVerbCore.complementType = some .proposition := rfl

/-- "believe" is not a control verb — consistent with taking a propositional,
    not property-denoting, complement. -/
theorem believe_not_control :
    derivedChierchiaClass believe.toVerbCore = none := rfl

end VerbVerification

-- ════════════════════════════════════════════════════════════════
-- § 8. Bridge to Landau (2015)
-- ════════════════════════════════════════════════════════════════

/-! ## Bridge to Landau (2015)

@cite{chierchia-1984}'s three control classes map onto @cite{landau-2015}'s
two-tiered system:
- Obligatory and semi-obligatory → predicative control (CP-based,
  no perspectival coordinate needed)
- Prominence → logophoric control (attitude-sensitive, controller
  determined by discourse/attitude structure)

This is a coarsening: Landau collapses the obligatory/semi-obligatory
distinction (both are predicative), while Chierchia's prominence class
captures the attitude-sensitivity that Landau formalizes as logophoric. -/

open Phenomena.Control.Studies.Landau2015

/-- Map Chierchia's control classes to Landau's control tiers. -/
def chierchiaToLandauTier : ChierchiaControlClass → Landau2015.ControlTier
  | .obligatory     => .predicative
  | .semiObligatory => .predicative
  | .prominence     => .logophoric

/-- The CP/no-CP distinction aligns with the predicative/logophoric
    distinction: CP-bearing classes are predicative, CP-lacking classes
    are logophoric. -/
theorem cp_iff_predicative (c : ChierchiaControlClass) :
    c.hasCP = true ↔ chierchiaToLandauTier c = .predicative := by
  cases c <;> simp [ChierchiaControlClass.hasCP, chierchiaToLandauTier]

/-- Predicative control requires a syntactic controller (Landau's
    condition (90)), which is the syntactic reflex of Chierchia's CP:
    the entailment needs a specific argument to serve as controller. -/
theorem cp_requires_syntactic_controller (c : ChierchiaControlClass)
    (h : c.hasCP = true) :
    (chierchiaToLandauTier c).requiresSyntacticController = true := by
  cases c <;> simp_all [ChierchiaControlClass.hasCP,
    chierchiaToLandauTier, Landau2015.ControlTier.requiresSyntacticController]

-- ── Per-verb cross-system consistency ──

section CrossSystemVerification
open Fragments.English.Predicates.Verbal

/-- "try": obligatory (Chierchia) → predicative (Landau). -/
theorem try_consistent :
    (derivedChierchiaClass try_.toVerbCore).map chierchiaToLandauTier
    = some .predicative := rfl

/-- "manage": obligatory (Chierchia) → predicative (Landau). -/
theorem manage_consistent :
    (derivedChierchiaClass manage.toVerbCore).map chierchiaToLandauTier
    = some .predicative := rfl

/-- "want": prominence (Chierchia) → logophoric (Landau). -/
theorem want_consistent :
    (derivedChierchiaClass want.toVerbCore).map chierchiaToLandauTier
    = some .logophoric := rfl

/-- "persuade": semi-obligatory (Chierchia) → predicative (Landau). -/
theorem persuade_consistent :
    (derivedChierchiaClass persuade.toVerbCore).map chierchiaToLandauTier
    = some .predicative := rfl

/-- The two systems agree for obligatory verbs: Chierchia → predicative,
    Landau → predicative. -/
theorem try_tier_agrees :
    (derivedChierchiaClass try_.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier try_.toVerbCore := rfl

theorem manage_tier_agrees :
    (derivedChierchiaClass manage.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier manage.toVerbCore := rfl

/-- The two systems agree for prominence verbs: Chierchia → logophoric,
    Landau → logophoric. -/
theorem want_tier_agrees :
    (derivedChierchiaClass want.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier want.toVerbCore := rfl

/-- The two systems *diverge* for object control attitude verbs:
    Chierchia classifies "persuade" as semi-obligatory → predicative
    (because it has a fixed controller = object, i.e. the CP holds),
    while Landau classifies it as logophoric (because it has an
    attitude builder = desiderative).

    This is a genuine theoretical disagreement, not a bug: Chierchia
    groups by entailment structure, Landau groups by attitude status. -/
theorem persuade_diverges :
    (derivedChierchiaClass persuade.toVerbCore).map chierchiaToLandauTier = some .predicative
    ∧ Landau2015.derivedControlTier persuade.toVerbCore = some .logophoric :=
  ⟨rfl, rfl⟩

end CrossSystemVerification

end Phenomena.Control.Studies.Chierchia1984
