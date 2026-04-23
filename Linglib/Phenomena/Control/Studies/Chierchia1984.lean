import Linglib.Theories.Syntax.ArgumentStructure.Alternation
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

Chierchia distinguishes three classes by their closure properties under
argument-structure operations (Ch IV §1):

1. **Obligatory control** (try, persuade, force, promise, want, enjoy,
   manage, begin): the verb entails that a specific argument has the
   complement property. The controller must be overtly present and bears
   a specific θ-role. Includes both subject control (try) and object
   control (persuade) verbs — the distinction is subject vs. object,
   not obligatory vs. semi-obligatory.
2. **Semi-obligatory control** (decide, signal, recommend): all the
   properties of obligatory control EXCEPT mandatory controller presence.
   The controller can be implicit or contextually recovered
   (e.g., "It was decided to leave").
3. **Prominence control** (bother, be dangerous, denounce): the controller
   is determined by discourse prominence, not by the CP. None of the six
   OC properties hold — no locality, no thematic uniqueness, split
   antecedents possible, long-distance control possible.

## Modal Qualification

Control predicates involve modal qualification (Ch IV §2.2):
- try(P)(j) ↔ □_{try,j} P(j) — in all situations where what j tries
  will eventually succeed, j has property P
- force(P)(x)(y) ↔ □_{force,y} P(x) — in all situations compatible with
  what y imposes on x, x has property P

Chierchia adopts @cite{kratzer-1981}'s theory of conversational backgrounds
to formalize this. Each control verb selects a conversational background
type (deontic for force, buletic for try) and a modal relation (necessity
or possibility). The formalization below uses the later two-parameter
framework (modal base + ordering source) from @cite{kratzer-1991}, which
refines Kratzer (1981)'s single-parameter approach.

## Visser's and Bach's Generalizations (derived)

- **Visser** (Ch IV §1.1, ex. 11): Subject control verbs cannot passivize.
  If try(P)(j) → P(j), passivizing removes j from the argument structure,
  leaving P(?) without a controller.
- **Bach** (attributed by Bresnan 1982; Ch IV §1.1, ex. 13-14): Object
  control verbs cannot detransitivize. If persuade(P)(x)(j) → P(x),
  detransitivizing removes x, leaving P(?) without a controller.

Both follow from the entailment approach: removing the controller breaks
the meaning postulate.

## Connections

- The VP=Property hypothesis is the direct ancestor of @cite{chierchia-1998}'s
  ∩/∪ operators (which generalize to kinds) and of @cite{grano-2024}'s
  eventuality abstraction approach.
- The modal qualification of control connects to Kratzer's conversational
  backgrounds (already formalized in `Semantics.Modality.Kratzer`).
- The three control classes cut differently from Landau's predicative/logophoric
  split: Chierchia classifies ALL verbs with the CP as obligatory (including
  attitude verbs like want), while Landau separates attitude verbs as logophoric.
-/

namespace Chierchia1984

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

@cite{chierchia-1984} Ch IV §2.2: control predicates involve modal
qualification. The verb's meaning is not simply "x does P" but "in all
situations compatible with certain conditions, x does P."

Chierchia adopts @cite{kratzer-1981}'s theory of conversational
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
(modal base + ordering source) from @cite{kratzer-1991}, which
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

/-- @cite{chierchia-1984}'s three control classes (Ch IV §1), distinguished
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
-- § 6. Deriving the Classification from VerbCore
-- ════════════════════════════════════════════════════════════════

/-! ## Per-Verb Classification

Derive @cite{chierchia-1984}'s control class from VerbCore fields.

In Chierchia's taxonomy, ALL control verbs with a fixed, lexically
determined controller are obligatory — regardless of whether they are
subject or object control, and regardless of whether they are attitude
verbs. The subject/object distinction and the attitude/non-attitude
distinction are orthogonal to the obligatory/semi-obligatory/prominence
trichotomy.

The semi-obligatory class (decide, signal, recommend) requires a
VerbCore field for controller optionality, which does not currently
exist. The prominence class (bother, be dangerous) requires verbs
not currently in the English Fragment. Therefore, all current Fragment
control verbs are classified as obligatory. -/

def derivedChierchiaClass (v : VerbCore) : Option ChierchiaControlClass :=
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
   denucleativizes A and maintains P (`Syntax.ArgumentStructure.Alternation.passivization`).
   Antipassivization (detransitivization) denucleativizes P and maintains A.

3. **Does removing the controller break the CP?** If the alternation
   denucleativizes or suppresses the controller, the CP cannot be
   satisfied → the alternation is blocked.

This replaces the stipulated `predictedPassivizable` case-split with a
derivation from `Syntax.ArgumentStructure.Alternation.passivization` and `ControlType`. -/

open Syntax.ArgumentStructure.Alternation

/-- Which TR-role serves as the controller, per @cite{chierchia-1984}'s CP.

    Subject control: A is the controller (the subject has property P).
    Object control: P is the controller (the object has property P).
    Raising/none: no semantic controller (the CP does not apply). -/
def controllerRole : ControlType → Option TRRole
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
open Fragments.English.Predicates.Verbal

-- ── Per-verb Chierchia class verification ──

/-- All control verbs in the Fragment are obligatory control in
    Chierchia's sense — they have a fixed, lexically determined
    controller and exhibit all six OC properties. -/

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

/-- "persuade" is obligatory control in Chierchia's system — it has
    a fixed controller (the object) and all six OC properties. The
    subject/object distinction does not affect the obligatory class. -/
theorem persuade_obligatory :
    derivedChierchiaClass persuade.toVerbCore = some .obligatory := rfl
theorem force_obligatory :
    derivedChierchiaClass force.toVerbCore = some .obligatory := rfl

/-- "want" is obligatory control in Chierchia's system — the subject
    is the fixed controller. Despite being an attitude verb, it has
    all six OC properties. (Contrast Landau, who classifies "want"
    as logophoric because of its attitude status.) -/
theorem want_obligatory :
    derivedChierchiaClass want.toVerbCore = some .obligatory := rfl
theorem hope_obligatory :
    derivedChierchiaClass hope.toVerbCore = some .obligatory := rfl
theorem promise_obligatory :
    derivedChierchiaClass promise.toVerbCore = some .obligatory := rfl

-- ── Passivizability: derived agrees with stipulated ──

/-- "try" (subject control): CP blocks passivization, stipulated not passivizable. -/
theorem try_passivizability_derived :
    derivedPassivizable try_.toVerbCore.controlType
    = try_.toVerbCore.passivizable := rfl

/-- "persuade" (object control): CP allows passivization, stipulated passivizable. -/
theorem persuade_passivizability_derived :
    derivedPassivizable persuade.toVerbCore.controlType
    = persuade.toVerbCore.passivizable := rfl

/-- "force" (object control): CP allows passivization, stipulated passivizable. -/
theorem force_passivizability_derived :
    derivedPassivizable force.toVerbCore.controlType
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

@cite{chierchia-1984} and @cite{landau-2015} cut the control verb
space differently:

- **Chierchia**: ALL verbs with the CP are obligatory control, regardless
  of attitude status. The CP is a meaning postulate that applies uniformly.
  The subject/object and attitude/non-attitude distinctions are orthogonal.
- **Landau**: attitude verbs (want, hope, promise, persuade) are logophoric
  (perspectival coordinate needed), non-attitude verbs (try, manage, force)
  are predicative.

The systematic divergence: Chierchia → obligatory → predicative for
ALL control verbs, while Landau → logophoric for attitude verbs. The
theories agree on non-attitude verbs (both predicative) and diverge
precisely on attitude verbs. -/

open Landau2015

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

/-! ### Non-attitude verbs: Chierchia and Landau agree

For verbs without an attitude builder (try, manage, begin, stop,
force, fail), both systems classify them as predicative control. -/

theorem try_agrees :
    (derivedChierchiaClass try_.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier try_.toVerbCore := rfl

theorem manage_agrees :
    (derivedChierchiaClass manage.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier manage.toVerbCore := rfl

theorem force_agrees :
    (derivedChierchiaClass force.toVerbCore).map chierchiaToLandauTier
    = Landau2015.derivedControlTier force.toVerbCore := rfl

/-! ### Attitude verbs: systematic divergence

For verbs with an attitude builder (want, hope, promise, persuade),
the two systems diverge: Chierchia classifies them as obligatory
(→ predicative), while Landau classifies them as logophoric.

This is a genuine theoretical disagreement: Chierchia groups by
entailment structure (all verbs with the CP are treated uniformly),
Landau groups by attitude status (attitude verbs introduce a
perspectival coordinate that changes the control mechanism). -/

theorem want_diverges :
    (derivedChierchiaClass want.toVerbCore).map chierchiaToLandauTier = some .predicative
    ∧ Landau2015.derivedControlTier want.toVerbCore = some .logophoric :=
  ⟨rfl, rfl⟩

theorem hope_diverges :
    (derivedChierchiaClass hope.toVerbCore).map chierchiaToLandauTier = some .predicative
    ∧ Landau2015.derivedControlTier hope.toVerbCore = some .logophoric :=
  ⟨rfl, rfl⟩

theorem promise_diverges :
    (derivedChierchiaClass promise.toVerbCore).map chierchiaToLandauTier = some .predicative
    ∧ Landau2015.derivedControlTier promise.toVerbCore = some .logophoric :=
  ⟨rfl, rfl⟩

theorem persuade_diverges :
    (derivedChierchiaClass persuade.toVerbCore).map chierchiaToLandauTier = some .predicative
    ∧ Landau2015.derivedControlTier persuade.toVerbCore = some .logophoric :=
  ⟨rfl, rfl⟩

end CrossSystemVerification

end Chierchia1984
