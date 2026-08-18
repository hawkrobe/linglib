import Linglib.Semantics.Presupposition.Basic
import Linglib.Features.Attitudes
import Linglib.Discourse.SpeechAct

/-!
# Doxastic attitude semantics

Accessibility-based semantics for doxastic attitude verbs (*believe*,
*know*, *think*) in the tradition of [hintikka-1962]: `R x w w'` reads
"`w'` is compatible with what `x` believes/knows in `w`", and
⟦x believes p⟧(w) is the universal modal over accessible worlds —
`BoxAt`, with `DiamondAt` its existential dual, both quantifying over a
finite `worlds` list as the decidable rendering.

A `DoxasticPredicate` bundles the accessibility relation with
veridicality and opacity. Its proposition-taking semantics
`HoldsAt` conjoins a veridicality check (`VeridicalityHolds`: veridical
verbs require the complement at the evaluation world,
`veridical_entails_complement`) with the universal modal, and
`toPartialProp` exposes the same content as a
`Semantics.Presupposition.PartialProp` — presupposition = veridicality
check, assertion = modal — connecting doxastic verbs to the projection
infrastructure. `HoldsAtQuestion` is the [karttunen-1977]
question-taking semantics: knowing a question is knowing a true answer.
`believeTemplate`/`knowTemplate`/`thinkTemplate` are the standard
instantiations, and `doxastic_k_axiom` records closure under known
implication.

Opacity: `SubstitutionMayFail` states that an opaque predicate can
distinguish co-extensional complements, and `DeDicto`/`DeRe` give the
two quantifier construals of an embedded indefinite. `psychMode` maps
veridicality to [searle-1983]'s psychological mode: veridical attitudes
are perception-like (the world must cause the state), non-veridical
ones belief-like.

The presuppositional typology of doxastic verbs ([glass-2025]) lives in
`Studies/Glass2025.lean`; the causal derivation of the contrafactive
gap ([roberts-ozyildiz-2025]) in `Studies/RobertsOzyildiz2025.lean`;
embedded scalar implicature ([goodman-stuhlmuller-2013]) in
`Studies/GoodmanStuhlmuller2013.lean`.
-/

namespace Doxastic

open Features (Veridicality)
export Features (Veridicality)

variable {W E : Type*}

/-! ### Accessibility modals -/

/-- Universal modal: `BoxAt R agent w worlds p` iff `p` holds at every
    accessible world in `worlds`. -/
def BoxAt (R : E → W → W → Prop) (agent : E) (w : W)
    (worlds : List W) (p : W → Prop) : Prop :=
  ∀ w' ∈ worlds, R agent w w' → p w'

/-- Existential modal: `DiamondAt R agent w worlds p` iff `p` holds at some
    accessible world in `worlds`. -/
def DiamondAt (R : E → W → W → Prop) (agent : E) (w : W)
    (worlds : List W) (p : W → Prop) : Prop :=
  ∃ w' ∈ worlds, R agent w w' ∧ p w'

instance (R : E → W → W → Prop) [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) (p : W → Prop) [DecidablePred p] :
    Decidable (BoxAt R agent w worlds p) :=
  inferInstanceAs (Decidable (∀ w' ∈ worlds, _))

instance (R : E → W → W → Prop) [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) (p : W → Prop) [DecidablePred p] :
    Decidable (DiamondAt R agent w worlds p) :=
  inferInstanceAs (Decidable (∃ w' ∈ worlds, _))

/-- Closure under known implication — the K axiom: if the agent
    believes `p` and believes `p → q`, the agent believes `q`. -/
theorem doxastic_k_axiom (R : E → W → W → Prop) (agent : E)
    (p q : W → Prop) (w : W) (worlds : List W)
    (hp : BoxAt R agent w worlds p)
    (hpq : BoxAt R agent w worlds (fun w' => p w' → q w')) :
    BoxAt R agent w worlds q :=
  fun w' hw' hR => hpq w' hw' hR (hp w' hw' hR)

/-! ### Doxastic predicates -/

/-- `VeridicalityHolds v p w` is the veridicality check: veridical
    verbs require `p w`; non-veridical verbs require nothing. -/
def VeridicalityHolds (v : Veridicality) (p : W → Prop) (w : W) : Prop :=
  match v with
  | .veridical => p w
  | .nonVeridical => True

instance (v : Veridicality) (p : W → Prop) [DecidablePred p] (w : W) :
    Decidable (VeridicalityHolds v p w) := by
  cases v <;> simp [VeridicalityHolds] <;> infer_instance

/-- A doxastic attitude predicate: an accessibility relation bundled
    with veridicality and opacity. -/
structure DoxasticPredicate (W E : Type*) where
  /-- Name of the predicate. -/
  name : String
  /-- Accessibility relation. -/
  access : E → W → W → Prop
  /-- Veridicality (veridical or not). -/
  veridicality : Veridicality
  /-- Does it create an opaque context (substitution failures)? -/
  createsOpaqueContext : Bool := true

/-- `V.HoldsAt agent p w worlds` iff the veridicality check passes at
    `w` and `p` holds at every accessible world:
    ⟦x V that p⟧(w) = VeridicalityHolds ∧ BoxAt. -/
def DoxasticPredicate.HoldsAt (V : DoxasticPredicate W E) (agent : E)
    (p : W → Prop) (w : W) (worlds : List W) : Prop :=
  VeridicalityHolds V.veridicality p w ∧ BoxAt V.access agent w worlds p

instance (V : DoxasticPredicate W E) [∀ a w w', Decidable (V.access a w w')]
    (agent : E) (p : W → Prop) [DecidablePred p] (w : W) (worlds : List W) :
    Decidable (V.HoldsAt agent p w worlds) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Veridical predicates entail their complement: if `x` knows `p` at
    `w`, then `p w`. -/
theorem veridical_entails_complement (V : DoxasticPredicate W E)
    (hV : V.veridicality = .veridical) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) (holds : V.HoldsAt agent p w worlds) : p w := by
  unfold DoxasticPredicate.HoldsAt at holds
  simp only [hV, VeridicalityHolds] at holds
  exact holds.1

open Semantics.Presupposition in
/-- The predicate application as a `PartialProp`: presupposition =
    veridicality check, assertion = universal modal. `HoldsAt` is the
    conjunction of the two fields. -/
def DoxasticPredicate.toPartialProp (V : DoxasticPredicate W E)
    (agent : E) (p : W → Prop) (worlds : List W) : PartialProp W :=
  { presup := fun w => VeridicalityHolds V.veridicality p w
  , assertion := fun w => BoxAt V.access agent w worlds p }

/-- `HoldsAtQuestion`: the [karttunen-1977] question-taking semantics —
    ⟦x knows Q⟧(w) = some true answer in `Q` is known (for
    non-veridical predicates the truth requirement is dropped). -/
def DoxasticPredicate.HoldsAtQuestion (V : DoxasticPredicate W E)
    (agent : E) (Q : (W → Prop) → Prop) (w : W) (worlds : List W)
    (answers : List (W → Prop)) : Prop :=
  ∃ p ∈ answers,
    Q p ∧ VeridicalityHolds V.veridicality p w ∧
    BoxAt V.access agent w worlds p

/-! ### Standard templates -/

/-- Abstract *believe*: non-veridical, opaque. -/
def believeTemplate (R : E → W → W → Prop) : DoxasticPredicate W E :=
  { name := "believe", access := R, veridicality := .nonVeridical }

/-- Abstract *know*: veridical, opaque. -/
def knowTemplate (R : E → W → W → Prop) : DoxasticPredicate W E :=
  { name := "know", access := R, veridicality := .veridical }

/-- Abstract *think*: non-veridical, opaque. -/
def thinkTemplate (R : E → W → W → Prop) : DoxasticPredicate W E :=
  { name := "think", access := R, veridicality := .nonVeridical }

/-! ### Opacity and construals -/

/-- An opaque predicate can distinguish co-extensional complements:
    some `p`, `q` agree at `w` but embed differently. -/
def SubstitutionMayFail (V : DoxasticPredicate W E) : Prop :=
  V.createsOpaqueContext = true →
  ∃ (agent : E) (p q : W → Prop) (w : W) (worlds : List W),
    (p w ↔ q w) ∧ p ≠ q ∧
    ¬ (V.HoldsAt agent p w worlds ↔ V.HoldsAt agent q w worlds)

/-- De re construal: the quantifier scopes over the attitude —
    some individual in the domain is believed to satisfy the
    predicate. The de dicto construal, with the quantifier under the
    attitude, is `HoldsAt` applied to the existential complement. -/
def DeRe {D : Type*} (V : DoxasticPredicate W E) (agent : E)
    (predicate : D → W → Prop) (domain : List D)
    (w : W) (worlds : List W) : Prop :=
  ∃ x ∈ domain, V.HoldsAt agent (predicate x) w worlds

/-! ### Psychological mode -/

/-- [searle-1983]'s psychological mode from veridicality: veridical
    attitudes are perception-like (the world must cause the state);
    non-veridical attitudes are belief-like (satisfaction requires only
    that the content match reality). -/
def psychMode : Veridicality → PsychMode
  | .veridical => .perception
  | .nonVeridical => .belief

end Doxastic
