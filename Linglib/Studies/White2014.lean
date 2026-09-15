import Linglib.Syntax.Category.Verb.Complement.Basic
import Linglib.Data.Examples.White2014

/-!
# White (2014): Factive-Implicatives and Modalized Complements

This file formalizes [white-2014]'s account of *remember* and *forget*, factive with a finite
complement and implicative with a nonfinite one. The verbs are always factive: the nonfinite
complement contains a covert root modal ([bhatt-1999]), so *remembered to take the trash out*
presupposes that John was supposed to, as *remembered that he was supposed to* does
(`Modalized`). Implicativity is an actuality entailment from restructuring: the attitude
combines with the modalized VP as a property of events, the restructuring rule binds the
attitude's own event and passes the matrix event to the VP (`restructure`), and matrix aspect
then binds that event in the evaluation world, so a remembered VP-event is actual
(`actuality`) and a not-remembered one is not (`negated_actuality`). A finite complement has
its own event binder, which shields the embedded event from the matrix one: *remembered that
he was supposed to* leaves the actuality of the event open (`exists_finite_not_actual`).

## Implementation notes

The attitude is Hintikkan over a memory accessibility relation and the modal is a necessity
over the best worlds of an ordering source, both with event arguments ([kratzer-1996],
[hacquard-2009]); the poster's auxiliary assumption, that an event occurring in two worlds is
described by the same predicates in both, is the hypothesis `EventDescriptionPreserved`, and
events are taken to persist into the worlds accessible from one where they occur. The
proceedings paper was not available; the analysis follows the author's NELS 44 poster, and
the example numbers are the poster's.

## References

* [white-2014]
* [bhatt-1999]
* [hacquard-2009]
* [karttunen-1971]
* [kratzer-1996]
-/

namespace White2014

/-! ### The covert modal -/

/-- Which complements contain a covert root modal: the nonfinite ones. -/
def Modalized (ct : ComplementType) : Prop := ct.isFinite = false

instance : DecidablePred Modalized := λ _ => inferInstanceAs (Decidable (_ = _))

/-- The finite clause and the infinitive of (1) and (2). -/
theorem modalized_infinitival_not_finite :
    Modalized .infinitival ∧ ¬ Modalized .finiteClause := by
  decide

/-! ### Attitude, modal, and restructuring -/

section Semantics

variable {W E X : Type*}

/-- The Hintikkan attitude with an event argument (9): the proposition holds in every world
the attitude event gives access to. -/
def attitude (mem : X → E → W → Set W) (p : W → Prop) (x : X) (e : E) (w : W) : Prop :=
  ∀ w' ∈ mem x e w, p w'

/-- The root necessity modal with an event argument (10): the property of events holds of
the event in every best world. -/
def mod (best : W → Set W) (f : E → W → Prop) (e : E) (w : W) : Prop :=
  ∀ w' ∈ best w, f e w'

/-- The restructuring rule: an attitude meeting a property of events binds its own event and
hands the matrix event to the property. -/
def restructure (att : (W → Prop) → X → E → W → Prop) (f : E → W → Prop) (x : X)
    (e : E) (w : W) : Prop :=
  ∃ e', att (f e) x e' w

/-- (11): *remember* restructured with the modalized VP. -/
theorem restructure_attitude_mod (mem : X → E → W → Set W) (best : W → Set W)
    (vp : E → W → Prop) (x : X) (e : E) (w : W) :
    restructure (attitude mem) (mod best vp) x e w ↔
      ∃ e', ∀ w' ∈ mem x e' w, ∀ w'' ∈ best w', vp e w'' :=
  Iff.rfl

variable (occurs : E → W → Prop)

/-- (12): *John remembered to VP*, with matrix aspect binding the VP-event in the evaluation
world. -/
def rememberedTo (mem : X → E → W → Set W) (best : W → Set W) (vp : E → W → Prop)
    (x : X) (w : W) : Prop :=
  ∃ e, occurs e w ∧ restructure (attitude mem) (mod best vp) x e w

/-- (14): *John remembered that he should VP*, whose complement binds its own event. -/
def rememberedThat (mem : X → E → W → Set W) (best : W → Set W) (vp : E → W → Prop)
    (x : X) (e : E) (w : W) : Prop :=
  attitude mem (λ w' => ∀ w'' ∈ best w', ∃ e', vp e' w'') x e w

/-- Preservation of event description: an event occurring in two worlds satisfies the same
predicate in both. -/
def EventDescriptionPreserved (vp : E → W → Prop) : Prop :=
  ∀ e w w', occurs e w → occurs e w' → vp e w → vp e w'

/-- Events persist into the accessible worlds. -/
def Persists (acc : W → Set W) : Prop := ∀ e w w', occurs e w → w' ∈ acc w → occurs e w'

variable {occurs} {mem : X → E → W → Set W} {best : W → Set W} {vp : E → W → Prop}

/-- The positive actuality entailment: a remembered VP-event is actual, given some remembered
best world for it to be described in. -/
theorem actuality (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs (λ w => ⋃ x, ⋃ e, mem x e w)) (hbest : Persists occurs best)
    (hne : ∀ x e w, ∃ w' ∈ mem x e w, (best w').Nonempty) {x : X} {w : W}
    (h : rememberedTo occurs mem best vp x w) : ∃ e, occurs e w ∧ vp e w := by
  obtain ⟨e, he, e', hatt⟩ := h
  obtain ⟨w', hw', w'', hw''⟩ := hne x e' w
  have hocc' : occurs e w' := hmem e w w' he (Set.mem_iUnion₂.mpr ⟨x, e', hw'⟩)
  exact ⟨e, he, hped e w'' w (hbest e w' w'' hocc' hw'') he (hatt w' hw' w'' hw'')⟩

/-- The negative actuality entailment: if John did not remember to VP there is no actual
VP-event, since such an event would persist into the remembered best worlds and be a
VP-event there, which is what remembering to VP says. -/
theorem negated_actuality [Nonempty E] (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs (λ w => ⋃ x, ⋃ e, mem x e w)) (hbest : Persists occurs best)
    {x : X} {w : W} (h : ¬ rememberedTo occurs mem best vp x w) :
    ¬ ∃ e, occurs e w ∧ vp e w := by
  rintro ⟨e, he, hvp⟩
  let e' : E := Classical.arbitrary E
  exact h ⟨e, he, e', λ w' hw' w'' hw'' =>
    hped e w w'' he (hbest e w' w'' (hmem e w w' he (Set.mem_iUnion₂.mpr ⟨x, e', hw'⟩)) hw'')
      hvp⟩

/-- No actuality entailment with a finite complement: the remembered obligation can hold
while no VP-event is actual. -/
theorem exists_finite_not_actual :
    ∃ (mem : Unit → Unit → Bool → Set Bool) (best : Bool → Set Bool)
      (vp : Unit → Bool → Prop) (occurs : Unit → Bool → Prop),
      rememberedThat mem best vp () () true ∧ ¬ ∃ e, occurs e true ∧ vp e true :=
  ⟨λ _ _ _ => {false}, λ _ => {false}, λ _ w => w = false, λ _ w => w = false,
    λ _ _ _ hw'' => ⟨(), hw''⟩, λ ⟨_, he, _⟩ => Bool.noConfusion he⟩

end Semantics

end White2014
