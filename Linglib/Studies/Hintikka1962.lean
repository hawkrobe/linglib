import Linglib.Discourse.Commitment.Frame

/-!
# Hintikka (1962): Knowledge and Belief

This file formalizes [hintikka-1962]'s analysis of Moore's sentence, "p but I do not believe
that p", in the doxastic logic of Chapter 4. The sentence is consistent,
`true_mem_mooreContent` exhibiting a model in which it holds, but its believed form is not:
`box_not_moore` shows that no world of a serial transitive frame satisfies the belief that p
holds and is not believed, and `mooreContent_doxasticallyIndefensible` states this as the
doxastic indefensibility of the sentence's content for any agent of a `Commitment.Frame`, the
book's notion restricted to propositional contents. The same reductio gives the knowledge
analogue, that one cannot know that p holds and is unknown (`knowledge_unknowable`), and,
under sincerity, that no assertion leaves a commitment to the Moore content behind, the
state-theoretic residue of the book's account of the sentence as a performatory rather than a
logical failure.

## Implementation notes

* Indefensibility is stated for a set of worlds where the book defines it over finite sets of
  sentences.

## References

* [hintikka-1962]
-/

namespace Hintikka1962

open Commitment
open ModalLogic (box box_four IsSerial)
open ModalLogic.Epistemic (knows)

variable {W A : Type*}

/-- The Moore reductio: no world satisfies `□(p ∧ ¬□p)` over a serial transitive relation.
The content is satisfiable; boxing it is not. -/
theorem box_not_moore {R : W → W → Prop} {p : W → Prop} {w : W}
    [hS : IsSerial R] [IsTrans W R] :
    ¬ box R (λ v => p v ∧ ¬ box R p v) w := λ h =>
  have ⟨v, hv⟩ := hS.serial w
  (h v hv).2 (box_four (λ u hu => (h u hu).1) v hv)

/-- The Moore content for the speaker `s` and the proposition `p`: the worlds where `p` holds
and `s` does not believe `p`. -/
def mooreContent (c : Frame W A) (s : A) (p : Set W) : Set W :=
  { w | w ∈ p ∧ ¬ c.Believes s p w }

/-- Doxastic indefensibility of a content for an agent in a commitment frame: the agent
believes it at no world. -/
def DoxasticallyIndefensible (c : Frame W A) (a : A) (P : Set W) : Prop :=
  ∀ w, ¬ c.Believes a P w

/-- Under KD4 belief no agent can believe the Moore content at any world. -/
theorem mooreContent_doxasticallyIndefensible
    (c : Frame W A) (a : A) (p : Set W) :
    DoxasticallyIndefensible c a (mooreContent c a p) :=
  λ _ => box_not_moore

/-- A two-world KD4 frame in which every world treats only `false` as belief-accessible. -/
def mooreWitness : Frame Bool Unit where
  belief _ _ v := v = false
  commitment _ _ _ _ := True
  belief_kd45 _ := { serial := λ _ => ⟨false, rfl⟩
                     trans := λ _ _ _ _ h => h
                     eucl := λ _ _ _ _ h => h }
  commitment_k45 _ _ := { trans := λ _ _ _ _ _ => trivial
                          eucl := λ _ _ _ _ _ => trivial }

/-- The Moore sentence is satisfiable: with `p := {true}` over `mooreWitness`, the world `true`
lies in the Moore content. Only the believed form fails. -/
theorem true_mem_mooreContent :
    true ∈ mooreContent mooreWitness () {true} :=
  ⟨rfl, λ h => Bool.false_ne_true (h false rfl)⟩

/-- The knowledge analogue: under KD4 knowledge, "p but I don't know whether p" cannot be
known. -/
theorem knowledge_unknowable
    {E : Type*} (Rs : E → W → W → Prop) (i : E)
    [IsSerial (Rs i)] [IsTrans W (Rs i)]
    (p : W → Prop) (w : W) :
    ¬ knows Rs i (λ v => p v ∧ ¬ knows Rs i p v) w :=
  box_not_moore

/-- Under sincerity no commitment state hosts a self-commitment to the Moore content: the
constraint on states that the book's performatory account of asserting the sentence leaves
behind. -/
theorem not_committed_mooreContent_of_sincere
    (c : Frame W A) (hsin : c.Sincere)
    (s b : A) (p : Set W) (w : W) :
    ¬ c.Committed s b (mooreContent c s p) w := λ hcom =>
  mooreContent_doxasticallyIndefensible c s p w
    (hsin.believes_of_committed hcom)

end Hintikka1962
