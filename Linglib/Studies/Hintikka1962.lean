import Linglib.Discourse.Commitment.Frame

/-!
# Hintikka (1962): Doxastic indefensibility of Moore's sentence
@cite{hintikka-1962}

@cite{hintikka-1962} Ch. 4 analysis of Moore's paradox. The sentence
"p but I do not believe that p" is not self-contradictory — there are
worlds where `p` holds while the speaker fails to believe `p`. But its
would-be-believed form `B_a (p ∧ ¬ B_a p)` is *indefensible* in any KD4
doxastic model: a 1-line specialisation of
`Core.Logic.Modal.box_not_moore` to the agent-indexed belief
accessibility of `CommitmentState`. The knowledge analogue specialises
the same substrate lemma to epistemic accessibility.
-/

namespace Hintikka1962

open Discourse.Commitment.Frame
open Core.Logic.Modal (box_not_moore AgentAccessRel IsSerial)
open Semantics.Modality.EpistemicLogic (knows)

variable {W A : Type*}

/-- The Moore content for speaker `s` and proposition `p`: worlds where
    `p` holds and `s` does not believe `p`. -/
def mooreContent (c : CommitmentState W A) (s : A) (p : Set W) : Set W :=
  { w | w ∈ p ∧ ¬ Believes c s p w }

/-- Doxastic indefensibility of a propositional content for an agent in
    a given commitment state: `a` does not believe `P` at any world.
    Restricted to set-valued contents; Hintikka §4.8's general
    definition ranges over finite *sets of sentences*. -/
def DoxasticallyIndefensible (c : CommitmentState W A) (a : A) (P : Set W) : Prop :=
  ∀ w, ¬ Believes c a P w

/-- **The Moore-paradox theorem**: under KD4 belief, no agent can
    believe the Moore content at any world. -/
theorem mooreContent_doxasticallyIndefensible
    (c : CommitmentState W A) (a : A) (p : Set W) :
    DoxasticallyIndefensible c a (mooreContent c a p) :=
  fun w => box_not_moore (c.belief a) (fun v => v ∈ p) w

/-- A two-world KD4 frame: every world treats only `false` as belief-
    accessible. Used as a witness for `true_mem_mooreContent`. -/
def mooreWitness : CommitmentState Bool Unit where
  belief _ _ v := v = false
  commitment _ _ _ _ := True
  interp _ := Set.univ
  belief_kd45 _ := { serial := fun _ => ⟨false, rfl⟩
                     trans := fun _ _ _ _ h => h
                     eucl := fun _ _ _ _ h => h }
  commitment_k4eucl _ _ := { trans := fun _ _ _ _ _ => trivial
                             eucl := fun _ _ _ _ _ => trivial }

/-- **Satisfiability of the Moore sentence**: with `p := {true}` over
    `mooreWitness`, the world `true` lies in `mooreContent`. The
    propositional content `p ∧ ¬B_a p` is consistent — contrast with
    `p ∧ ¬p`, which has no models; only the *believed* form fails. -/
theorem true_mem_mooreContent :
    true ∈ mooreContent mooreWitness () {true} :=
  ⟨rfl, fun h => Bool.false_ne_true (h false rfl)⟩

/-- **Epistemic analogue** (Hintikka §4.11): under KD4 knowledge,
    "p but I don't know whether p" is unknowable. Direct corollary of
    `box_not_moore` for `knows`. -/
theorem knowledge_unknowable
    {E : Type*} (Rs : AgentAccessRel W E) (i : E)
    [IsSerial (Rs i)] [IsTrans W (Rs i)]
    (p : W → Prop) (w : W) :
    ¬ knows Rs i (fun v => p v ∧ ¬ knows Rs i p v) w :=
  box_not_moore (Rs i) p w

/-- **Performatory corollary** (state-theoretic restatement of Hintikka
    §4.10): under sincerity, no commitment state hosts a self-commitment
    to the Moore content. Hintikka's performatoriness claim is about the
    *act* of asserting; this is the resulting constraint on states a
    sincere assertion could leave behind. -/
theorem not_committed_mooreContent_of_sincere
    (c : CommitmentState W A) (hsin : Sincere c)
    (s b : A) (p : Set W) (w : W) :
    ¬ Committed c s b (mooreContent c s p) w := fun hcom =>
  mooreContent_doxasticallyIndefensible c s p w
    (committed_implies_believes_of_sincere hsin s b _ w hcom)

end Hintikka1962
