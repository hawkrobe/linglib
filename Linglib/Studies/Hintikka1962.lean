import Linglib.Discourse.Commitment.Frame

/-!
# Hintikka (1962): Doxastic indefensibility of Moore's sentence
@cite{hintikka-1962}

@cite{hintikka-1962} Ch. 4 §§4.5–4.10's analysis of Moore's paradox. The
sentence "p but I do not believe that p" (Hintikka's (8)) is not self-
contradictory — there are worlds where `p` holds while the speaker fails
to believe `p`. But its would-be-believed form `B_a (p ∧ ¬ B_a p)`
(Hintikka's (30)) is *indefensible* in any KD4 doxastic model: this is a
1-line specialisation of `Core.Logic.Intensional.boxR_not_moore` to the
agent-indexed belief accessibility of `CommitmentState`.
-/

namespace Hintikka1962

open Discourse.Commitment.Frame
open Core.Logic.Intensional (boxR_not_moore)

variable {W A : Type*}

/-- The Moore content for speaker `s` and proposition `p`: worlds where
    `p` holds and `s` does not believe `p`. Hintikka's (8). -/
def mooreContent (c : CommitmentState W A) (s : A) (p : Set W) : Set W :=
  { w | w ∈ p ∧ ¬ Believes c s p w }

/-- Doxastic indefensibility of a single propositional content for an
    agent in a given commitment state: `a` does not believe `P` at any
    world. Restricted to set-valued contents; Hintikka §4.8's general
    definition ranges over finite *sets of sentences*. -/
def DoxasticallyIndefensible (c : CommitmentState W A) (a : A) (P : Set W) : Prop :=
  ∀ w, ¬ Believes c a P w

/-- **The Moore-paradox theorem** (Hintikka §4.7): under KD4 belief
    (seriality + positive introspection), no agent can believe the Moore
    content at any world. -/
theorem mooreContent_doxasticallyIndefensible
    (c : CommitmentState W A) (a : A) (p : Set W) :
    DoxasticallyIndefensible c a (mooreContent c a p) :=
  fun w => boxR_not_moore (c.belief a) (c.belief_serial a) (c.belief_trans a)
    (fun v => v ∈ p) w

/-- **Performatory corollary** (state-theoretic restatement of
    Hintikka §4.10): under sincerity, no commitment state hosts a self-
    commitment to the Moore content. Hintikka's performatoriness claim
    is about the *act* of asserting; this is the resulting constraint on
    states a sincere assertion could leave behind. -/
theorem moore_no_sincere_model
    (c : CommitmentState W A) (hsin : Sincere c)
    (s b : A) (p : Set W) (w : W) :
    ¬ Committed c s b (mooreContent c s p) w := fun hcom =>
  mooreContent_doxasticallyIndefensible c s p w
    (committed_implies_believes_of_sincere hsin s b _ w hcom)

end Hintikka1962
