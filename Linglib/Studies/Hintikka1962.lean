import Linglib.Discourse.Commitment.Frame

/-!
# Hintikka (1962): Doxastic indefensibility of Moore's sentence
@cite{hintikka-1962}

@cite{hintikka-1962} Ch. 4 §§4.5–4.10's analysis of Moore's paradox.
The sentence "p but I do not believe that p" (Hintikka's (8)) is not
self-contradictory as a proposition — there can be worlds where p
holds while the speaker doesn't believe p. But its would-be-believed
form, `B_a(p ∧ ¬B_a p)` (Hintikka's (30)), is *indefensible* in any
KD45 doxastic model. The reductio (Hintikka §4.7 (33)–(39)) uses
(C.BB*) — positive introspection — exactly the 4-axiom we already
have as `believes_four`.

Hintikka's notion of *doxastic indefensibility* (§4.8) is the
substrate-level concept: a content `P` is doxastically indefensible
for agent `a` iff no commitment state admits `a` as believing `P`.
-/

namespace Hintikka1962

open Discourse.Commitment.Frame

variable {W A : Type*}

/-- The Moore content for speaker `s` and proposition `p`: worlds where
    `p` holds and `s` does not believe `p`. Hintikka's (8). -/
def mooreContent (c : CommitmentState W A) (s : A) (p : Set W) : Set W :=
  { w | w ∈ p ∧ ¬ Believes c s p w }

/-- **Doxastic indefensibility** (Hintikka §4.8) of a content for an
    agent in a given commitment state: agent `a` does not believe `P`
    at any world. -/
def DoxasticallyIndefensible (c : CommitmentState W A) (a : A) (P : Set W) : Prop :=
  ∀ w, ¬ Believes c a P w

/-- **The Moore-paradox theorem** (Hintikka §4.7 (33)–(39)): under
    KD45 belief, no agent can believe the Moore content at any world.

    Reductio: from `B_a(p ∧ ¬B_a p)` we get `B_a p` (the box distributes
    over the first conjunct) and `B_a ¬B_a p` (the second). Positive
    introspection (`believes_four` = Hintikka's (C.BB*)) on the first
    yields `B_a B_a p`; seriality (KD45 D-axiom) picks a belief-
    accessible world `v` where both `B_a p v` and `¬B_a p v` hold.
    Contradiction. -/
theorem moore_unbelievable
    (c : CommitmentState W A) (a : A) (p : Set W) (w : W) :
    ¬ Believes c a (mooreContent c a p) w := by
  intro hbel
  -- Speaker believes p: first conjunct propagates through the box.
  have hbel_p : Believes c a p w := fun v hv => (hbel v hv).1
  -- Positive introspection: speaker believes that they believe p.
  have hbel_bel_p : Believes c a { v | Believes c a p v } w :=
    believes_four c a p w hbel_p
  -- Seriality: pick a belief-accessible world.
  obtain ⟨v, hv⟩ := c.belief_serial a w
  -- At v: ¬ Believes c a p v (from mooreContent) ∧ Believes c a p v (from 4).
  exact (hbel v hv).2 (hbel_bel_p v hv)

/-- The Moore content is doxastically indefensible (§4.8 in Hintikka's
    generalisation of §4.7). Restatement of `moore_unbelievable`. -/
theorem mooreContent_doxasticallyIndefensible
    (c : CommitmentState W A) (a : A) (p : Set W) :
    DoxasticallyIndefensible c a (mooreContent c a p) :=
  fun w => moore_unbelievable c a p w

/-- **Performatory consequence** (Hintikka §4.10): under sincerity, no
    commitment state can host a self-commitment to the Moore content.
    Asserting "p but I don't believe p" commits the speaker (by
    sincerity) to believing the Moore content — which is impossible. -/
theorem moore_no_sincere_model
    (c : CommitmentState W A) (hsin : Sincere c)
    (s b : A) (p : Set W) (w : W) :
    ¬ Committed c s b (mooreContent c s p) w := by
  intro hcom
  exact moore_unbelievable c s p w
    (committed_implies_believes_of_sincere hsin s b _ w hcom)

end Hintikka1962
