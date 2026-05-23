import Linglib.Theories.Dialogue.SAL.Frame
import Linglib.Core.Logic.Intensional.RestrictedModality
import Linglib.Semantics.Modality.EpistemicLogic

/-!
# SAL Modal Operators
@cite{van-der-leer-2026}

van der Leer 2026 Definition 3 (state satisfaction): the modal
operators `B_a π` (agent `a` believes `π`) and `C_{a,b} π` (agent `a`
is committed towards `b` to `π`) interpret box-style over the
respective accessibility relations of a `CommitmentState`.

This file is a thin presentational layer:

* `Believes c a π w` is `EpistemicLogic.knows c.belief a (· ∈ π) w`
  — the existing multi-agent epistemic operator from
  `Semantics/Modality/EpistemicLogic.lean`. Using `knows`
  via SAL is a doxastic interpretation: KD45 belief, not S5 knowledge.
* `Committed c a b π w` is `boxR (c.commitment a b) (· ∈ π) w` — the
  pair-indexed analogue. No existing operator in the substrate covers
  the pair-indexed deontic case (commitment is genuinely ternary), so
  this is the new SAL-specific contribution.

The existing `Core.Logic.Intensional.RestrictedModality` API gives us
the K/T/D/4/B axiom theorems for free, and the SAL-specific frame
conditions (`belief_trans/eucl/serial`, `commitment_trans/eucl`) feed
directly into them.

Sincerity (Def 5.1: `B_x ⊆ O_{x,y}`) and Competence (Def 5.2: `B_y ⊆
B_x`) are recorded as Prop-valued conditions on commitment states.
Together they yield Theorem 26: under Sincerity+Competence,
commitment transfers to belief in the addressee — the *mediated CG
update* @cite{bary-2025} demanded.

## Deferred consolidation

`Theories/Dialogue/CommitmentSpace.lean` houses Krifka 2015's
non-Kripke commitment-space substrate (states are lists of indexed
commitments). `Theories/Discourse/EvidentialIllocution.lean` houses
the Faller assert/present pair as a record. Both should eventually
be presented as projections of the SAL substrate; this is queued for
a follow-up consolidation pass once the SAL theorem battery is
established.
-/

namespace Dialogue.SAL

open Core.Logic.Intensional (boxR diamondR boxR_K boxR_four)
open Semantics.Modality.EpistemicLogic (knows)

variable {W : Type*} {A : Type*}

/-- Agent `a` believes `π` at world `w` in state `c`. Defined as the
    existing `EpistemicLogic.knows` (which is itself `boxR (Rs i) φ w`)
    consumed with `c.belief` as the `AgentAccessRel`. SAL's doxastic
    reading of the operator (KD45 belief vs. S5 knowledge) is reflected
    in the frame conditions on `c.belief` (transitive + Euclidean +
    serial — KD45). -/
def Believes (c : CommitmentState W A) (a : A) (π : Set W) (w : W) : Prop :=
  knows c.belief a (fun v => v ∈ π) w

theorem Believes_eq_boxR (c : CommitmentState W A) (a : A) (π : Set W) (w : W) :
    Believes c a π w ↔ boxR (c.belief a) (fun v => v ∈ π) w := Iff.rfl

/-- Agent `a` is committed towards `b` to `π` at world `w` in state `c`
    iff every `O_{a,b}`-accessible world from `w` lies in `π`.

    Definitionally `boxR (c.commitment a b) (fun v => v ∈ π) w`. -/
def Committed (c : CommitmentState W A) (a b : A) (π : Set W) (w : W) : Prop :=
  boxR (c.commitment a b) (fun v => v ∈ π) w

/-- Belief is K4D — the **4 axiom** holds via `belief_trans`.
    Derives from the substrate's `boxR_four` applied to the unfolded
    `Believes`. -/
theorem believes_four (c : CommitmentState W A) (a : A) (π : Set W) (w : W)
    (h : Believes c a π w) :
    Believes c a (fun v => Believes c a π v) w :=
  boxR_four (c.belief a) (c.belief_trans a) (fun v => v ∈ π) w h

/-- Commitment is K4 — the **4 axiom** holds via `commitment_trans`. -/
theorem committed_four (c : CommitmentState W A) (a b : A) (π : Set W) (w : W)
    (h : Committed c a b π w) :
    Committed c a b (fun v => Committed c a b π v) w :=
  boxR_four (c.commitment a b) (c.commitment_trans a b) (fun v => v ∈ π) w h

/-- van der Leer 2026 Definition 5.1: state `c` satisfies **Sincerity**
    iff every belief-accessible world (for any agent) is also
    commitment-accessible (for that agent towards anyone). Operationally:
    if you believe it, you act as if you're committed to it. -/
def Sincere (c : CommitmentState W A) : Prop :=
  ∀ x y w v, c.belief x w v → c.commitment x y w v

/-- van der Leer 2026 Definition 5.2: state `c` satisfies **Competence**
    iff for every (x, y), every world `y` finds doxastically possible
    is also one `x` finds doxastically possible. Operationally: the
    speaker is well-informed on what the addressee considers a live
    possibility. -/
def Competent (c : CommitmentState W A) : Prop :=
  ∀ x y w v, c.belief y w v → c.belief x w v

/-! ### § Headline modal theorems

These pre-stage the full SAL theorem battery in
`Theories/Dialogue/SAL/Theorems.lean`; here we prove the
sincerity-and-competence transfer at the level of states, before
discourse-update machinery is in scope.
-/

/-- van der Leer 2026 Theorem 26.1: in a Sincerity-satisfying state, a
    commitment of `a` (towards anyone `b`) entails `a`'s belief.

    The proof uses the abstract observation that if `R₁ ⊆ R₂`, then
    `boxR R₂ p` entails `boxR R₁ p` (box is anti-monotone in the
    accessibility relation). Sincerity says `B_a ⊆ O_{a,b}` so
    `Committed = boxR O_{a,b}` entails `Believes = boxR B_a`. -/
theorem committed_implies_believes_of_sincere
    {c : CommitmentState W A} (h : Sincere c) (a b : A) (π : Set W) (w : W) :
    Committed c a b π w → Believes c a π w :=
  fun hcom v hbel => hcom v (h a b w v hbel)

/-- van der Leer 2026 Theorem 26.2: in a Competence-satisfying state,
    `a`'s belief entails `b`'s belief (for the addressee whose beliefs
    `a` is competent on). -/
theorem believes_a_implies_believes_b_of_competent
    {c : CommitmentState W A} (h : Competent c) (a b : A) (π : Set W) (w : W) :
    Believes c a π w → Believes c b π w :=
  fun hbel v hbelB => hbel v (h a b w v hbelB)

/-- van der Leer 2026 Theorem 26.3 (composed): in a state satisfying
    BOTH Sincerity and Competence, `a`'s commitment to `b` of `π`
    entails `b`'s belief in `π`. The mediated common-ground update
    @cite{bary-2025} demanded — derived, not stipulated. -/
theorem committed_implies_addressee_believes_of_sincere_competent
    {c : CommitmentState W A}
    (hsin : Sincere c) (hcomp : Competent c)
    (a b : A) (π : Set W) (w : W) :
    Committed c a b π w → Believes c b π w :=
  fun hcom => believes_a_implies_believes_b_of_competent hcomp a b π w
    (committed_implies_believes_of_sincere hsin a b π w hcom)

end Dialogue.SAL
