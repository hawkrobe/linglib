import Mathlib.Data.Set.Basic
import Linglib.Core.Logic.Intensional.Defs
import Linglib.Core.Logic.Intensional.RestrictedModality
import Linglib.Semantics.Modality.EpistemicLogic

/-!
# Doxastic / Deontic Commitment Frame
@cite{hintikka-1962} @cite{stalnaker-1984}

Multi-relational Kripke frame for doxastic-deontic discourse logic:
per-agent belief accessibility (KD45 — @cite{hintikka-1962}) plus
pair-indexed commitment accessibility (K4 + Euclidean, **not**
serial — so commitment violations are expressible). The `Sincere`
and `Competent` frame conditions (@cite{stalnaker-1984}) bridge
commitment to belief.

## Main definitions

* `PairAccessRel W A` — pair-indexed deontic accessibility.
* `CommitmentState W A` — frame: belief + commitment + valuation +
  bundled per-agent KD45 and per-pair K4-Euclidean frame conditions.
* `Believes`, `Committed` — modal operators.
* `Sincere`, `Competent` — frame conditions linking belief and
  commitment.
* `committed_implies_believes_of_sincere` and corollaries —
  the @cite{hintikka-1962}/@cite{stalnaker-1984} transfer theorems.
-/

namespace Discourse.Commitment.Frame

open Core.Logic.Intensional (AccessRel AgentAccessRel IsKD45Frame IsK4EuclFrame
  IsEuclidean boxR diamondR boxR_K boxR_four)
open Semantics.Modality.EpistemicLogic (knows)

/-- Pair-indexed deontic accessibility: `commitment a b w v` means at
    `w`, the world `v` is among those satisfying everything `a` is
    committed-towards-`b` to. Genuinely ternary; no analogue in
    linglib's unary-belief substrate. -/
abbrev PairAccessRel (W A : Type*) := A → A → AccessRel W

/-- Multi-relational Kripke frame: belief (KD45) + commitment (K4 +
    Eucl., not serial) + atomic valuation. -/
structure CommitmentState (W : Type*) (A : Type*) where
  /-- Per-agent doxastic accessibility. -/
  belief : AgentAccessRel W A
  /-- Pair-indexed deontic accessibility. -/
  commitment : PairAccessRel W A
  /-- Atomic-proposition valuation. -/
  interp : String → Set W
  /-- Belief is KD45 (serial + transitive + euclidean) per agent. -/
  belief_kd45 : ∀ a, IsKD45Frame (belief a)
  /-- Commitment is K4-Euclidean (no seriality — violations are
      expressible) per pair. -/
  commitment_k4eucl : ∀ a b, IsK4EuclFrame (commitment a b)

namespace CommitmentState
variable {W : Type*} {A : Type*}

instance (c : CommitmentState W A) (a : A) : IsKD45Frame (c.belief a) :=
  c.belief_kd45 a

instance (c : CommitmentState W A) (a b : A) : IsK4EuclFrame (c.commitment a b) :=
  c.commitment_k4eucl a b

/-- The trivial state: every world doxastically/commitmentally
    accessible from every world; every atom true everywhere. -/
def trivial : CommitmentState W A where
  belief _ _ _ := True
  commitment _ _ _ _ := True
  interp _ := Set.univ
  belief_kd45 _ := { serial := fun w => ⟨w, _root_.trivial⟩
                     trans := fun _ _ _ _ _ => _root_.trivial
                     eucl := fun _ _ _ _ _ => _root_.trivial }
  commitment_k4eucl _ _ := { trans := fun _ _ _ _ _ => _root_.trivial
                             eucl := fun _ _ _ _ _ => _root_.trivial }

/-- `a`'s commitment-towards-`b` is empty — operationally, `a` is
    committed to a contradiction. -/
def commitmentEmpty (c : CommitmentState W A) (a b : A) : Prop :=
  ∀ w v, ¬ c.commitment a b w v

/-- Restrict `a`'s commitment-towards-`b` edges to π-targets;
    leave other edges unchanged. `O^c[π]_{a,b} = O^c_{a,b} ∩
    {(w, v) | v ∈ π}`. -/
def restrictCommitment (c : CommitmentState W A) (a b : A) (π : Set W) :
    CommitmentState W A where
  belief := c.belief
  commitment a' b' w v := c.commitment a' b' w v ∧ ((a' = a ∧ b' = b) → v ∈ π)
  interp := c.interp
  belief_kd45 := c.belief_kd45
  commitment_k4eucl a' b' :=
    { trans := by
        intro w v u hwv hvu
        refine ⟨IsTrans.trans w v u hwv.1 hvu.1, ?_⟩
        intro h; exact hvu.2 h
      eucl := by
        intro w v u hwv hwu
        refine ⟨IsEuclidean.eucl w v u hwv.1 hwu.1, ?_⟩
        intro h; exact hwu.2 h }

@[simp] theorem restrictCommitment_other
    (c : CommitmentState W A) (a b : A) (π : Set W) (a' b' : A)
    (h : ¬ (a' = a ∧ b' = b)) (w v : W) :
    (c.restrictCommitment a b π).commitment a' b' w v ↔ c.commitment a' b' w v := by
  simp only [restrictCommitment]
  exact ⟨fun ⟨hcom, _⟩ => hcom, fun hcom => ⟨hcom, fun hh => absurd hh h⟩⟩

@[simp] theorem restrictCommitment_belief
    (c : CommitmentState W A) (a b : A) (π : Set W) :
    (c.restrictCommitment a b π).belief = c.belief := rfl

@[simp] theorem restrictCommitment_interp
    (c : CommitmentState W A) (a b : A) (π : Set W) :
    (c.restrictCommitment a b π).interp = c.interp := rfl

end CommitmentState

/-! ### Modal operators -/

variable {W : Type*} {A : Type*}

/-- `a` believes `π` at `w`: every belief-accessible world from `w`
    lies in `π`. KD45 belief (Hintikka 1962). -/
def Believes (c : CommitmentState W A) (a : A) (π : Set W) (w : W) : Prop :=
  knows c.belief a (fun v => v ∈ π) w

theorem Believes_eq_boxR (c : CommitmentState W A) (a : A) (π : Set W) (w : W) :
    Believes c a π w ↔ boxR (c.belief a) (fun v => v ∈ π) w := Iff.rfl

/-- `a` committed towards `b` to `π` at `w`: every `O_{a,b}`-accessible
    world from `w` lies in `π`. K4 + Eucl. (Stalnaker 1984). -/
def Committed (c : CommitmentState W A) (a b : A) (π : Set W) (w : W) : Prop :=
  boxR (c.commitment a b) (fun v => v ∈ π) w

/-- Belief satisfies the 4 axiom (positive introspection). -/
theorem believes_four (c : CommitmentState W A) (a : A) (π : Set W) (w : W)
    (h : Believes c a π w) :
    Believes c a (fun v => Believes c a π v) w :=
  boxR_four (c.belief a) (fun v => v ∈ π) w h

/-- Commitment satisfies the 4 axiom. -/
theorem committed_four (c : CommitmentState W A) (a b : A) (π : Set W) (w : W)
    (h : Committed c a b π w) :
    Committed c a b (fun v => Committed c a b π v) w :=
  boxR_four (c.commitment a b) (fun v => v ∈ π) w h

/-! ### Frame conditions linking belief and commitment -/

/-- **Sincerity** (@cite{stalnaker-1984}): for every agent pair, belief
    is contained in commitment. "If you believe it, you act as if
    committed to it." -/
def Sincere (c : CommitmentState W A) : Prop :=
  ∀ x y w v, c.belief x w v → c.commitment x y w v

/-- **Competence** (@cite{stalnaker-1984}): for every pair `(x, y)`,
    `y`'s doxastically accessible worlds are also `x`-accessible.
    "`x` is well-informed about what `y` considers possible." -/
def Competent (c : CommitmentState W A) : Prop :=
  ∀ x y w v, c.belief y w v → c.belief x w v

/-- In a Sincerity-satisfying state, commitment entails belief.
    @cite{hintikka-1962} / @cite{stalnaker-1984} transfer, used as a
    lemma in @cite{van-der-leer-2026}. -/
theorem committed_implies_believes_of_sincere
    {c : CommitmentState W A} (h : Sincere c) (a b : A) (π : Set W) (w : W) :
    Committed c a b π w → Believes c a π w :=
  fun hcom v hbel => hcom v (h a b w v hbel)

/-- In a Competence-satisfying state, `a`'s belief entails `b`'s
    belief (@cite{van-der-leer-2026}). -/
theorem believes_a_implies_believes_b_of_competent
    {c : CommitmentState W A} (h : Competent c) (a b : A) (π : Set W) (w : W) :
    Believes c a π w → Believes c b π w :=
  fun hbel v hbelB => hbel v (h a b w v hbelB)

/-- Composed: Sincerity + Competence ⇒ `a`'s commitment-to-`b` of `π`
    entails `b`'s belief in `π`. The mediated CommonGround-update of
    @cite{bary-2025}, derived not stipulated (@cite{van-der-leer-2026}). -/
theorem committed_implies_addressee_believes_of_sincere_competent
    {c : CommitmentState W A} (hsin : Sincere c) (hcomp : Competent c)
    (a b : A) (π : Set W) (w : W) :
    Committed c a b π w → Believes c b π w :=
  fun hcom => believes_a_implies_believes_b_of_competent hcomp a b π w
    (committed_implies_believes_of_sincere hsin a b π w hcom)

/-! ### Refinement: information-narrowing preorder on commitment states -/

/-- `c'` strictly refines `c`: belief and commitment relations narrow,
    valuation is preserved, and the states are distinct. The substrate
    notion of "discourse progress" — any later state in a coherent
    conversation refines the earlier. -/
def CooperativeExt (c c' : CommitmentState W A) : Prop :=
  (∀ a w v, c'.belief a w v → c.belief a w v) ∧
  (∀ a b w v, c'.commitment a b w v → c.commitment a b w v) ∧
  (c.interp = c'.interp) ∧
  c ≠ c'

/-- Reflexive closure of `CooperativeExt`. -/
def CooperativeExtRefl (c c' : CommitmentState W A) : Prop :=
  c = c' ∨ CooperativeExt c c'

theorem cooperativeExtRefl_refl (c : CommitmentState W A) :
    CooperativeExtRefl c c := Or.inl rfl

theorem not_cooperativeExt_self (c : CommitmentState W A) :
    ¬ CooperativeExt c c := fun h => h.2.2.2 rfl

/-! ### Mutual commitment (per-state) -/

/-- All agent pairs are mutually committed to `π` at `w`. The deontic
    analogue of `EpistemicLogic.commonBelief`. -/
def MutuallyCommittedAt (c : CommitmentState W A) (π : Set W) (w : W) : Prop :=
  ∀ a b, Committed c a b π w

end Discourse.Commitment.Frame
