import Mathlib.Order.Basic
import Linglib.Discourse.Commitment.Frame

/-!
# Van der Leer 2026: Speech-Act Logic (SAL)
@cite{van-der-leer-2026}

A propositional dynamic logic of speech acts over commitment-state
Kripke frames. Speech acts are *actions*
(`α ::= assert | question | ~α | α;β | π ↪ α/β`) interpreted as
updates on commitment spaces (Definition 10+).

## Main definitions

* `CommitmentSpace` — Definition 8: set of states with a `⊑`-minimal
  root and projected continuations.
* `SpeechAct` — Definition 20: the PDL action language.
* `apply` — interpretation of `SpeechAct` as commitment-space update.
* Headline theorems T25, T26, T27, T30, T32, T33.
* `FBProjection` — F&B 2010 as a SAL projection.
-/

namespace VanDerLeer2026

open Discourse.Commitment.Frame

variable {W : Type*} {A : Type*}

/-! ## §1 Commitment spaces (Definition 8) -/

/-- Definition 8: a set of commitment states with a unique `⊑`-minimal
    root. The root is the current state; non-root members are projected
    futures (admissible continuations under the Collaborative Principle). -/
structure CommitmentSpace (W : Type*) (A : Type*) where
  states : Set (CommitmentState W A)
  root : CommitmentState W A
  root_mem : root ∈ states
  root_minimal : ∀ c ∈ states, CooperativeExtRefl root c

namespace CommitmentSpace

/-- The trivial space: only the root state, no projected futures. -/
def singleton (root : CommitmentState W A) : CommitmentSpace W A where
  states := {root}
  root := root
  root_mem := rfl
  root_minimal := fun c hc => by
    simp only [Set.mem_singleton_iff] at hc
    exact Or.inl hc.symm

@[simp] theorem singleton_root (c : CommitmentState W A) :
    (singleton c).root = c := rfl

@[simp] theorem singleton_states (c : CommitmentState W A) :
    (singleton c).states = {c} := rfl

/-- A proposition is mutually committed throughout the space (every
    state, every agent pair). Geurts 2019 fixed-point characterisation
    lifted to the space level. -/
def MutuallyCommitted (C : CommitmentSpace W A) (π : Set W) : Prop :=
  ∀ c ∈ C.states, ∀ w, MutuallyCommittedAt c π w

/-- A proposition is commonly believed via the substrate's
    `EpistemicLogic.commonBelief` on the state's belief relation. -/
def CommonlyBelieved (c : CommitmentState W A) (group : List A)
    (π : Set W) (bound : ℕ) (w : W) : Prop :=
  Semantics.Modality.EpistemicLogic.commonBelief c.belief group
    (fun v => v ∈ π) bound w

end CommitmentSpace

/-! ## §2 Speech-act action language (Definitions 20-24) -/

/-- The action language: assert, question, sequential composition,
    denegation, empty. -/
inductive SpeechAct (W : Type*) (A : Type*) where
  | empty
  | assert (a b : A) (π : Set W)
  | question (a b : A) (π : Set W)
  | seq (α β : SpeechAct W A)
  | denegate (α : SpeechAct W A)

/-- Update a commitment state with `assert_{a,b}(π)`: restrict the
    `(a, b)` commitment relation to π-targets. -/
def assertOnState (a b : A) (π : Set W) (c : CommitmentState W A) :
    CommitmentState W A :=
  c.restrictCommitment a b π

/-- The headline assert update: new root is `assertOnState` of the
    prior root; we expose the singleton form for the basic theorems. -/
def applyAssert (a b : A) (π : Set W) (C : CommitmentSpace W A) :
    CommitmentSpace W A :=
  CommitmentSpace.singleton (assertOnState a b π C.root)

/-- Interpretation of `SpeechAct` as a commitment-space update.
    `question`, `denegate` are placeholders for the basic theorems. -/
def apply : SpeechAct W A → CommitmentSpace W A → CommitmentSpace W A
  | .empty,          C => C
  | .assert a b π,   C => applyAssert a b π C
  | .question _ _ _, C => C
  | .seq α β,        C => apply β (apply α C)
  | .denegate _,     C => C

@[simp] theorem apply_empty (C : CommitmentSpace W A) :
    apply (SpeechAct.empty : SpeechAct W A) C = C := rfl

@[simp] theorem apply_assert (a b : A) (π : Set W) (C : CommitmentSpace W A) :
    apply (SpeechAct.assert a b π) C = applyAssert a b π C := rfl

@[simp] theorem apply_seq (α β : SpeechAct W A) (C : CommitmentSpace W A) :
    apply (SpeechAct.seq α β) C = apply β (apply α C) := rfl

/-! ## §3 Headline theorems T25-T33 -/

/-- **T25** — after `assert_{a,b}(π)`, `a` is committed to `π` at the
    new root. -/
theorem assert_creates_commitment
    (a b : A) (π : Set W) (C : CommitmentSpace W A) (w : W) :
    Committed (apply (SpeechAct.assert a b π) C).root a b π w := by
  intro v hcom
  exact hcom.2 ⟨rfl, rfl⟩

/-- **T26** — under Sincerity + Competence, commitment transfers to
    the addressee's belief. The mediated CommonGround-update of @cite{bary-2025}. -/
theorem committed_implies_belief_under_sincerity_competence
    {c : CommitmentState W A} (hsin : Sincere c) (hcomp : Competent c)
    (a b : A) (π : Set W) (w : W) :
    Committed c a b π w → Believes c b π w :=
  committed_implies_addressee_believes_of_sincere_competent hsin hcomp a b π w

/-- **T27.1** — under Sincerity, commitment to `p` entails commitment
    to "I believe `p`". The formal direction of @cite{krifka-2024}'s
    "buffet is open" puzzle. -/
theorem commit_implies_commit_believe_of_sincere
    (c : CommitmentState W A) (hsin : Sincere c)
    (a b : A) (p : Set W) (w : W) :
    Committed c a b p w → Committed c a b (fun v => Believes c a p v) w := by
  intro hcom v hcom_wv v' hbel_vv'
  have hcom_vv' : c.commitment a b v v' := hsin a b v v' hbel_vv'
  have hcom_wv' : c.commitment a b w v' :=
    IsTrans.trans w v v' hcom_wv hcom_vv'
  exact hcom v' hcom_wv'

/-- **T27.2** — non-converse: there exist sincere states where
    `C_{a,b} (B_a p)` holds but `C_{a,b} p` does not. TODO: full
    countermodel construction. -/
theorem not_commit_believe_implies_commit_in_general :
    ¬ ∀ (W : Type) (A : Type) (c : CommitmentState W A) (_hsin : Sincere c)
        (a b : A) (p : Set W) (w : W),
      Committed c a b (fun v => Believes c a p v) w → Committed c a b p w := by
  sorry

/-- **T30** — commitment persists under unrelated assertion. -/
theorem commitment_persists_under_unrelated_assertion
    (a b a' b' : A) (h_ne : ¬ (a = a' ∧ b = b'))
    (π π' : Set W) (C : CommitmentSpace W A) (w : W)
    (h : Committed C.root a b π w) :
    Committed (apply (SpeechAct.assert a' b' π') C).root a b π w := by
  intro v hcom
  have hiff := CommitmentState.restrictCommitment_other
    C.root a' b' π' a b h_ne w v
  exact h v (hiff.mp hcom)

/-- **T32** — every assertion update produces a non-empty space. -/
theorem assert_well_defined (a b : A) (π : Set W) (C : CommitmentSpace W A) :
    (apply (SpeechAct.assert a b π) C).root ∈
      (apply (SpeechAct.assert a b π) C).states :=
  (apply (SpeechAct.assert a b π) C).root_mem

/-- **T33** — asserting `∅` yields a violation state (empty `O_{a,b}`). -/
theorem assert_contradiction_yields_violation
    (a b : A) (C : CommitmentSpace W A) :
    (apply (SpeechAct.assert a b ∅) C).root.commitmentEmpty a b := by
  intro w v hcom
  exact absurd (hcom.2 ⟨rfl, rfl⟩) (Set.notMem_empty v)

/-! ## §4 Farkas-Bruce 2010 as a SAL projection -/

namespace FBProjection

/-- F&B's `DC_x`: propositions `x` is publicly committed to,
    projected from a SAL state by ranging over all addressees. -/
def discourseCommitment (c : CommitmentState W A) (x : A) (w : W) (π : Set W) : Prop :=
  ∀ y, Committed c x y π w

/-- F&B's `cg` (common ground) projected as universally-believed
    propositions. -/
def commonGround (c : CommitmentState W A) (w : W) (π : Set W) : Prop :=
  ∀ a, Believes c a π w

/-- After `assert_{a,b}(π)`, `a`'s F&B-style discourse commitment
    includes `π` (towards `b`). -/
theorem assert_adds_to_DC
    (a b : A) (π : Set W) (C : CommitmentSpace W A) (w : W) :
    Committed (apply (SpeechAct.assert a b π) C).root a b π w :=
  assert_creates_commitment a b π C w

/-- Under sincerity+competence, the addressee believes the asserted
    `π` — the F&B "ASSERT enters CommonGround" effect, mediated. -/
theorem assert_enters_CG_under_sincerity_competence
    (a b : A) (π : Set W) (C : CommitmentSpace W A) (w : W)
    (hsin : Sincere (apply (SpeechAct.assert a b π) C).root)
    (hcomp : Competent (apply (SpeechAct.assert a b π) C).root) :
    Believes (apply (SpeechAct.assert a b π) C).root b π w :=
  committed_implies_belief_under_sincerity_competence
    hsin hcomp a b π w
    (assert_creates_commitment a b π C w)

/-- **The Bary 2025 critique made visible**: under sincerity+competence,
    `DC_x ⊆ cg` — but in general they differ. F&B's conflation of the
    two sets works only in the ideal case. -/
theorem dc_subset_cg_under_sincerity_competence
    (c : CommitmentState W A) (hsin : Sincere c) (hcomp : Competent c)
    (x : A) (w : W) (π : Set W) :
    discourseCommitment c x w π → commonGround c w π := by
  intro hdc a
  exact committed_implies_belief_under_sincerity_competence
    hsin hcomp x a π w (hdc a)

end FBProjection

end VanDerLeer2026
