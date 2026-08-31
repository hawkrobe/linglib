import Linglib.Discourse.SpeechAct
import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.CommonGround

/-!
# Brandom 1994: deontic scorekeeping

This file formalizes the scorekeeping model of assertion in [brandom-1994]. A discursive score
records two deontic statuses for each interlocutor, commitment and entitlement, and the content of
a claim is its role in three broadly inferential structures: what follows from it
commitment-preservingly, what it entitles, and what it rules out — committive inferences,
permissive inferences, and incompatibilities.

Entitlement has a default and challenge structure. Attributing a commitment normally carries an
attribution of entitlement along with it, and asserting authorizes others to re-assert, so a
hearer's entitlement may be inherited by deferral to the speaker; a challenge withdraws the default
without withdrawing the commitment. Because the two statuses answer to different inferential
relations, a scorecard can carry commitment without entitlement, and two scorekeepers can disagree
about a third party's score.

## Main definitions

* `InferentialRole` — the committive, permissive and incompatibility relations
* `CommittedTo`, `EntitledTo` — the two statuses, closed under their own consequence relations
* `assert`, `challenge`, `defer` — the scorekeeping moves

## Main results

* `entitlement_not_closed_under_committive` — the two statuses answer to different inferences
* `challenge_leaves_commitment` — a challenged assertion is a commitment without entitlement
* `incompatible_commitment_defeats_entitlement` — what a score rules out, it is not entitled to
* `deferral_entitles_hearer` — asserting authorizes the hearer to re-assert
* `scorekeepers_can_disagree` — after a challenge the two scorecards differ

## References

* [brandom-1994]
* [brandom-1983]
-/

namespace Brandom1994

open Discourse.Commitment (CommitmentSlate)

/-! ### Deontic status -/

/-- The status a scorekeeper attributes to an interlocutor: what they have committed themselves to,
and what they are entitled to. -/
structure NormativeStatus (W : Type*) where
  commitments : CommitmentSlate W
  entitlements : CommitmentSlate W

namespace NormativeStatus
variable {W : Type*}

/-- No commitments, no entitlements. -/
def empty : NormativeStatus W := ⟨CommitmentSlate.empty, CommitmentSlate.empty⟩

/-- Undertake a commitment. -/
def commit (ns : NormativeStatus W) (p : W → Prop) : NormativeStatus W :=
  { ns with commitments := ns.commitments.add p }

/-- Acquire an entitlement. -/
def entitle (ns : NormativeStatus W) (p : W → Prop) : NormativeStatus W :=
  { ns with entitlements := ns.entitlements.add p }

/-- Withdraw an entitlement, leaving the commitment in place — what a challenge does. -/
def withdrawEntitlement [DecidableEq (W → Prop)] (ns : NormativeStatus W) (p : W → Prop) :
    NormativeStatus W :=
  { ns with entitlements := ⟨ns.entitlements.commitments.filter (fun q => decide (q ≠ p))⟩ }

end NormativeStatus

/-! ### Inferential role -/

/-- The three broadly inferential structures a content's role consists in: the commitments it
carries with it, the entitlements it confers, and what it precludes. -/
structure InferentialRole (W : Type*) where
  /-- Commitment-preserving consequence, roughly the deductive case. -/
  committive : (W → Prop) → (W → Prop) → Prop
  /-- Entitlement-preserving consequence, roughly the inductive case. -/
  permissive : (W → Prop) → (W → Prop) → Prop
  /-- What a claim rules out. -/
  incompatible : (W → Prop) → (W → Prop) → Prop
  /-- Incompatibility is symmetric: ruling out is mutual. -/
  incompatible_symm : ∀ p q, incompatible p q → incompatible q p

variable {W : Type*}

/-- What a score commits an interlocutor to: what they have acknowledged, closed under committive
consequence — one is committed to the consequences of one's commitments whether or not one has
acknowledged them. -/
inductive CommittedTo (R : InferentialRole W) (ns : NormativeStatus W) : (W → Prop) → Prop where
  /-- An acknowledged commitment. -/
  | acknowledged {p} (h : p ∈ ns.commitments.commitments) : CommittedTo R ns p
  /-- A consequential commitment, along a committive inference. -/
  | consequential {p q} (hp : CommittedTo R ns p) (hpq : R.committive p q) : CommittedTo R ns q

/-- What a score entitles an interlocutor to: what they are entitled to outright or along a
permissive inference, provided nothing they are committed to rules it out. Entitlement travels the
permissive relation, not the committive one, and is defeasible where the committive status is
not. -/
def EntitledTo (R : InferentialRole W) (ns : NormativeStatus W) (p : W → Prop) : Prop :=
  (p ∈ ns.entitlements.commitments ∨
      ∃ q ∈ ns.entitlements.commitments, R.permissive q p) ∧
    ¬ ∃ q, CommittedTo R ns q ∧ R.incompatible p q

/-- A score is in good order when every acknowledged commitment is one the interlocutor is entitled
to — no commitment stands unvindicated. -/
def Vindicated (R : InferentialRole W) (ns : NormativeStatus W) : Prop :=
  ∀ p ∈ ns.commitments.commitments, EntitledTo R ns p

/-- Committing to something a claim rules out defeats entitlement to the claim: what the score
precludes, it is not entitled to. -/
theorem incompatible_commitment_defeats_entitlement (R : InferentialRole W)
    (ns : NormativeStatus W) (p q : W → Prop) (hq : CommittedTo R ns q)
    (hinc : R.incompatible p q) : ¬ EntitledTo R ns p :=
  fun h => h.2 ⟨q, hq, hinc⟩

/-- Commitment carries along committive inferences by construction; the corresponding closure fails
for entitlement, which is the point of keeping the two relations apart. -/
theorem committed_of_committive (R : InferentialRole W) (ns : NormativeStatus W) {p q : W → Prop}
    (hp : CommittedTo R ns p) (hpq : R.committive p q) : CommittedTo R ns q :=
  .consequential hp hpq

/-- Entitlement is not closed under committive consequence: a score may entitle `p` and carry `p`
to `q` committively without entitling `q`. Deductive consequence preserves commitment, not
entitlement. -/
theorem entitlement_not_closed_under_committive :
    ∃ (R : InferentialRole Bool) (ns : NormativeStatus Bool) (p q : Bool → Prop),
      EntitledTo R ns p ∧ R.committive p q ∧ ¬ EntitledTo R ns q := by
  refine ⟨⟨fun a b => a = (fun w => w = true) ∧ b = (fun _ => True), fun _ _ => False,
      fun _ _ => False, by simp⟩,
    ⟨CommitmentSlate.empty, ⟨[fun w => w = true]⟩⟩, (fun w => w = true), (fun _ => True),
    ⟨.inl (by simp), by rintro ⟨q, -, hinc⟩; exact hinc⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨(h | ⟨q, -, hq⟩), -⟩
  · simp only [List.mem_singleton] at h
    have := congrFun h false
    simp at this
  · exact hq

/-! ### Scorekeeping -/

/-- The two roles a scorekeeping episode distinguishes. -/
inductive Interlocutor where
  | speaker
  | hearer
  deriving DecidableEq, Repr, Inhabited

/-- A score: what each interlocutor attributes to each. `card k i` is `k`'s attribution to `i`, and
two scorekeepers' attributions to the same interlocutor may differ. -/
structure Score (W : Type*) where
  card : Interlocutor → Interlocutor → NormativeStatus W

namespace Score
variable {W : Type*}

/-- Everyone attributes the empty status to everyone. -/
def empty : Score W := ⟨fun _ _ => NormativeStatus.empty⟩

/-- Update one cell of the score. -/
def update (s : Score W) (k i : Interlocutor) (f : NormativeStatus W → NormativeStatus W) :
    Score W :=
  ⟨fun k' i' => if k' = k ∧ i' = i then f (s.card k i) else s.card k' i'⟩

@[simp] theorem card_update_self (s : Score W) (k i : Interlocutor)
    (f : NormativeStatus W → NormativeStatus W) : (s.update k i f).card k i = f (s.card k i) := by
  simp [update]

@[simp] theorem card_update_of_ne (s : Score W) {k i k' i' : Interlocutor}
    (f : NormativeStatus W → NormativeStatus W) (h : ¬ (k' = k ∧ i' = i)) :
    (s.update k i f).card k' i' = s.card k' i' := by
  simp [update, h]

end Score

/-- Asserting `p`: the speaker undertakes commitment to `p`, and every scorekeeper attributes that
commitment along with entitlement by default. -/
def assert (s : Score W) (p : W → Prop) : Score W :=
  ⟨fun k i =>
    if i = .speaker then ((s.card k i).commit p).entitle p else s.card k i⟩

/-- Deferral: the hearer, having heard the speaker assert `p`, inherits entitlement to `p` by
deferring to the speaker's authority — the communicational function of assertion is to license
others to re-assert. -/
def defer (s : Score W) (p : W → Prop) : Score W :=
  s.update .hearer .hearer (·.entitle p)

/-- A challenge by the hearer: a demand for reasons, which withdraws the hearer's attribution of
default entitlement while leaving the attributed commitment standing. -/
def challenge [DecidableEq (W → Prop)] (s : Score W) (p : W → Prop) : Score W :=
  s.update .hearer .speaker (·.withdrawEntitlement p)

/-- Asserting attributes commitment and, by default, entitlement — on every scorecard. -/
theorem assert_attributes_default_entitlement (s : Score W) (p : W → Prop) (k : Interlocutor) :
    p ∈ ((assert s p).card k .speaker).commitments.commitments ∧
      p ∈ ((assert s p).card k .speaker).entitlements.commitments := by
  constructor <;> simp [assert, NormativeStatus.commit, NormativeStatus.entitle,
    CommitmentSlate.add]

/-- Deferral entitles the hearer to what the speaker asserted, without the hearer having grounds of
their own. -/
theorem deferral_entitles_hearer (s : Score W) (p : W → Prop) :
    p ∈ ((defer (assert s p) p).card .hearer .hearer).entitlements.commitments := by
  simp [defer, NormativeStatus.entitle, CommitmentSlate.add]

/-- A challenged assertion is a commitment the hearer no longer grants entitlement to: the
challenge takes back the default without taking back the commitment. This is the configuration
that has no counterpart where a context set is all the score records. -/
theorem challenge_leaves_commitment [DecidableEq (W → Prop)] (s : Score W) (p : W → Prop) :
    p ∈ ((challenge (assert s p) p).card .hearer .speaker).commitments.commitments ∧
      p ∉ ((challenge (assert s p) p).card .hearer .speaker).entitlements.commitments := by
  refine ⟨by simp [challenge, assert, NormativeStatus.commit, NormativeStatus.entitle,
      NormativeStatus.withdrawEntitlement, CommitmentSlate.add], ?_⟩
  simp [challenge, assert, NormativeStatus.commit, NormativeStatus.entitle,
    NormativeStatus.withdrawEntitlement, CommitmentSlate.add]

/-- Scorekeepers can disagree: after the hearer challenges, the speaker's own scorecard still
grants entitlement where the hearer's does not, so there is no single score the two share. -/
theorem scorekeepers_can_disagree [DecidableEq (W → Prop)] (s : Score W) (p : W → Prop) :
    p ∈ ((challenge (assert s p) p).card .speaker .speaker).entitlements.commitments ∧
      p ∉ ((challenge (assert s p) p).card .hearer .speaker).entitlements.commitments := by
  refine ⟨?_, (challenge_leaves_commitment s p).2⟩
  have hcell : (challenge (assert s p) p).card .speaker .speaker
      = (assert s p).card .speaker .speaker := by
    simp [challenge, Score.update]
  rw [hcell]
  simp [assert, NormativeStatus.commit, NormativeStatus.entitle, CommitmentSlate.add]

/-! ### Projection to a common ground -/

/-- The worlds compatible with everything each interlocutor is self-attributed to be committed to.
Projecting a score this way is lossy: the disagreement of `scorekeepers_can_disagree` and the
commitment/entitlement distinction are both invisible in the result. -/
def contextSet (s : Score W) : W → Prop := fun w =>
  (s.card .speaker .speaker).commitments.toContextSet w ∧
    (s.card .hearer .hearer).commitments.toContextSet w

instance : HasCommonGround (Score W) W where
  commonGround s := Filter.principal {w | contextSet s w}

end Brandom1994
