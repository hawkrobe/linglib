import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.Roles

/-!
# Rising and falling declaratives

[gunlogson-2001] represents a two-party context as the pair of the participants' commitment
sets, the worlds compatible with each one's public beliefs (60), and reads a declarative's
intonation as choosing whose commitment set its content updates: falling for the speaker's,
rising for the addressee's (77), (78). Which participant is committed to what defines the
statuses of a proposition — a commitment of a participant, a joint commitment, resolved,
controversial — and the bias of a context toward it (63)–(68). [gunlogson-2008] refines the
addressee's commitment under a rising declarative as attributed by the speaker rather than
self-generated, the `Commitment.Source` coordinate.

## Main definitions

* `Commitment.commitmentSet` — `cs_X` (60).
* `Commitment.falling`, `Commitment.rising` — (78), (77).
* `Commitment.IsCommitmentOf`, `IsJoint`, `IsResolved`, `IsControversial`, `IsBiased`,
  `IsNeutral` — (63)–(68).

## Main results

* `Commitment.commitmentSet_falling`, `Commitment.commitmentSet_rising` — each intonation
  narrows exactly one commitment set.
* `Commitment.isBiased_falling` — a falling declarative biases the context toward its content.

## References

* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
* [C. Gunlogson, *A Question of Commitment* (2008)][gunlogson-2008]
-/

namespace Commitment

open Discourse (DiscourseRole)

variable {W : Type*} (K : State DiscourseRole W) (x : DiscourseRole) (p : Set W)

/-- `cs_X` (60): the worlds compatible with `x`'s public commitments. -/
def commitmentSet : Set W := contextSet (ofCommitter K x)

/-- A falling declarative (78): the speaker commits to `p`. -/
def falling : State DiscourseRole W := insert (commit .speaker p) K

/-- A rising declarative (77): the addressee is committed to `p`, attributed by the speaker. -/
def rising : State DiscourseRole W :=
  insert (commit .addressee p .doxastic .otherGenerated) K

/-- (63): `p` is a commitment of `x`. -/
def IsCommitmentOf : Prop := (commitmentSet K x).Nonempty ∧ commitmentSet K x ⊆ p

/-- (64): `p` is a joint commitment. -/
def IsJoint : Prop := ∀ x, IsCommitmentOf K x p

/-- (65): `p` is resolved. -/
def IsResolved : Prop := IsJoint K p ∨ IsJoint K pᶜ

/-- (66): `p` is controversial — someone is committed against it, it is unresolved, and no
commitment set is empty. -/
def IsControversial : Prop :=
  (∃ x, IsCommitmentOf K x pᶜ) ∧ ¬ IsResolved K p ∧ ∀ x, (commitmentSet K x).Nonempty

/-- (67): the context is biased toward `p`. -/
def IsBiased : Prop := IsControversial K pᶜ ∧ ¬ IsControversial K p

/-- (68): the context is neutral with respect to `p`. -/
def IsNeutral : Prop := ¬ IsControversial K p ∧ ¬ IsControversial K pᶜ

theorem ofCommitter_insert_of_eq (c : Commitment DiscourseRole W) (h : c.committer = x) :
    ofCommitter (insert c K) x = insert c (ofCommitter K x) := by
  ext d
  simp only [ofCommitter, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨rfl | hd, hc⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hd, hc⟩
  · rintro (rfl | ⟨hd, hc⟩)
    · exact ⟨Or.inl rfl, h⟩
    · exact ⟨Or.inr hd, hc⟩

theorem ofCommitter_insert_of_ne (c : Commitment DiscourseRole W) (h : c.committer ≠ x) :
    ofCommitter (insert c K) x = ofCommitter K x := by
  ext d
  simp only [ofCommitter, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨rfl | hd, hc⟩
    · exact absurd hc h
    · exact ⟨hd, hc⟩
  · rintro ⟨hd, hc⟩
    exact ⟨Or.inr hd, hc⟩

@[simp] theorem commitmentSet_empty :
    commitmentSet (∅ : State DiscourseRole W) x = Set.univ := by
  simp [commitmentSet, ofCommitter]

/-- A falling declarative narrows the speaker's commitment set by its content and leaves the
addressee's alone. -/
theorem commitmentSet_falling :
    commitmentSet (falling K p) .speaker = p ∩ commitmentSet K .speaker ∧
      commitmentSet (falling K p) .addressee = commitmentSet K .addressee := by
  refine ⟨?_, ?_⟩
  · rw [commitmentSet, falling, ofCommitter_insert_of_eq K .speaker _ rfl,
      contextSet_insert_of_commit rfl]
    rfl
  · rw [commitmentSet, falling, ofCommitter_insert_of_ne K .addressee _ (by simp)]
    rfl

/-- A rising declarative narrows the addressee's commitment set by its content and leaves the
speaker's alone. -/
theorem commitmentSet_rising :
    commitmentSet (rising K p) .addressee = p ∩ commitmentSet K .addressee ∧
      commitmentSet (rising K p) .speaker = commitmentSet K .speaker := by
  refine ⟨?_, ?_⟩
  · rw [commitmentSet, rising, ofCommitter_insert_of_eq K .addressee _ rfl,
      contextSet_insert_of_commit rfl]
    rfl
  · rw [commitmentSet, rising, ofCommitter_insert_of_ne K .speaker _ (by simp)]
    rfl

end Commitment
