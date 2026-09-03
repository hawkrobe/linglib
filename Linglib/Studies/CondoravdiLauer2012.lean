import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.Roles

/-!
# Condoravdi and Lauer 2012: imperatives as preferential commitments

[condoravdi-lauer-2012] give declaratives and imperatives the same kind of conventional effect,
a public commitment to act, differing in the attitude the speaker is committed to act under: a
declarative adds `PB(Sp, p)`, a commitment to act as though believing `p`; an imperative adds
`PEP(Sp, p)`, a commitment to act as though `p` were a maximal element of the speaker's
effective preferences (§3.2, §3.3). That is the `Commitment.Force` coordinate, and the two
attitudes project separately: the doxastic context set of a declarative narrows and its
preferential one does not, and conversely for an imperative.

## Main results

* `declarative_contextSets`, `imperative_contextSets` — each form narrows exactly one of the
  two projections.

## References

* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and illocutionary force*
  (2012)][condoravdi-lauer-2012]
-/

namespace CondoravdiLauer2012

open Commitment
open Discourse (DiscourseRole)

/-- Whether the addressee is sitting. -/
inductive AddrPosture
  | sitting
  | standing
  deriving DecidableEq

/-- The addressee is sitting. -/
def isSitting : Set AddrPosture := {.sitting}

/-- *The addressee is sitting.* -/
def declarative : Set (Commitment DiscourseRole AddrPosture) := {commit .speaker isSitting}

/-- *Sit down!* -/
def imperative : Set (Commitment DiscourseRole AddrPosture) :=
  {commit .speaker isSitting .preferential}

theorem ofForce_singleton_self (c : Commitment DiscourseRole AddrPosture) (f : Force)
    (h : c.force = f) : ofForce {c} f = {c} := by
  ext d
  simp only [ofForce, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_iff_left_iff_imp]
  rintro rfl
  exact h

theorem ofForce_singleton_of_ne (c : Commitment DiscourseRole AddrPosture) {f : Force}
    (h : c.force ≠ f) : ofForce {c} f = ∅ := by
  ext d
  simp only [ofForce, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl
  exact h

theorem contextSet_singleton_commit (c : Commitment DiscourseRole AddrPosture)
    (h : c.polarity = .commit) : contextSet {c} = c.content := by
  have : contents {c} = {c.content} := by
    ext φ
    simp [contents, h, eq_comm]
  rw [contextSet, this, Set.sInter_singleton]

/-- A declarative narrows the doxastic context set and leaves the preferential one alone. -/
theorem declarative_contextSets :
    contextSet (ofForce declarative .doxastic) = isSitting ∧
      contextSet (ofForce declarative .preferential) = Set.univ := by
  refine ⟨?_, ?_⟩
  · rw [declarative, ofForce_singleton_self _ .doxastic rfl, contextSet_singleton_commit _ rfl]
    rfl
  · rw [declarative, ofForce_singleton_of_ne _ (by decide), contextSet_empty]

/-- An imperative narrows the preferential context set and leaves the doxastic one alone. -/
theorem imperative_contextSets :
    contextSet (ofForce imperative .preferential) = isSitting ∧
      contextSet (ofForce imperative .doxastic) = Set.univ := by
  refine ⟨?_, ?_⟩
  · rw [imperative, ofForce_singleton_self _ .preferential rfl, contextSet_singleton_commit _ rfl]
    rfl
  · rw [imperative, ofForce_singleton_of_ne _ (by decide), contextSet_empty]

end CondoravdiLauer2012
