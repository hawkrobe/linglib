import Linglib.Discourse.Commitment.Space

/-!
# Cohen and Krifka 2014: superlative quantifiers and meta-speech acts

Over commitment spaces (§2), [cohen-krifka-2014] define the meta-speech act `GRANT φ` as the
denegation of asserting `¬φ` (38): it keeps the root and prunes the continuations in which the
speaker asserts `¬φ`, so it includes but does not enforce the assertion of `φ`, and asserting is
the denegation of granting the negation (40). Superlative quantifiers are then quantifiers over
GRANTs (§3): *at most n* is the conjunction, over `m > n`, of the denegations of `GRANT φ(m)`,
which by (40) is the conjunction of the assertions of `¬φ(m)` (44)–(46), and *at least n* is
the same over `m < n` (49)–(51). Their truth conditions are derived: what the speaker asserts
outright is an entailment, and that no further `¬φ(m)` is asserted is an implicature (§3.2),
so *at least three* commits the speaker against two, one and zero but not against four.

## Main results

* `grant_root`, `sdiff_grant_states` (substrate) — GRANT keeps the root; `ASSERT φ` is
  `∼GRANT ¬φ` (40).
* `contextSet_assert_subset_grant` — asserting is stronger than granting (p. 54).
* `atMost_excludes`, `atLeast_excludes` — the entailed exclusions of (46) and (51).
* `atLeast_not_excludes` — the implicature is not an entailment (53).

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
-/

namespace CohenKrifka2014

open Commitment Commitment.Space
open Discourse (DiscourseRole)

variable {W : Type*} (C : Space (Set (Commitment DiscourseRole W))) (φ : Set W)

/-- Asserting `φ` narrows the context set at least as much as granting it (p. 54). -/
theorem contextSet_assert_subset_grant
    (h : (⟨.speaker, φᶜ, .commit, .doxastic, .selfGenerated⟩ : Commitment DiscourseRole W) ∉
      C.root) :
    contextSet (C.assert .speaker φ).root ⊆ contextSet (C.grant .speaker φ h).root := by
  rw [contextSet_assert_root, grant_root]
  exact Set.inter_subset_right

/-- Strictly: granting leaves worlds that asserting removes. -/
theorem exists_mem_grant_not_assert :
    ∃ (C : Space (Set (Commitment DiscourseRole Bool))) (φ : Set Bool) (h : _) (w : Bool),
      w ∈ contextSet (C.grant .speaker φ h).root ∧ w ∉ contextSet (C.assert .speaker φ).root :=
  ⟨full ∅, {true}, Set.notMem_empty _, false, by simp [grant_root, full_root, contextSet_empty],
    by rw [contextSet_assert_root, full_root, contextSet_empty]; simp⟩

/-- *At most `n`* (44)–(46): for every `m > n`, the speaker asserts `¬φ(m)`. -/
def atMost (n : ℕ) (φ : ℕ → Set W) : Space (Set (Commitment DiscourseRole W)) :=
  C.reroot (C.root ∪ {c | ∃ m > n, c = commit .speaker (φ m)ᶜ})

/-- *At least `n`* (49)–(51): for every `m < n`, the speaker asserts `¬φ(m)`. -/
def atLeast (n : ℕ) (φ : ℕ → Set W) : Space (Set (Commitment DiscourseRole W)) :=
  C.reroot (C.root ∪ {c | ∃ m < n, c = commit .speaker (φ m)ᶜ})

/-- The entailments of *at most `n`* (46): every `φ(m)` with `m > n` is excluded. -/
theorem atMost_excludes (n : ℕ) (φ : ℕ → Set W) {m : ℕ} (h : n < m) :
    contextSet (atMost C n φ).root ⊆ (φ m)ᶜ :=
  Set.sInter_subset_of_mem ⟨commit .speaker (φ m)ᶜ, ⟨Or.inr ⟨m, h, rfl⟩, rfl⟩, rfl⟩

/-- The entailments of *at least `n`* (51): every `φ(m)` with `m < n` is excluded. -/
theorem atLeast_excludes (n : ℕ) (φ : ℕ → Set W) {m : ℕ} (h : m < n) :
    contextSet (atLeast C n φ).root ⊆ (φ m)ᶜ :=
  Set.sInter_subset_of_mem ⟨commit .speaker (φ m)ᶜ, ⟨Or.inr ⟨m, h, rfl⟩, rfl⟩, rfl⟩

/-- *At least `n`* does not exclude `φ(m)` for `m ≥ n` (53): that is an implicature. -/
theorem atLeast_not_excludes (n : ℕ) (φ : ℕ → Set W) (hφ : Function.Injective φ) {m : ℕ}
    (h : n ≤ m) (hroot : commit .speaker (φ m)ᶜ ∉ C.root) :
    commit .speaker (φ m)ᶜ ∉ (atLeast C n φ).root := by
  rintro (hc | ⟨k, hk, e⟩)
  · exact hroot hc
  · have := hφ (compl_inj_iff.1 (congrArg content e))
    omega

end CohenKrifka2014
