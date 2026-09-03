import Linglib.Discourse.Commitment.Space
import Linglib.Discourse.Commitment.Table
import Linglib.Features.Acceptability
import Linglib.Semantics.Questions.Bias

/-!
# Krifka 2015: bias in commitment space semantics

[krifka-2015] models a conversation as a commitment space, the current commitment state with
its projected continuations, and speech acts as its updates (`Commitment.Space`). An assertion
`S⊢φ` re-roots the space at the state that records the speaker's commitment (14), so the root
narrows at once — where [farkas-bruce-2010], whom Krifka credits for his rejection operator
(p. 331), leave the common ground untouched until acceptance. A question keeps the root and
restricts the continuations to assertions by the addressee: a monopolar question projects only
the addressee's assertion of `φ` (27), so *yes* is a projected continuation and *no* requires a
prior rejection (28), while a bipolar question is the disjunction of the two monopolar questions
(23), (31), projecting both answers (24). Low negation is a monopolar question about `¬φ` (29);
high negation projects the addressee's refusal `¬S₂⊢φ` (39), weaker than `S₂⊢¬φ` since a
consistent commitment to `¬φ` already excludes a commitment to `φ` (p. 340). Table 1 (p. 341)
records how the three question forms are licensed by the contextual evidence of
[buring-gunlogson-2000]. A matching tag conjoins an assertion with the monopolar question of the
same content (44); a reverse tag disjoins the assertion with the monopolar question of the
negation (45).

## Main definitions

* `Weather`, `raining`, `C₀` — the two-world fixture and the initial space, the free space on
  the empty commitment state.
* `table1`, `noNegLicensing` — Table 1 and its explanation.
* `matchingTag`, `reverseTag` — (44), (45).

## Main results

* `assert_root`, `assert_contextSet_vs_farkasBruce_cg` — (14) and the contrast with the Table.
* `monopolar_yes_mem`, `monopolar_no_not_mem`, `bipolar_yes_mem`, `bipolar_no_mem` — (23)–(28).
* `highNegation_refusal_mem`, `not_mem_slate_of_commit_compl` — (39) and p. 340.
* `monopolar_not_inquisitive`, `bipolar_inquisitive` — the issue projection sees the bipolar
  question but not the monopolar one.
* `matchingTag_root`, `reverseTag_root`, `reverseTag_branches` — (44), (45).

## References

* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [D. Büring and C. Gunlogson, *Aren't Positive and Negative Polar Questions the Same?*
  (2000)][buring-gunlogson-2000]
-/

namespace Krifka2015

open Commitment Commitment.Space
open Discourse (DiscourseRole)
open Questions.Bias (ContextualEvidence)
open Features (Acceptability)

/-! ### The fixture -/

/-- Two worlds: it is raining or it is not. -/
inductive Weather
  | rain
  | noRain
  deriving DecidableEq

/-- It is raining. -/
def raining : Set Weather := {.rain}

theorem raining_ne_compl : raining ≠ rainingᶜ := fun h =>
  (Set.ext_iff.1 h .rain).1 rfl rfl

/-- The initial commitment space: no commitments, every development licit. -/
def C₀ : Space (Set (Commitment DiscourseRole Weather)) := full ∅

theorem mem_insert_empty_iff {x y : Commitment DiscourseRole Weather} :
    x ∈ insert y (∅ : Set (Commitment DiscourseRole Weather)) ↔ x = y := by simp

/-! ### Assertion (14) -/

/-- An assertion re-roots the space at the state recording the speaker's commitment. -/
theorem assert_root :
    (C₀.assert .speaker raining).root = insert (commit .speaker raining) ∅ := rfl

/-- Krifka's root narrows at once; the Table of [farkas-bruce-2010] leaves the common ground as
it was (p. 331). -/
theorem assert_contextSet_vs_farkasBruce_cg :
    contextSet (C₀.assert .speaker raining).root = raining ∧
      ((Table.empty : Table DiscourseRole Weather).assert .speaker raining).cg = ⊤ :=
  ⟨by rw [contextSet_assert_root, show C₀.root = ∅ from rfl, contextSet_empty, Set.inter_univ],
    rfl⟩

/-! ### Questions (23)–(28) -/

/-- A monopolar question keeps the root (27). -/
theorem monopolar_root : (C₀.monopolarQuestion .addressee raining).root = ∅ := rfl

/-- *Yes* is a projected continuation of the monopolar question (28a). -/
theorem monopolar_yes_mem :
    insert (commit .addressee raining) ∅ ∈ (C₀.monopolarQuestion .addressee raining).states :=
  Or.inr (Or.inl rfl)

/-- *No* is not: it requires a prior rejection (28b). -/
theorem monopolar_no_not_mem :
    insert (commit .addressee rainingᶜ) ∅ ∉ (C₀.monopolarQuestion .addressee raining).states := by
  rintro (h | h | ⟨-, h⟩)
  · exact (Set.insert_nonempty _ _).ne_empty h
  · exact raining_ne_compl (congrArg content (mem_insert_empty_iff.1 (h ▸ Set.mem_insert _ _))).symm
  · exact raining_ne_compl (congrArg content (mem_insert_empty_iff.1 (h (Set.mem_insert _ _))))

/-- Both answers are projected continuations of the bipolar question (24). -/
theorem bipolar_yes_mem :
    insert (commit .addressee raining) ∅ ∈ (C₀.bipolarQuestion .addressee raining).states :=
  Or.inl monopolar_yes_mem

theorem bipolar_no_mem :
    insert (commit .addressee rainingᶜ) ∅ ∈ (C₀.bipolarQuestion .addressee raining).states :=
  Or.inr (Or.inr (Or.inl rfl))

/-! ### Negated questions (29), (39) -/

/-- High negation projects the addressee's refusal (39). -/
theorem highNegation_refusal_mem :
    insert (refuse .addressee raining) ∅ ∈ (C₀.highNegationQuestion .addressee raining).states :=
  Or.inr (Or.inl rfl)

/-- `¬S₂⊢φ` is weaker than `S₂⊢¬φ` (p. 340): a consistent commitment to `¬φ` already excludes
a commitment to `φ`. -/
theorem not_mem_slate_of_commit_compl (K : Set (Commitment DiscourseRole Weather))
    (h : commit .addressee rainingᶜ ∈ K) (hne : (contextSet (ofCommitter K .addressee)).Nonempty) :
    raining ∉ slate (ofCommitter K .addressee) :=
  not_mem_slate_of_compl_mem _ ⟨_, ⟨⟨h, rfl⟩, rfl⟩, rfl⟩ hne

/-! ### The issue projection -/

theorem contextSet_insert_commit_empty (a : DiscourseRole) (φ : Set Weather) :
    contextSet (insert (commit a φ) (∅ : Set (Commitment DiscourseRole Weather))) = φ := by
  rw [contextSet_insert_of_commit rfl, contextSet_empty, Set.inter_univ]
  rfl

/-- Every continuation of the monopolar question records the addressee's commitment, so its
context set lies inside `raining`. -/
theorem monopolar_continuation_subset {c : Set (Commitment DiscourseRole Weather)}
    (hc : c ∈ (C₀.monopolarQuestion .addressee raining).continuations) :
    contextSet c ⊆ raining := by
  obtain ⟨hc, hne⟩ := hc
  rcases hc with rfl | rfl | ⟨-, hc⟩
  · exact absurd rfl hne
  · exact (contextSet_insert_commit_empty _ _).le
  · exact contextSet_subset_of_mem_contents _ ⟨_, ⟨hc (Set.mem_insert _ _), rfl⟩, rfl⟩

theorem monopolar_continuation_mem :
    insert (commit .addressee raining) ∅ ∈
      (C₀.monopolarQuestion .addressee raining).continuations :=
  ⟨monopolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩

/-- A monopolar question raises no inquisitive issue: its bias is invisible to the issue
observable. -/
theorem monopolar_not_inquisitive :
    ¬ (C₀.monopolarQuestion .addressee raining).toIssue.isInquisitive := by
  intro h
  have hmem : raining ∈ (C₀.monopolarQuestion .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, monopolar_continuation_mem,
      (contextSet_insert_commit_empty _ _).ge⟩)
  refine h ?_
  have : (C₀.monopolarQuestion .addressee raining).toIssue.info = raining := by
    refine Set.Subset.antisymm (Set.sUnion_subset fun i hi => ?_) (Set.subset_sUnion_of_mem hmem)
    rcases (mem_toIssue_iff _).1 hi with ⟨h0, -⟩ | ⟨c, hc, hic⟩
    · exact absurd monopolar_continuation_mem (h0 ▸ Set.notMem_empty _)
    · exact hic.trans (monopolar_continuation_subset hc)
  rw [this]
  exact hmem

/-- Every continuation of the bipolar question records one of the two answers. -/
theorem bipolar_continuation_subset {c : Set (Commitment DiscourseRole Weather)}
    (hc : c ∈ (C₀.bipolarQuestion .addressee raining).continuations) :
    contextSet c ⊆ raining ∨ contextSet c ⊆ rainingᶜ := by
  obtain ⟨hc, hne⟩ := hc
  rcases hc with (rfl | rfl | ⟨-, hc⟩) | (rfl | rfl | ⟨-, hc⟩)
  · exact absurd rfl hne
  · exact Or.inl (contextSet_insert_commit_empty _ _).le
  · exact Or.inl (contextSet_subset_of_mem_contents _ ⟨_, ⟨hc (Set.mem_insert _ _), rfl⟩, rfl⟩)
  · exact absurd rfl hne
  · exact Or.inr (contextSet_insert_commit_empty _ _).le
  · exact Or.inr (contextSet_subset_of_mem_contents _ ⟨_, ⟨hc (Set.mem_insert _ _), rfl⟩, rfl⟩)

/-- A bipolar question raises a genuine issue. -/
theorem bipolar_inquisitive : (C₀.bipolarQuestion .addressee raining).toIssue.isInquisitive := by
  intro hinfo
  have hyes : raining ∈ (C₀.bipolarQuestion .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, ⟨bipolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩,
      (contextSet_insert_commit_empty _ _).ge⟩)
  have hno : rainingᶜ ∈ (C₀.bipolarQuestion .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, ⟨bipolar_no_mem, (Set.insert_nonempty _ _).ne_empty⟩,
      (contextSet_insert_commit_empty _ _).ge⟩)
  have hrain : Weather.rain ∈ (C₀.bipolarQuestion .addressee raining).toIssue.info :=
    Set.subset_sUnion_of_mem hyes rfl
  have hnoRain : Weather.noRain ∈ (C₀.bipolarQuestion .addressee raining).toIssue.info :=
    Set.subset_sUnion_of_mem hno fun h => Weather.noConfusion h
  rcases (mem_toIssue_iff _).1 hinfo with ⟨h0, -⟩ | ⟨c, hc, hsub⟩
  · have hmem : insert (commit .addressee raining) ∅ ∈
        (C₀.bipolarQuestion .addressee raining).continuations :=
      ⟨bipolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩
    rw [h0] at hmem
    exact hmem
  · rcases bipolar_continuation_subset hc with h | h
    · exact Weather.noConfusion (h (hsub hnoRain))
    · exact h (hsub hrain) rfl

/-! ### Table 1 (p. 341) -/

/-- The three question forms of Table 1. -/
inductive NegationType
  | noNeg
  | lowNeg
  | highNeg
  deriving DecidableEq, Repr

/-- Which reading licenses the question without negation in each context (p. 341). -/
inductive NoNegReading
  | monopolarLicensed
  | bipolarLicensed
  | bothDegraded
  deriving DecidableEq, Repr

/-- Table 1: acceptability by contextual evidence and question form; the parenthesised `(#)`
is `marginal`. -/
def table1 : ContextualEvidence → NegationType → Acceptability
  | .forP,     .noNeg   => .ok
  | .forP,     .lowNeg  => .anomalous
  | .forP,     .highNeg => .anomalous
  | .neutral,  .noNeg   => .ok
  | .neutral,  .lowNeg  => .anomalous
  | .neutral,  .highNeg => .ok
  | .againstP, .noNeg   => .marginal
  | .againstP, .lowNeg  => .ok
  | .againstP, .highNeg => .ok

/-- The explanation of the no-negation column: the monopolar reading is licensed by evidence
for `φ`, the bipolar reading by neutral evidence, and neither by evidence against. -/
def noNegLicensing : ContextualEvidence → NoNegReading
  | .forP     => .monopolarLicensed
  | .neutral  => .bipolarLicensed
  | .againstP => .bothDegraded

/-- Low negation is only monopolar and high negation is weaker: the columns of Table 1 differ
exactly where the readings predict. -/
theorem table1_columns_differ :
    (∀ e, table1 e .lowNeg = .ok ↔ e = .againstP) ∧
      (∀ e, table1 e .highNeg = .ok ↔ e ≠ .forP) := by
  refine ⟨fun e => ?_, fun e => ?_⟩ <;> cases e <;> decide

/-! ### Question tags (44), (45) -/

variable (C : Space (Set (Commitment DiscourseRole Weather))) (φ : Set Weather)

/-- A matching tag (44): the conjunction of the assertion with the monopolar question of the same
content, whose result is the state in which both participants are committed. -/
def matchingTag : Space (Set (Commitment DiscourseRole Weather)) :=
  (C.assert .speaker φ).assert .addressee φ

/-- A reverse tag (45): the disjunction of the assertion with the monopolar question of the
negation, rooted at the current state. -/
def reverseTag : Space (Set (Commitment DiscourseRole Weather)) :=
  C.propose ((C.assert .speaker φ).states ∪ (C.monopolarQuestion .addressee φᶜ).states) <| by
    rintro d (hd | rfl | hd)
    · exact C.root_mem_lowerBounds_reroot (Set.subset_insert _ _) hd
    · exact le_rfl
    · exact C.root_mem_lowerBounds_reroot (Set.subset_insert _ _) hd

/-- After a matching tag the proposed commitments obtain unless the addressee reacts. -/
theorem matchingTag_root :
    (matchingTag C₀ raining).root =
      insert (commit .addressee raining) (insert (commit .speaker raining) ∅) := rfl

/-- A reverse tag keeps the root: the speaker's commitment is only one branch. -/
theorem reverseTag_root : (reverseTag C₀ raining).root = ∅ := rfl

/-- Its branches: the speaker's assertion, and the addressee's assertion of the negation. -/
theorem reverseTag_branches :
    insert (commit .speaker raining) ∅ ∈ (reverseTag C₀ raining).states ∧
      insert (commit .addressee rainingᶜ) ∅ ∈ (reverseTag C₀ raining).states :=
  ⟨Or.inr (Or.inl (Or.inl rfl)), Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩

end Krifka2015
