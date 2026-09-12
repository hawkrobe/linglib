import Linglib.Discourse.Commitment.Space
import Linglib.Discourse.Commitment.Table
import Linglib.Semantics.Questions.Bias

/-!
# Krifka (2015): Bias in Commitment Space Semantics

This file formalizes [krifka-2015]'s commitment space semantics of biased questions. A
conversation is a commitment space, the current commitment state with its projected
continuations (`Commitment.Space`), and speech acts are its updates. An assertion re-roots the
space at the state recording the speaker's commitment (14), so the root narrows at once, where
[farkas-bruce-2010], whom the paper credits for its rejection operator, leave the common ground
untouched until acceptance. A question keeps the root and restricts the continuations to
assertions by the addressee. A monopolar question projects only the addressee's assertion of
`φ` (27), so *yes* is a projected continuation and *no* requires a prior rejection (28), while a
bipolar question is the disjunction of the two monopolar questions ((23), (31)) and projects
both answers (24); the issue projection of the library sees the bipolar question but not the
monopolar one (`monopolar_not_inquisitive`). Low negation is a monopolar question about `¬φ`
(29); high negation projects the addressee's refusal `¬S₂⊢φ` (39), weaker than `S₂⊢¬φ`, since
a consistent commitment to `¬φ` already excludes a commitment to `φ`. The licensing of the
three question forms by the contextual evidence of [buring-gunlogson-2000] then reproduces the
paper's Table 1 (`table1`). A matching tag conjoins an assertion with the monopolar question of
the same content (44), and a reverse tag disjoins the assertion with the monopolar question of
the negation (`reverseTag`, (45)).

## Implementation notes

* The fixture is a two-world space, raining or not, rooted at the empty commitment state.
* Contextual evidence is the set of worlds it leaves open: the proposition, everything, or its
  complement. A monopolar question is licensed by evidence for its proposed assertion, a
  bipolar question by neutral evidence, and the high-negation question wherever the evidence
  is not for `φ`; the low-negation question has only the monopolar reading, its bipolar reading
  being blocked by the question without negation.

## References

* [krifka-2015]
* [farkas-bruce-2010] — the Table and the rejection operator
* [buring-gunlogson-2000] — contextual evidence and the three question forms
-/

namespace Krifka2015

open Commitment Commitment.Space
open Question

/-! ### The fixture -/

/-- Two worlds: it is raining or it is not. -/
inductive Weather
  | rain
  | noRain
  deriving DecidableEq

/-- It is raining. -/
def raining : Set Weather := {.rain}

theorem raining_ne_compl : raining ≠ rainingᶜ := λ h =>
  (Set.ext_iff.1 h .rain).1 rfl rfl

/-- The initial commitment space: no commitments, every development licit. -/
def C₀ : Space (State Discourse.Role Weather) := full ∅

theorem mem_insert_empty_iff {x y : Commitment Discourse.Role Weather} :
    x ∈ insert y (∅ : State Discourse.Role Weather) ↔ x = y := by simp

/-! ### Assertion (14) -/

/-- An assertion re-roots the space at the state recording the speaker's commitment. -/
theorem assert_root :
    (C₀.assert .speaker raining).root = insert (commit .speaker raining) ∅ := rfl

/-- Krifka's root narrows at once; the Table of [farkas-bruce-2010] leaves the common ground as
it was (p. 331). -/
theorem assert_contextSet_vs_farkasBruce_cg :
    contextSet (C₀.assert .speaker raining).root = raining ∧
      ((Table.empty : Table Discourse.Role Weather).assert .speaker raining).cg = ⊤ :=
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
theorem not_mem_slate_of_commit_compl (K : State Discourse.Role Weather)
    (h : commit .addressee rainingᶜ ∈ K) (hne : (contextSet (ofCommitter K .addressee)).Nonempty) :
    raining ∉ slate (ofCommitter K .addressee) :=
  not_mem_slate_of_compl_mem _ ⟨_, ⟨⟨h, rfl⟩, rfl⟩, rfl⟩ hne

/-! ### The issue projection -/

theorem contextSet_insert_commit_empty (a : Discourse.Role) (φ : Set Weather) :
    contextSet (insert (commit a φ) (∅ : State Discourse.Role Weather)) = φ := by
  rw [contextSet_insert_of_commit rfl, contextSet_empty, Set.inter_univ]
  rfl

/-- Every continuation of the monopolar question records the addressee's commitment, so its
context set lies inside `raining`. -/
theorem monopolar_continuation_subset {c : State Discourse.Role Weather}
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
    refine Set.Subset.antisymm (Set.sUnion_subset λ i hi => ?_) (Set.subset_sUnion_of_mem hmem)
    rcases (mem_toIssue_iff _).1 hi with ⟨h0, -⟩ | ⟨c, hc, hic⟩
    · exact absurd monopolar_continuation_mem (h0 ▸ Set.notMem_empty _)
    · exact hic.trans (monopolar_continuation_subset hc)
  rw [this]
  exact hmem

/-- Every continuation of the bipolar question records one of the two answers. -/
theorem bipolar_continuation_subset {c : State Discourse.Role Weather}
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
    Set.subset_sUnion_of_mem hno λ h => Weather.noConfusion h
  rcases (mem_toIssue_iff _).1 hinfo with ⟨h0, -⟩ | ⟨c, hc, hsub⟩
  · have hmem : insert (commit .addressee raining) ∅ ∈
        (C₀.bipolarQuestion .addressee raining).continuations :=
      ⟨bipolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩
    rw [h0] at hmem
    exact hmem
  · rcases bipolar_continuation_subset hc with h | h
    · exact Weather.noConfusion (h (hsub hnoRain))
    · exact h (hsub hrain) rfl

/-! ### Table 1 -/

/-- The worlds the contextual evidence of [buring-gunlogson-2000] leaves open. -/
def evidence (φ : Set Weather) : ContextualEvidence → Set Weather
  | .forP => φ
  | .neutral => Set.univ
  | .againstP => φᶜ

/-- A monopolar question proposing `S₂⊢φ` is licensed by evidence for `φ`. -/
def MonopolarLicensed (E φ : Set Weather) : Prop := E ⊆ φ

/-- A bipolar question is licensed by neutral evidence. -/
def BipolarLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ ∧ ¬ E ⊆ φᶜ

/-- The high-negation question, proposing the refusal `¬S₂⊢φ`, is licensed wherever the
evidence is not for `φ`. -/
def HighNegationLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ

/-- The question without negation is licensed on either of its readings; the question with low
negation only on the monopolar reading of `¬φ`; the question with high negation as such. -/
def Licensed (E φ : Set Weather) : PQForm → Prop
  | .PosQ => MonopolarLicensed E φ ∨ BipolarLicensed E φ
  | .LoNQ => MonopolarLicensed E φᶜ
  | .HiNQ => HighNegationLicensed E φ

theorem raining_ne_empty : raining ≠ ∅ := (Set.singleton_nonempty _).ne_empty

theorem raining_ne_univ : raining ≠ Set.univ := λ h =>
  Weather.noConfusion (Set.eq_univ_iff_forall.1 h .noRain)

/-- Table 1: with evidence for `φ` only the question without negation is licensed, read
monopolar; with neutral evidence the question without negation, read bipolar, and the
high-negation question; with evidence against `φ` both negated questions and not the question
without negation. -/
theorem table1 (e : ContextualEvidence) :
    (Licensed (evidence raining e) raining .PosQ ↔ e ≠ .againstP) ∧
      (Licensed (evidence raining e) raining .LoNQ ↔ e = .againstP) ∧
      (Licensed (evidence raining e) raining .HiNQ ↔ e ≠ .forP) := by
  cases e <;> simp [Licensed, MonopolarLicensed, BipolarLicensed, HighNegationLicensed, evidence,
    raining_ne_empty, raining_ne_univ]

/-! ### Question tags (44), (45) -/

variable (C : Space (State Discourse.Role Weather)) (φ : Set Weather)

/-- A matching tag (44): the conjunction of the assertion with the monopolar question of the same
content, whose result is the state in which both participants are committed. -/
def matchingTag : Space (State Discourse.Role Weather) :=
  (C.assert .speaker φ).assert .addressee φ

/-- A reverse tag (45): the disjunction of the assertion with the monopolar question of the
negation, rooted at the current state. -/
def reverseTag : Space (State Discourse.Role Weather) :=
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
