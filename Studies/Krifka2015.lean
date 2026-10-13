module

public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Commitment.Table
public import Studies.BuringGunlogson2000

/-!
# Krifka (2015): Bias in Commitment Space Semantics

Krifka models a conversation as a commitment space, the current commitment state with the
continuations it projects. An assertion moves the root to the state recording the speaker's
commitment, so the root narrows at once, where the Table of Farkas and Bruce leaves the common
ground untouched until acceptance. A question keeps the root and proposes continuations in which
the addressee asserts. A monopolar question proposes one assertion, so *yes* is a projected
continuation and *no* needs a prior rejection; a bipolar question is the disjunction of the two
monopolar questions and projects both answers. A question with low negation is a monopolar
question about `¬φ`, and one with high negation proposes the addressee's refusal to commit to
`φ`, which is weaker. A matching question tag conjoins an assertion with the monopolar question
of the same content, and a reverse tag disjoins it with the monopolar question of the negation.

## Main statements

* `monopolar_not_inquisitive`, `bipolar_inquisitive`: a bipolar question raises an issue and a
  monopolar question does not, its bias being invisible to the issue projection.
* `table1`: licensing the three question types by the contextual evidence of Büring and
  Gunlogson reproduces the paper's table of acceptable uses.
* `matchingTag_eq`, `isLeast_reverseTag`: after a matching tag both participants are committed
  unless the addressee reacts, while a reverse tag keeps the root.

## Implementation notes

* The fixture is a two-world space, raining or not, rooted at the empty commitment state.
* Contextual evidence is the set of worlds it leaves open: the proposition, everything, or its
  complement. A monopolar question is licensed by evidence for its proposed assertion, a
  bipolar question by neutral evidence, and the high-negation question wherever the evidence
  is not for `φ`; the low-negation question has only the monopolar reading, its bipolar reading
  being blocked by the question without negation. These conditions are stated on the evidence
  and are not derived from the spaces.

## References

* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [D. Büring and C. Gunlogson, *Aren't Positive and Negative Polar Questions the Same?*
  (2000)][buring-gunlogson-2000]
-/

@[expose] public section

namespace Krifka2015

open Commitment Space Question

/-! ### Questions as meta-speech acts -/

section Questions

variable {A W : Type*} (C : Space (State A W)) (a : A) (φ : Set W) {d : State A W}

/-- A monopolar question keeps the root and proposes `a`'s assertion of `φ` (27). -/
def monopolarQuestion : Space (State A W) := C.restrict (C.assert a φ)

/-- A bipolar question keeps the root and proposes `a`'s assertion of `φ` or of `¬φ` (23). -/
def bipolarQuestion : Space (State A W) := C.restrict (↑(C.assert a φ) ∪ ↑(C.assert a φᶜ))

/-- A high-negation question keeps the root and proposes `a`'s refusal `¬S⊢φ` (39). -/
def highNegationQuestion : Space (State A W) := C.restrict (C.update {refuse a φ})

theorem mem_monopolarQuestion :
    d ∈ monopolarQuestion C a φ ↔ d = C.root ∨ d ∈ C ∧ commit a φ ∈ d := by
  rw [monopolarQuestion, assert, restrict_coe_update, mem_restrict, Set.mem_Ici]
  exact or_congr_right (and_congr_right fun _ ↦ Set.singleton_subset_iff)

theorem mem_highNegationQuestion :
    d ∈ highNegationQuestion C a φ ↔ d = C.root ∨ d ∈ C ∧ refuse a φ ∈ d := by
  rw [highNegationQuestion, restrict_coe_update, mem_restrict, Set.mem_Ici]
  exact or_congr_right (and_congr_right fun _ ↦ Set.singleton_subset_iff)

/-- A bipolar question is the disjunction of the two monopolar questions (31). -/
theorem coe_bipolarQuestion :
    (bipolarQuestion C a φ : Set (State A W)) =
      ↑(monopolarQuestion C a φ) ∪ ↑(monopolarQuestion C a φᶜ) :=
  C.coe_restrict_union _ _

end Questions

/-! ### The fixture -/

/-- In one world it is raining and in the other it is not. -/
inductive Weather
  | rain
  | noRain
  deriving DecidableEq

/-- It is raining. -/
def raining : Set Weather := {.rain}

theorem raining_ne_compl : raining ≠ rainingᶜ := fun h ↦
  (Set.ext_iff.1 h .rain).1 rfl rfl

/-- The initial commitment space has no commitments and leaves every development licit. -/
def C₀ : Space (State Discourse.Role Weather) := Space.Ici ∅

theorem mem_insert_empty_iff {x y : Commitment Discourse.Role Weather} :
    x ∈ insert y (∅ : State Discourse.Role Weather) ↔ x = y := by simp

theorem contextSet_insert_commit_empty (a : Discourse.Role) (φ : Set Weather) :
    contextSet (insert (commit a φ) (∅ : State Discourse.Role Weather)) = φ := by
  rw [contextSet_insert_of_commit rfl, contextSet_empty, Set.inter_univ]
  rfl

/-! ### Assertion (14) -/

/-- An assertion re-roots the space at the state recording the speaker's commitment. -/
theorem assert_root :
    (C₀.assert .speaker raining).root = insert (commit .speaker raining) ∅ := rfl

/-- Krifka's root narrows at once; the Table of [farkas-bruce-2010] leaves the common ground as
it was (p. 331). -/
theorem assert_contextSet_vs_farkasBruce_cg :
    contextSet (C₀.assert .speaker raining).root = raining ∧
      ((Table.empty : Table Discourse.Role Weather).assert .speaker raining).commonGround = ⊤ :=
  ⟨contextSet_insert_commit_empty _ _, rfl⟩

/-! ### Questions (23)–(28) -/

/-- A monopolar question keeps the root (27). -/
theorem monopolar_root : (monopolarQuestion C₀ .addressee raining).root = ∅ := rfl

theorem insert_commit_mem_monopolarQuestion (φ : Set Weather) :
    insert (commit .addressee φ) ∅ ∈ monopolarQuestion C₀ .addressee φ :=
  (mem_monopolarQuestion ..).2 (Or.inr ⟨Set.empty_subset _, Set.mem_insert _ _⟩)

/-- *Yes* is a projected continuation of the monopolar question (28a). -/
theorem monopolar_yes_mem :
    insert (commit .addressee raining) ∅ ∈ monopolarQuestion C₀ .addressee raining :=
  insert_commit_mem_monopolarQuestion raining

/-- *No* is not a projected continuation, since it requires a prior rejection (28b). -/
theorem monopolar_no_not_mem :
    insert (commit .addressee rainingᶜ) ∅ ∉ monopolarQuestion C₀ .addressee raining := by
  rw [mem_monopolarQuestion]
  rintro (h | ⟨-, h⟩)
  · exact (Set.insert_nonempty _ _).ne_empty h
  · exact raining_ne_compl (congrArg content (mem_insert_empty_iff.1 h))

/-- Both answers are projected continuations of the bipolar question (24). -/
theorem bipolar_yes_mem :
    insert (commit .addressee raining) ∅ ∈ bipolarQuestion C₀ .addressee raining :=
  (coe_bipolarQuestion ..).ge (Or.inl monopolar_yes_mem)

theorem bipolar_no_mem :
    insert (commit .addressee rainingᶜ) ∅ ∈ bipolarQuestion C₀ .addressee raining :=
  (coe_bipolarQuestion ..).ge (Or.inr (insert_commit_mem_monopolarQuestion rainingᶜ))

/-! ### Negated questions (29), (39) -/

/-- High negation projects the addressee's refusal (39). -/
theorem highNegation_refusal_mem :
    insert (refuse .addressee raining) ∅ ∈ highNegationQuestion C₀ .addressee raining :=
  (mem_highNegationQuestion ..).2 (Or.inr ⟨Set.empty_subset _, Set.mem_insert _ _⟩)

/-- `¬S₂⊢φ` is weaker than `S₂⊢¬φ` (p. 340), since a consistent commitment to `¬φ` already
excludes a commitment to `φ`. -/
theorem not_mem_slate_of_commit_compl (K : State Discourse.Role Weather)
    (h : commit .addressee rainingᶜ ∈ K) (hne : (contextSet (ofCommitter K .addressee)).Nonempty) :
    raining ∉ slate (ofCommitter K .addressee) :=
  not_mem_slate_of_compl_mem _ ⟨_, ⟨⟨h, rfl⟩, rfl⟩, rfl⟩ hne

/-! ### The issue projection -/

/-- Every continuation of the monopolar question records the addressee's commitment, so its
context set lies inside the proposed proposition. -/
theorem monopolar_continuation_subset {φ : Set Weather} {c : State Discourse.Role Weather}
    (hc : c ∈ (monopolarQuestion C₀ .addressee φ).continuations) : contextSet c ⊆ φ := by
  obtain ⟨hc, hne⟩ := hc
  rcases (mem_monopolarQuestion ..).1 hc with rfl | ⟨-, hc⟩
  · exact absurd rfl hne
  · exact contextSet_subset_of_mem_contents _ ⟨_, ⟨hc, rfl⟩, rfl⟩

theorem monopolar_continuation_mem :
    insert (commit .addressee raining) ∅ ∈
      (monopolarQuestion C₀ .addressee raining).continuations :=
  ⟨monopolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩

/-- A monopolar question raises no inquisitive issue, so its bias is invisible to the issue
observable. -/
theorem monopolar_not_inquisitive :
    ¬ (monopolarQuestion C₀ .addressee raining).toIssue.IsInquisitive := by
  intro h
  have hmem : raining ∈ (monopolarQuestion C₀ .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, monopolar_continuation_mem,
      (contextSet_insert_commit_empty _ _).ge⟩)
  refine h ?_
  have : (monopolarQuestion C₀ .addressee raining).toIssue.info = raining := by
    refine Set.Subset.antisymm (Set.sUnion_subset fun i hi ↦ ?_) (Set.subset_sUnion_of_mem hmem)
    rcases (mem_toIssue_iff _).1 hi with ⟨h0, -⟩ | ⟨c, hc, hic⟩
    · exact absurd monopolar_continuation_mem (h0 ▸ Set.notMem_empty _)
    · exact hic.trans (monopolar_continuation_subset hc)
  rw [this]
  exact hmem

/-- Every continuation of the bipolar question records one of the two answers. -/
theorem bipolar_continuation_subset {c : State Discourse.Role Weather}
    (hc : c ∈ (bipolarQuestion C₀ .addressee raining).continuations) :
    contextSet c ⊆ raining ∨ contextSet c ⊆ rainingᶜ :=
  ((coe_bipolarQuestion ..).le hc.1).imp
    (fun h ↦ monopolar_continuation_subset ⟨h, hc.2⟩)
    (fun h ↦ monopolar_continuation_subset ⟨h, hc.2⟩)

/-- A bipolar question raises a genuine issue. -/
theorem bipolar_inquisitive : (bipolarQuestion C₀ .addressee raining).toIssue.IsInquisitive := by
  intro hinfo
  have hyes : raining ∈ (bipolarQuestion C₀ .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, ⟨bipolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩,
      (contextSet_insert_commit_empty _ _).ge⟩)
  have hno : rainingᶜ ∈ (bipolarQuestion C₀ .addressee raining).toIssue :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, ⟨bipolar_no_mem, (Set.insert_nonempty _ _).ne_empty⟩,
      (contextSet_insert_commit_empty _ _).ge⟩)
  have hrain : Weather.rain ∈ (bipolarQuestion C₀ .addressee raining).toIssue.info :=
    Set.subset_sUnion_of_mem hyes rfl
  have hnoRain : Weather.noRain ∈ (bipolarQuestion C₀ .addressee raining).toIssue.info :=
    Set.subset_sUnion_of_mem hno fun h ↦ Weather.noConfusion h
  rcases (mem_toIssue_iff _).1 hinfo with ⟨h0, -⟩ | ⟨c, hc, hsub⟩
  · have hmem : insert (commit .addressee raining) ∅ ∈
        (bipolarQuestion C₀ .addressee raining).continuations :=
      ⟨bipolar_yes_mem, (Set.insert_nonempty _ _).ne_empty⟩
    rw [h0] at hmem
    exact hmem
  · rcases bipolar_continuation_subset hc with h | h
    · exact Weather.noConfusion (h (hsub hnoRain))
    · exact h (hsub hrain) rfl

/-! ### Table 1 -/

/-- The contextual evidence of [buring-gunlogson-2000] leaves open `φ`, its complement, or every
world, according to the sign of `φ` it supports. -/
def evidence (φ : Set Weather) : SignType → Set Weather
  | .pos => φ
  | .neg => φᶜ
  | .zero => Set.univ

/-- A monopolar question proposing `S₂⊢φ` is licensed by evidence for `φ`. -/
def MonopolarLicensed (E φ : Set Weather) : Prop := E ⊆ φ

/-- A bipolar question is licensed by neutral evidence. -/
def BipolarLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ ∧ ¬ E ⊆ φᶜ

/-- The high-negation question, proposing the refusal `¬S₂⊢φ`, is licensed wherever the
evidence is not for `φ`. -/
def HighNegationLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ

/-- Each question is licensed on particular readings. The question without negation, `none`, is
licensed on either of its readings; the question with low negation, about `¬φ`
(`some .negative`), only on the monopolar reading of `¬φ`; the question with high negation,
about `φ` (`some .positive`), as such. -/
def Licensed (E φ : Set Weather) : Option Polarity → Prop
  | none => MonopolarLicensed E φ ∨ BipolarLicensed E φ
  | some .negative => MonopolarLicensed E φᶜ
  | some .positive => HighNegationLicensed E φ

theorem raining_ne_empty : raining ≠ ∅ := (Set.singleton_nonempty _).ne_empty

theorem raining_ne_univ : raining ≠ Set.univ := fun h ↦
  Weather.noConfusion (Set.eq_univ_iff_forall.1 h .noRain)

/-- Licensing reproduces Table 1. With evidence for `φ` only the question without negation is
licensed, read monopolar; with neutral evidence the question without negation, read bipolar, and
the high-negation question; with evidence against `φ` both negated questions and not the
question without negation. -/
theorem table1 (e : SignType) :
    (Licensed (evidence raining e) raining none ↔ e ≠ -1) ∧
      (Licensed (evidence raining e) raining (some .negative) ↔ e = -1) ∧
      (Licensed (evidence raining e) raining (some .positive) ↔ e ≠ 1) := by
  cases e <;> simp [Licensed, MonopolarLicensed, BipolarLicensed,
    HighNegationLicensed, evidence, raining_ne_empty, raining_ne_univ]

/-- The licensing conditions are the evidence conditions of [buring-gunlogson-2000]. -/
theorem licensed_iff_felicitous (r : Option Polarity) (e : SignType) :
    Licensed (evidence raining e) raining r ↔ BuringGunlogson2000.Felicitous r e := by
  have h : ∀ e : SignType, (e ≠ -1 ↔ BuringGunlogson2000.Felicitous none e) ∧
      (e = -1 ↔ BuringGunlogson2000.Felicitous (some .negative) e) ∧
      (e ≠ 1 ↔ BuringGunlogson2000.Felicitous (some .positive) e) := by decide
  rcases r with _ | _ | _
  exacts [(table1 e).1.trans (h e).1, (table1 e).2.2.trans (h e).2.2,
    (table1 e).2.1.trans (h e).2.1]

/-! ### Question tags (44), (45) -/

section Tags

variable {W : Type*} (C : Space (State Discourse.Role W)) (φ : Set W)

/-- A matching tag (44) conjoins the assertion with the monopolar question of the same
content. -/
def matchingTag : Set (State Discourse.Role W) :=
  ↑(C.assert .speaker φ) ∩ ↑(monopolarQuestion C .addressee φ)

/-- A reverse tag (45) disjoins the assertion with the monopolar question of the negation. -/
def reverseTag : Set (State Discourse.Role W) :=
  ↑(C.assert .speaker φ) ∪ ↑(monopolarQuestion C .addressee φᶜ)

/-- A matching tag is the speaker's assertion followed by the addressee's, so the proposed
commitments obtain unless the addressee reacts. -/
theorem matchingTag_eq (hk : commit .speaker φ ∉ C.root)
    (h : insert (commit .addressee φ) (insert (commit .speaker φ) C.root) ∈ C) :
    matchingTag C φ = ↑((C.assert .speaker φ).assert .addressee φ) := by
  ext d
  simp only [matchingTag, Set.mem_inter_iff, SetLike.mem_coe, mem_assert, mem_monopolarQuestion,
    root_assert]
  constructor
  · rintro ⟨hs, rfl | ⟨-, ha⟩⟩
    · exact absurd ((C.root_mem_assert_iff _ _ _).1 ((C.mem_assert _ _ _).2 hs)) hk
    · exact Or.inr ⟨hs, ha⟩
  · rintro (rfl | ⟨hs, ha⟩)
    · exact ⟨Or.inr ⟨h, Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩,
        Or.inr ⟨h, Set.mem_insert _ _⟩⟩
    · refine ⟨hs, Or.inr ⟨?_, ha⟩⟩
      rcases hs with rfl | hs
      · rwa [Set.insert_eq_of_mem ha] at h
      · exact hs.1

/-- A reverse tag keeps the root, the speaker's commitment being only one branch. -/
theorem isLeast_reverseTag : IsLeast (reverseTag C φ) C.root :=
  ⟨Or.inr (Space.root_mem _), by
    rintro d (hd | hd)
    · exact (Set.subset_insert _ _).trans ((C.assert .speaker φ).root_le hd)
    · exact (monopolarQuestion C .addressee φᶜ).root_le hd⟩

end Tags

/-- After a matching tag both participants are committed at the root. -/
theorem isLeast_matchingTag :
    IsLeast (matchingTag C₀ raining)
      (insert (commit .addressee raining) (insert (commit .speaker raining) ∅)) := by
  rw [matchingTag_eq C₀ raining (Set.notMem_empty _) (Set.empty_subset _)]
  exact Space.isLeast _

/-- The branches of a reverse tag are the speaker's assertion and the addressee's assertion of
the negation. -/
theorem reverseTag_branches :
    insert (commit .speaker raining) ∅ ∈ reverseTag C₀ raining ∧
      insert (commit .addressee rainingᶜ) ∅ ∈ reverseTag C₀ raining :=
  ⟨Or.inl (Space.root_mem _), Or.inr (insert_commit_mem_monopolarQuestion rainingᶜ)⟩

end Krifka2015
