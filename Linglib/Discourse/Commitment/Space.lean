import Mathlib.Order.Interval.Set.Basic
import Linglib.Discourse.Commitment.Basic
import Linglib.Semantics.Questions.Basic
import Linglib.Discourse.QUD.Issue
import Linglib.Discourse.Roles

/-!
# Commitment spaces

A commitment space is a set of discourse states with a least member, its root: the current
state together with its projected continuations ([cohen-krifka-2014] (22), [krifka-2015] (2),
[van-der-leer-2026] Definition 8). Over any preorder of states the operations are the same:
a basic speech act re-roots the space at the updated root and keeps the states above it, which
on a projected continuation is Cohen and Krifka's restriction `C + A = {c ∈ C | √C + A ⊆ c}`;
a question keeps the root and proposes continuations; a denegation removes the states an act
would reach, which is a rooted space exactly when the act is not redundant, so that two
denegations cancel and de Morgan's laws hold for them ([cohen-krifka-2014] (28), (34)).

Commitment Space Semantics is the instance over sets of `Commitment`s ordered by inclusion,
where the root is the intersection of the space: assertion `S⊢φ`, refusal `¬S⊢φ`, monopolar,
bipolar and high-negation questions ([krifka-2015] (14), (27), (23), (39)), and `GRANT φ` as the
denegation of asserting `¬φ` ([cohen-krifka-2014] (38)). The issue a space raises, its
`Discourse.HasIssue` projection, is settled by the information states inside some
continuation's context set.

## Main definitions

* `Commitment.Space S` — rooted sets of states, with `restrict`, `reroot`, `propose`, `sdiff`,
  `union`, `denegate`, and the free space `full`.
* `Space.assert`, `Space.refuse`, `Space.monopolarQuestion`, `Space.bipolarQuestion`,
  `Space.highNegationQuestion`, `Space.grant` — Commitment Space Semantics.
* `Space.toIssue` — the issue projection.

## Main results

* `Space.reroot_eq_restrict`, `Space.assert_states_of_mem` — a projected assertion is Cohen and
  Krifka's restriction.
* `Space.sdiff_sdiff_states`, `Space.union_sdiff_sdiff`, `Space.sdiff_grant_states` — (28), (34)
  and (40) of [cohen-krifka-2014].
* `Space.assert_assert_comm`, `Space.full_assert` — assertions commute, and on the free space
  assertion is the free space of the extended root.

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
-/

namespace Commitment


/-- A commitment space: a set of states with a least member, its root. -/
@[ext]
structure Space (S : Type*) [Preorder S] where
  states : Set S
  root : S
  isLeast : IsLeast states root

namespace Space

section Preorder

variable {S : Type*} [Preorder S] (C : Space S) {c d : S}

theorem root_mem : C.root ∈ C.states := C.isLeast.1
theorem root_le (hc : c ∈ C.states) : C.root ≤ c := C.isLeast.2 hc

/-- The continuations: the members other than the root. -/
def continuations : Set S := C.states \ {C.root}

/-- The space with only its root. -/
def singleton (c : S) : Space S := ⟨{c}, c, isLeast_singleton⟩

/-- The free space on `c`: every state above `c`. -/
def full (c : S) : Space S := ⟨Set.Ici c, c, isLeast_Ici⟩

/-- `C` restricted to the members above `c`, re-rooted at `c`. -/
def restrict (hc : c ∈ C.states) : Space S :=
  ⟨{d ∈ C.states | c ≤ d}, c, ⟨⟨hc, le_rfl⟩, fun _ h => h.2⟩⟩

/-- Re-root `C` at `c`, keeping the members above `c`. -/
def reroot (c : S) : Space S :=
  ⟨insert c {d ∈ C.states | c ≤ d}, c, ⟨Set.mem_insert _ _, by
    rintro d (rfl | ⟨-, hd⟩)
    · exact le_rfl
    · exact hd⟩⟩

/-- Keep the root and adjoin the states of `D`, all above the root. -/
def propose (D : Set S) (h : C.root ∈ lowerBounds D) : Space S :=
  ⟨insert C.root D, C.root, ⟨Set.mem_insert _ _, by
    rintro d (rfl | hd)
    · exact le_rfl
    · exact h hd⟩⟩

/-- Remove the members of `D`, which must miss the root. -/
def sdiff (D : Set S) (h : C.root ∉ D) : Space S :=
  ⟨C.states \ D, C.root, ⟨⟨C.root_mem, h⟩, fun _ hd => C.root_le hd.1⟩⟩

/-- The union of two spaces with the same root. -/
def union (C D : Space S) (h : C.root = D.root) : Space S :=
  ⟨C.states ∪ D.states, C.root, ⟨Or.inl C.root_mem, by
    rintro x (hx | hx)
    · exact C.root_le hx
    · exact h ▸ D.root_le hx⟩⟩

@[simp] theorem singleton_states (c : S) : (singleton c).states = {c} := rfl
@[simp] theorem singleton_root (c : S) : (singleton c).root = c := rfl
@[simp] theorem full_states (c : S) : (full c).states = Set.Ici c := rfl
@[simp] theorem full_root (c : S) : (full c).root = c := rfl
@[simp] theorem restrict_states (hc : c ∈ C.states) :
    (C.restrict hc).states = {d ∈ C.states | c ≤ d} := rfl
@[simp] theorem restrict_root (hc : c ∈ C.states) : (C.restrict hc).root = c := rfl
@[simp] theorem reroot_states (c : S) :
    (C.reroot c).states = insert c {d ∈ C.states | c ≤ d} := rfl
@[simp] theorem reroot_root (c : S) : (C.reroot c).root = c := rfl
@[simp] theorem propose_states (D : Set S) (h : C.root ∈ lowerBounds D) :
    (C.propose D h).states = insert C.root D := rfl
@[simp] theorem propose_root (D : Set S) (h : C.root ∈ lowerBounds D) :
    (C.propose D h).root = C.root := rfl
@[simp] theorem sdiff_states (D : Set S) (h : C.root ∉ D) : (C.sdiff D h).states = C.states \ D :=
  rfl
@[simp] theorem sdiff_root (D : Set S) (h : C.root ∉ D) : (C.sdiff D h).root = C.root := rfl
@[simp] theorem union_states (C D : Space S) (h : C.root = D.root) :
    (C.union D h).states = C.states ∪ D.states := rfl
@[simp] theorem union_root (C D : Space S) (h : C.root = D.root) : (C.union D h).root = C.root :=
  rfl

theorem root_mem_lowerBounds_reroot (h : C.root ≤ c) :
    C.root ∈ lowerBounds (C.reroot c).states := by
  rintro d (rfl | ⟨-, hd⟩)
  · exact h
  · exact h.trans hd

/-- Re-rooting at a member is restriction. -/
theorem reroot_eq_restrict (hc : c ∈ C.states) : C.reroot c = C.restrict hc := by
  ext x
  · simp only [reroot_states, restrict_states, Set.mem_insert_iff, Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, Or.inr⟩
    rcases h with rfl | h
    exacts [⟨hc, le_rfl⟩, h]
  · rfl

/-- Restriction is transitive. -/
theorem restrict_restrict (hc : c ∈ C.states) (hd : d ∈ (C.restrict hc).states) :
    (C.restrict hc).restrict hd = C.restrict hd.1 := by
  ext x
  · simp only [restrict_states, Set.mem_ofPred_eq]
    exact ⟨fun ⟨⟨hx, _⟩, hdx⟩ => ⟨hx, hdx⟩, fun ⟨hx, hdx⟩ => ⟨⟨hx, hd.2.trans hdx⟩, hdx⟩⟩
  · rfl

/-- On the free space, re-rooting above the root is the free space of the new root. -/
theorem reroot_full (h : c ≤ d) : (full c).reroot d = full d := by
  ext x
  · simp only [reroot_states, full_states, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_Ici]
    refine ⟨fun hx => ?_, fun hx => Or.inr ⟨h.trans hx, hx⟩⟩
    rcases hx with rfl | hx
    exacts [le_rfl, hx.2]
  · rfl

/-- Two denegations cancel ([cohen-krifka-2014] (28)). -/
theorem sdiff_sdiff_states {D : Set S} (hD : D ⊆ C.states) (h : C.root ∉ D) :
    C.states \ (C.sdiff D h).states = D :=
  Set.sdiff_sdiff_cancel_left hD

/-- De Morgan for denegations ([cohen-krifka-2014] (34)): `∼A ∨ ∼B = ∼[A & B]`. -/
theorem union_sdiff_sdiff (D E : Set S) (hD : C.root ∉ D) (hE : C.root ∉ E) :
    (C.sdiff D hD).union (C.sdiff E hE) rfl = C.sdiff (D ∩ E) fun h => hD h.1 :=
  Space.ext Set.sdiff_inter.symm rfl

end Preorder

section PartialOrder

variable {S : Type*} [PartialOrder S] (C : Space S) {c d : S}

/-- The root is the unique least member. -/
theorem eq_root (h : IsLeast C.states c) : c = C.root := h.unique C.isLeast

/-- Re-rooting twice upward is re-rooting once. -/
theorem reroot_reroot (h : c ≤ d) : (C.reroot c).reroot d = C.reroot d := by
  ext x
  · simp only [reroot_states, Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨rfl | ⟨hx, -⟩, hdx⟩)
      · exact Or.inl rfl
      · exact Or.inl (le_antisymm h hdx)
      · exact Or.inr ⟨hx, hdx⟩
    · rintro (rfl | ⟨hx, hdx⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr ⟨hx, h.trans hdx⟩, hdx⟩
  · rfl

end PartialOrder

end Space


/-! ### Commitment space semantics -/

namespace Space

variable {A W : Type*} (C : Space (Set (Commitment A W))) (a : A) (φ : Set W)
  (force : Commitment.Force)

/-- `C + S⊢φ` ([cohen-krifka-2014] (23), [krifka-2015] (3), (14)): re-root at the root
extended by `a`'s commitment to `φ`. -/
def assert (force : Commitment.Force := .doxastic) : Space (Set (Commitment A W)) :=
  C.reroot (insert ⟨a, φ, .commit, force, .selfGenerated⟩ C.root)

/-- `C + ¬S⊢φ` ([krifka-2015] (39)): re-root at the root extended by `a`'s refusal to commit
to `φ`. -/
def refuse (force : Commitment.Force := .doxastic) : Space (Set (Commitment A W)) :=
  C.reroot (insert ⟨a, φ, .refuse, force, .selfGenerated⟩ C.root)

/-- A monopolar question ([krifka-2015] (27)): keep the root and propose the addressee's
assertion of `φ`. -/
def monopolarQuestion : Space (Set (Commitment A W)) :=
  C.propose (C.assert a φ).states (C.root_mem_lowerBounds_reroot (Set.subset_insert _ _))

/-- A bipolar question ([krifka-2015] (23), (31)): the disjunction of the two monopolar
questions. -/
def bipolarQuestion : Space (Set (Commitment A W)) :=
  (C.monopolarQuestion a φ).union (C.monopolarQuestion a φᶜ) rfl

/-- A high-negation question ([krifka-2015] (39)): propose the addressee's refusal. -/
def highNegationQuestion : Space (Set (Commitment A W)) :=
  C.propose (C.refuse a φ).states (C.root_mem_lowerBounds_reroot (Set.subset_insert _ _))

/-- Denegation `C + ∼A` ([cohen-krifka-2014] (26), [krifka-2015] (5)): the states not reached by
`A`, for a non-redundant `A`. -/
def denegate {S : Type*} [Preorder S] (C : Space S) (act : Space S → Space S)
    (h : C.root ∉ (act C).states) : Space S :=
  C.sdiff (act C).states h

@[simp] theorem assert_root :
    (C.assert a φ force).root = insert ⟨a, φ, .commit, force, .selfGenerated⟩ C.root := rfl
@[simp] theorem refuse_root :
    (C.refuse a φ force).root = insert ⟨a, φ, .refuse, force, .selfGenerated⟩ C.root := rfl
@[simp] theorem monopolarQuestion_root : (C.monopolarQuestion a φ).root = C.root := rfl
@[simp] theorem bipolarQuestion_root : (C.bipolarQuestion a φ).root = C.root := rfl
@[simp] theorem highNegationQuestion_root : (C.highNegationQuestion a φ).root = C.root := rfl
@[simp] theorem denegate_root {S : Type*} [Preorder S] (C : Space S) (act) (h) :
    (C.denegate act h).root = C.root := rfl

/-- The root is in the result of an assertion iff the assertion is redundant. -/
theorem root_mem_assert_iff :
    C.root ∈ (C.assert a φ force).states ↔
      (⟨a, φ, .commit, force, .selfGenerated⟩ : Commitment A W) ∈ C.root := by
  simp only [assert, reroot_states, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.insert_subset_iff,
    Set.Subset.rfl, and_true]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Set.insert_eq_self.1 h.symm
    · exact h
  · exact fun h => Or.inr ⟨C.root_mem, h⟩

/-- `GRANT φ = ∼ASSERT ¬φ` ([cohen-krifka-2014] (38)), for a non-redundant `ASSERT ¬φ`. -/
def grant (h : (⟨a, φᶜ, .commit, .doxastic, .selfGenerated⟩ : Commitment A W) ∉ C.root) :
    Space (Set (Commitment A W)) :=
  C.denegate (·.assert a φᶜ) (mt (C.root_mem_assert_iff a φᶜ .doxastic).1 h)

@[simp] theorem grant_root (h) : (C.grant a φ h).root = C.root := rfl

/-- The performative update: the root commits `a` to `φ`. -/
theorem mem_contents_assert_root : φ ∈ contents (C.assert a φ force).root :=
  ⟨_, ⟨Set.mem_insert _ _, rfl⟩, rfl⟩

/-- The context set narrows by exactly `φ`. -/
theorem contextSet_assert_root : contextSet (C.assert a φ force).root = φ ∩ contextSet C.root :=
  contextSet_insert_of_commit rfl

/-- Consecutive assertions commute ([cohen-krifka-2014] (31), [krifka-2015] (6)). -/
theorem assert_assert_comm (b : A) (ψ : Set W) (g : Commitment.Force) :
    (C.assert a φ force).assert b ψ g = (C.assert b ψ g).assert a φ force := by
  simp only [assert, reroot_root]
  rw [reroot_reroot _ (Set.subset_insert _ _), reroot_reroot _ (Set.subset_insert _ _),
    Set.insert_comm]

/-- On the free space, assertion is the free space of the extended root. -/
theorem full_assert (c : Set (Commitment A W)) :
    (full c).assert a φ force = full (insert ⟨a, φ, .commit, force, .selfGenerated⟩ c) :=
  reroot_full (Set.subset_insert _ _)

/-- A projected assertion is a restriction ([cohen-krifka-2014] (23)). -/
theorem assert_states_of_mem (h : insert ⟨a, φ, .commit, force, .selfGenerated⟩ C.root ∈ C.states) :
    (C.assert a φ force).states =
      {d ∈ C.states | insert ⟨a, φ, .commit, force, .selfGenerated⟩ C.root ⊆ d} := by
  rw [assert, reroot_eq_restrict _ h, restrict_states]

/-- `ASSERT φ = ∼GRANT ¬φ` ([cohen-krifka-2014] (40)), for a projected, non-redundant assertion. -/
theorem sdiff_grant_states
    (hmem : insert ⟨a, φ, .commit, .doxastic, .selfGenerated⟩ C.root ∈ C.states)
    (h : (⟨a, φ, .commit, .doxastic, .selfGenerated⟩ : Commitment A W) ∉ C.root) :
    C.states \ (C.grant a φᶜ (by simpa using h)).states = (C.assert a φ).states := by
  have : (C.assert a φ).states ⊆ C.states := by
    rw [assert_states_of_mem _ _ _ _ hmem]; exact fun _ hd => hd.1
  simp only [grant, denegate, compl_compl]
  exact C.sdiff_sdiff_states this _

open scoped Classical in
/-- The issue a space raises: with no continuations, the trivial issue over the root's context
set; otherwise an information state settles it iff it lies inside some continuation's. -/
noncomputable def toIssue : Question W :=
  if C.continuations = ∅ then Question.ofSet (contextSet C.root)
  else ⨆ c ∈ C.continuations, Question.ofSet (contextSet c)

noncomputable instance : Discourse.HasIssue (Space (Set (Commitment A W))) W := ⟨toIssue⟩

theorem mem_toIssue_iff {i : Set W} :
    i ∈ C.toIssue ↔
      (C.continuations = ∅ ∧ i ⊆ contextSet C.root) ∨ ∃ c ∈ C.continuations, i ⊆ contextSet c := by
  unfold toIssue
  split_ifs with h
  · simp [h, Question.mem_ofSet]
  · simp only [h, false_and, false_or, Question.mem_biSup_iff, Question.mem_ofSet]
    refine ⟨fun h' => h'.elim (fun e => ?_) id, Or.inr⟩
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨c, hc, e ▸ Set.empty_subset _⟩

/-- The common ground of a space is what its root entails; the speaker's assertion is
Stalnakerian on it. -/
instance : HasAssertion (Space (Set (Commitment Discourse.DiscourseRole W))) W where
  commonGround C := slate C.root
  initial := full ∅
  assert C φ := C.assert .speaker φ
  commonGround_initial := slate_empty
  commonGround_assert _ _ := slate_insert_of_commit rfl

end Space



end Commitment
