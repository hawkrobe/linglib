import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.QUD.Issue
import Linglib.Semantics.Questions.Hamblin

/-!
# The Table

This file defines the context structure of [farkas-bruce-2010]: the participants' discourse
commitments, the common ground, and the Table, a stack of the issues under discussion with the
most recent on top. A declarative raises its proposition as an issue, `Question.ofSet p`, and a
polar interrogative raises `Question.polar p`; the complete answers of an issue are its
alternatives, `Question.alt`, and a common ground settles an issue when it entails one of them.
Each issue on the Table projects the common grounds that would settle it, and the projected set
is derived from the common ground and the stack. The moves of the paper are functions on the
structure, and the file proves what each does to the projected set, the commitment lists, and
the Table.

A Table is a discourse state in both projections: its common ground is the `cg` coordinate
(`HasCommonGround`) and its current issue is the top of the stack (`Discourse.HasIssue`). It is
not a `HasAssertion` instance under its own `assert`, which leaves the common ground alone and
moves only the projected set.

## Main definitions

* `Question.SettledBy P f`: the common ground `f` entails a complete answer of the issue `P`.
* `Commitment.Table A W`: the context structure, with `Table.dc a` the propositions `a` has
  publicly committed to and `Table.projectedSet` the projected set, the fold of the paper's
  `ps ∪ P` over the stack.
* `Table.IsStable`, `Table.InCrisis`, `Table.Shared`: an empty Table; an inconsistent common
  ground or no consistent projected common ground; a proposition every participant is
  committed to.
* `Table.assert`, `Table.polarQuestion`, `Table.confirm`, `Table.increaseCG`,
  `Table.agreeToDisagree`: the default assertion (9), the default polar question (12),
  assertion confirmation (16), the common-ground increasing operation M' (17), and agreeing to
  disagree (23). Total denial (22) is `assert` of the negation.

## Main results

* `Table.le_cg_of_mem_projectedSet`, `Table.settledBy_of_mem_projectedSet`: a projected common
  ground refines the current one and settles every issue on the Table.
* `Table.inCrisis_iff`: with the projected set derived, crisis is having no consistent
  projected common ground; the inconsistent-common-ground clause is subsumed.
* `Table.projectedSet_assert_compl`, `Table.inCrisis_assert_compl`: a denied assertion projects
  nothing consistent (21) and leaves the conversation in crisis.
* `Table.increaseCG_push_of_settledBy`, `Table.increaseCG_commit_self`, `Table.dc_increaseCG`:
  M' pops the issues the new common ground settles and strips the shared proposition from every
  commitment list.
* `Table.agreeToDisagree_assert_assert`: agreeing to disagree removes the contradictory pair
  from the Table and keeps the commitments (23).

## Implementation notes

* The paper notes that the projected set can always be rebuilt from the common ground and the
  Table, so it is derived rather than stored.
* Whether a common ground entails a complete answer is not decidable, so `Table.increaseCG`,
  which pops issues while it does, is classical and noncomputable.
* The paper's `remove` deletes the top-most occurrence of an item, and agreeing to disagree
  applies it to the denial on top of the assertion it denies, so `Table.agreeToDisagree` pops
  twice.
* `Table.confirm` records the confirming commitment as other-generated, the distinction of
  `Commitment.Source`.

## References

* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
-/

open Filter

namespace Question

variable {W : Type*} {P : Question W} {f g : Filter W} {p : Set W}

/-- The common ground `f` settles the issue `P` when it entails one of its complete answers. -/
def SettledBy (P : Question W) (f : Filter W) : Prop := ∃ q ∈ alt P, q ∈ f

theorem SettledBy.mono (h : f ≤ g) : P.SettledBy g → P.SettledBy f :=
  Exists.imp fun _ ⟨hq, hg⟩ ↦ ⟨hq, h hg⟩

/-- A common ground settling an issue has a context set resolving it. -/
theorem SettledBy.ker_mem (h : P.SettledBy f) : f.ker ∈ P :=
  let ⟨q, hq, hf⟩ := h
  P.downward_closed q (mem_of_mem_alt hq) _ (ker_mono (le_principal_iff.2 hf) |>.trans_eq
    (ker_principal q))

/-- The trivial issue is settled by every common ground. -/
@[simp] theorem settledBy_top : (⊤ : Question W).SettledBy f := ⟨_, by simp, univ_mem⟩

@[simp] theorem settledBy_ofSet : (ofSet p).SettledBy f ↔ p ∈ f := by simp [SettledBy]

/-- A common ground settles the polar question of `p` when it decides `p`. -/
@[simp] theorem settledBy_polar : (polar p).SettledBy f ↔ p ∈ f ∨ pᶜ ∈ f := by
  by_cases h : p = ∅ ∨ p = Set.univ
  · rcases h with rfl | rfl <;> simp [polar_empty, polar_univ]
  · simp [SettledBy, mem_alt_polar_of_nontrivial (not_or.1 h).1 (not_or.1 h).2]

end Question

namespace Commitment

open Question

/-- The context structure `K` of [farkas-bruce-2010]: the Table as a stack of issues, the
participants' discourse commitments, and the common ground. -/
@[ext]
structure Table (A W : Type*) where
  stack : List (Question W)
  commitments : State A W
  cg : Filter W

namespace Table

variable {A W : Type*} (K : Table A W) (a : A) (p : Set W) (P : Question W)

/-- The initial context: nothing on the Table, no commitments, the trivial common ground. -/
def empty : Table A W := ⟨[], ∅, ⊤⟩

instance : Inhabited (Table A W) := ⟨empty⟩

instance : HasCommonGround (Table A W) W := ⟨cg⟩

/-- The current issue is the top of the Table, the trivial issue when the Table is empty. -/
instance : Discourse.HasIssue (Table A W) W := ⟨fun K ↦ K.stack.headD ⊤⟩

/-- A conversation is stable when its Table is empty. -/
def IsStable : Prop := K.stack = []

/-- `DC_a`: the propositions `a` has publicly committed to. -/
def dc : Set (Set W) := contents (ofCommitter K.commitments a)

/-- Every participant is committed to `p`. -/
def Shared : Prop := ∀ a : A, p ∈ K.dc a

/-! ### The projected set -/

/-- `ps ∪ P`: add each complete answer of `P` to each projected common ground, discarding the
inconsistent results. -/
def project (ps : Set (Filter W)) (P : Question W) : Set (Filter W) :=
  Set.image2 (fun f q ↦ f ⊓ 𝓟 q) ps (alt P) \ {⊥}

/-- The projected set, rebuilt from the common ground by the issues on the Table, oldest first:
the common grounds that canonically settle what is at issue. -/
def projectedSet : Set (Filter W) := K.stack.foldr (fun P ps ↦ project ps P) {K.cg}

/-- A conversation is in crisis when its common ground or every projected common ground is
inconsistent. -/
def InCrisis : Prop := K.cg = ⊥ ∨ ∀ f ∈ K.projectedSet, f = ⊥

/-! ### Moves -/

/-- Place an issue on the Table. -/
def push : Table A W := { K with stack := P :: K.stack }

/-- Remove the top issue. -/
def pop : Table A W := { K with stack := K.stack.tail }

/-- Commit `a` to `p`. -/
def commit (force : Commitment.Force := .doxastic) (source : Commitment.Source := .selfGenerated) :
    Table A W :=
  { K with commitments := insert (Commitment.commit a p force source) K.commitments }

/-- Default assertion (9): `a` commits to `p` and places the declarative's issue on the Table. -/
def assert : Table A W := (K.commit a p).push (ofSet p)

/-- Default polar question (12): place the interrogative's issue on the Table. -/
abbrev polarQuestion : Table A W := K.push (polar p)

/-- Assertion confirmation (16): the addressee commits to the asserted proposition, on the
strength of the assertion. -/
abbrev confirm : Table A W := K.commit a p .doxastic .otherGenerated

open scoped Classical in
/-- The common-ground increasing operation M' (17): `p` enters the common ground, leaves the
individual commitment lists, and the issues the new common ground settles are popped from the
top of the Table. -/
noncomputable def increaseCG : Table A W where
  stack := K.stack.dropWhile fun P ↦ decide (P.SettledBy (K.cg ⊓ 𝓟 p))
  commitments := {c ∈ K.commitments | c.content ≠ p}
  cg := K.cg ⊓ 𝓟 p

/-- Agreeing to disagree (23), from a Table with the denial on top of the assertion it denies:
the contradictory pair leaves the Table, the commitments stay. -/
def agreeToDisagree : Table A W := K.pop.pop

/-! ### Coordinates of the moves -/

@[simp] theorem empty_stack : (empty : Table A W).stack = [] := rfl
@[simp] theorem empty_commitments : (empty : Table A W).commitments = ∅ := rfl
@[simp] theorem empty_cg : (empty : Table A W).cg = ⊤ := rfl
@[simp] theorem push_stack : (K.push P).stack = P :: K.stack := rfl
@[simp] theorem push_commitments : (K.push P).commitments = K.commitments := rfl
@[simp] theorem push_cg : (K.push P).cg = K.cg := rfl
@[simp] theorem pop_stack : K.pop.stack = K.stack.tail := rfl
@[simp] theorem pop_commitments : K.pop.commitments = K.commitments := rfl
@[simp] theorem pop_cg : K.pop.cg = K.cg := rfl
@[simp] theorem commit_stack (f s) : (K.commit a p f s).stack = K.stack := rfl
@[simp] theorem commit_commitments (f s) :
    (K.commit a p f s).commitments = insert (Commitment.commit a p f s) K.commitments := rfl
@[simp] theorem commit_cg (f s) : (K.commit a p f s).cg = K.cg := rfl
@[simp] theorem assert_stack : (K.assert a p).stack = ofSet p :: K.stack := rfl
@[simp] theorem assert_commitments :
    (K.assert a p).commitments = insert (Commitment.commit a p) K.commitments := rfl
@[simp] theorem assert_cg : (K.assert a p).cg = K.cg := rfl

open scoped Classical in
@[simp] theorem increaseCG_stack :
    (K.increaseCG p).stack = K.stack.dropWhile fun P ↦ decide (P.SettledBy (K.cg ⊓ 𝓟 p)) :=
  rfl
@[simp] theorem increaseCG_commitments :
    (K.increaseCG p).commitments = {c ∈ K.commitments | c.content ≠ p} := rfl
@[simp] theorem increaseCG_cg : (K.increaseCG p).cg = K.cg ⊓ 𝓟 p := rfl
@[simp] theorem agreeToDisagree_stack : K.agreeToDisagree.stack = K.stack.tail.tail := rfl
@[simp] theorem agreeToDisagree_commitments : K.agreeToDisagree.commitments = K.commitments :=
  rfl
@[simp] theorem agreeToDisagree_cg : K.agreeToDisagree.cg = K.cg := rfl

@[simp] theorem commonGround_eq : HasCommonGround.commonGround K = K.cg := rfl
@[simp] theorem toIssue_empty : Discourse.HasIssue.toIssue (empty : Table A W) = ⊤ := rfl
@[simp] theorem toIssue_push : Discourse.HasIssue.toIssue (K.push P) = P := rfl
@[simp] theorem toIssue_commit (f s) :
    Discourse.HasIssue.toIssue (K.commit a p f s) = Discourse.HasIssue.toIssue K := rfl
@[simp] theorem toIssue_assert : Discourse.HasIssue.toIssue (K.assert a p) = ofSet p := rfl

/-! ### Stability -/

@[simp] theorem empty_isStable : (empty : Table A W).IsStable := rfl

theorem not_isStable_push : ¬ (K.push P).IsStable := List.cons_ne_nil _ _

/-- A stable conversation has no issue. -/
theorem toIssue_of_isStable (h : K.IsStable) : Discourse.HasIssue.toIssue K = ⊤ := by
  change K.stack.headD ⊤ = ⊤
  rw [show K.stack = [] from h, List.headD_nil]

theorem isStable_increaseCG_of_isStable (h : K.IsStable) : (K.increaseCG p).IsStable := by
  show (K.increaseCG p).stack = []
  rw [increaseCG_stack, show K.stack = [] from h, List.dropWhile_nil]

/-! ### Discourse commitments -/

@[simp] theorem dc_empty : (empty : Table A W).dc a = ∅ := by
  simp [dc, ofCommitter, contents]

@[simp] theorem dc_push : (K.push P).dc = K.dc := rfl
@[simp] theorem dc_pop : K.pop.dc = K.dc := rfl
@[simp] theorem dc_agreeToDisagree : K.agreeToDisagree.dc = K.dc := rfl

@[simp] theorem dc_commit_self (f s) : (K.commit a p f s).dc a = insert p (K.dc a) := by
  rw [dc, dc, commit_commitments, ofCommitter_insert_of_eq _ _ _ (commit_committer a p f s),
    contents_insert_of_commit (commit_polarity a p f s), commit_content]

theorem dc_commit_of_ne (f s) {b : A} (h : b ≠ a) : (K.commit a p f s).dc b = K.dc b := by
  rw [dc, dc, commit_commitments,
    ofCommitter_insert_of_ne _ _ _ ((commit_committer a p f s).trans_ne h.symm)]

theorem mem_dc_commit_iff (f s) {b : A} {q : Set W} :
    q ∈ (K.commit a p f s).dc b ↔ (b = a ∧ q = p) ∨ q ∈ K.dc b := by
  by_cases hb : b = a
  · subst hb; simp
  · simp [dc_commit_of_ne _ _ _ _ _ hb, hb]

theorem mem_dc_commit_self (f s) : p ∈ (K.commit a p f s).dc a := by simp

@[simp] theorem dc_assert : (K.assert a p).dc a = insert p (K.dc a) := dc_commit_self K a p _ _

theorem dc_assert_of_ne {b : A} (h : b ≠ a) : (K.assert a p).dc b = K.dc b :=
  dc_commit_of_ne K a p _ _ h

/-- The asserted proposition enters the author's commitments. -/
theorem mem_dc_assert : p ∈ (K.assert a p).dc a := mem_dc_commit_self K a p _ _

/-- M' strips the shared proposition from every commitment list. -/
theorem dc_increaseCG : (K.increaseCG p).dc a = K.dc a \ {p} := by
  ext q
  simp only [dc, ofCommitter, contents, increaseCG_commitments, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, ⟨⟨⟨hc, hp⟩, ha⟩, hpol⟩, rfl⟩
    exact ⟨⟨c, ⟨⟨hc, ha⟩, hpol⟩, rfl⟩, hp⟩
  · rintro ⟨⟨c, ⟨⟨hc, ha⟩, hpol⟩, rfl⟩, hp⟩
    exact ⟨c, ⟨⟨⟨hc, hp⟩, ha⟩, hpol⟩, rfl⟩

/-! ### The moves on the Table -/

open scoped Classical in
/-- M' pops a settled issue from the top of the Table and goes on popping. -/
theorem increaseCG_push_of_settledBy (h : P.SettledBy (K.cg ⊓ 𝓟 p)) :
    (K.push P).increaseCG p = K.increaseCG p :=
  Table.ext (by simp [h]) rfl rfl

open scoped Classical in
/-- M' stops at the first unsettled issue. -/
theorem increaseCG_push_stack_of_not_settledBy (h : ¬ P.SettledBy (K.cg ⊓ 𝓟 p)) :
    ((K.push P).increaseCG p).stack = P :: K.stack := by
  simp [h]

/-- The commitment that triggers M' is stripped along with the rest. -/
theorem increaseCG_commit_self (f s) : (K.commit a p f s).increaseCG p = K.increaseCG p :=
  Table.ext rfl
    (Set.ext fun c ↦ ⟨fun ⟨h, hp⟩ ↦ ⟨h.resolve_left fun e ↦ hp (by rw [e]; rfl), hp⟩,
      fun ⟨h, hp⟩ ↦ ⟨.inr h, hp⟩⟩)
    rfl

/-- Agreeing to disagree after a denial leaves the Table and the common ground as before the
assertion, with both commitments recorded. -/
theorem agreeToDisagree_assert_assert (b : A) (q : Set W) :
    ((K.assert a p).assert b q).agreeToDisagree = (K.commit a p).commit b q := rfl

/-! ### Projected common grounds -/

variable {K a p P} {ps : Set (Filter W)} {f : Filter W}

theorem mem_project :
    f ∈ project ps P ↔ (∃ g ∈ ps, ∃ q ∈ alt P, g ⊓ 𝓟 q = f) ∧ f ≠ ⊥ :=
  Iff.rfl

theorem ne_bot_of_mem_project (h : f ∈ project ps P) : f ≠ ⊥ := h.2

theorem exists_le_of_mem_project (h : f ∈ project ps P) : ∃ g ∈ ps, f ≤ g :=
  let ⟨g, hg, _, _, e⟩ := h.1
  ⟨g, hg, e ▸ inf_le_left⟩

/-- Every projected common ground settles the issue it was projected from. -/
theorem settledBy_of_mem_project (h : f ∈ project ps P) : P.SettledBy f :=
  let ⟨_, _, q, hq, e⟩ := h.1
  ⟨q, hq, e ▸ mem_inf_of_right (mem_principal_self q)⟩

variable (K a p P)

/-- A stable conversation projects only its common ground. -/
theorem projectedSet_of_isStable (h : K.IsStable) : K.projectedSet = {K.cg} := by
  rw [projectedSet, show K.stack = [] from h, List.foldr_nil]

@[simp] theorem projectedSet_push : (K.push P).projectedSet = project K.projectedSet P := rfl

@[simp] theorem projectedSet_commit (f s) : (K.commit a p f s).projectedSet = K.projectedSet :=
  rfl

/-- An assertion projects confirmation: its content is added to each projected common ground. -/
@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet = project K.projectedSet (ofSet p) := rfl

/-- A projected common ground refines the current one. -/
theorem le_cg_of_mem_projectedSet (h : f ∈ K.projectedSet) : f ≤ K.cg := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact le_of_eq h
  | cons P T ih =>
    obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project h
    exact hfg.trans (ih hg)

/-- Every projected common ground settles every issue on the Table. -/
theorem settledBy_of_mem_projectedSet (hf : f ∈ K.projectedSet) (hP : P ∈ K.stack) :
    P.SettledBy f := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact (List.not_mem_nil hP).elim
  | cons Q T ih =>
    rcases List.mem_cons.1 hP with rfl | hP
    · exact settledBy_of_mem_project hf
    · obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project hf
      exact (ih hg hP).mono hfg

/-- Every projected common ground settles the current issue. -/
theorem settles_of_mem_projectedSet (hf : f ∈ K.projectedSet) :
    Discourse.HasIssue.settles f.ker K := by
  change f.ker ∈ K.stack.headD ⊤
  cases h : K.stack with
  | nil => exact mem_top
  | cons P T =>
    exact (settledBy_of_mem_projectedSet K P hf (h ▸ List.mem_cons_self)).ker_mem

/-- The asserted proposition holds in every projected common ground. -/
theorem mem_of_mem_projectedSet_assert (h : f ∈ (K.assert a p).projectedSet) : p ∈ f :=
  settledBy_ofSet.1 (settledBy_of_mem_project h)

/-- The sentence radical of a polar question is decided in every projected common ground. -/
theorem mem_or_compl_mem_of_mem_projectedSet_polarQuestion
    (h : f ∈ (K.polarQuestion p).projectedSet) : p ∈ f ∨ pᶜ ∈ f :=
  settledBy_polar.1 (settledBy_of_mem_project h)

/-- With the projected set derived, a conversation is in crisis exactly when no projected common
ground is consistent. -/
theorem inCrisis_iff : K.InCrisis ↔ ∀ f ∈ K.projectedSet, f = ⊥ :=
  ⟨fun h ↦ h.elim
    (fun hcg _ hf ↦ le_bot_iff.1 ((le_cg_of_mem_projectedSet K hf).trans_eq hcg)) id, Or.inr⟩

/-- After an assertion has been denied, nothing consistent is projected (21). -/
theorem projectedSet_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).projectedSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun f ⟨⟨g, hg, q, hq, e⟩, hne⟩ ↦ by
    rw [alt_ofSet, Set.mem_singleton_iff] at hq
    subst hq e
    refine hne (inf_principal_eq_bot.2 ?_)
    rw [compl_compl]
    exact mem_of_mem_projectedSet_assert K a p hg

/-- A denied assertion leaves the conversation in crisis. -/
theorem inCrisis_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).InCrisis :=
  (inCrisis_iff _).2 fun f hf ↦
    absurd (projectedSet_assert_compl K a p b ▸ hf) (Set.notMem_empty f)

end Table

end Commitment
