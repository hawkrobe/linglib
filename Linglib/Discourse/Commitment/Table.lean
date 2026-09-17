import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.QUD.Issue
import Linglib.Semantics.Questions.Hamblin

/-!
# The Table

This file defines the context structure of [farkas-bruce-2010]: the participants' discourse
commitments, the common ground, and the Table, a stack of the issues under discussion with the
most recent on top. A declarative raises its proposition as an issue, `Question.ofSet p`, and a
polar interrogative raises `Question.polar p`; the complete answers of an issue are its
alternatives, `Question.alt`, the interrogative denotation of [karttunen-1977], and a common
ground decides an issue when it entails one of them. Each issue on the Table projects the common
grounds that would decide it, and the projected set is derived from the common ground and the
stack. The moves of the paper are functions on the structure, and the file proves what each does
to the projected set, the commitment lists, and the Table.

A Table is a discourse state in both projections: its common ground is the `cg` coordinate
(`HasCommonGround`) and its current issue is the top of the stack (`Discourse.HasIssue`). It is
not a `HasAssertion` instance under its own `assert`, which leaves the common ground alone and
moves only the projected set.

## Main definitions

* `Question.DecidedBy P f`: the common ground `f` entails a complete answer of the issue `P`.
* `Commitment.Table A W`: the context structure, with `Table.dc a` the propositions `a` has
  publicly committed to and `Table.projectedSet` the projected set, the fold of the paper's
  `ps ∪ P` over the stack.
* `Table.IsStable`, `Table.InCrisis`, `Table.Shared`: an empty Table; an inconsistent common
  ground or no consistent projected common ground; a proposition every participant is
  committed to.
* `Table.assert`, `Table.polarQuestion`, `Table.settle`, `Table.agreeToDisagree`: the
  default assertion (9), which commits its author as in [gunlogson-2001], the default polar
  question (12), the common-ground increasing operation M' (17), and agreeing to disagree (23).
  Assertion confirmation (16) is `Table.commit` of the proposition on top of the Table, and
  total denial (22) is `assert` of its negation.

## Main results

* `Table.le_cg_of_mem_projectedSet`, `Table.decidedBy_of_mem_projectedSet`: a projected common
  ground refines the current one and decides every issue on the Table.
* `Table.inCrisis_iff`: with the projected set derived, crisis is having no consistent
  projected common ground; the inconsistent-common-ground clause is subsumed.
* `Table.projectedSet_assert_compl`, `Table.inCrisis_assert_compl`: a denied assertion projects
  nothing consistent (21) and leaves the conversation in crisis.
* `Table.settle_push_of_decidedBy`, `Table.settle_assert_self`,
  `Table.dc_settle`: M' pops the issues the new common ground decides and strips the
  shared proposition from every commitment list.
* `Table.agreeToDisagree_assert_assert`, `Table.inCrisis_agreeToDisagree_assert_assert`:
  agreeing to disagree keeps the commitments, restores the Table, and restores the crisis
  status of the input context (23).

## Implementation notes

* The paper notes that the projected set can always be rebuilt from the common ground and the
  Table, so it is derived rather than stored.
* A common ground is a filter of propositions, so a proposition follows from it when it belongs
  to the filter. This is the intersection-based entailment the paper's footnote 8 sets aside as
  too coarse-grained: here every necessary proposition is decided by every common ground, and
  `Question.decidedBy_top` records that the trivial issue is always decided.
* M' (17) applies in the paper only once the proposition is on every commitment list;
  `Table.settle` is the operation itself, and the trigger is a hypothesis on the caller,
  `Table.Shared`. Its popping clause is read as "pop from the top while decided", which
  follows the stack wording of (17) and agrees with the paper's examples; the gloss after
  (17) can also be read as removing every decided item from anywhere in the stack, and the
  clause pops on an entailed complete answer where the gloss says a decided one, which differ
  for a declarative whose negation the new common ground entails. Whether a common ground
  entails a complete answer is not decidable, so `Table.settle` is classical and
  noncomputable.
* Agreeing to disagree requires a denial on top of the assertion it denies, which is where
  total denial (22) leaves the Table, and removes both; `Table.agreeToDisagree` pops twice and
  does not check the precondition.

## References

* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
* [L. Karttunen, *Syntax and Semantics of Questions* (1977)][karttunen-1977]
-/

open Filter

namespace Question

variable {W : Type*} {P : Question W} {f g : Filter W} {p : Set W}

/-- The common ground `f` decides the issue `P` when it entails one of its complete answers. -/
def DecidedBy (P : Question W) (f : Filter W) : Prop := ∃ q ∈ alt P, q ∈ f

theorem DecidedBy.mono (h : f ≤ g) : P.DecidedBy g → P.DecidedBy f :=
  Exists.imp fun _ ⟨hq, hg⟩ ↦ ⟨hq, h hg⟩

/-- A common ground deciding an issue has a context set resolving it. -/
theorem DecidedBy.ker_mem (h : P.DecidedBy f) : f.ker ∈ P :=
  let ⟨q, hq, hf⟩ := h
  P.downward_closed q (mem_of_mem_alt hq) _ (ker_mono (le_principal_iff.2 hf) |>.trans_eq
    (ker_principal q))

/-- The trivial issue is decided by every common ground. -/
@[simp] theorem decidedBy_top : (⊤ : Question W).DecidedBy f := ⟨_, by simp, univ_mem⟩

@[simp] theorem decidedBy_ofSet : (ofSet p).DecidedBy f ↔ p ∈ f := by simp [DecidedBy]

/-- A proposition is decided relative to a common ground when it or its negation follows from
it; that is the polar question of `p` being decided. -/
@[simp] theorem decidedBy_polar : (polar p).DecidedBy f ↔ p ∈ f ∨ pᶜ ∈ f := by
  by_cases h : p = ∅ ∨ p = Set.univ
  · rcases h with rfl | rfl <;> simp [polar_empty, polar_univ]
  · simp [DecidedBy, mem_alt_polar_of_nontrivial (not_or.1 h).1 (not_or.1 h).2]

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
def polarQuestion : Table A W := K.push (polar p)

open scoped Classical in
/-- The common-ground increasing operation M' (17), applied once `p` is on every commitment
list: `p` enters the common ground, leaves the individual commitment lists, and the issues the
new common ground decides are popped from the top of the Table. -/
noncomputable def settle : Table A W where
  stack := K.stack.dropWhile fun P ↦ decide (P.DecidedBy (K.cg ⊓ 𝓟 p))
  commitments := {c ∈ K.commitments | c.content ≠ p}
  cg := K.cg ⊓ 𝓟 p

/-- Agreeing to disagree (23), from a Table with the denial on top of the assertion it denies:
the contradictory pair leaves the Table and the commitments stay. -/
def agreeToDisagree : Table A W := K.pop.pop

/-! ### Coordinates of the moves -/

@[simp] theorem stack_empty : (empty : Table A W).stack = [] := rfl
@[simp] theorem commitments_empty : (empty : Table A W).commitments = ∅ := rfl
@[simp] theorem cg_empty : (empty : Table A W).cg = ⊤ := rfl
@[simp] theorem stack_push : (K.push P).stack = P :: K.stack := rfl
@[simp] theorem commitments_push : (K.push P).commitments = K.commitments := rfl
@[simp] theorem cg_push : (K.push P).cg = K.cg := rfl
@[simp] theorem stack_pop : K.pop.stack = K.stack.tail := rfl
@[simp] theorem commitments_pop : K.pop.commitments = K.commitments := rfl
@[simp] theorem cg_pop : K.pop.cg = K.cg := rfl
@[simp] theorem stack_commit (f s) : (K.commit a p f s).stack = K.stack := rfl
@[simp] theorem commitments_commit (f s) :
    (K.commit a p f s).commitments = insert (Commitment.commit a p f s) K.commitments := rfl
@[simp] theorem cg_commit (f s) : (K.commit a p f s).cg = K.cg := rfl
@[simp] theorem stack_assert : (K.assert a p).stack = ofSet p :: K.stack := rfl
@[simp] theorem commitments_assert :
    (K.assert a p).commitments = insert (Commitment.commit a p) K.commitments := rfl
@[simp] theorem cg_assert : (K.assert a p).cg = K.cg := rfl
@[simp] theorem stack_polarQuestion : (K.polarQuestion p).stack = polar p :: K.stack := rfl
@[simp] theorem commitments_polarQuestion : (K.polarQuestion p).commitments = K.commitments :=
  rfl
@[simp] theorem cg_polarQuestion : (K.polarQuestion p).cg = K.cg := rfl

open scoped Classical in
@[simp] theorem stack_settle :
    (K.settle p).stack = K.stack.dropWhile fun P ↦ decide (P.DecidedBy (K.cg ⊓ 𝓟 p)) :=
  rfl
@[simp] theorem commitments_settle :
    (K.settle p).commitments = {c ∈ K.commitments | c.content ≠ p} := rfl
@[simp] theorem cg_settle : (K.settle p).cg = K.cg ⊓ 𝓟 p := rfl
@[simp] theorem stack_agreeToDisagree : K.agreeToDisagree.stack = K.stack.tail.tail := rfl
@[simp] theorem commitments_agreeToDisagree : K.agreeToDisagree.commitments = K.commitments :=
  rfl
@[simp] theorem cg_agreeToDisagree : K.agreeToDisagree.cg = K.cg := rfl

@[simp] theorem commonGround_eq : HasCommonGround.commonGround K = K.cg := rfl
@[simp] theorem toIssue_empty : Discourse.HasIssue.toIssue (empty : Table A W) = ⊤ := rfl
@[simp] theorem toIssue_push : Discourse.HasIssue.toIssue (K.push P) = P := rfl
@[simp] theorem toIssue_commit (f s) :
    Discourse.HasIssue.toIssue (K.commit a p f s) = Discourse.HasIssue.toIssue K := rfl
@[simp] theorem toIssue_assert : Discourse.HasIssue.toIssue (K.assert a p) = ofSet p := rfl
@[simp] theorem toIssue_polarQuestion :
    Discourse.HasIssue.toIssue (K.polarQuestion p) = polar p := rfl

/-! ### Stability -/

@[simp] theorem empty_isStable : (empty : Table A W).IsStable := rfl

theorem not_isStable_push : ¬ (K.push P).IsStable := List.cons_ne_nil _ _

variable {K} in
/-- A stable conversation has no issue. -/
theorem toIssue_of_isStable (h : K.IsStable) : Discourse.HasIssue.toIssue K = ⊤ := by
  change K.stack.headD ⊤ = ⊤
  rw [show K.stack = [] from h, List.headD_nil]

variable {K} in
theorem isStable_settle_of_isStable (h : K.IsStable) : (K.settle p).IsStable := by
  show (K.settle p).stack = []
  rw [stack_settle, show K.stack = [] from h, List.dropWhile_nil]

/-! ### Discourse commitments -/

@[simp] theorem dc_empty : (empty : Table A W).dc a = ∅ := by
  simp [dc, ofCommitter, contents]

@[simp] theorem dc_push : (K.push P).dc = K.dc := rfl
@[simp] theorem dc_pop : K.pop.dc = K.dc := rfl
@[simp] theorem dc_polarQuestion : (K.polarQuestion p).dc = K.dc := rfl
@[simp] theorem dc_agreeToDisagree : K.agreeToDisagree.dc = K.dc := rfl

@[simp] theorem dc_commit_self (f s) : (K.commit a p f s).dc a = insert p (K.dc a) := by
  rw [dc, dc, commitments_commit, ofCommitter_insert_of_eq _ _ _ (commit_committer a p f s),
    contents_insert_of_commit (commit_polarity a p f s), commit_content]

variable {K a p} in
theorem dc_commit_of_ne {f s} {b : A} (h : b ≠ a) : (K.commit a p f s).dc b = K.dc b := by
  rw [dc, dc, commitments_commit,
    ofCommitter_insert_of_ne _ _ _ ((commit_committer a p f s).trans_ne h.symm)]

theorem mem_dc_commit_iff (f s) {b : A} {q : Set W} :
    q ∈ (K.commit a p f s).dc b ↔ (b = a ∧ q = p) ∨ q ∈ K.dc b := by
  by_cases hb : b = a
  · subst hb; simp
  · simp [dc_commit_of_ne hb, hb]

theorem mem_dc_commit_self (f s) : p ∈ (K.commit a p f s).dc a := by simp

@[simp] theorem dc_assert : (K.assert a p).dc a = insert p (K.dc a) := dc_commit_self K a p _ _

variable {K a p} in
theorem dc_assert_of_ne {b : A} (h : b ≠ a) : (K.assert a p).dc b = K.dc b :=
  dc_commit_of_ne h

/-- The asserted proposition enters the author's commitments. -/
theorem mem_dc_assert : p ∈ (K.assert a p).dc a := mem_dc_commit_self K a p _ _

/-- M' strips the shared proposition from every commitment list. -/
theorem dc_settle : (K.settle p).dc a = K.dc a \ {p} := by
  ext q
  simp only [dc, ofCommitter, contents, commitments_settle, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, ⟨⟨⟨hc, hp⟩, ha⟩, hpol⟩, rfl⟩
    exact ⟨⟨c, ⟨⟨hc, ha⟩, hpol⟩, rfl⟩, hp⟩
  · rintro ⟨⟨c, ⟨⟨hc, ha⟩, hpol⟩, rfl⟩, hp⟩
    exact ⟨c, ⟨⟨⟨hc, hp⟩, ha⟩, hpol⟩, rfl⟩

/-! ### The moves on the Table -/

variable {K p P} in
/-- M' pops a decided issue from the top of the Table and goes on popping. -/
theorem settle_push_of_decidedBy (h : P.DecidedBy (K.cg ⊓ 𝓟 p)) :
    (K.push P).settle p = K.settle p :=
  Table.ext (by simp [h]) rfl rfl

variable {K p P} in
/-- M' stops at the first undecided issue. -/
theorem stack_settle_push_of_not_decidedBy (h : ¬ P.DecidedBy (K.cg ⊓ 𝓟 p)) :
    ((K.push P).settle p).stack = P :: K.stack := by
  simp [h]

/-- The commitment that triggers M' is stripped along with the rest. -/
theorem settle_commit_self (f s) : (K.commit a p f s).settle p = K.settle p :=
  Table.ext rfl
    (Set.ext fun c ↦ ⟨fun ⟨h, hp⟩ ↦ ⟨h.resolve_left fun e ↦ hp (by rw [e]; rfl), hp⟩,
      fun ⟨h, hp⟩ ↦ ⟨.inr h, hp⟩⟩)
    rfl

/-- M' with the asserted proposition pops the assertion and strips its commitment. -/
theorem settle_assert_self : (K.assert a p).settle p = K.settle p :=
  (settle_push_of_decidedBy
    (decidedBy_ofSet.2 (mem_inf_of_right (mem_principal_self p)))).trans
    (settle_commit_self K a p _ _)

/-- M' with the sentence radical of a polar question pops the question. -/
theorem settle_polarQuestion_self : (K.polarQuestion p).settle p = K.settle p :=
  settle_push_of_decidedBy (decidedBy_polar.2 (.inl (mem_inf_of_right (mem_principal_self p))))

/-- Agreeing to disagree after two assertions, the denial being the case `q = pᶜ`, leaves the
Table and the common ground as before them, with both commitments recorded. -/
theorem agreeToDisagree_assert_assert (b : A) (q : Set W) :
    ((K.assert a p).assert b q).agreeToDisagree = (K.commit a p).commit b q := rfl

/-- Agreeing to disagree restores the crisis status of the context before the assertions. -/
theorem inCrisis_agreeToDisagree_assert_assert (b : A) (q : Set W) :
    ((K.assert a p).assert b q).agreeToDisagree.InCrisis ↔ K.InCrisis := Iff.rfl

/-! ### Projected common grounds -/

variable {K a p P} {ps : Set (Filter W)} {f : Filter W}

theorem mem_project :
    f ∈ project ps P ↔ (∃ g ∈ ps, ∃ q ∈ alt P, g ⊓ 𝓟 q = f) ∧ f ≠ ⊥ :=
  Iff.rfl

theorem ne_bot_of_mem_project (h : f ∈ project ps P) : f ≠ ⊥ := h.2

theorem exists_le_of_mem_project (h : f ∈ project ps P) : ∃ g ∈ ps, f ≤ g :=
  let ⟨g, hg, _, _, e⟩ := h.1
  ⟨g, hg, e ▸ inf_le_left⟩

/-- Every projected common ground decides the issue it was projected from. -/
theorem decidedBy_of_mem_project (h : f ∈ project ps P) : P.DecidedBy f :=
  let ⟨_, _, q, hq, e⟩ := h.1
  ⟨q, hq, e ▸ mem_inf_of_right (mem_principal_self q)⟩

/-- A single common ground consistent with `p` projects the one common ground with `p`. -/
theorem project_singleton_ofSet (h : f ⊓ 𝓟 p ≠ ⊥) : project {f} (ofSet p) = {f ⊓ 𝓟 p} := by
  rw [project, Set.image2_singleton_left, alt_ofSet, Set.image_singleton,
    Set.sdiff_singleton_eq_self (Set.notMem_singleton_iff.2 h.symm)]

/-- A single common ground consistent with `p` and with `¬p` projects both resolutions. -/
theorem project_singleton_polar (hp : f ⊓ 𝓟 p ≠ ⊥) (hnp : f ⊓ 𝓟 pᶜ ≠ ⊥) :
    project {f} (polar p) = {f ⊓ 𝓟 p, f ⊓ 𝓟 pᶜ} := by
  rw [project, Set.image2_singleton_left,
    alt_polar_of_nontrivial (fun e ↦ hp (by simp [e])) (fun e ↦ hnp (by simp [e])),
    Set.image_pair, Set.sdiff_singleton_eq_self (by simp [hp.symm, hnp.symm])]

/-- A stable conversation projects only its common ground. -/
theorem projectedSet_of_isStable (h : K.IsStable) : K.projectedSet = {K.cg} := by
  rw [projectedSet, show K.stack = [] from h, List.foldr_nil]

/-- A projected common ground refines the current one. -/
theorem le_cg_of_mem_projectedSet (h : f ∈ K.projectedSet) : f ≤ K.cg := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact le_of_eq h
  | cons P T ih =>
    obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project h
    exact hfg.trans (ih hg)

/-- Every projected common ground decides every issue on the Table. -/
theorem decidedBy_of_mem_projectedSet (hf : f ∈ K.projectedSet) (hP : P ∈ K.stack) :
    P.DecidedBy f := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact (List.not_mem_nil hP).elim
  | cons Q T ih =>
    rcases List.mem_cons.1 hP with rfl | hP
    · exact decidedBy_of_mem_project hf
    · obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project hf
      exact (ih hg hP).mono hfg

/-- Every projected common ground settles the current issue. -/
theorem settles_of_mem_projectedSet (hf : f ∈ K.projectedSet) :
    Discourse.HasIssue.settles f.ker K := by
  change f.ker ∈ K.stack.headD ⊤
  cases h : K.stack with
  | nil => exact mem_top
  | cons P T =>
    exact (decidedBy_of_mem_projectedSet (P := P) hf (h ▸ List.mem_cons_self)).ker_mem

/-- The asserted proposition holds in every projected common ground. -/
theorem mem_of_mem_projectedSet_assert (h : f ∈ (K.assert a p).projectedSet) : p ∈ f :=
  decidedBy_ofSet.1 (decidedBy_of_mem_project h)

/-- The sentence radical of a polar question is decided in every projected common ground. -/
theorem mem_or_compl_mem_of_mem_projectedSet_polarQuestion
    (h : f ∈ (K.polarQuestion p).projectedSet) : p ∈ f ∨ pᶜ ∈ f :=
  decidedBy_polar.1 (decidedBy_of_mem_project h)

variable (K a p P)

@[simp] theorem projectedSet_push : (K.push P).projectedSet = project K.projectedSet P := rfl

@[simp] theorem projectedSet_commit (f s) : (K.commit a p f s).projectedSet = K.projectedSet :=
  rfl

/-- An assertion projects confirmation: its content is added to each projected common ground. -/
@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet = project K.projectedSet (ofSet p) := rfl

/-- A polar question projects resolution: each alternative is added to each projected common
ground. -/
@[simp] theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet = project K.projectedSet (polar p) := rfl

/-- With the projected set derived, a conversation is in crisis exactly when no projected common
ground is consistent. -/
theorem inCrisis_iff : K.InCrisis ↔ ∀ f ∈ K.projectedSet, f = ⊥ :=
  ⟨fun h ↦ h.elim
    (fun hcg _ hf ↦ le_bot_iff.1 ((le_cg_of_mem_projectedSet hf).trans_eq hcg)) id, Or.inr⟩

/-- After an assertion has been denied, nothing consistent is projected (21). -/
theorem projectedSet_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).projectedSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun f hf ↦ by
    rw [projectedSet_assert, mem_project, alt_ofSet] at hf
    obtain ⟨⟨g, hg, q, rfl, rfl⟩, hne⟩ := hf
    refine hne (inf_principal_eq_bot.2 ?_)
    rw [compl_compl]
    exact mem_of_mem_projectedSet_assert hg

/-- A denied assertion leaves the conversation in crisis. -/
theorem inCrisis_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).InCrisis :=
  (inCrisis_iff _).2 fun f hf ↦
    absurd (projectedSet_assert_compl K a p b ▸ hf) (Set.notMem_empty f)

end Table

end Commitment
