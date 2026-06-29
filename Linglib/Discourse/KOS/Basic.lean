import Linglib.Discourse.KOS.Defs
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.Support

/-!
# KOS: DGB Operations
[ginzburg-2012] Ch. 4

Operations on the Dialogue Gameboard: pushing onto QUD, downdating
resolved questions, recording moves, asserting facts. Plus the
`HasContextSet` bridge connecting DGB facts to the standard common
ground type, the `non-resolve-cond` well-formedness check, and the
partition-based answerhood predicate `PropResolvesQUD`.

## Structure

- §1. DGB structural lemmas (initial state)
- §2. DGB update operations: pushQud, downdateQud, addFact, recordMove, assertFact
- §3. DGB content mapping: mapFacts, mapQud
- §4. HasContextSet bridge to CommonGround
- §5. QUD downdate properties + non-resolve-cond well-formedness
- §6. Partition-based answerhood (`PropResolvesQUD`)

## Answerhood

KOS's "fact resolves question" relation is the `Question.Support`
typeclass (Prop-valued, mathlib-shaped). With QUD now storing
`InfoStruc QContent Cont` (per Ch. 6 final), the support check on
`f ⊨ is.q` projects through the InfoStruc's question field.
-/

namespace Discourse.KOS

open Question

-- ════════════════════════════════════════════════════
-- § 1. DGB Structural Lemmas
-- ════════════════════════════════════════════════════

/-- An empty DGB has no moves. -/
theorem DGB.initial_no_moves {Participant Fact QContent : Type*} {Cont : Type} :
    (DGB.initial : DGB Participant Fact QContent Cont).moves = [] := rfl

/-- An empty DGB has empty QUD. -/
theorem DGB.initial_no_qud {Participant Fact QContent : Type*} {Cont : Type} :
    (DGB.initial : DGB Participant Fact QContent Cont).qud = [] := rfl

/-- An empty DGB has no latest move. -/
theorem DGB.initial_no_latestMove {Participant Fact QContent : Type*} {Cont : Type} :
    (DGB.initial : DGB Participant Fact QContent Cont).latestMove = none := rfl

-- ════════════════════════════════════════════════════
-- § 2. DGB Update Operations
-- ════════════════════════════════════════════════════

/-- Push a bare question onto the QUD stack, wrapping it in an
`InfoStruc` with no FECs.

Ch. 4: when a question is asked, it becomes the maximal element of QUD. -/
def DGB.pushQud {P Fact QContent : Type*} {Cont : Type}
    (dgb : DGB P Fact QContent Cont) (q : QContent) :
    DGB P Fact QContent Cont :=
  { dgb with qud := (.fromQuestion q) :: dgb.qud }

/-- Remove resolved questions from QUD.

Ch. 4: QUD-downdate removes a question q from QUD when FACTS contextually
entail an answer to q. Now QUD entries are `InfoStruc`s; the support check
projects through `is.q`. -/
def DGB.downdateQud {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) : DGB P Fact QContent Cont :=
  { dgb with
    qud := dgb.qud.filter fun is => !dgb.facts.any fun f => decide (f ⊨ is.q) }

/-- Add a fact to the DGB's FACTS. -/
def DGB.addFact {P Fact QContent : Type*} {Cont : Type}
    (dgb : DGB P Fact QContent Cont) (p : Fact) :
    DGB P Fact QContent Cont :=
  { dgb with facts := p :: dgb.facts }

/-- Record a move in the DGB's MOVES list. -/
def DGB.recordMove {P Fact QContent : Type*} {Cont : Type}
    (dgb : DGB P Fact QContent Cont) (m : IllocMove Fact QContent) :
    DGB P Fact QContent Cont :=
  { dgb with moves := dgb.moves ++ [m] }

/-- Push a LocProp onto Pending (Ch. 6 ungrounded utterance). -/
def DGB.pushPending {P Fact QContent : Type*} {Cont : Type}
    (dgb : DGB P Fact QContent Cont) (lp : LocProp Cont) :
    DGB P Fact QContent Cont :=
  { dgb with pending := lp :: dgb.pending }

/-- Assert: add fact to FACTS, record the move, and downdate QUD.

Ch. 4 (p. 95, ex. 66): assertion adds content to FACTS, pushes
About(p,?) onto QUD, and any resolved question is removed. -/
def DGB.assertFact {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) (p : Fact) :
    DGB P Fact QContent Cont :=
  (dgb.addFact p).downdateQud

-- ════════════════════════════════════════════════════
-- § 3. HasContextSet Bridge
-- ════════════════════════════════════════════════════

open CommonGround in
/-- DGB with `Set W` facts projects to a context set.
    [ginzburg-2012] Ch. 4: the DGB's FACTS field IS the common ground. -/
instance {W Participant QContent : Type*} {Cont : Type} :
    HasContextSet (DGB Participant (Set W) QContent Cont) W where
  toContextSet dgb := λ w => ∀ p ∈ dgb.facts, p w

open CommonGround in
/-- TIS with `Set W` facts inherits the DGB's context set. -/
instance {W Participant QContent : Type*} {Cont : Type} :
    HasContextSet (TIS Participant (Set W) QContent Cont) W where
  toContextSet tis := λ w => ∀ p ∈ tis.dgb.facts, p w

open CommonGround in
/-- TIS context set is extracted from the DGB. -/
theorem tis_contextSet_eq_dgb {W Participant QContent : Type*} {Cont : Type}
    (tis : TIS Participant (Set W) QContent Cont) :
    HasContextSet.toContextSet tis = HasContextSet.toContextSet tis.dgb := rfl

-- ════════════════════════════════════════════════════
-- § 4. QUD Downdate Properties + Non-Resolve-Cond
-- ════════════════════════════════════════════════════

/-- Downdate never increases QUD size. -/
theorem downdateQud_length_le {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) :
    dgb.downdateQud.qud.length ≤ dgb.qud.length := by
  simp only [DGB.downdateQud]
  exact List.length_filter_le _ _

/-- If a fact resolves the only question on QUD, downdate removes it. -/
theorem downdateQud_removes_resolved {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) (is : InfoStruc QContent Cont) (f : Fact)
    (hq : dgb.qud = [is]) (hf : f ∈ dgb.facts) (hr : f ⊨ is.q) :
    dgb.downdateQud.qud = [] := by
  unfold DGB.downdateQud
  rw [hq]
  simp only [List.filter_cons, List.filter_nil]
  have : dgb.facts.any (fun f => decide (f ⊨ is.q)) = true :=
    List.any_eq_true.mpr ⟨f, hf, decide_eq_true hr⟩
  simp [this]

/-! ## DGB Well-Formedness: Non-Resolve-Cond

[ginzburg-2012] ex. 100 (p. 111): the DGB includes a well-formedness
constraint `non-resolve-cond` requiring that no question on QUD is already
resolved by FACTS. This prevents trivially answered questions from lingering
on QUD — they should be downdated. -/

/-- The non-resolve-cond: no question on QUD is resolved by FACTS.
[ginzburg-2012] ex. 100 (p. 111). -/
def DGB.nonResolveCond {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) : Prop :=
  ∀ is ∈ dgb.qud, ¬ ∃ f ∈ dgb.facts, f ⊨ is.q

instance {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) : Decidable (dgb.nonResolveCond) := by
  unfold DGB.nonResolveCond
  exact List.decidableBAll _ _

/-- An empty DGB trivially satisfies non-resolve-cond. -/
theorem DGB.initial_nonResolveCond {P Fact QContent : Type*} {Cont : Type}
    [DecidableSupport Fact QContent] :
    (DGB.initial : DGB P Fact QContent Cont).nonResolveCond := by
  intro is hist
  exact absurd hist List.not_mem_nil

/-- After QUD-downdate, non-resolve-cond holds: all remaining questions
are unresolved by FACTS. -/
theorem downdateQud_restores_nonResolveCond
    {P Fact QContent : Type*} {Cont : Type} [DecidableSupport Fact QContent]
    (dgb : DGB P Fact QContent Cont) :
    dgb.downdateQud.nonResolveCond := by
  intro is hist ⟨f, hf, hsupp⟩
  simp only [DGB.downdateQud, List.mem_filter] at hist
  obtain ⟨_, hist2⟩ := hist
  -- hist2 : decide (¬ dgb.facts.any fun f' => decide (f' ⊨ is.q)) = true
  -- but f ∈ dgb.facts and f ⊨ is.q, so the any IS true, contradiction
  have : (dgb.facts.any fun f' => decide (f' ⊨ is.q)) = true :=
    List.any_eq_true.mpr ⟨f, hf, decide_eq_true hsupp⟩
  simp [this] at hist2

-- ════════════════════════════════════════════════════
-- § 5. Partition-Based Answerhood
-- ════════════════════════════════════════════════════

/-! ## Partition-Based Support

Ch. 4 defines QUD-downdate in terms of FACTS resolving questions.
The `Support` typeclass abstracts this. Here we connect it to the
partition-based `QUD W` from `Discourse/QUD.lean`
([groenendijk-stokhof-1984]):

A `Set W` fact supports a `QUD W` question when the fact determines
a unique cell — all worlds where the fact holds are in the same
partition cell. -/

/-- A `Set W` resolves a `QUD W` if all fact-worlds are in the same
partition cell. Prop-valued; `Decidable` via the bundled per-pair
predicate decidability. -/
def PropResolvesQUD {W : Type*} (worlds : List W)
    (fact : Set W) [DecidablePred fact] (q : QUD W) : Prop :=
  ∀ w₁ ∈ worlds.filter (fun w => decide (fact w)),
    ∀ w₂ ∈ worlds.filter (fun w => decide (fact w)),
      q.sameAnswer w₁ w₂ = true

instance {W : Type*} (worlds : List W) (fact : Set W) [DecidablePred fact]
    (q : QUD W) : Decidable (PropResolvesQUD worlds fact q) := by
  unfold PropResolvesQUD; infer_instance

/-! Worked partition consumers below construct their own
`DecidableSupport` instances at the concrete fact-type (e.g.
`rainSupport` uses `RainProp.toProp`, where `DecidablePred` is
automatic). A generic `Set W → DecidableSupport` factory would have
to choose `Classical.decPred fact` and the resulting kernel
unfolding doesn't align cleanly between the `supports` and
`decSupports` fields; consumers requiring it can construct the
instance locally. -/

end Discourse.KOS
