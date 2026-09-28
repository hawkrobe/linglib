module

public import Linglib.Discourse.Gameboard.Defs
public import Linglib.Discourse.QUD.Issue

/-!
# Dialogue gameboard operations

The updates of the dialogue gameboard `DGB` of [ginzburg-2012]: pushing a question onto QUD,
adding a fact, recording a move or a pending utterance, changing the turn, and QUD-downdate
(`DGB.downdateQud`), which removes from QUD every question that some fact resolves, the function
NonResolve of Fact Update/QUD-Downdate ((44) p. 86). A gameboard satisfies `non-resolve-cond`
(`DGB.NonResolveCond`, ex. 100 p. 111) when no fact resolves a question under discussion. Downdate
establishes the condition and is idle exactly on the gameboards that satisfy it
(`DGB.downdateQud_eq_self_iff`); pushing a question keeps it exactly when no fact resolves that
question, the Question Introduction Appropriateness Condition ((52) p. 89,
`DGB.nonResolveCond_pushQud_iff`). A gameboard whose facts are sets of worlds determines a common
ground, and one whose questions are `Question W` has the question at the head of QUD as its issue.

## Implementation notes

* Resolution is an explicit relation `R : Fact → QContent → Prop`, not an instance on the content
  types: resolvedness is "not purely semantic" but agent-relative (p. 86), so the types of facts
  and questions do not determine it.
* The downdate is that of (44). Appendix B's version ((16) p. 370) lets NonResolve return any
  sub-poset of QUD free of resolved questions, and also removes a question once a fact resolves
  whether the participant wishes to discuss it.
* (53) and ex. 100 state `non-resolve-cond` as `¬Resolve(FACTS, q)`, resolution by FACTS as a
  whole, while (44) and (52) quantify over its members. `DGB.NonResolveCond` follows the members,
  so that downdate establishes it.

## References

* [ginzburg-2012]
-/

@[expose] public section

namespace Discourse.Gameboard

namespace DGB

variable {P Fact QContent : Type*} {Cont : Type} (dgb : DGB P Fact QContent Cont)

@[simp] theorem moves_initial : (initial : DGB P Fact QContent Cont).moves = [] := rfl

@[simp] theorem qud_initial : (initial : DGB P Fact QContent Cont).qud = [] := rfl

@[simp] theorem latestMove_initial : (initial : DGB P Fact QContent Cont).latestMove = none := rfl

/-- Push a question onto QUD, with no focus-establishing constituents: asking a question makes it
MaxQUD. -/
def pushQud (q : QContent) : DGB P Fact QContent Cont :=
  { dgb with qud := .fromQuestion q :: dgb.qud }

/-- Add a fact to FACTS. -/
def addFact (p : Fact) : DGB P Fact QContent Cont :=
  { dgb with facts := p :: dgb.facts }

/-- Record a move as the latest in MOVES. -/
def recordMove (m : LocProp Cont) : DGB P Fact QContent Cont :=
  { dgb with moves := dgb.moves ++ [m] }

/-- Push an ungrounded utterance onto PENDING. -/
def pushPending (lp : LocProp Cont) : DGB P Fact QContent Cont :=
  { dgb with pending := lp :: dgb.pending }

/-- Turn change: the addressee takes the turn. -/
def swapTurn : DGB P Fact QContent Cont :=
  { dgb with spkr := dgb.addr, addr := dgb.spkr }

/-- The question of MaxQUD. -/
def maxQud : Option QContent :=
  dgb.qud.head?.map (·.q)

/-- The content of the latest move. -/
def latestContent : Option Cont :=
  dgb.latestMove.map (·.cont)

@[simp] theorem swapTurn_pushQud (q : QContent) :
    dgb.swapTurn.pushQud q = (dgb.pushQud q).swapTurn := rfl

@[simp] theorem swapTurn_recordMove (m : LocProp Cont) :
    dgb.swapTurn.recordMove m = (dgb.recordMove m).swapTurn := rfl

@[simp] theorem latestMove_recordMove (m : LocProp Cont) :
    (dgb.recordMove m).latestMove = some m := by
  simp [latestMove, recordMove]

section Downdate

variable (R : Fact → QContent → Prop)

/-- `non-resolve-cond`: no fact resolves a question under discussion ([ginzburg-2012] ex. 100
p. 111), `R` being the resolution relation. -/
def NonResolveCond : Prop :=
  ∀ i ∈ dgb.qud, ¬∃ f ∈ dgb.facts, R f i.q

instance [DecidableRel R] : Decidable (dgb.NonResolveCond R) :=
  inferInstanceAs (Decidable (∀ i ∈ dgb.qud, _))

theorem nonResolveCond_initial : (initial : DGB P Fact QContent Cont).NonResolveCond R :=
  fun _ h ↦ absurd h List.not_mem_nil

/-- The Question Introduction Appropriateness Condition ([ginzburg-2012] (52) p. 89): pushing `q`
keeps `non-resolve-cond` exactly when no fact resolves `q`. -/
theorem nonResolveCond_pushQud_iff {q : QContent} :
    (dgb.pushQud q).NonResolveCond R ↔ (¬∃ f ∈ dgb.facts, R f q) ∧ dgb.NonResolveCond R :=
  List.forall_mem_cons

variable [DecidableRel R]

/-- QUD-downdate: remove from QUD every question that some fact resolves (NonResolve,
[ginzburg-2012] (44) p. 86). -/
def downdateQud : DGB P Fact QContent Cont :=
  { dgb with qud := dgb.qud.filter fun i ↦ ¬∃ f ∈ dgb.facts, R f i.q }

@[simp] theorem facts_downdateQud : (dgb.downdateQud R).facts = dgb.facts := rfl

@[simp] theorem mem_qud_downdateQud {i : InfoStruc QContent Cont} :
    i ∈ (dgb.downdateQud R).qud ↔ i ∈ dgb.qud ∧ ¬∃ f ∈ dgb.facts, R f i.q := by
  simp [downdateQud]

theorem length_qud_downdateQud_le : (dgb.downdateQud R).qud.length ≤ dgb.qud.length :=
  List.length_filter_le _ _

theorem nonResolveCond_downdateQud : (dgb.downdateQud R).NonResolveCond R :=
  fun _ h ↦ ((dgb.mem_qud_downdateQud R).1 h).2

/-- Downdate is idle exactly on gameboards satisfying `non-resolve-cond`. -/
theorem downdateQud_eq_self_iff : dgb.downdateQud R = dgb ↔ dgb.NonResolveCond R := by
  cases dgb
  simp [downdateQud, NonResolveCond, List.filter_eq_self]

end Downdate

deriving instance DecidableEq for DGB

end DGB

/-- A gameboard whose facts are sets of worlds determines the common ground they jointly
entail. -/
instance {W P QContent : Type*} {Cont : Type} :
    HasCommonGround (DGB P (Set W) QContent Cont) W where
  commonGround dgb := Filter.principal fun w ↦ ∀ p ∈ dgb.facts, p w

/-- A total information state has the common ground of its gameboard. -/
instance {W P QContent : Type*} {Cont : Type} :
    HasCommonGround (TIS P (Set W) QContent Cont) W where
  commonGround tis := Filter.principal fun w ↦ ∀ p ∈ tis.dgb.facts, p w

theorem tis_commonGround_eq_dgb {W P QContent : Type*} {Cont : Type}
    (tis : TIS P (Set W) QContent Cont) :
    commonGround tis = commonGround tis.dgb := rfl

/-- The current issue of a gameboard with question contents is the head of its QUD, the
trivial issue when the QUD is empty (MaxQUD, [ginzburg-2012] §4.3.3 p. 68). -/
instance {W P Fact : Type*} {Cont : Type} :
    Discourse.HasIssue (DGB P Fact (Question W) Cont) W where
  toIssue dgb := (dgb.qud.head?.map InfoStruc.q).getD ⊤

/-- A total information state has the issue of its gameboard. -/
instance {W P Fact : Type*} {Cont : Type} :
    Discourse.HasIssue (TIS P Fact (Question W) Cont) W where
  toIssue tis := Discourse.HasIssue.toIssue tis.dgb

section Issue

variable {W P Fact : Type*} {Cont : Type} (dgb : DGB P Fact (Question W) Cont)

@[simp] theorem toIssue_pushQud (q : Question W) :
    Discourse.HasIssue.toIssue (dgb.pushQud q) = q := rfl

@[simp] theorem toIssue_addFact (p : Fact) :
    Discourse.HasIssue.toIssue (dgb.addFact p) = Discourse.HasIssue.toIssue dgb := rfl

@[simp] theorem toIssue_initial :
    Discourse.HasIssue.toIssue (DGB.initial : DGB P Fact (Question W) Cont) = ⊤ := rfl

end Issue

end Discourse.Gameboard
