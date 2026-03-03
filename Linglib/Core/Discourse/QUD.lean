import Mathlib.Data.Set.Basic

/-!
# QUD (Question Under Discussion) @cite{roberts-2012}

A QUD partitions the meaning space into equivalence classes. Two meanings are
equivalent under a QUD if they "answer the question the same way."

The file also contains inquisitive semantics core types (`InfoState`, `Issue`)
and @cite{roberts-2012}'s formalization of question entailment, subquestions, and
discourse move relevance.

-/

/-- A QUD partitions the meaning space via an equivalence relation.
Two meanings are equivalent if they "answer the question the same way." -/
structure QUD (M : Type*) where
  /-- Are two meanings equivalent under this QUD? -/
  sameAnswer : M → M → Bool
  /-- Equivalence must be reflexive -/
  refl : ∀ m, sameAnswer m m = true
  /-- Equivalence must be symmetric -/
  symm : ∀ m1 m2, sameAnswer m1 m2 = sameAnswer m2 m1
  /-- Equivalence must be transitive -/
  trans : ∀ m1 m2 m3, sameAnswer m1 m2 = true → sameAnswer m2 m3 = true → sameAnswer m1 m3 = true
  /-- Name for display/debugging -/
  name : String := ""

namespace QUD

variable {M : Type*}

section EquivalenceProperties

variable (q : QUD M)

/-- Reflexivity is guaranteed by construction -/
theorem isReflexive : ∀ m, q.sameAnswer m m = true := q.refl

/-- Symmetry is guaranteed by construction -/
theorem isSymmetric : ∀ m1 m2, q.sameAnswer m1 m2 = q.sameAnswer m2 m1 := q.symm

/-- Transitivity is guaranteed by construction -/
theorem isTransitive : ∀ m1 m2 m3,
    q.sameAnswer m1 m2 = true → q.sameAnswer m2 m3 = true → q.sameAnswer m1 m3 = true := q.trans

end EquivalenceProperties

/-- Convert QUD's equivalence relation to a Mathlib `Setoid`.

This enables `Finpartition.ofSetoid` for partition-based expected utility
decomposition, replacing ~200 lines of custom foldl arithmetic. -/
def toSetoid (q : QUD M) : Setoid M where
  r := λ a b => q.sameAnswer a b = true
  iseqv := {
    refl := λ a => q.refl a
    symm := λ {a b} h => by rw [q.symm] at h; exact h
    trans := λ {a b c} h1 h2 => q.trans a b c h1 h2
  }

instance decidableRel_toSetoid (q : QUD M) : DecidableRel q.toSetoid.r :=
  λ a b => inferInstanceAs (Decidable (q.sameAnswer a b = true))

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension). -/
def trivial : QUD M where
  sameAnswer _ _ := true
  refl _ := rfl
  symm _ _ := rfl
  trans _ _ _ _ _ := rfl
  name := "trivial"

/-- Compose two QUDs: equivalent iff equivalent under both. -/
def compose (q1 q2 : QUD M) : QUD M where
  sameAnswer m1 m2 := q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2
  refl m := by simp [q1.refl, q2.refl]
  symm m1 m2 := by rw [q1.symm, q2.symm, Bool.and_comm]
  trans m1 m2 m3 h12 h23 := by
    simp only [Bool.and_eq_true] at *
    exact ⟨q1.trans m1 m2 m3 h12.1 h23.1, q2.trans m1 m2 m3 h12.2 h23.2⟩
  name := s!"{q1.name}∧{q2.name}"

instance : Mul (QUD M) where
  mul := compose

/-- The equivalence class (partition cell) of a meaning under a QUD. -/
def cell (q : QUD M) (m : M) : Set M :=
  {m' : M | q.sameAnswer m m' = true}

/-- Two meanings are in the same cell iff they have the same answer. -/
theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq]

/-- Build QUD from a projection function using `DecidableEq` on the codomain.
Avoids the need for `BEq` + `LawfulBEq`; useful when the codomain only derives
`DecidableEq` (which is common for inductive types in Lean 4).

Example: `QUD.ofDecEq MagriWorld.grade` partitions by grade value. -/
def ofDecEq {α : Type*} [DecidableEq α] (project : M → α) (name : String := "") : QUD M where
  sameAnswer w v := decide (project w = project v)
  refl w := decide_eq_true_eq.mpr rfl
  symm w v := by
    show decide (project w = project v) = decide (project v = project w)
    congr 1; exact propext ⟨Eq.symm, Eq.symm⟩
  trans w v u h1 h2 := by
    rw [decide_eq_true_eq] at *
    exact h1.trans h2
  name := name

/-- Build QUD from a projection function with `BEq`/`LawfulBEq` codomain.

This is the primary constructor for QUDs over types with Boolean equality.
`exact`, `binaryPartition`, and `PrecisionProjection.applyToQUD` all
delegate to this. -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (name : String := "") : QUD M where
  sameAnswer m1 m2 := f m1 == f m2
  refl m := beq_self_eq_true (f m)
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := name

@[simp] theorem ofProject_sameAnswer {A : Type} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = (f m1 == f m2) := rfl

/-- `sameAnswer` for projection QUD iff same image under `f`. -/
theorem ofProject_sameAnswer_iff {A : Type} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = true ↔ f m1 = f m2 := by
  simp only [ofProject_sameAnswer, beq_iff_eq]

/-- For projection QUDs, cells are exactly fibers of the projection. -/
theorem ofProject_cell_eq_fiber {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m : M) :
    (ofProject f).cell m = {m' : M | f m' = f m} := by
  ext m'
  simp only [cell, Set.mem_setOf_eq, ofProject_sameAnswer, beq_iff_eq]
  exact eq_comm

section BEqConstructors
variable [BEq M]

/-- The identity QUD: speaker wants to convey exact meaning.
Each meaning is its own equivalence class. -/
def exact [LawfulBEq M] : QUD M where
  sameAnswer m1 m2 := m1 == m2
  refl m := beq_self_eq_true m
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := "exact"

end BEqConstructors

end QUD

namespace ProductQUD

variable {A B : Type} [BEq A] [BEq B] [LawfulBEq A] [LawfulBEq B]

/-- QUD that cares only about first component -/
def fst : QUD (A × B) :=
  QUD.ofProject Prod.fst "fst"

/-- QUD that cares only about second component -/
def snd : QUD (A × B) :=
  QUD.ofProject Prod.snd "snd"

/-- QUD that cares about both components (exact) -/
def both : QUD (A × B) :=
  QUD.exact (M := A × B)

end ProductQUD

/-- Precision projection for numeric meanings (approximate vs exact). -/
structure PrecisionProjection (N : Type) where
  /-- Round/approximate the value -/
  round : N → N
  /-- Name -/
  name : String := ""

namespace PrecisionProjection

/-- Exact precision: no rounding -/
def exact {N : Type} : PrecisionProjection N where
  round := id
  name := "exact"

/-- Round to nearest multiple of k -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := (n / k) * k
  name := s!"round{k}"

/-- Compose precision with a QUD. Delegates to `QUD.ofProject`. -/
def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M :=
  QUD.ofProject (prec.round ∘ proj) prec.name

end PrecisionProjection

-- ============================================================================
-- Inquisitive Semantics Core Types
-- ============================================================================
--
-- The `QUD M` type above partitions a meaning space M by an equivalence
-- relation. The types below represent the *intensional* side: propositions
-- as sets of worlds, questions as sets of propositions (alternatives).
--
-- The connection: a `QUD M` induces an `Issue W` when we fix a world type W
-- and a denotation function M → (W → Bool). Each equivalence class of the
-- QUD maps to an alternative of the Issue. `QUD.refines` (Core/Partition.lean)
-- corresponds to `questionEntails` below: if Q refines q at the partition
-- level, then Q entails q at the issue level.
--
-- References:
-- - @cite{ciardelli-groenendijk-roelofsen-2019}. Inquisitive Semantics. OUP.
-- - @cite{roberts-2012}. Information structure in discourse. S&P 5(6).

namespace Discourse

-- Information States

/-- An information state: worlds compatible with current information.

In standard Inquisitive Semantics, an info state is a SET of worlds.
Here we represent it as a characteristic function σ : W → Bool.

Semantically: σ w = true means "world w is compatible with the information".
The empty info state (σ = λ_ => false) represents inconsistent information. -/
abbrev InfoState (W : Type*) := W → Bool

/-- The absurd/inconsistent info state: no worlds are compatible. -/
def absurdState {W : Type*} : InfoState W := λ _ => false

/-- The trivial info state: all worlds are compatible (total ignorance). -/
def trivialState {W : Type*} : InfoState W := λ _ => true

/-- Check if an info state is empty (inconsistent). -/
def InfoState.isEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  !worlds.any σ

/-- Check if an info state is non-empty. -/
def InfoState.isNonEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  worlds.any σ

/-- Info state σ is a subset of σ' (σ ⊆ σ'). -/
def InfoState.subset {W : Type*} (σ σ' : InfoState W) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → σ' w

/-- Intersection of two info states. -/
def InfoState.inter {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w && σ' w

/-- Union of two info states. -/
def InfoState.union {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w || σ' w

-- Support and Entailment

/-- Info state σ supports proposition p iff σ ⊆ ⟦p⟧.

This is the fundamental relation in Inquisitive Semantics:
σ ⊨ p (σ supports p) iff every world in σ makes p true.

If σ is empty, it supports every proposition (ex falso quodlibet). -/
def supports {W : Type*} (σ : InfoState W) (p : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → p w

/-- Propositional entailment: p entails q iff every p-world is a q-world.

Equivalently: the info state ⟦p⟧ supports ⟦q⟧ over all worlds. -/
def propEntails {W : Type*} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !p w || q w

-- Issues (Questions in Inquisitive Semantics)

/-- An issue: set of information states that resolve the question.

In full Inquisitive Semantics, issues must be:
1. **Downward-closed**: if σ resolves and σ' ⊆ σ, then σ' resolves
2. **Non-empty**: the absurd state ∅ resolves every issue

Here we represent an issue by its maximal (largest) resolving states,
called **alternatives**. Downward closure is then implicit.

This representation aligns with Hamblin semantics: the alternatives are
the possible complete answers. -/
structure Issue (W : Type*) where
  /-- The maximal resolving states (alternatives) -/
  alternatives : List (InfoState W)

namespace Issue

variable {W : Type*}

/-- Check if an info state resolves the issue.

σ resolves Q iff σ is contained in some alternative.
(Downward closure: any sub-state of an alternative also resolves.) -/
def resolves (q : Issue W) (σ : InfoState W) (worlds : List W) : Bool :=
  q.alternatives.any λ alt => σ.subset alt worlds

/-- An issue is inquisitive if it has multiple alternatives.

Non-inquisitive issues have exactly one alternative (assertions).
Inquisitive issues genuinely ask for information. -/
def isInquisitive (q : Issue W) : Bool :=
  q.alternatives.length > 1

/-- An issue is informative if not all states resolve it.

Non-informative issues are resolved by the trivial state (tautologies).
Informative issues rule out some possibilities. -/
def isInformative (q : Issue W) (worlds : List W) : Bool :=
  !q.resolves trivialState worlds

/-- The empty issue: resolved by any info state. -/
def empty : Issue W := { alternatives := [trivialState] }

/-- The absurd issue: resolved only by the absurd state. -/
def absurd : Issue W := { alternatives := [absurdState] }

/-- A proposition is a mention-some answer to Q: it resolves Q by settling
at least one alternative without settling all of them.

In the decision-theoretic setting, mention-some answerhood is defined
relative to a decision problem (see `Core.Agent.DecisionTheory.isMentionSome`).
This definition is the purely logical version from inquisitive semantics:
an answer settles Q partially. -/
def isMentionSomeAnswer (q : Issue W) (answer : InfoState W) (worlds : List W) : Bool :=
  -- Settles at least one alternative (answer ⊆ some alt)
  q.alternatives.any (fun alt => answer.subset alt worlds) &&
  -- Doesn't settle all alternatives
  q.alternatives.any (fun alt => !(answer.subset alt worlds))

/-- A proposition is a mention-all answer to Q: it settles all alternatives
(resolves Q completely by being contained in every alternative). -/
def isMentionAllAnswer (q : Issue W) (answer : InfoState W) (worlds : List W) : Bool :=
  q.alternatives.all (fun alt => answer.subset alt worlds)

/-- Number of alternatives (possible complete answers). -/
def numAlternatives (q : Issue W) : Nat :=
  q.alternatives.length

-- Issue Operations

/-- Intersection of two issues (conjunction): Q ∩ Q'. -/
def inter (q q' : Issue W) (worlds : List W) : Issue W :=
  let pairs := q.alternatives.flatMap λ a =>
    q'.alternatives.filterMap λ a' =>
      let intersection := a.inter a'
      if intersection.isNonEmpty worlds then some intersection else none
  { alternatives := pairs }

/-- Union of two issues (disjunction): Q ∪ Q'. -/
def union (q q' : Issue W) : Issue W :=
  { alternatives := q.alternatives ++ q'.alternatives }

/-- Create an Issue from a polar question.

"Is p true?" has two alternatives: ⟦p⟧ and ⟦¬p⟧. -/
def polar (p : W → Bool) : Issue W :=
  { alternatives := [p, λ w => !p w] }

/-- Create an Issue from a list of alternatives (direct construction). -/
def ofAlternatives (alts : List (InfoState W)) : Issue W :=
  { alternatives := alts }

/-- Create a wh-question Issue: "which x satisfies P?" -/
def which {E : Type*} (domain : List E) (pred : E → W → Bool) : Issue W :=
  { alternatives := domain.map λ e => λ w => pred e w }

end Issue

-- Propositional Content of Issues

/-- The informational content of an issue: the union of all alternatives.

This is what the issue "presupposes" — the proposition that SOME alternative
is true. -/
def Issue.infoContent {W : Type*} (q : Issue W) : W → Bool :=
  λ w => q.alternatives.any λ alt => alt w

/-- The highlighted/informational content of an issue. Alias for `infoContent`.

In the standard inquisitive semantics framework, the informational content
(union of all alternatives) IS the highlighted content for declarative
sentences. We keep this alias because @cite{ippolito-kiss-williams-2025} Def. 16 uses "highlighted
content" terminology in defining the at-issue content of discourse *only*. -/
abbrev Issue.highlighted {W : Type*} (q : Issue W) : W → Bool :=
  q.infoContent

-- Theorems

/-- Polar questions are always inquisitive (two alternatives). -/
theorem polar_is_inquisitive {W : Type*} (p : W → Bool) :
    (Issue.polar p).isInquisitive = true := rfl

/-- The empty issue is not inquisitive. -/
theorem empty_not_inquisitive {W : Type*} :
    (Issue.empty : Issue W).isInquisitive = false := rfl

-- ============================================================================
-- @cite{roberts-2012}: QUD Structure, Subquestions, and Relevance
-- ============================================================================
--
-- Roberts' QUD theory introduces hierarchical question structure: a QUD
-- decomposes into subquestions, and discourse moves are relevant iff they
-- address the QUD or its subquestions.
--
-- The connection to QUD.refines (Core/Partition.lean):
-- - QUD.refines q q'   ≡  q's partition refines q' (knows q → knows q')
-- - questionEntails Q q ≡  every alternative of Q entails some alt of q
-- These are the same relation at different levels of abstraction.

/-- A proposition p partially answers an issue q if p entails at least one
of q's alternatives.

@cite{roberts-2012}: a partial answer to Q is a proposition that, when added to
the common ground, resolves at least one alternative. We use the strong
version: p entails (is a subset) some alternative of q. -/
def partiallyAnswers {W : Type*} (p : W → Bool) (q : Issue W) (worlds : List W) : Bool :=
  q.alternatives.any fun alt => propEntails p alt worlds

/-- Question q₁ entails question q₂ iff every alternative of q₁ entails
some alternative of q₂.

@cite{roberts-2012} Def. 8 (following @cite{groenendijk-stokhof-1984}:16):
"One interrogative q₁ entails another q₂ iff every proposition that
answers q₁ answers q₂ as well."

At the partition level, this corresponds to `QUD.refines` (Core/Partition.lean):
if Q refines q, then knowing Q's answer determines q's answer. -/
def questionEntails {W : Type*} (q₁ q₂ : Issue W) (worlds : List W) : Bool :=
  q₁.alternatives.all fun alt₁ =>
    q₂.alternatives.any fun alt₂ => propEntails alt₁ alt₂ worlds

/-- q is a subquestion of Q iff Q entails q: answering Q yields a
complete answer to q.

@cite{roberts-2012} Def. 8–9. At the partition level, this is `QUD.refines`:
the parent question's partition is a refinement of the subquestion's. -/
def isSubquestion {W : Type*} (q parent : Issue W) (worlds : List W) : Bool :=
  questionEntails parent q worlds

/-- A discourse move (assertion or question) is relevant to the QUD if
it partially answers the QUD or a subquestion.

@cite{roberts-2012} Def. 15 / @cite{ippolito-kiss-williams-2025} assumption iii, p. 225:
"S is relevant to QUD if S is either a subquestion of QUD or an answer
to a subquestion q of QUD."

For assertions (single-alternative issues): checks whether the propositional
content partially answers the QUD or a subquestion.
For questions (multi-alternative issues): checks whether any alternative
partially answers the QUD or a subquestion — resolving the question would
inform a subquestion. -/
def moveRelevant {W : Type*} (den : Issue W) (qud : Issue W)
    (subquestions : List (Issue W)) (worlds : List W) : Bool :=
  den.alternatives.any fun alt =>
    partiallyAnswers alt qud worlds ||
    subquestions.any fun sq =>
      partiallyAnswers alt sq worlds

/-- `propEntails` is reflexive. -/
theorem propEntails_refl {W : Type*} (p : W → Bool) (worlds : List W) :
    propEntails p p worlds = true := by
  unfold propEntails
  simp [List.all_eq_true]

/-- `questionEntails` is reflexive: every question entails itself. -/
theorem questionEntails_refl {W : Type*} (q : Issue W) (worlds : List W) :
    questionEntails q q worlds = true := by
  unfold questionEntails
  simp only [List.all_eq_true, List.any_eq_true]
  intro alt hMem
  exact ⟨alt, hMem, propEntails_refl alt worlds⟩

/-- Subquestion is reflexive: every question is a subquestion of itself. -/
theorem isSubquestion_refl {W : Type*} (q : Issue W) (worlds : List W) :
    isSubquestion q q worlds = true :=
  questionEntails_refl q worlds

/-- Partial answerhood of an alternative implies move relevance.

If some alternative of a move partially answers the QUD directly,
the move is relevant (even without subquestions). -/
theorem partiallyAnswers_implies_relevant {W : Type*}
    (den : Issue W) (qud : Issue W) (worlds : List W)
    (alt : W → Bool) (hAlt : alt ∈ den.alternatives)
    (hPA : partiallyAnswers alt qud worlds = true) :
    moveRelevant den qud [] worlds = true := by
  unfold moveRelevant
  rw [List.any_eq_true]
  exact ⟨alt, hAlt, by simp [hPA]⟩

end Discourse
