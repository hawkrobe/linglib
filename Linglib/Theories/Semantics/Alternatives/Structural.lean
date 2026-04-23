import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Linglib.Core.Tree
import Linglib.Theories.Semantics.Alternatives.Source

/-!
# Structurally-Defined Alternatives
@cite{katzir-2007}

Katzir, R. (2007). Structurally-defined alternatives.
Linguistics and Philosophy, 30(6), 669–690.

Scalar alternatives are not stipulated via Horn scales but generated
structurally. The alternatives to a sentence φ are all parse trees
obtainable from φ by three operations — deletion, contraction, and
substitution — using items from the substitution source L(φ).

## Key Definitions

- **Substitution source** (def 41): L(φ) = lexicon ∪ subtrees(φ)
- **Structural complexity** (def 19): ψ ≲ φ iff φ can be transformed
  to ψ by deletion, contraction, and substitution with items from L(φ).
  Also: φ ∼ ψ (equal complexity) and ψ < φ (strictly less complex).
- **Structural alternatives** (def 20): A_str(φ) := {ψ : ψ ≲ φ}
- **Conversational principle** (def 21): do not assert φ if ∃ φ' ∈ A_str(φ)
  with ⟦φ'⟧ ⊂ ⟦φ⟧ and φ' weakly assertable

## The Symmetry Problem

The naïve conversational principle says: don't assert φ if there is a
stronger alternative φ'. The symmetry problem (Kroch 1972; von Fintel
& Heim class notes; see p. 673) is that for any stronger φ', there
exists a symmetric alternative φ'' = φ ∧ ¬φ' which is also stronger,
licensing the opposite inference.

Katzir's solution: restrict alternatives to those obtainable by
structural operations. For φ = "John ate some of the cake":
- φ' = "John ate all of the cake" ∈ A_str(φ) — by substituting
  the Det leaf "some" with "all" (both in the lexicon, same category)
- φ'' = "John ate some but not all" ∉ A_str(φ) — requires ConjP/NegP
  structure not available in L(φ)

## Tree Type

Uses the unified `Tree C W` from `Core.Tree`. All definitions are
parameterized over the category type `C`, so they work with UD-grounded
`Cat`, framework-specific categories, or any `C` with `BEq`/`DecidableEq`.

## Connection to Linglib

- **Horn scales subsumed**: Lexical substitution of same-category items
  is a special case of structural alternatives (§8)
- **Fills truthmaker gap**: `AlternativeSensitive.lean`'s `IsTruthmaker`
  requires ALT_S computed via structural alternative generation
- **Economy connection**: @cite{katzir-singh-2015}'s complexity ordering
  in `KatzirSingh2015.lean` is based on structural complexity (def 19)
-/

namespace Alternatives.Structural

open Core.Tree
open Tree

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Substitution Source (def 41)
-- ═══════════════════════════════════════════════════════════════════════

/-- The substitution source for φ (def 41, final version):
the union of the lexicon of the language with the set of all subtrees
of φ. The revised definition (adding subtrees) is needed to handle
Matsumoto's examples (§5) where a complex sub-constituent of φ serves
as a substitution source for a simpler constituent elsewhere in φ.

The initial definition (def 18) used only the lexicon; def 41 adds
subtrees of φ to derive the inference in examples like:
  "It was warm yesterday, and it is a little bit more than warm today"
where "a little bit more than warm" (a subtree of φ) substitutes for
"warm" in the left conjunct. -/
def substitutionSource {C W : Type} (lexicon : List (Tree C W))
    (φ : Tree C W) : List (Tree C W) :=
  lexicon ++ φ.subtrees

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Structural Operations (def 19)
-- ═══════════════════════════════════════════════════════════════════════

/-- One structural operation on parse trees (p. 678).
`StructOp source φ ψ` means ψ is obtained from φ by one application of
deletion, contraction, or substitution with items from `source`.

The three operations:
- **Deletion**: remove a subtree (a child from a node)
- **Contraction**: remove an edge and identify endpoints (replace a node
  with one of its same-category children)
- **Substitution**: replace any constituent with a same-category item
  from the substitution source L(φ)

The `inBind` constructor extends Katzir's original PF-only operations
to handle binding structures, allowing structural operations inside
the body of a λ-binder. -/
inductive StructOp {C W : Type} (source : List (Tree C W)) :
    Tree C W → Tree C W → Prop where
  /-- Substitute: replace tree with a same-category item from source. -/
  | subst {φ ψ : Tree C W}
    (h_cat : ψ.cat = φ.cat) (h_src : ψ ∈ source) :
    StructOp source φ ψ
  /-- Delete: remove the i-th child from a node. -/
  | delete {cat : C} {cs : List (Tree C W)} (i : Fin cs.length) :
    StructOp source (.node cat cs) (.node cat (cs.eraseIdx i))
  /-- Contract: replace a node with one of its same-category children. -/
  | contract {cat : C} {cs : List (Tree C W)}
    {child : Tree C W}
    (h_mem : child ∈ cs) (h_cat : child.cat = cat) :
    StructOp source (.node cat cs) child
  /-- Recursive: apply an operation inside one child of a node. -/
  | inChild {cat : C} {cs : List (Tree C W)}
    (i : Fin cs.length) {ψ_child : Tree C W}
    (h_step : StructOp source (cs.get i) ψ_child) :
    StructOp source (.node cat cs) (.node cat (cs.set i ψ_child))
  /-- Recursive: apply an operation inside a binder body. -/
  | inBind {n : Nat} {cat : C} {body body' : Tree C W}
    (h_step : StructOp source body body') :
    StructOp source (.bind n cat body) (.bind n cat body')

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Structural Complexity and Alternatives (defs 19–20)
-- ═══════════════════════════════════════════════════════════════════════

/-- Structural complexity ordering (def 19): ψ ≲ φ iff φ can be
transformed into ψ by a finite chain of structural operations
using items from `source`.

Formally: the reflexive-transitive closure of `StructOp source`. -/
def atMostAsComplex {C W : Type} (source : List (Tree C W))
    (ψ φ : Tree C W) : Prop :=
  Relation.ReflTransGen (StructOp source) φ ψ

/-- Equal complexity (def 19): φ ∼ ψ iff φ ≲ ψ ∧ ψ ≲ φ. -/
def equalComplexity {C W : Type} (source : List (Tree C W))
    (φ ψ : Tree C W) : Prop :=
  atMostAsComplex source φ ψ ∧ atMostAsComplex source ψ φ

/-- Strictly less complex (def 19): ψ < φ iff ψ ≲ φ ∧ ¬(φ ≲ ψ). -/
def strictlyLessComplex {C W : Type} (source : List (Tree C W))
    (ψ φ : Tree C W) : Prop :=
  atMostAsComplex source ψ φ ∧ ¬atMostAsComplex source φ ψ

/-- Structural alternatives (def 20):
A_str(φ) := {ψ : ψ ≲ φ}, where ≲ uses L(φ) = lexicon ∪ subtrees(φ). -/
def structuralAlternatives {C W : Type} (lex : List (Tree C W))
    (φ : Tree C W) : Set (Tree C W) :=
  {ψ | atMostAsComplex (substitutionSource lex φ) ψ φ}

/-- The Katzir source as an `AlternativeSource`. Pragmatic competition
operators (`violatesMP`, `violatesMaximize`, `violatesMCIs`) accept any
`AlternativeSource (Tree C W)`; pass `katzirSource lex` to recover the
classical Katzir 2007 competition. Other sources include
`Indirect.indirectFrom` (Jeretič et al. 2025). -/
def katzirSource {C W : Type} (lex : List (Tree C W)) :
    Alternatives.AlternativeSource (Tree C W) :=
  structuralAlternatives lex

/-- φ is always a structural alternative to itself (reflexivity of ≲). -/
theorem self_is_alternative {C W : Type} (lex : List (Tree C W))
    (φ : Tree C W) :
    φ ∈ structuralAlternatives lex φ :=
  Relation.ReflTransGen.refl

theorem self_mem_katzirSource {C W : Type} (lex : List (Tree C W))
    (φ : Tree C W) : φ ∈ katzirSource lex φ :=
  Relation.ReflTransGen.refl

-- ═══════════════════════════════════════════════════════════════════════
-- §3a  equalComplexity is an equivalence relation
-- ═══════════════════════════════════════════════════════════════════════

namespace equalComplexity

variable {C W : Type} {source : List (Tree C W)}

theorem refl (φ : Tree C W) : equalComplexity source φ φ :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem symm {a b : Tree C W} (h : equalComplexity source a b) :
    equalComplexity source b a :=
  ⟨h.2, h.1⟩

theorem trans {a b c : Tree C W}
    (h₁ : equalComplexity source a b) (h₂ : equalComplexity source b c) :
    equalComplexity source a c :=
  ⟨Relation.ReflTransGen.trans h₂.1 h₁.1,
   Relation.ReflTransGen.trans h₁.2 h₂.2⟩

end equalComplexity

-- ═══════════════════════════════════════════════════════════════════════
-- §3b  Building blocks for `equalComplexity` proofs
-- ═══════════════════════════════════════════════════════════════════════

/-- A single same-category terminal substitution gives equal complexity,
    provided BOTH terminals are in the source (so the substitution is
    reversible). The standard atom for any `equalComplexity` chain. -/
theorem equalComplexity_terminal_subst {C W : Type}
    (source : List (Tree C W)) (cat : C) (oldW newW : W)
    (h_old : Tree.terminal cat oldW ∈ source)
    (h_new : Tree.terminal cat newW ∈ source) :
    equalComplexity source (.terminal cat oldW) (.terminal cat newW) :=
  ⟨Relation.ReflTransGen.single (StructOp.subst rfl h_old),
   Relation.ReflTransGen.single (StructOp.subst rfl h_new)⟩

-- TODO: `reflTransGen_StructOp_inChild` + `equalComplexity_inChild`
-- (the "lift through inChild navigation" infrastructure that would let
-- consumers chain leaf substitutions at arbitrary tree paths) belong
-- here. The proof requires `Relation.ReflTransGen.lift` plus list-set
-- API (`List.length_set`, `List.get_set`, set-set idempotency) and is
-- non-trivial. Deferred until the next consumer wants it.

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Worked Example: Some/All (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

/-- Vocabulary for the worked examples. -/
inductive ExWord where
  | john | ate | some_ | all_ | cake
  | apple | pear | or_ | and_
  | tall | man
  | but_ | not_
  deriving DecidableEq, Repr

section SomeAll

open Cat ExWord

/-- Minimal lexicon: terminal items available for substitution. -/
def exLexicon : List (Tree Cat ExWord) :=
  [.terminal .N .john, .terminal .V .ate,
   .terminal .Det .some_, .terminal .Det .all_,
   .terminal .N .cake, .terminal .N .apple, .terminal .N .pear,
   .terminal .Conj .or_, .terminal .Conj .and_,
   .terminal .Adj .tall, .terminal .N .man]

/-- φ = "John ate some cake" (simplified parse tree). -/
def someSentence : Tree Cat ExWord :=
  .node .S [
    .terminal .N .john,
    .node .VP [.terminal .V .ate, .terminal .Det .some_, .terminal .N .cake]]

/-- φ' = "John ate all cake" — the scalar alternative. -/
def allSentence : Tree Cat ExWord :=
  .node .S [
    .terminal .N .john,
    .node .VP [.terminal .V .ate, .terminal .Det .all_, .terminal .N .cake]]

/-- Leaf substitution of "some" → "all" produces the expected tree. -/
theorem leafSubst_some_all :
    someSentence.leafSubst .some_ .all_ .Det = allSentence := by rfl

/-- φ' is a structural alternative to φ: substitute Det leaf "some"
with "all" from the lexicon (both Det, same category).

This is the paper's ex. (25): φ = "John ate some of the cake",
φ' = "John ate all of the cake". Since "all" and "some" are both
in the lexicon and both Det, substitution yields φ' ∼ φ, so
φ' ∈ A_str(φ). -/
theorem all_is_alternative_to_some :
    allSentence ∈ structuralAlternatives exLexicon someSentence := by
  unfold structuralAlternatives atMostAsComplex
  apply Relation.ReflTransGen.single
  apply StructOp.inChild ⟨1, by simp⟩
  apply StructOp.inChild ⟨1, by simp⟩
  apply StructOp.subst
  · rfl
  · simp [substitutionSource, exLexicon]

/-- Equal complexity: "some" ↔ "all" by mutual substitution (same
number of operations in each direction). φ' ∼ φ in the sense of def 19:
both φ ≲ φ' and φ' ≲ φ hold (each obtained from the other by one
leaf substitution). -/
theorem some_all_equal_complexity :
    equalComplexity (substitutionSource exLexicon someSentence)
      someSentence allSentence := by
  constructor
  · -- someSentence ≲ allSentence: substitute "all" back to "some"
    apply Relation.ReflTransGen.single
    apply StructOp.inChild ⟨1, by simp⟩
    apply StructOp.inChild ⟨1, by simp⟩
    apply StructOp.subst
    · rfl
    · simp [substitutionSource, exLexicon]
  · -- allSentence ≲ someSentence
    apply Relation.ReflTransGen.single
    apply StructOp.inChild ⟨1, by simp⟩
    apply StructOp.inChild ⟨1, by simp⟩
    apply StructOp.subst
    · rfl
    · simp [substitutionSource, exLexicon]

end SomeAll

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Symmetry Problem Solved (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

section SymmetryProblem

open Cat ExWord

/-- φ'' = "John ate some but not all cake" — the symmetric alternative
that the naïve principle cannot exclude.

Under the naïve principle, φ'' is stronger than φ (⟦φ''⟧ ⊂ ⟦φ⟧) and
should block assertion of φ. But it licenses the inference that John
ate ALL of the cake — the opposite of the correct implicature.
Katzir's structural approach excludes φ'' because it requires ConjP
and NegP structure not derivable from L(φ). -/
def someButNotAllSentence : Tree Cat ExWord :=
  .node .S [
    .terminal .N .john,
    .node .VP [
      .terminal .V .ate,
      .node .ConjP [
        .terminal .Det .some_,
        .terminal .Conj .but_,
        .node .NegP [.terminal .Neg .not_, .terminal .Det .all_]],
      .terminal .N .cake]]

/-- φ'' contains ConjP — a category absent from φ and L(φ). -/
theorem symmetric_has_conjp :
    someButNotAllSentence.containsCat .ConjP = true := by native_decide

/-- φ does not contain ConjP. -/
theorem some_lacks_conjp :
    someSentence.containsCat .ConjP = false := by native_decide

/-- No item in L(someSentence) contains ConjP: the lexicon consists
of terminal leaves (which have no internal structure) and the subtrees
of φ are {S[...], N(john), VP[...], V(ate), Det(some), N(cake)} —
none contain ConjP. -/
theorem source_lacks_conjp :
    (substitutionSource exLexicon someSentence).all
      (fun t => !t.containsCat .ConjP) = true := by native_decide

-- ── Private helpers for category_preservation ──────────────────

private theorem containsCatList_false_of_mem {C W : Type} [BEq C] (c : C)
    (cs : List (Tree C W)) (t : Tree C W)
    (h : Tree.containsCat.containsCatList c cs = false)
    (ht : t ∈ cs) :
    t.containsCat c = false := by
  induction cs with
  | nil => exact absurd ht List.not_mem_nil
  | cons x xs ih =>
    simp only [Tree.containsCat.containsCatList, Bool.or_eq_false_iff] at h
    cases List.mem_cons.mp ht with
    | inl heq => subst heq; exact h.1
    | inr hmem => exact ih h.2 hmem

private theorem containsCatList_eraseIdx {C W : Type} [BEq C] (c : C)
    (cs : List (Tree C W)) (i : Nat) (hi : i < cs.length)
    (h : Tree.containsCat.containsCatList c cs = false) :
    Tree.containsCat.containsCatList c (cs.eraseIdx i) = false := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [Tree.containsCat.containsCatList, Bool.or_eq_false_iff] at h
    cases i with
    | zero => simp [List.eraseIdx]; exact h.2
    | succ n =>
      have hn : n < xs.length := by simp [List.length] at hi; omega
      simp only [List.eraseIdx, Tree.containsCat.containsCatList, Bool.or_eq_false_iff]
      exact ⟨h.1, ih n hn h.2⟩

private theorem containsCatList_set {C W : Type} [BEq C] (c : C)
    (cs : List (Tree C W)) (i : Nat) (hi : i < cs.length)
    (t : Tree C W)
    (h_cs : Tree.containsCat.containsCatList c cs = false)
    (h_t : t.containsCat c = false) :
    Tree.containsCat.containsCatList c (cs.set i t) = false := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [Tree.containsCat.containsCatList, Bool.or_eq_false_iff] at h_cs
    cases i with
    | zero =>
      simp only [List.set, Tree.containsCat.containsCatList, Bool.or_eq_false_iff]
      exact ⟨h_t, h_cs.2⟩
    | succ n =>
      have hn : n < xs.length := by simp [List.length] at hi; omega
      simp only [List.set, Tree.containsCat.containsCatList, Bool.or_eq_false_iff]
      exact ⟨h_cs.1, ih n hn h_cs.2⟩

private theorem structOp_preserves_no_cat {C W : Type} [BEq C]
    (source : List (Tree C W)) (c : C)
    (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, s.containsCat c = false)
    (h_φ : φ.containsCat c = false)
    (h_step : StructOp source φ ψ) :
    ψ.containsCat c = false := by
  induction h_step with
  | subst _ h_src => exact h_source _ h_src
  | @delete cat cs i =>
    unfold Tree.containsCat at h_φ ⊢
    simp only [Bool.or_eq_false_iff] at h_φ ⊢
    exact ⟨h_φ.1, containsCatList_eraseIdx c cs i i.isLt h_φ.2⟩
  | @contract cat cs child h_mem _ =>
    unfold Tree.containsCat at h_φ
    simp only [Bool.or_eq_false_iff] at h_φ
    exact containsCatList_false_of_mem c cs child h_φ.2 h_mem
  | @inChild cat cs i ψ_child _ ih =>
    unfold Tree.containsCat at h_φ ⊢
    simp only [Bool.or_eq_false_iff] at h_φ ⊢
    constructor
    · exact h_φ.1
    · exact containsCatList_set c cs i i.isLt ψ_child h_φ.2
        (ih (containsCatList_false_of_mem c cs (cs.get i) h_φ.2
          (List.get_mem cs i)))
  | @inBind n cat body body' _ ih =>
    unfold Tree.containsCat at h_φ ⊢
    simp only [Bool.or_eq_false_iff] at h_φ ⊢
    exact ⟨h_φ.1, ih h_φ.2⟩

-- ── Main invariant ──────────────────────────────────────────────

/-- Key invariant: structural operations preserve absence of a category
when that category does not appear in the substitution source.

If no item in `source` contains category `c`, and tree `φ` does not
contain `c`, then no tree reachable from φ by structural operations
contains `c`. This is because:
- Substitution can only introduce material from `source` (which lacks `c`)
- Deletion removes material (can't introduce `c`)
- Contraction promotes a subtree (which also lacks `c` by hypothesis)

Proof by induction on `ReflTransGen`, reducing to the single-step
`structOp_preserves_no_cat` which case-splits on the five `StructOp`
constructors. -/
theorem category_preservation {C W : Type} [BEq C]
    (source : List (Tree C W)) (c : C)
    (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, s.containsCat c = false)
    (h_φ : φ.containsCat c = false)
    (h_reach : atMostAsComplex source ψ φ) :
    ψ.containsCat c = false := by
  unfold atMostAsComplex at h_reach
  induction h_reach with
  | refl => exact h_φ
  | tail _ h_last ih =>
    exact structOp_preserves_no_cat source c _ _ h_source ih h_last

/-- The symmetric alternative φ'' is NOT a structural alternative to φ.

Proof sketch: L(φ) contains no item with category ConjP
(`source_lacks_conjp`), and φ itself lacks ConjP (`some_lacks_conjp`),
so by `category_preservation` every tree in A_str(φ) lacks ConjP.
But φ'' contains ConjP (`symmetric_has_conjp`) — contradiction.

This is the paper's central result: structure alone excludes the
symmetric alternative, solving the symmetry problem without lexical
stipulation of which alternatives are "good." -/
theorem symmetry_problem_solved :
    someButNotAllSentence ∉ structuralAlternatives exLexicon
      someSentence := by
  intro h
  have h_preserved := category_preservation
    (substitutionSource exLexicon someSentence) .ConjP
    someSentence someButNotAllSentence
    (by intro s hs
        have := List.all_eq_true.mp source_lacks_conjp s hs
        simp at this; exact this)
    (by native_decide)
    h
  exact absurd symmetric_has_conjp (by rw [h_preserved]; decide)

end SymmetryProblem

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Disjunction: Or/And (§4.2)
-- ═══════════════════════════════════════════════════════════════════════

section Disjunction

open Cat ExWord

/-- φ = "John ate the apple or the pear" (ex. 26a). -/
def orSentence : Tree Cat ExWord :=
  .node .S [
    .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .apple]],
    .terminal .Conj .or_,
    .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .pear]]]

/-- φ' = "John ate the apple and the pear" (ex. 26b).
Obtained by substituting Conj "or" with "and". -/
def andSentence : Tree Cat ExWord :=
  .node .S [
    .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .apple]],
    .terminal .Conj .and_,
    .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .pear]]]

/-- Leaf substitution of "or" → "and" produces the conjunction. -/
theorem leafSubst_or_and :
    orSentence.leafSubst .or_ .and_ .Conj = andSentence := by rfl

/-- "and" alternative obtainable by one substitution step. -/
theorem and_is_alternative_to_or :
    andSentence ∈ structuralAlternatives exLexicon orSentence := by
  unfold structuralAlternatives atMostAsComplex
  apply Relation.ReflTransGen.single
  apply StructOp.inChild ⟨1, by simp⟩
  apply StructOp.subst
  · rfl
  · simp [substitutionSource, exLexicon]

/-- The left disjunct "John ate the apple" is an alternative to the
disjunction — obtainable by deletion of the right disjunct and the
conjunction.

This derives the effect of Sauerland's L operator (which returns
the left argument of a binary connective) from structural operations
alone, without stipulating L as a primitive. The paper (p. 683) notes
that L and R are "somewhat stipulative" and that structural
alternatives derive the same predictions. -/
def leftDisjunct : Tree Cat ExWord :=
  .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .apple]]

theorem left_disjunct_is_alternative :
    leftDisjunct ∈ structuralAlternatives exLexicon orSentence := by
  unfold structuralAlternatives atMostAsComplex
  -- Two steps: delete child 2 (right disjunct), then delete child 1 (Conj)
  apply Relation.ReflTransGen.head
  · exact StructOp.delete ⟨2, by simp⟩
  apply Relation.ReflTransGen.head
  · exact StructOp.delete ⟨1, by simp [List.eraseIdx]⟩
  -- Now we have .node .S [leftDisjunct] — need contraction
  apply Relation.ReflTransGen.single
  apply StructOp.contract
  · exact List.Mem.head _
  · rfl

/-- The right disjunct is also an alternative (Sauerland's R operator). -/
def rightDisjunct : Tree Cat ExWord :=
  .node .S [.terminal .N .john, .node .VP [.terminal .V .ate, .terminal .N .pear]]

theorem right_disjunct_is_alternative :
    rightDisjunct ∈ structuralAlternatives exLexicon orSentence := by
  unfold structuralAlternatives atMostAsComplex
  apply Relation.ReflTransGen.head
  · exact StructOp.delete ⟨0, by simp⟩
  apply Relation.ReflTransGen.head
  · exact StructOp.delete ⟨0, by simp [List.eraseIdx]⟩
  apply Relation.ReflTransGen.single
  apply StructOp.contract
  · exact List.Mem.head _
  · rfl

end Disjunction

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Deletion Alternatives (§4.3)
-- ═══════════════════════════════════════════════════════════════════════

section Deletion

open Cat ExWord

/-- "A tall man" parse tree (ex. 29a). -/
def tallMan : Tree Cat ExWord :=
  .node .NP [.terminal .Adj .tall, .terminal .N .man]

/-- "A man" — obtained by deleting the Adj modifier (ex. 29b). -/
def justMan : Tree Cat ExWord :=
  .node .NP [.terminal .N .man]

/-- Deletion produces a simpler alternative: "a man" ∈ A_str("a tall man").

Under the structural approach, any modifier can be deleted to produce
an alternative. Since the modified NP entails the bare NP ("a tall man
came" → "a man came"), the bare NP is a stronger alternative in
upward-entailing contexts, triggering no implicature. In DE contexts,
entailment reverses and deletion alternatives generate inferences
(§4.3, exx. 30–32). -/
theorem deletion_produces_alternative :
    justMan ∈ structuralAlternatives exLexicon tallMan := by
  unfold structuralAlternatives atMostAsComplex
  apply Relation.ReflTransGen.single
  exact StructOp.delete ⟨0, by simp⟩

/-- Deletion reduces tree size. -/
theorem deletion_reduces_size :
    justMan.size < tallMan.size := by native_decide

end Deletion

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Bridge: Horn Scales ⊆ Structural Alternatives
-- ═══════════════════════════════════════════════════════════════════════

/-- Lift a ReflTransGen chain at position i through inChild. -/
private theorem lift_at_position {C W : Type} {source : List (Tree C W)}
    {cat : C} (cs : List (Tree C W))
    (i : Nat) (hi : i < cs.length) (ψ : Tree C W)
    (h : Relation.ReflTransGen (StructOp source) cs[i] ψ) :
    Relation.ReflTransGen (StructOp source)
      (.node cat cs) (.node cat (cs.set i ψ)) := by
  induction h with
  | refl => rw [List.set_getElem_self hi]
  | @tail b d _ hbd ih =>
    apply ih.trans
    apply Relation.ReflTransGen.single
    have hlen : i < (cs.set i b).length := by rw [List.length_set]; exact hi
    rw [show cs.set i d = (cs.set i b).set i d from (List.set_set ..).symm]
    apply StructOp.inChild ⟨i, hlen⟩
    have hget : (cs.set i b).get ⟨i, hlen⟩ = b := List.getElem_set_self ..
    rw [hget]; exact hbd

/-- Lift a ReflTransGen chain through a bind constructor. -/
private theorem lift_bind {C W : Type} {source : List (Tree C W)}
    {n : Nat} {cat : C} {body body' : Tree C W}
    (h : Relation.ReflTransGen (StructOp source) body body') :
    Relation.ReflTransGen (StructOp source) (.bind n cat body) (.bind n cat body') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h_last ih => exact ih.trans (Relation.ReflTransGen.single (StructOp.inBind h_last))

/-- leafSubstList is just List.map. -/
private theorem leafSubstList_eq_map {C W : Type} [BEq C] [BEq W]
    (α β : W) (c : C) (cs : List (Tree C W)) :
    Tree.leafSubst.leafSubstList α β c cs =
    cs.map (·.leafSubst α β c) := by
  induction cs with
  | nil => rfl
  | cons t ts ih =>
    simp only [Tree.leafSubst.leafSubstList, List.map_cons]
    exact congrArg _ ih

/-- Process children one at a time: .node cat cs →* .node cat (cs.map f). -/
private theorem mapChildren_reachable {C W : Type} {source : List (Tree C W)}
    {cat : C} {cs : List (Tree C W)} {f : Tree C W → Tree C W}
    (hf : ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructOp source) cs[i] (f cs[i])) :
    Relation.ReflTransGen (StructOp source)
      (.node cat cs) (.node cat (cs.map f)) := by
  suffices h : ∀ k (hk : k ≤ cs.length),
    Relation.ReflTransGen (StructOp source)
      (.node cat cs)
      (.node cat (List.take k (cs.map f) ++ List.drop k cs)) by
    have h' := h cs.length le_rfl
    rw [List.take_of_length_le (by simp), List.drop_length, List.append_nil] at h'
    exact h'
  intro k
  induction k with
  | zero => intro _; simp; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro hk
    have hk' : k < cs.length := by omega
    apply Relation.ReflTransGen.trans (ih (by omega))
    have hmid_len : (List.take k (cs.map f) ++ List.drop k cs).length = cs.length := by
      simp [List.length_take, List.length_drop, List.length_map]; omega
    have htk_len : (List.take k (cs.map f)).length = k := by
      simp [List.length_take, List.length_map]; omega
    have hmid_k : (List.take k (cs.map f) ++ List.drop k cs)[k]'(by omega) = cs[k] := by
      rw [List.getElem_append_right (by omega)]
      simp [htk_len, List.getElem_drop]
    suffices heq : List.take (k + 1) (cs.map f) ++ List.drop (k + 1) cs =
        (List.take k (cs.map f) ++ List.drop k cs).set k (f cs[k]) by
      rw [heq]
      apply lift_at_position _ k (by omega) (f cs[k])
      rw [hmid_k]; exact hf k hk'
    have htk1_len : (List.take (k + 1) (cs.map f)).length = k + 1 := by
      simp [List.length_take, List.length_map]; omega
    apply List.ext_getElem
    · simp [List.length_set, List.length_take, List.length_drop, List.length_map]; omega
    · intro i hi1 hi2
      by_cases hik : i = k
      · subst hik
        rw [List.getElem_set_self, List.getElem_append_left (by omega)]
        simp [List.getElem_take, List.getElem_map]
      · rw [List.getElem_set_ne (Ne.symm hik)]
        by_cases hilt : i < k
        · rw [List.getElem_append_left (by omega),
              List.getElem_append_left (by omega)]
          simp [List.getElem_take, List.getElem_map]
        · rw [List.getElem_append_right (by omega),
              List.getElem_append_right (by omega)]
          simp [htk1_len, htk_len, List.getElem_drop]
          congr 1; omega

set_option maxHeartbeats 400000 in
/-- Leaf substitution is reachable via structural operations for any
source containing `.terminal c β`. -/
private theorem leafSubst_reachable {C W : Type} [BEq C] [LawfulBEq C] [BEq W]
    {source : List (Tree C W)} (α β : W) (c : C)
    (h_β : Tree.terminal c β ∈ source)
    (φ : Tree C W) :
    Relation.ReflTransGen (StructOp source) φ (φ.leafSubst α β c) := by
  refine Tree.rec
    (motive_1 := fun φ => Relation.ReflTransGen (StructOp source) φ (φ.leafSubst α β c))
    (motive_2 := fun cs => ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructOp source) cs[i] ((cs[i]).leafSubst α β c))
    ?_ ?_ ?_ ?_ ?_ ?_ φ
  · -- terminal case
    intro c' w
    simp only [Tree.leafSubst]
    split
    · rename_i h
      rw [Bool.and_eq_true] at h
      have hc : c = c' := eq_of_beq h.1
      subst hc
      exact Relation.ReflTransGen.single (StructOp.subst rfl h_β)
    · exact Relation.ReflTransGen.refl
  · -- node case
    intro c' cs ih_cs
    show Relation.ReflTransGen (StructOp source) (.node c' cs)
      (.node c' (Tree.leafSubst.leafSubstList α β c cs))
    rw [leafSubstList_eq_map]
    exact mapChildren_reachable ih_cs
  · -- trace case
    intro n c'
    exact Relation.ReflTransGen.refl
  · -- bind case
    intro n c' body ih_body
    exact lift_bind ih_body
  · -- nil case
    intro i hi; exact absurd hi (by simp)
  · -- cons case
    intro head tail ih_head ih_tail i hi
    match i, hi with
    | 0, _ => exact ih_head
    | i+1, hi => exact ih_tail i (by simp [List.length_cons] at hi; omega)

/-- Horn scale alternatives are a special case of structural alternatives.

If two words α and β are on the same Horn scale (and therefore have the
same syntactic category), then for any sentence tree φ containing α,
the tree φ[β/α] obtained by leaf substitution is a structural alternative
to φ. This is because:
1. β is in the lexicon (hence in L(φ))
2. β has the same category as α
3. Leaf substitution is a sequence of `StructOp.subst` steps (one per
   occurrence of α)

This means the scale-based approach to alternatives (listing Horn sets
like ⟨some, most, all⟩) is not wrong — it is subsumed by the structural
approach. Everything a Horn scale generates, structural operations
generate too. But structural operations also generate alternatives that
scales miss: deletion alternatives in DE contexts (§4.3), and
sub-constituent alternatives for disjunction (§4.2). -/
theorem horn_alternatives_are_structural {C W : Type} [BEq C] [LawfulBEq C] [BEq W]
    (lex : List (Tree C W)) (φ : Tree C W)
    (α β : W) (c : C)
    (_h_α_in_lex : Tree.terminal c α ∈ lex)
    (_h_β_in_lex : Tree.terminal c β ∈ lex) :
    φ.leafSubst α β c ∈ structuralAlternatives lex φ := by
  unfold structuralAlternatives atMostAsComplex
  exact leafSubst_reachable α β c (List.mem_append_left _ _h_β_in_lex) φ

-- ═══════════════════════════════════════════════════════════════════════
-- §9  Maximize Content Principle (generalized)
-- ═══════════════════════════════════════════════════════════════════════

/-- Generic "maximize content" principle parameterized over content dimension.

Scalar inferences arise from comparing a sentence φ with formal alternatives
φ' that are more informative along some content dimension. The same reasoning
applies to three dimensions:

- **At-issue content** → Scalar Implicatures (Conversational Principle, @cite{katzir-2007})
- **Presuppositional content** → Antipresuppositions (Maximize Presupposition, @cite{schlenker-2012})
- **CI content** → Anti-Conventional Implicatures (MCIs!, @cite{lo-guercio-2025})

All three are instances of: do not use φ if there is a formal alternative
φ' ∈ F(φ) such that (a) φ' is strictly more informative along the relevant
content dimension, (b) φ' is contextually relevant, and (c) ¬φ' is innocently
excludable.

`contentFn` maps each tree to its content along the relevant dimension.

The competitor set is supplied as an `AlternativeSource` parameter so
that the same operator works for Katzir alternatives
(`katzirSource lex`), indirect alternatives
(`Indirect.indirectFromKatzir`, @cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025}),
or any other source. -/
def violatesMaximize {C W World : Type}
    (src : Alternatives.AlternativeSource (Tree C W))
    (contentFn : Tree C W → World → Bool)
    (φ : Tree C W)
    (weaklyAssertable : Tree C W → Bool) : Prop :=
  ∃ φ' ∈ src φ,
    (∀ w, contentFn φ' w = true → contentFn φ w = true) ∧
    (∃ w, contentFn φ w = true ∧ contentFn φ' w = false) ∧
    weaklyAssertable φ' = true

/-- The neo-Gricean conversational principle: `violatesMaximize` applied
to at-issue (truth-conditional) content. @cite{katzir-2007} def 21. -/
abbrev violatesConversationalPrinciple {C W World : Type}
    (src : Alternatives.AlternativeSource (Tree C W))
    (meaning : Tree C W → World → Bool)
    (φ : Tree C W)
    (weaklyAssertable : Tree C W → Bool) : Prop :=
  violatesMaximize src meaning φ weaklyAssertable

/-- Maximize Presupposition (@cite{schlenker-2012}): `violatesMaximize`
applied to presuppositional content. Do not use φ if there is a
competitor φ' (from `src`) with the same assertive content but stronger
presupposition.

Pass `katzirSource lex` for Katzir alternatives;
`Indirect.indirectFromKatzir lex pron` for indirect alternatives
(@cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025}). -/
def violatesMP {C W World : Type}
    (src : Alternatives.AlternativeSource (Tree C W))
    (presupFn : Tree C W → World → Bool)
    (assertionFn : Tree C W → World → Bool)
    (φ : Tree C W)
    (weaklyAssertable : Tree C W → Bool) : Prop :=
  ∃ φ' ∈ src φ,
    (∀ w, assertionFn φ' w = assertionFn φ w) ∧
    (∀ w, presupFn φ' w = true → presupFn φ w = true) ∧
    (∃ w, presupFn φ w = true ∧ presupFn φ' w = false) ∧
    weaklyAssertable φ' = true

/-- Maximize Conventional Implicatures (@cite{lo-guercio-2025} def 15):
`violatesMaximize` applied to CI content. Unlike MP!, does NOT require
the same assertive content — CI content is independent of truth conditions.

Do not use φ if there is a formal alternative φ' ∈ F(φ) such that:
a. ⟦φ'⟧ᵘ ⊂ ⟦φ⟧ᵘ (CI-stronger)
b. φ' ∈ C (contextually relevant)
c. ¬⟦φ'⟧ᵘ doesn't contradict the negation of CI content of any element in C -/
abbrev violatesMCIs {C W World : Type}
    (src : Alternatives.AlternativeSource (Tree C W))
    (ciContentFn : Tree C W → World → Bool)
    (φ : Tree C W)
    (weaklyAssertable : Tree C W → Bool) : Prop :=
  violatesMaximize src ciContentFn φ weaklyAssertable

-- ═══════════════════════════════════════════════════════════════════════
-- §10  Bridge to Economy of Structure (@cite{katzir-singh-2015})
-- ═══════════════════════════════════════════════════════════════════════

/-- At-least-as-good-as relation (def 23, p. 680):
φ ≲ ψ iff φ ≲_struct ψ ∧ ⟦φ⟧ ⊆ ⟦ψ⟧.

This combines structural complexity (from def 19) with semantic
entailment. It is the relation that @cite{katzir-singh-2015} use as
the basis for the Answer Condition in `KatzirSingh2015.lean`, where
it appears as `Scenario.atLeastAsGood`.

The key insight: in `KatzirSingh2015.lean`, complexity is an abstract
`ℕ` parameter. Here, structural complexity gives that parameter its
intended content — the number of structural operations needed. -/
def atLeastAsGoodAs {C W World : Type}
    (lex : List (Tree C W))
    (meaning : Tree C W → World → Bool)
    (φ ψ : Tree C W) : Prop :=
  atMostAsComplex (substitutionSource lex ψ) φ ψ ∧
  ∀ w, meaning φ w = true → meaning ψ w = true

end Alternatives.Structural
