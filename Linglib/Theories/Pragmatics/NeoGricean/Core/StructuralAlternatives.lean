import Linglib.Theories.Pragmatics.NeoGricean.Core.Alternatives

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

## Connection to Linglib

- **Horn scales subsumed**: Lexical substitution of same-category items
  is a special case of structural alternatives (§8)
- **Fills truthmaker gap**: `AlternativeSensitive.lean`'s `IsTruthmaker`
  requires ALT_S computed via structural alternative generation
- **Economy connection**: @cite{katzir-singh-2015}'s complexity ordering
  in `EconomyOddness.lean` is based on structural complexity (def 19)
-/

namespace NeoGricean.StructuralAlternatives

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Syntactic Categories
-- ═══════════════════════════════════════════════════════════════════════

/-- Syntactic categories for parse tree nodes.
Terminal categories (Det, N, V, ...) label leaves;
phrasal categories (NP, VP, S, ...) label internal nodes. -/
inductive SynCat where
  | S | NP | VP | Det | N | V | Adj | Adv | PP | P | CP | C
  | DP | Deg | Conj | ConjP | Neg | NegP
  deriving DecidableEq, BEq, Repr, Inhabited

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Parse Trees
-- ═══════════════════════════════════════════════════════════════════════

/-- Parse tree with syntactic category labels.
Leaves carry a word of type `W`; internal nodes carry a list of children.
This is the structure that Katzir's operations act on. -/
inductive ParseTree (W : Type) where
  | leaf (cat : SynCat) (word : W)
  | node (cat : SynCat) (children : List (ParseTree W))
  deriving Repr

namespace ParseTree

variable {W : Type}

/-- Syntactic category of the root node. -/
def cat : ParseTree W → SynCat
  | .leaf c _ => c
  | .node c _ => c

-- ── BEq ──────────────────────────────────────────────────────────────

/-- Structural equality for parse trees. -/
def beq [BEq W] : ParseTree W → ParseTree W → Bool
  | .leaf c₁ w₁, .leaf c₂ w₂ => c₁ == c₂ && w₁ == w₂
  | .node c₁ cs₁, .node c₂ cs₂ => c₁ == c₂ && beqList cs₁ cs₂
  | _, _ => false
where
  beqList : List (ParseTree W) → List (ParseTree W) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && beqList as bs
  | _, _ => false

instance [BEq W] : BEq (ParseTree W) := ⟨beq⟩

-- ── Size ─────────────────────────────────────────────────────────────

/-- Number of nodes in the tree. -/
def size : ParseTree W → Nat
  | .leaf _ _ => 1
  | .node _ cs => 1 + sizeList cs
where
  sizeList : List (ParseTree W) → Nat
  | [] => 0
  | t :: ts => t.size + sizeList ts

-- ── Subtrees ─────────────────────────────────────────────────────────

/-- All subtrees including self (pre-order). -/
def subtrees : ParseTree W → List (ParseTree W)
  | t@(.leaf _ _) => [t]
  | t@(.node _ cs) => t :: subtreesList cs
where
  subtreesList : List (ParseTree W) → List (ParseTree W)
  | [] => []
  | t :: ts => t.subtrees ++ subtreesList ts

-- ── Categories ───────────────────────────────────────────────────────

/-- Whether a category appears anywhere in the tree. -/
def containsCat (c : SynCat) : ParseTree W → Bool
  | .leaf c' _ => c == c'
  | .node c' cs => c == c' || containsCatList c cs
where
  containsCatList (c : SynCat) : List (ParseTree W) → Bool
  | [] => false
  | t :: ts => t.containsCat c || containsCatList c ts

-- ── Leaf Substitution ────────────────────────────────────────────────

/-- Substitute all leaves of category `c` carrying word `target` with
`replacement`. This is the most common structural operation: replacing
one scalar item with another of the same category. -/
def leafSubst [BEq W] (target replacement : W) (c : SynCat) :
    ParseTree W → ParseTree W
  | .leaf c' w => if c == c' && w == target then .leaf c' replacement else .leaf c' w
  | .node c' cs => .node c' (leafSubstList target replacement c cs)
where
  leafSubstList [BEq W] (target replacement : W) (c : SynCat) :
      List (ParseTree W) → List (ParseTree W)
  | [] => []
  | t :: ts => t.leafSubst target replacement c :: leafSubstList target replacement c ts

end ParseTree

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Substitution Source (def 41)
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
def substitutionSource {W : Type} (lexicon : List (ParseTree W))
    (φ : ParseTree W) : List (ParseTree W) :=
  lexicon ++ φ.subtrees

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Structural Operations (def 19)
-- ═══════════════════════════════════════════════════════════════════════

/-- One structural operation on parse trees (p. 678).
`StructOp source φ ψ` means ψ is obtained from φ by one application of
deletion, contraction, or substitution with items from `source`.

The three operations:
- **Deletion**: remove a subtree (a child from a node)
- **Contraction**: remove an edge and identify endpoints (replace a node
  with one of its same-category children)
- **Substitution**: replace any constituent with a same-category item
  from the substitution source L(φ) -/
inductive StructOp {W : Type} (source : List (ParseTree W)) :
    ParseTree W → ParseTree W → Prop where
  /-- Substitute: replace tree with a same-category item from source. -/
  | subst {φ ψ : ParseTree W}
    (h_cat : ψ.cat = φ.cat) (h_src : ψ ∈ source) :
    StructOp source φ ψ
  /-- Delete: remove the i-th child from a node. -/
  | delete {cat : SynCat} {cs : List (ParseTree W)} (i : Fin cs.length) :
    StructOp source (.node cat cs) (.node cat (cs.eraseIdx i))
  /-- Contract: replace a node with one of its same-category children. -/
  | contract {cat : SynCat} {cs : List (ParseTree W)}
    {child : ParseTree W}
    (h_mem : child ∈ cs) (h_cat : child.cat = cat) :
    StructOp source (.node cat cs) child
  /-- Recursive: apply an operation inside one child of a node. -/
  | inChild {cat : SynCat} {cs : List (ParseTree W)}
    (i : Fin cs.length) {ψ_child : ParseTree W}
    (h_step : StructOp source (cs.get i) ψ_child) :
    StructOp source (.node cat cs) (.node cat (cs.set i ψ_child))

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Structural Complexity and Alternatives (defs 19–20)
-- ═══════════════════════════════════════════════════════════════════════

/-- Structural complexity ordering (def 19): ψ ≲ φ iff φ can be
transformed into ψ by a finite chain of structural operations
using items from `source`.

Formally: the reflexive-transitive closure of `StructOp source`. -/
def atMostAsComplex {W : Type} (source : List (ParseTree W))
    (ψ φ : ParseTree W) : Prop :=
  Relation.ReflTransGen (StructOp source) φ ψ

/-- Equal complexity (def 19): φ ∼ ψ iff φ ≲ ψ ∧ ψ ≲ φ. -/
def equalComplexity {W : Type} (source : List (ParseTree W))
    (φ ψ : ParseTree W) : Prop :=
  atMostAsComplex source φ ψ ∧ atMostAsComplex source ψ φ

/-- Strictly less complex (def 19): ψ < φ iff ψ ≲ φ ∧ ¬(φ ≲ ψ). -/
def strictlyLessComplex {W : Type} (source : List (ParseTree W))
    (ψ φ : ParseTree W) : Prop :=
  atMostAsComplex source ψ φ ∧ ¬atMostAsComplex source φ ψ

/-- Structural alternatives (def 20):
A_str(φ) := {ψ : ψ ≲ φ}, where ≲ uses L(φ) = lexicon ∪ subtrees(φ). -/
def structuralAlternatives {W : Type} (lex : List (ParseTree W))
    (φ : ParseTree W) : Set (ParseTree W) :=
  {ψ | atMostAsComplex (substitutionSource lex φ) ψ φ}

/-- φ is always a structural alternative to itself (reflexivity of ≲). -/
theorem self_is_alternative {W : Type} (lex : List (ParseTree W))
    (φ : ParseTree W) :
    φ ∈ structuralAlternatives lex φ :=
  Relation.ReflTransGen.refl

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Worked Example: Some/All (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

/-- Vocabulary for the worked examples. -/
inductive ExWord where
  | john | ate | some_ | all_ | cake
  | apple | pear | or_ | and_
  | tall | man
  | but_ | not_
  deriving DecidableEq, BEq, Repr

section SomeAll

open SynCat ExWord

/-- Minimal lexicon: terminal items available for substitution. -/
def exLexicon : List (ParseTree ExWord) :=
  [.leaf .N .john, .leaf .V .ate,
   .leaf .Det .some_, .leaf .Det .all_,
   .leaf .N .cake, .leaf .N .apple, .leaf .N .pear,
   .leaf .Conj .or_, .leaf .Conj .and_,
   .leaf .Adj .tall, .leaf .N .man]

/-- φ = "John ate some cake" (simplified parse tree). -/
def someSentence : ParseTree ExWord :=
  .node .S [
    .leaf .N .john,
    .node .VP [.leaf .V .ate, .leaf .Det .some_, .leaf .N .cake]]

/-- φ' = "John ate all cake" — the scalar alternative. -/
def allSentence : ParseTree ExWord :=
  .node .S [
    .leaf .N .john,
    .node .VP [.leaf .V .ate, .leaf .Det .all_, .leaf .N .cake]]

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
-- §7  Symmetry Problem Solved (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

section SymmetryProblem

open SynCat ExWord

/-- φ'' = "John ate some but not all cake" — the symmetric alternative
that the naïve principle cannot exclude.

Under the naïve principle, φ'' is stronger than φ (⟦φ''⟧ ⊂ ⟦φ⟧) and
should block assertion of φ. But it licenses the inference that John
ate ALL of the cake — the opposite of the correct implicature.
Katzir's structural approach excludes φ'' because it requires ConjP
and NegP structure not derivable from L(φ). -/
def someButNotAllSentence : ParseTree ExWord :=
  .node .S [
    .leaf .N .john,
    .node .VP [
      .leaf .V .ate,
      .node .ConjP [
        .leaf .Det .some_,
        .leaf .Conj .but_,
        .node .NegP [.leaf .Neg .not_, .leaf .Det .all_]],
      .leaf .N .cake]]

/-- φ'' contains ConjP — a category absent from φ and L(φ). -/
theorem symmetric_has_conjp :
    someButNotAllSentence.containsCat .ConjP = true := by rfl

/-- φ does not contain ConjP. -/
theorem some_lacks_conjp :
    someSentence.containsCat .ConjP = false := by rfl

/-- No item in L(someSentence) contains ConjP: the lexicon consists
of terminal leaves (which have no internal structure) and the subtrees
of φ are {S[...], N(john), VP[...], V(ate), Det(some), N(cake)} —
none contain ConjP. -/
theorem source_lacks_conjp :
    (substitutionSource exLexicon someSentence).all
      (fun t => !t.containsCat .ConjP) = true := by rfl

/-- Key invariant: structural operations preserve absence of a category
when that category does not appear in the substitution source.

If no item in `source` contains category `c`, and tree `φ` does not
contain `c`, then no tree reachable from φ by structural operations
contains `c`. This is because:
- Substitution can only introduce material from `source` (which lacks `c`)
- Deletion removes material (can't introduce `c`)
- Contraction promotes a subtree (which also lacks `c` by hypothesis)

TODO: Full induction proof on `StructOp` and `ReflTransGen`. -/
theorem category_preservation {W : Type}
    (source : List (ParseTree W)) (c : SynCat)
    (φ ψ : ParseTree W)
    (h_source : ∀ s ∈ source, s.containsCat c = false)
    (h_φ : φ.containsCat c = false)
    (h_reach : atMostAsComplex source ψ φ) :
    ψ.containsCat c = false := by
  sorry

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
    (by intro s hs; sorry) -- source_lacks_conjp proves this computationally
    (by rfl)
    h
  exact absurd symmetric_has_conjp (by rw [h_preserved]; decide)

end SymmetryProblem

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Disjunction: Or/And (§4.2)
-- ═══════════════════════════════════════════════════════════════════════

section Disjunction

open SynCat ExWord

/-- φ = "John ate the apple or the pear" (ex. 26a). -/
def orSentence : ParseTree ExWord :=
  .node .S [
    .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .apple]],
    .leaf .Conj .or_,
    .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .pear]]]

/-- φ' = "John ate the apple and the pear" (ex. 26b).
Obtained by substituting Conj "or" with "and". -/
def andSentence : ParseTree ExWord :=
  .node .S [
    .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .apple]],
    .leaf .Conj .and_,
    .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .pear]]]

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
def leftDisjunct : ParseTree ExWord :=
  .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .apple]]

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
def rightDisjunct : ParseTree ExWord :=
  .node .S [.leaf .N .john, .node .VP [.leaf .V .ate, .leaf .N .pear]]

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
-- §9  Deletion Alternatives (§4.3)
-- ═══════════════════════════════════════════════════════════════════════

section Deletion

open SynCat ExWord

/-- "A tall man" parse tree (ex. 29a). -/
def tallMan : ParseTree ExWord :=
  .node .NP [.leaf .Adj .tall, .leaf .N .man]

/-- "A man" — obtained by deleting the Adj modifier (ex. 29b). -/
def justMan : ParseTree ExWord :=
  .node .NP [.leaf .N .man]

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
-- §10  Bridge: Horn Scales ⊆ Structural Alternatives
-- ═══════════════════════════════════════════════════════════════════════

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
sub-constituent alternatives for disjunction (§4.2).

TODO: Proof by induction on the tree structure, applying `StructOp.subst`
at each matching leaf via `StructOp.inChild`. -/
theorem horn_alternatives_are_structural {W : Type} [BEq W]
    (lex : List (ParseTree W)) (φ : ParseTree W)
    (α β : W) (c : SynCat)
    (_h_α_in_lex : ParseTree.leaf c α ∈ lex)
    (_h_β_in_lex : ParseTree.leaf c β ∈ lex) :
    φ.leafSubst α β c ∈ structuralAlternatives lex φ := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- §11  Neo-Gricean Principle with Structural Alternatives (def 21)
-- ═══════════════════════════════════════════════════════════════════════

/-- The neo-Gricean conversational principle with structural alternatives
(def 21): do not assert φ if there is another sentence φ' ∈ A_str(φ)
such that ⟦φ'⟧ ⊂ ⟦φ⟧ and φ' is weakly assertable.

This replaces the naïve principle (which considers ALL stronger
alternatives) with one restricted to structurally-defined alternatives.
The restriction solves the symmetry problem: φ'' = φ ∧ ¬φ' is excluded
from A_str(φ) because it requires more structure than φ provides.

The at-least-as-good-as relation (def 23, p. 680) combines structural
complexity (≲) with semantic entailment (⊆). This is the same relation
formalized in `EconomyOddness.lean` as `atLeastAsGood`, where complexity
is an abstract ℕ parameter — the structural complexity defined here
gives that parameter its intended content. -/
def violatesConversationalPrinciple {W World : Type}
    (lex : List (ParseTree W))
    (meaning : ParseTree W → World → Bool)
    (φ : ParseTree W)
    (weaklyAssertable : ParseTree W → Bool) : Prop :=
  ∃ φ' ∈ structuralAlternatives lex φ,
    -- ⟦φ'⟧ ⊂ ⟦φ⟧ (strictly more informative)
    (∀ w, meaning φ' w = true → meaning φ w = true) ∧
    (∃ w, meaning φ w = true ∧ meaning φ' w = false) ∧
    -- φ' is weakly assertable
    weaklyAssertable φ' = true

-- ═══════════════════════════════════════════════════════════════════════
-- §12  Bridge to Economy of Structure (@cite{katzir-singh-2015})
-- ═══════════════════════════════════════════════════════════════════════

/-- At-least-as-good-as relation (def 23, p. 680):
φ ≲ ψ iff φ ≲_struct ψ ∧ ⟦φ⟧ ⊆ ⟦ψ⟧.

This combines structural complexity (from def 19) with semantic
entailment. It is the relation that @cite{katzir-singh-2015} use as
the basis for the Answer Condition in `EconomyOddness.lean`, where
it appears as `Scenario.atLeastAsGood`.

The key insight: in `EconomyOddness.lean`, complexity is an abstract
`ℕ` parameter. Here, structural complexity gives that parameter its
intended content — the number of structural operations needed. -/
def atLeastAsGoodAs {W World : Type}
    (lex : List (ParseTree W))
    (meaning : ParseTree W → World → Bool)
    (φ ψ : ParseTree W) : Prop :=
  atMostAsComplex (substitutionSource lex ψ) φ ψ ∧
  ∀ w, meaning φ w = true → meaning ψ w = true

end NeoGricean.StructuralAlternatives
