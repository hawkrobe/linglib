import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Alternatives.Source

/-!
# Structurally-defined alternatives

The alternatives of a parse tree in [katzir-2007]: the trees obtainable from it by deletion,
contraction, and substitution of a constituent by a same-category item of the substitution
source, the lexicon together with the tree's own subtrees. `StructOp` is one such operation,
`atMostAsComplex` its reflexive-transitive closure, the complexity preorder of the paper's
definition (19), `equalComplexity` its equivalence kernel, and `structuralAlternatives` the set
of trees at most as complex as the given one, definition (20); `katzirSource` packages it as an
`Alternatives.Source` for the competition principles of `Alternatives.Competition`.

Two general facts serve the paper's examples, which live in `Studies/Katzir2007.lean`. No
operation introduces a category absent from the tree and the source
(`category_preservation`), which is what excludes the symmetric alternatives; and substituting
one lexical item for another of the same category throughout a tree, a Horn-scale alternative,
is a chain of substitutions (`horn_alternatives_are_structural`), so scalar alternatives are a
special case.

## Implementation notes

`atMostAsComplex` is reachability, not an operation count, so `equalComplexity`, mutual
reachability, is coarser than the paper's equal complexity, and `strictlyLessComplex` is
reachability-strict. The `inBind` constructor extends the operations into the body of a
binder, which the paper's trees lack.

## References

* [katzir-2007]
* [fox-katzir-2011]
-/

namespace Alternatives.Structural

open Syntax
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

Formally: the reflexive-transitive closure of `StructOp source`. This is
the *reachability preorder* underlying [katzir-2007]'s ≲, which suffices
for `A_str` as a set (def 20) and for the worked examples. It is *not* a
graded operation-count: two mutually-reachable trees need not take the
same number of steps, so `equalComplexity` (mutual reachability) is
coarser than Katzir's "equal complexity" ∼, and the strict orderings the
paper uses in §4.2–§4.3 are reachability-strict, not count-strict. -/
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

/-- The Katzir source as an `Alternatives.Source`. Pragmatic competition
operators (`violatesMP`, `violatesMaximize`, `violatesMCIs` in
`Alternatives.Competition`) accept any `Source (Tree C W)`; pass
`katzirSource lex` to recover the classical Katzir 2007 competition.
Other sources include `Alternatives.indirectFrom` (Jeretič et al. 2025). -/
def katzirSource {C W : Type} (lex : List (Tree C W)) :
    Alternatives.Source (Tree C W) :=
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

/-- `equalComplexity source` is an equivalence relation — the equivalence
kernel of the `atMostAsComplex source` preorder. Bundled so consumers can
take a `Setoid`/quotient or feed mathlib's `Equivalence` API. -/
theorem equivalence : Equivalence (equalComplexity source) :=
  ⟨refl, symm, trans⟩

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

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Category preservation
-- ═══════════════════════════════════════════════════════════════════════

private theorem structOp_preserves_no_cat {C W : Type} [DecidableEq C]
    (source : List (Tree C W)) (c : C)
    (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, ¬ ContainsCat c s)
    (h_φ : ¬ ContainsCat c φ)
    (h_step : StructOp source φ ψ) :
    ¬ ContainsCat c ψ := by
  induction h_step with
  | subst _ h_src => exact h_source _ h_src
  | @delete cat cs i =>
    rw [Tree.containsCat_node_iff] at h_φ ⊢; push Not at h_φ ⊢
    exact ⟨h_φ.1, λ t ht => h_φ.2 t ((List.eraseIdx_sublist cs i).subset ht)⟩
  | @contract cat cs child h_mem _ =>
    rw [Tree.containsCat_node_iff] at h_φ; push Not at h_φ; exact h_φ.2 child h_mem
  | @inChild cat cs i ψ_child _ ih =>
    rw [Tree.containsCat_node_iff] at h_φ ⊢; push Not at h_φ ⊢
    have hih := ih (h_φ.2 (cs.get i) (List.get_mem cs i))
    refine ⟨h_φ.1, λ t ht => ?_⟩
    rcases List.mem_or_eq_of_mem_set ht with ht' | rfl
    · exact h_φ.2 t ht'
    · exact hih
  | @inBind n cat body body' _ ih =>
    rw [Tree.containsCat_bind_iff] at h_φ ⊢; push Not at h_φ ⊢
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
theorem category_preservation {C W : Type} [DecidableEq C]
    (source : List (Tree C W)) (c : C)
    (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, ¬ ContainsCat c s)
    (h_φ : ¬ ContainsCat c φ)
    (h_reach : atMostAsComplex source ψ φ) :
    ¬ ContainsCat c ψ := by
  unfold atMostAsComplex at h_reach
  induction h_reach with
  | refl => exact h_φ
  | tail _ h_last ih =>
    exact structOp_preserves_no_cat source c _ _ h_source ih h_last

/-- One structural operation cannot introduce a subtree property that no source item has,
that the tree lacks, and that a node cannot acquire by losing a child, by having a child
replaced, or by a change of a binder's body. -/
private theorem structOp_preserves_free {C W : Type} (source : List (Tree C W))
    (Bad : Tree C W → Prop) (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ Bad t)
    (h_delete : ∀ (cat : C) (cs : List (Tree C W)) (i : Fin cs.length),
      ¬ Bad (.node cat cs) → ¬ Bad (.node cat (cs.eraseIdx i)))
    (h_set : ∀ (cat : C) (cs : List (Tree C W)) (i : Fin cs.length) (ψ : Tree C W),
      ¬ Bad (.node cat cs) → ¬ Bad (.node cat (cs.set i ψ)))
    (h_bind : ∀ (n : ℕ) (cat : C) (body body' : Tree C W),
      ¬ Bad (.bind n cat body) → ¬ Bad (.bind n cat body'))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ Bad t) (h_step : StructOp source φ ψ) :
    ∀ t ∈ ψ.subtrees, ¬ Bad t := by
  induction h_step with
  | subst _ h_src => exact h_source _ h_src
  | @delete cat cs i =>
    rw [Tree.subtrees_node] at h_φ ⊢
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_delete cat cs i (h_φ _ (List.mem_cons_self ..))
    · obtain ⟨c, hc, htc⟩ := List.mem_flatMap.mp ht
      exact h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨c, (List.eraseIdx_sublist cs i).subset hc, htc⟩))
  | @contract cat cs child h_mem _ =>
    rw [Tree.subtrees_node] at h_φ
    exact λ t ht => h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, h_mem, ht⟩))
  | @inChild cat cs i ψ_child _ ih =>
    rw [Tree.subtrees_node] at h_φ ⊢
    have hih := ih λ t ht =>
      h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨cs.get i, List.get_mem cs i, ht⟩))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_set cat cs i ψ_child (h_φ _ (List.mem_cons_self ..))
    · obtain ⟨c, hc, htc⟩ := List.mem_flatMap.mp ht
      rcases List.mem_or_eq_of_mem_set hc with hc | rfl
      · exact h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, htc⟩))
      · exact hih t htc
  | @inBind n cat body body' _ ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_bind n cat body body' (h_φ _ (List.mem_cons_self ..))
    · exact ih (λ t ht => h_φ t (List.mem_cons_of_mem _ ht)) t ht

/-- A subtree property that no source item has, that the host lacks, and that a node cannot
acquire by losing a child, by having a child replaced, or by a change of a binder's body,
is absent from every structural alternative of the host. -/
theorem subtree_preservation {C W : Type} (source : List (Tree C W)) (Bad : Tree C W → Prop)
    (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ Bad t)
    (h_delete : ∀ (cat : C) (cs : List (Tree C W)) (i : Fin cs.length),
      ¬ Bad (.node cat cs) → ¬ Bad (.node cat (cs.eraseIdx i)))
    (h_set : ∀ (cat : C) (cs : List (Tree C W)) (i : Fin cs.length) (ψ : Tree C W),
      ¬ Bad (.node cat cs) → ¬ Bad (.node cat (cs.set i ψ)))
    (h_bind : ∀ (n : ℕ) (cat : C) (body body' : Tree C W),
      ¬ Bad (.bind n cat body) → ¬ Bad (.bind n cat body'))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ Bad t) (h_reach : atMostAsComplex source ψ φ) :
    ∀ t ∈ ψ.subtrees, ¬ Bad t := by
  unfold atMostAsComplex at h_reach
  induction h_reach with
  | refl => exact h_φ
  | tail _ h_last ih =>
    exact structOp_preserves_free source Bad h_source h_delete h_set h_bind ih h_last

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Horn scales are structural alternatives
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

/-- Lift a ReflTransGen chain through a bind constructor: a special case of
`Relation.ReflTransGen.lift` with the homomorphism `StructOp.inBind`. -/
private theorem lift_bind {C W : Type} {source : List (Tree C W)}
    {n : Nat} {cat : C} {body body' : Tree C W}
    (h : Relation.ReflTransGen (StructOp source) body body') :
    Relation.ReflTransGen (StructOp source) (.bind n cat body) (.bind n cat body') :=
  Relation.ReflTransGen.lift (λ t => Tree.bind n cat t)
    (λ _ _ h => StructOp.inBind h) body body' h

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

/-- Leaf substitution is reachable via structural operations for any
source containing `.terminal c β`. -/
private theorem leafSubst_reachable {C W : Type} [BEq C] [LawfulBEq C] [BEq W]
    {source : List (Tree C W)} (α β : W) (c : C)
    (h_β : Tree.terminal c β ∈ source)
    (φ : Tree C W) :
    Relation.ReflTransGen (StructOp source) φ (φ.leafSubst α β c) := by
  refine Tree.rec
    (motive_1 := λ φ => Relation.ReflTransGen (StructOp source) φ (φ.leafSubst α β c))
    (motive_2 := λ cs => ∀ (i : Nat) (hi : i < cs.length),
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


end Alternatives.Structural
