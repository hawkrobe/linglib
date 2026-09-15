import Mathlib.Logic.Relation
import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Finset.Basic
import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Alternatives.Basic

/-!
# Structural alternatives

This file defines the structural alternatives of a parse tree ([katzir-2007]): the trees
obtainable from it by deletion, contraction, and substitution of a constituent by a
same-category item of the substitution source, the lexicon together with the tree's own
subtrees. `StructOp` is one such operation, `atMostAsComplex` its reflexive-transitive
closure, the complexity preorder of the paper's definition (19), `equalComplexity` the
antisymmetrization of that preorder, and `structuralAlternatives` the set of trees at most as
complex as the given one, definition (20). Structural alternatives form an alternative source
for the competition relation of `Alternatives.Competition`, and `indirectFrom` is the
combinator on sources of [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]: the
pronounceable expressions of no greater size that mean what a silent alternative means.

No operation introduces a category absent from the tree and the source
(`category_preservation`), which is what excludes the symmetric alternatives, nor a subtree
property the operations cannot create (`subtree_preservation`); and substituting one lexical
item for another of the same category throughout a tree, a Horn-scale alternative, is a chain
of substitutions (`horn_alternatives_are_structural`), so scalar alternatives are a special
case. More generally the Hamblin composition engine of `Alternatives/Basic`, applied to a tree
whose terminals evoke their same-category lexical items, generates exactly the substitution
fragment: its alternatives are structural (`hamblin_alternatives_subset`), while deletion and
contraction, which act on the whole tree, lie outside any pointwise composition.

## Main definitions

* `substitutionSource` — the lexicon together with the subtrees of the host.
* `StructOp`, `atMostAsComplex`, `equalComplexity` — one operation, its reflexive-transitive
  closure as a preorder, and the equal-complexity equivalence.
* `structuralAlternatives` — the trees at most as complex as the host over its source.
* `hamblin` — the Hamblin composition of a tree over a lexicon, a `WithAlternatives` value.
* `indirectFrom` — the indirect-alternative combinator on sources.

## Main results

* `category_preservation`, `subtree_preservation` — the operations create no category and no
  subtree property absent from the host and the source.
* `horn_alternatives_are_structural` — leaf substitution of a same-category lexical item is a
  structural alternative.
* `hamblin_alternatives_subset` — the alternatives composed by the Hamblin engine over the
  lexicon are structural alternatives.

## Implementation notes

`atMostAsComplex` is reachability, not an operation count, so `equalComplexity`, mutual
reachability, is coarser than the paper's equal complexity. The `inBind` constructor extends
the operations into the body of a binder, which the paper's trees lack.

## References

* [katzir-2007]
* [fox-katzir-2011]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
-/

namespace Alternatives

open Syntax Tree

variable {C W : Type*}

/-- The substitution source of `φ` (the paper's definition (41)): the lexicon together with
the subtrees of `φ`, so that a complex constituent of `φ` can replace a simpler one
elsewhere in it. -/
def substitutionSource (lex : Finset (Tree C W)) (φ : Tree C W) : Set (Tree C W) :=
  ↑lex ∪ {t | t ∈ φ.subtrees}

theorem forall_mem_substitutionSource {lex : Finset (Tree C W)} {φ : Tree C W}
    {P : Tree C W → Prop} :
    (∀ t ∈ substitutionSource lex φ, P t) ↔ (∀ t ∈ lex, P t) ∧ ∀ t ∈ φ.subtrees, P t := by
  simp only [substitutionSource, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, or_imp,
    forall_and]

/-- One structural operation on parse trees: substitution of a constituent by a same-category
item of the source, deletion of a child, contraction of a node to one of its same-category
children, and the recursive cases inside a child or a binder body. -/
inductive StructOp (source : Set (Tree C W)) : Tree C W → Tree C W → Prop where
  /-- Substitute a tree by a same-category item of the source. -/
  | subst {φ ψ : Tree C W} (h_cat : ψ.cat = φ.cat) (h_src : ψ ∈ source) : StructOp source φ ψ
  /-- Delete the `i`-th child of a node. -/
  | delete {cat : C} {cs : List (Tree C W)} (i : Fin cs.length) :
    StructOp source (.node cat cs) (.node cat (cs.eraseIdx i))
  /-- Contract a node to one of its same-category children. -/
  | contract {cat : C} {cs : List (Tree C W)} {child : Tree C W} (h_mem : child ∈ cs)
    (h_cat : child.cat = cat) : StructOp source (.node cat cs) child
  /-- Apply an operation inside one child of a node. -/
  | inChild {cat : C} {cs : List (Tree C W)} (i : Fin cs.length) {ψ_child : Tree C W}
    (h_step : StructOp source (cs.get i) ψ_child) :
    StructOp source (.node cat cs) (.node cat (cs.set i ψ_child))
  /-- Apply an operation inside a binder body. -/
  | inBind {n : Nat} {cat : C} {body body' : Tree C W} (h_step : StructOp source body body') :
    StructOp source (.bind n cat body) (.bind n cat body')

/-- `ψ` is at most as complex as `φ` when a chain of structural operations over the source
leads from `φ` to `ψ`, the paper's definition (19) as a reachability preorder. -/
def atMostAsComplex (source : Set (Tree C W)) (ψ φ : Tree C W) : Prop :=
  Relation.ReflTransGen (StructOp source) φ ψ

instance (source : Set (Tree C W)) : IsPreorder (Tree C W) (atMostAsComplex source) where
  refl _ := Relation.ReflTransGen.refl
  trans _ _ _ h₁ h₂ := h₂.trans h₁

/-- Equal complexity: each is at most as complex as the other. -/
def equalComplexity (source : Set (Tree C W)) : Tree C W → Tree C W → Prop :=
  AntisymmRel (atMostAsComplex source)

theorem equalComplexity.equivalence (source : Set (Tree C W)) :
    Equivalence (equalComplexity source) :=
  (AntisymmRel.setoid (Tree C W) (atMostAsComplex source)).iseqv

/-- A same-category terminal substitution with both terminals in the source is reversible,
so the two terminals are of equal complexity. -/
theorem equalComplexity_terminal_subst {source : Set (Tree C W)} {cat : C} {oldW newW : W}
    (h_old : Tree.terminal cat oldW ∈ source) (h_new : Tree.terminal cat newW ∈ source) :
    equalComplexity source (.terminal cat oldW) (.terminal cat newW) :=
  ⟨Relation.ReflTransGen.single (StructOp.subst rfl h_old),
   Relation.ReflTransGen.single (StructOp.subst rfl h_new)⟩

/-- The structural alternatives of `φ`, the paper's definition (20): the trees at most as
complex as `φ` over its substitution source. -/
def structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) : Set (Tree C W) :=
  {ψ | atMostAsComplex (substitutionSource lex φ) ψ φ}

theorem self_mem_structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) :
    φ ∈ structuralAlternatives lex φ :=
  Relation.ReflTransGen.refl

/-! ### Category and subtree preservation -/

private theorem structOp_preserves_no_cat [DecidableEq C]
    (source : Set (Tree C W)) (c : C)
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

/-- No tree reachable by structural operations contains a category absent from the source
and the host: substitution introduces only source material, deletion removes material, and
contraction promotes a subtree. -/
theorem category_preservation [DecidableEq C]
    (source : Set (Tree C W)) (c : C)
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
private theorem structOp_preserves_free (source : Set (Tree C W))
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
theorem subtree_preservation (source : Set (Tree C W)) (Bad : Tree C W → Prop)
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

/-! ### Horn scales are structural alternatives -/

/-- Lift a ReflTransGen chain at position i through inChild. -/
private theorem lift_at_position {source : Set (Tree C W)}
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
private theorem lift_bind {source : Set (Tree C W)}
    {n : Nat} {cat : C} {body body' : Tree C W}
    (h : Relation.ReflTransGen (StructOp source) body body') :
    Relation.ReflTransGen (StructOp source) (.bind n cat body) (.bind n cat body') :=
  Relation.ReflTransGen.lift (λ t => Tree.bind n cat t)
    (λ _ _ h => StructOp.inBind h) body body' h

/-- leafSubstList is just List.map. -/
private theorem leafSubstList_eq_map [BEq C] [BEq W]
    (α β : W) (c : C) (cs : List (Tree C W)) :
    Tree.leafSubst.leafSubstList α β c cs =
    cs.map (·.leafSubst α β c) := by
  induction cs with
  | nil => rfl
  | cons t ts ih =>
    simp only [Tree.leafSubst.leafSubstList, List.map_cons]
    exact congrArg _ ih

/-- Children reachable one by one make the node reachable: with `cs'` pointwise reachable from
`cs`, `node cat cs` reaches `node cat cs'` by operations inside successive children. -/
private theorem pointwise_reachable {source : Set (Tree C W)} {cat : C}
    {cs cs' : List (Tree C W)} (hlen : cs'.length = cs.length)
    (hf : ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructOp source) cs[i] (cs'[i]'(hlen ▸ hi))) :
    Relation.ReflTransGen (StructOp source) (.node cat cs) (.node cat cs') := by
  suffices h : ∀ k (hk : k ≤ cs.length),
    Relation.ReflTransGen (StructOp source)
      (.node cat cs) (.node cat (List.take k cs' ++ List.drop k cs)) by
    have h' := h cs.length le_rfl
    rw [List.take_of_length_le (by omega), List.drop_length, List.append_nil] at h'
    exact h'
  intro k
  induction k with
  | zero => intro _; simp; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro hk
    have hk' : k < cs.length := by omega
    apply Relation.ReflTransGen.trans (ih (by omega))
    have htk_len : (List.take k cs').length = k := by simp [List.length_take]; omega
    have hmid_k : (List.take k cs' ++ List.drop k cs)[k]'(by simp [List.length_take]; omega)
        = cs[k] := by
      rw [List.getElem_append_right (by omega)]
      simp [htk_len, List.getElem_drop]
    suffices heq : List.take (k + 1) cs' ++ List.drop (k + 1) cs =
        (List.take k cs' ++ List.drop k cs).set k (cs'[k]'(by omega)) by
      rw [heq]
      apply lift_at_position _ k (by simp [List.length_take]; omega)
      rw [hmid_k]; exact hf k hk'
    have htk1_len : (List.take (k + 1) cs').length = k + 1 := by simp [List.length_take]; omega
    apply List.ext_getElem
    · simp [List.length_set, List.length_take, List.length_drop]; omega
    · intro i hi1 hi2
      by_cases hik : i = k
      · subst hik
        rw [List.getElem_set_self, List.getElem_append_left (by omega)]
        simp [List.getElem_take]
      · rw [List.getElem_set_ne (Ne.symm hik)]
        by_cases hilt : i < k
        · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
          simp [List.getElem_take]
        · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
          simp [htk1_len, htk_len, List.getElem_drop]
          congr 1; omega

/-- Process children one at a time: .node cat cs →* .node cat (cs.map f). -/
private theorem mapChildren_reachable {source : Set (Tree C W)}
    {cat : C} {cs : List (Tree C W)} {f : Tree C W → Tree C W}
    (hf : ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructOp source) cs[i] (f cs[i])) :
    Relation.ReflTransGen (StructOp source)
      (.node cat cs) (.node cat (cs.map f)) :=
  pointwise_reachable (by simp) λ i hi => by rw [List.getElem_map]; exact hf i hi

/-- Leaf substitution is reachable via structural operations for any
source containing `.terminal c β`. -/
private theorem leafSubst_reachable [BEq C] [LawfulBEq C] [BEq W]
    {source : Set (Tree C W)} (α β : W) (c : C)
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

/-- Leaf substitution of a same-category lexical item throughout a tree is a structural
alternative, so Horn-scale alternatives are a special case of structural ones. -/
theorem horn_alternatives_are_structural [BEq C] [LawfulBEq C] [BEq W] (lex : Finset (Tree C W))
    (φ : Tree C W) (α β : W) (c : C) (h_β : Tree.terminal c β ∈ lex) :
    φ.leafSubst α β c ∈ structuralAlternatives lex φ :=
  leafSubst_reachable α β c (Set.mem_union_left _ (Finset.mem_coe.2 h_β)) φ

/-! ### Hamblin composition generates the substitution fragment

The composition engine of `Alternatives/Basic` computes alternatives pointwise from the parts:
`hamblin lex φ` gives each terminal the same-category items of the lexicon as alternatives and
composes the constructors through the applicative. Every alternative it evokes is a chain of
substitutions at the leaves, hence a structural alternative (`hamblin_alternatives_subset`);
deletion and contraction lie outside the compositional fragment, so the converse fails. -/

/-- The Hamblin composition of a tree over a lexicon: a terminal evokes itself and the
same-category items of the lexicon, and the constructors compose pointwise. -/
def hamblin (lex : Finset (Tree C W)) : Tree C W → WithAlternatives (Tree C W)
  | t@(.terminal c _) => ⟨t, insert t {s | s ∈ lex ∧ s.cat = c}⟩
  | .node c cs => Tree.node c <$> hamblinList lex cs
  | t@(.trace _ _) => pure t
  | .bind n c body => Tree.bind n c <$> hamblin lex body
where
  /-- The pointwise composition of a list of children. -/
  hamblinList (lex : Finset (Tree C W)) : List (Tree C W) → WithAlternatives (List (Tree C W))
  | [] => pure []
  | t :: ts => (· :: ·) <$> hamblin lex t <*> hamblinList lex ts

/-- The ordinary value of the composition is the tree itself. -/
theorem hamblin_ordinary (lex : Finset (Tree C W)) (φ : Tree C W) :
    (hamblin lex φ).ordinary = φ := by
  refine Tree.rec (motive_1 := λ φ => (hamblin lex φ).ordinary = φ)
    (motive_2 := λ cs => (hamblin.hamblinList lex cs).ordinary = cs) ?_ ?_ ?_ ?_ ?_ ?_ φ
  · intro c w; rfl
  · intro c cs ih; simp only [hamblin, WithAlternatives.ordinary_map, ih]
  · intro n c; rfl
  · intro n c body ih; simp only [hamblin, WithAlternatives.ordinary_map, ih]
  · rfl
  · intro t ts iht ihts
    simp only [hamblin.hamblinList, WithAlternatives.ordinary_seq, WithAlternatives.ordinary_map,
      iht, ihts]

/-- The composition is well formed: the tree is among its own alternatives. -/
theorem hamblin_wellFormed (lex : Finset (Tree C W)) (φ : Tree C W) :
    (hamblin lex φ).WellFormed := by
  refine Tree.rec (motive_1 := λ φ => (hamblin lex φ).WellFormed)
    (motive_2 := λ cs => (hamblin.hamblinList lex cs).WellFormed) ?_ ?_ ?_ ?_ ?_ ?_ φ
  · intro c w; exact Set.mem_insert _ _
  · intro c cs ih; exact ih.map
  · intro n c; exact WithAlternatives.WellFormed.unfeatured _
  · intro n c body ih; exact ih.map
  · exact WithAlternatives.WellFormed.unfeatured _
  · intro t ts iht ihts
    exact WithAlternatives.mem_alternatives_seq.2
      ⟨_, WithAlternatives.mem_alternatives_map.2 ⟨_, iht, rfl⟩, _, ihts, rfl⟩

/-- Over any source containing the lexicon, every alternative the composition evokes is
reachable from the tree by structural operations. -/
theorem reachable_of_mem_hamblin {source : Set (Tree C W)} (lex : Finset (Tree C W))
    (hlex : ↑lex ⊆ source) (φ : Tree C W) :
    ∀ ψ ∈ (hamblin lex φ).alternatives, Relation.ReflTransGen (StructOp source) φ ψ := by
  refine Tree.rec
    (motive_1 := λ φ => ∀ ψ ∈ (hamblin lex φ).alternatives,
      Relation.ReflTransGen (StructOp source) φ ψ)
    (motive_2 := λ cs => ∀ cs' ∈ (hamblin.hamblinList lex cs).alternatives,
      List.Forall₂ (Relation.ReflTransGen (StructOp source)) cs cs') ?_ ?_ ?_ ?_ ?_ ?_ φ
  · intro c w ψ hψ
    rcases hψ with rfl | ⟨hlex', hcat⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (StructOp.subst hcat (hlex (Finset.mem_coe.2 hlex')))
  · intro c cs ih ψ hψ
    obtain ⟨cs', hcs', rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    have h := ih cs' hcs'
    exact pointwise_reachable h.length_eq.symm λ i hi => h.get hi (h.length_eq ▸ hi)
  · intro n c ψ hψ
    have h : ψ ∈ ({Tree.trace n c} : Set (Tree C W)) := by
      simpa [hamblin, WithAlternatives.alternatives_pure] using hψ
    obtain rfl := Set.mem_singleton_iff.1 h
    exact Relation.ReflTransGen.refl
  · intro n c body ih ψ hψ
    obtain ⟨body', hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    exact lift_bind (ih body' hb)
  · intro cs' hcs'
    have h : cs' ∈ ({[]} : Set (List (Tree C W))) := by
      simpa [hamblin.hamblinList, WithAlternatives.alternatives_pure] using hcs'
    obtain rfl := Set.mem_singleton_iff.1 h
    exact List.Forall₂.nil
  · intro t ts iht ihts cs' hcs'
    obtain ⟨g, hg, bs, hbs, rfl⟩ := WithAlternatives.mem_alternatives_seq.1 hcs'
    obtain ⟨b, hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hg
    exact List.Forall₂.cons (iht b hb) (ihts bs hbs)

/-- The compositional fragment: the alternatives the Hamblin engine evokes from the lexicon are
structural alternatives. -/
theorem hamblin_alternatives_subset (lex : Finset (Tree C W)) (φ : Tree C W) :
    (hamblin lex φ).alternatives ⊆ structuralAlternatives lex φ :=
  reachable_of_mem_hamblin lex Set.subset_union_left φ

/-! ### Indirect alternatives -/

variable {S M : Type*}

/-- The indirect-alternative combinator (eq. 43,
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]).

`indirectFrom base pron meaning size s` is the set of *pronounceable*
expressions `s'` such that `size s' ≤ size s` and there is some
*unpronounceable* `sₓ ∈ base s` with `meaning s' = meaning sₓ`.

Both the surrogate `s'` (the indirect alternative `I`) and the witness
`sₓ` are constrained by `pron`: `I` must be pronounceable while `sₓ` —
the silent structural alternative it stands in for — must not be, per
the paper's definition. -/
def indirectFrom (base : S → Set S) (pron : S → Prop)
    (meaning : S → M) (size : S → Nat) :
    S → Set S :=
  fun s =>
    {s' | pron s' ∧ size s' ≤ size s ∧ ∃ sₓ ∈ base s, ¬ pron sₓ ∧ meaning s' = meaning sₓ}

variable {base : S → Set S} {pron : S → Prop}
  {meaning : S → M} {size : S → Nat} {s' s : S}

/-- Membership in the indirect-alternative source. -/
@[simp] theorem mem_indirectFrom :
    s' ∈ indirectFrom base pron meaning size s ↔
      pron s' ∧ size s' ≤ size s ∧ ∃ sₓ ∈ base s, ¬ pron sₓ ∧ meaning s' = meaning sₓ :=
  Iff.rfl

/-- Indirect alternatives are at most as complex as the original. -/
theorem size_le_of_mem (h : s' ∈ indirectFrom base pron meaning size s) :
    size s' ≤ size s := h.2.1

/-- The indirect-alternative set is empty when the base source contains
no unpronounceable witnesses — the genuine refinement: an indirect
alternative requires a *silent* witness in the base. -/
theorem indirectFrom_eq_empty_of_forall_pron (allPron : ∀ x ∈ base s, pron x) :
    indirectFrom base pron meaning size s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨_, _, sₓ, hMem, hUnpron, _⟩
  exact hUnpron (allPron sₓ hMem)

end Alternatives
