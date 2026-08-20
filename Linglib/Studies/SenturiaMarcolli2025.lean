import Linglib.Core.Data.RoseTree.Leaves
import Mathlib.Logic.Relation
import Linglib.Core.Data.RoseTree.FilterMap
import Linglib.Core.Data.RoseTree.DecEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The algebraic structure of morphosyntax

[senturia-marcolli-2025] models Distributed Morphology inside the Merge
algebra of [marcolli-chomsky-berwick-2025]: morphological objects are
built by the same free non-associative commutative magma as syntactic
objects, differing only in labeling — an internal vertex carries the
union of its children's feature bundles, so a bundle is derived from the
tree rather than stipulated. On this carrier fusion is the magma
operation itself, fission restricts the tree along a partition of its
bundle, and impoverishment is a fission component: the paper reduces the
four DM operations to fusion and fission.

## Main definitions

* `bundle` — the feature bundle of a morphological object, the set of
  features at its leaves
* `fuse`, `restrict` — fusion as magma grafting, and the vertex-wise
  restriction producing the two fission outputs
* `FeatureCorrespondence`, `Morphosyntactic`, `Matched` — the
  syntax-morphology feature correspondence and morphosyntactic trees in
  labeled form: each syntactic leaf carries its datum and its inserted
  morphological object
* `toSyntactic`, `msFeatures` — the forgetful projection to the
  syntactic tree, and the total feature content of an assembly

## Main statements

* `bundle_fuse` — the fused bundle is the union of the input bundles,
  an instance of the labeling law: fusion needs nothing beyond the magma
* `bundle_restrict` — a fission output's bundle is the input bundle
  restricted to the kept features
* `restrict_copies_shared` — features shared out to both sides of the
  partition survive in both outputs
* `bundle_fuse_restrict` — fission followed by fusion restores the
  bundle, and `fuse_restrict_ne` — but not the tree
* `msFeatures_fuse`, `msFeatures_fission_partition` — at the application
  site, fusion and disjoint fission move the syntax-morphology boundary
  (`toSyntactic` collapses or grows a cherry) while the total feature
  content is invariant
* `matched_fused_iff` — the fused site is matched exactly when the union
  bundle matches the projecting datum
* `PostSyntactic.toFinset_msFeatures_eq`,
  `Derivation.toFinset_msFeatures_subset` — along the post-syntactic
  semigroup the total feature set is invariant; the full Distributed
  Morphology semigroup can only shrink it

## TODO

The workspace Hopf algebra with obliteration via the coproduct, and the
colored correspondence between the syntactic and morphosyntactic
algebras over the Merge operad.

## References

* [I. Senturia and M. Marcolli, *The algebraic structure of
  morphosyntax*][senturia-marcolli-2025]
* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical structure of
  syntactic Merge*][marcolli-chomsky-berwick-2025]
-/

namespace SenturiaMarcolli2025

open RoseTree

variable {F : Type*} [DecidableEq F]

/-! ### Morphological objects and the derived bundle labeling

A morphological object is a nonplanar tree with single features at the
leaves and bare structural vertices elsewhere — the alphabet `F ⊕ Unit`,
exactly the carrier shape of syntactic objects with features in place of
the lexical items. Definition 2.1 of [senturia-marcolli-2025] labels
each internal vertex with the union of its children's bundles, so every
vertex label is determined by the leaves below it; `bundle` is the
root's. -/

/-- Features occur only at leaves: internal vertices are structural.
Restriction can leave childless or non-branching structural vertices, so
arity is not constrained (the extended morphological objects of
[senturia-marcolli-2025] Definition 2.8). -/
inductive IsMorphological : RoseTree (F ⊕ Unit) → Prop
  | leaf (x : F ⊕ Unit) : IsMorphological (.node x [])
  | node {cs : List (RoseTree (F ⊕ Unit))} (hne : cs ≠ [])
      (h : ∀ c ∈ cs, IsMorphological c) : IsMorphological (.node (.inr ()) cs)

/-- The multiset of leaf features of a planar tree. -/
def leafFeatures (t : RoseTree (F ⊕ Unit)) : Multiset F :=
  t.leaves.filterMap Sum.getLeft?

/-- The feature bundle of a morphological object: the set of features at
its leaves, the root label of [senturia-marcolli-2025] Definition 2.1. -/
def bundle (S : Nonplanar (F ⊕ Unit)) : Finset F :=
  (S.leaves.filterMap Sum.getLeft?).toFinset

@[simp] theorem bundle_mk (t : RoseTree (F ⊕ Unit)) :
    bundle (Nonplanar.mk t) = (leafFeatures t).toFinset := rfl

@[simp] theorem bundle_leaf (f : F) :
    bundle (Nonplanar.leaf (.inl f)) = {f} := by
  rw [show bundle (Nonplanar.leaf (.inl f)) = ({f} : Multiset F).toFinset from rfl]
  exact Multiset.toFinset_singleton f

@[simp] theorem bundle_leaf_inr :
    bundle (Nonplanar.leaf (.inr () : F ⊕ Unit)) = ∅ := rfl

/-- The multiset of leaf features of a morphological object; `bundle` is
its underlying set. Fission with an overlapping partition duplicates
features, which only the multiset records. -/
def features (S : Nonplanar (F ⊕ Unit)) : Multiset F :=
  S.leaves.filterMap Sum.getLeft?

omit [DecidableEq F] in
@[simp] theorem features_mk (t : RoseTree (F ⊕ Unit)) :
    features (Nonplanar.mk t) = leafFeatures t := rfl

theorem bundle_eq_toFinset_features (S : Nonplanar (F ⊕ Unit)) :
    bundle S = (features S).toFinset := rfl

/-- A structural vertex contributes nothing to the bundle: the leaf
features of a structural node are the concatenation of its children's,
whether or not children remain. -/
private theorem filterMap_list_sum {α β : Type*} (g : α → Option β)
    (l : List (Multiset α)) :
    Multiset.filterMap g l.sum = (l.map (Multiset.filterMap g)).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp [Multiset.filterMap_add, ih]

omit [DecidableEq F] in
theorem leafFeatures_node_inr (cs : List (RoseTree (F ⊕ Unit))) :
    leafFeatures (.node (.inr ()) cs) = (cs.map leafFeatures).sum := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [leafFeatures, leaves_node_cons, filterMap_list_sum, List.map_map]
    rfl

/-! ### Fusion

Fusion merges the bundles at two adjacent leaves of the syntactic tree
into one ([senturia-marcolli-2025] §5.1, Swahili negation *si-* fusing
NEG with first-singular agreement). On morphological objects it is the
magma operation itself — grafting under a fresh structural root — which
is why fusion is the one DM operation available inside syntax. -/

/-- Fusion of two morphological objects: the magma product, grafting
both under a structural root ([senturia-marcolli-2025] Definition 5.2). -/
noncomputable def fuse (S₁ S₂ : Nonplanar (F ⊕ Unit)) : Nonplanar (F ⊕ Unit) :=
  Nonplanar.node (.inr ()) {S₁, S₂}

/-- The fused bundle is the union of the input bundles — the labeling
law itself, so fusion needs nothing beyond the magma. -/
theorem bundle_fuse (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    bundle (fuse S₁ S₂) = bundle S₁ ∪ bundle S₂ := by
  refine Quotient.inductionOn₂ S₁ S₂ fun p q => ?_
  show bundle (Nonplanar.node (.inr ()) {Nonplanar.mk p, Nonplanar.mk q}) = _
  rw [Nonplanar.node_pair_mk]
  simp only [bundle_mk, leafFeatures_node_inr, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Multiset.toFinset_add]
  rfl

omit [DecidableEq F] in
/-- Fusion is additive on the feature multiset: nothing is lost,
duplicated, or created. -/
theorem features_fuse (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    features (fuse S₁ S₂) = features S₁ + features S₂ := by
  refine Quotient.inductionOn₂ S₁ S₂ fun p q => ?_
  show features (Nonplanar.node (.inr ()) {Nonplanar.mk p, Nonplanar.mk q}) = _
  rw [Nonplanar.node_pair_mk]
  simp only [features_mk, leafFeatures_node_inr, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rfl

/-! ### Fission

Fission splits one bundle into two along a partition `B ∖ A = B₁ ⊔ B₂`,
with the residue `A` copied into both outputs ([senturia-marcolli-2025]
§5.2; Ṣanʕānī Arabic discontinuous agreement, where person and number of
a single head surface as prefix and suffix). Each output is the input
tree restricted vertex-wise to the kept features: leaves outside the
kept set are deleted, structural vertices stay, and vanished subtrees
may leave non-branching structural vertices behind — the extended
morphological objects. -/

/-- Keep a leaf feature iff it lies in `C`; structural vertices always
survive. -/
def keep (C : Finset F) : F ⊕ Unit → Option (F ⊕ Unit)
  | .inl f => if f ∈ C then some (.inl f) else none
  | .inr _ => some (.inr ())

/-- Restriction of a morphological object to the features in `C`: the
construction of a single fission output ([senturia-marcolli-2025]
Definition 5.6, with `C = Bᵢ ∪ A`). `none` only for a single leaf
outside `C`. -/
def restrict (C : Finset F) (S : Nonplanar (F ⊕ Unit)) :
    Option (Nonplanar (F ⊕ Unit)) :=
  S.filterMap (keep C)

private theorem sum_leafFeatures_filterMap (C : Finset F)
    (cs : List (RoseTree (F ⊕ Unit)))
    (ih : ∀ c ∈ cs, ((c.filterMap (keep C)).elim 0 leafFeatures)
      = (leafFeatures c).filter (· ∈ C)) :
    ((cs.filterMap (RoseTree.filterMap (keep C))).map leafFeatures).sum
      = ((cs.map leafFeatures).sum).filter (· ∈ C) := by
  induction cs with
  | nil => simp
  | cons c cs ihcs =>
    have hc := ih c (List.mem_cons_self ..)
    have hrest := ihcs fun d hd => ih d (List.mem_cons_of_mem _ hd)
    cases hcc : RoseTree.filterMap (keep C) c with
    | none =>
      rw [hcc, Option.elim_none] at hc
      rw [List.filterMap_cons_none hcc]
      simp only [List.map_cons, List.sum_cons, Multiset.filter_add, ← hc,
        hrest, zero_add]
    | some c' =>
      rw [hcc, Option.elim_some] at hc
      rw [List.filterMap_cons_some hcc]
      simp only [List.map_cons, List.sum_cons, Multiset.filter_add, ← hc, hrest]

private theorem leafFeatures_filterMap_keep (C : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    ((t.filterMap (keep C)).elim 0 leafFeatures)
      = (leafFeatures t).filter (· ∈ C) := by
  induction ht with
  | leaf x =>
    cases x with
    | inl f =>
      have e : Multiset.filterMap Sum.getLeft? ({Sum.inl f} : Multiset (F ⊕ Unit))
          = ({f} : Multiset F) := rfl
      by_cases hf : f ∈ C <;>
        simp [keep, hf, leafFeatures, e, Multiset.filter_singleton]
    | inr u =>
      have e : Multiset.filterMap Sum.getLeft? ({Sum.inr u} : Multiset (F ⊕ Unit))
          = (0 : Multiset F) := rfl
      simp [keep, leafFeatures, e]
  | @node cs hne h ih =>
    have hstep : RoseTree.filterMap (keep C) (.node (.inr ()) cs)
        = some (.node (.inr ()) (RoseTree.filterMapList (keep C) cs)) := rfl
    rw [hstep, Option.elim_some, leafFeatures_node_inr, leafFeatures_node_inr,
      RoseTree.filterMapList_eq_filterMap]
    exact sum_leafFeatures_filterMap C cs ih

/-- The bundle of a fission output is the input bundle restricted to the
kept features: the vertex law `B_w ∩ (Bᵢ ∪ A)` of
[senturia-marcolli-2025] Definition 5.6, at the root. -/
theorem bundle_restrict {C : Finset F} {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) {S' : Nonplanar (F ⊕ Unit)}
    (h : restrict C (Nonplanar.mk t) = some S') :
    bundle S' = bundle (Nonplanar.mk t) ∩ C := by
  rw [restrict, Nonplanar.filterMap_mk] at h
  cases hc : t.filterMap (keep C) with
  | none => rw [hc, Option.map_none] at h; exact absurd h (by simp)
  | some t' =>
    rw [hc, Option.map_some, Option.some.injEq] at h
    subst h
    have key := leafFeatures_filterMap_keep C ht
    rw [hc, Option.elim_some] at key
    rw [bundle_mk, bundle_mk, key, Multiset.toFinset_filter,
      Finset.filter_mem_eq_inter]

/-- Multiset form of `bundle_restrict`: restriction filters the feature
multiset, `none` counting as empty. -/
theorem features_restrict (C : Finset F) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) :
    (restrict C (Nonplanar.mk t)).elim 0 features
      = (features (Nonplanar.mk t)).filter (· ∈ C) := by
  rw [restrict, Nonplanar.filterMap_mk]
  have key := leafFeatures_filterMap_keep C ht
  cases hc : t.filterMap (keep C) with
  | none => rw [hc, Option.elim_none] at key; simpa using key
  | some t' => rw [hc, Option.elim_some] at key; simpa using key

/-- Features copied into both sides of the fission partition survive in
both outputs: the residue of a discontinuously realized bundle is
pronounced on both exponents. -/
theorem restrict_copies_shared {A C₁ C₂ : Finset F}
    (h₁ : A ⊆ C₁) (h₂ : A ⊆ C₂) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) {S₁' S₂' : Nonplanar (F ⊕ Unit)}
    (e₁ : restrict C₁ (Nonplanar.mk t) = some S₁')
    (e₂ : restrict C₂ (Nonplanar.mk t) = some S₂') :
    A ∩ bundle (Nonplanar.mk t) ⊆ bundle S₁' ∩ bundle S₂' := by
  rw [bundle_restrict ht e₁, bundle_restrict ht e₂]
  intro f hf
  simp only [Finset.mem_inter] at hf ⊢
  exact ⟨⟨hf.2, h₁ hf.1⟩, hf.2, h₂ hf.1⟩

/-! ### Impoverishment as fission plus fusion

[senturia-marcolli-2025] Propositions 5.20–5.21: impoverishment and
obliteration are not independent operations. Discarding a subbundle is
keeping one fission output (`bundle_restrict` with the kept part as
`C`); the trace-maintaining variant fissions and refuses at the same
vertex, restoring the bundle without restoring the tree. Obliteration
replaces a whole morphological object by the unit of the workspace
algebra, which lives in the second slice. -/

/-- Fission followed by fusion restores the bundle: the trace-maintaining
impoverishment composite leaves the feature content intact. -/
theorem bundle_fuse_restrict {C₁ C₂ : Finset F} {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) (hcover : bundle (Nonplanar.mk t) ⊆ C₁ ∪ C₂)
    {S₁' S₂' : Nonplanar (F ⊕ Unit)}
    (e₁ : restrict C₁ (Nonplanar.mk t) = some S₁')
    (e₂ : restrict C₂ (Nonplanar.mk t) = some S₂') :
    bundle (fuse S₁' S₂') = bundle (Nonplanar.mk t) := by
  rw [bundle_fuse, bundle_restrict ht e₁, bundle_restrict ht e₂,
    ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hcover]

/-! ### The tree is not restored

Fission at a partition whose residue is copied into both outputs, then
fusion, restores the bundle but not the tree: the copied feature now
occupies a leaf on each side, so the composite has strictly more leaves.
The witness is [senturia-marcolli-2025] Example 5.7: `[φ, α, β, γ]` with
kept sets `[φ, γ]` and `[φ, α, β]`. -/

private inductive Feat where
  | phi | alpha | beta | gamma
  deriving DecidableEq, Repr

private def exTree : RoseTree (Feat ⊕ Unit) :=
  .node (.inr ()) [.node (.inr ()) [.node (.inl .phi) [], .node (.inl .alpha) []],
    .node (.inr ()) [.node (.inl .beta) [], .node (.inl .gamma) []]]

/-- Restriction to `{φ, γ}` and `{φ, α, β}` followed by fusion yields a
five-leaf object: `φ` is realized on both sides, so the composite is not
the original four-leaf tree even though its bundle is
(`bundle_fuse_restrict`). -/
theorem fuse_restrict_ne (S₁' S₂' : Nonplanar (Feat ⊕ Unit))
    (e₁ : restrict {.phi, .gamma} (Nonplanar.mk exTree) = some S₁')
    (e₂ : restrict {.phi, .alpha, .beta} (Nonplanar.mk exTree) = some S₂') :
    fuse S₁' S₂' ≠ Nonplanar.mk exTree := by
  have c₁ : exTree.filterMap (keep {.phi, .gamma})
      = some (.node (.inr ()) [.node (.inr ()) [.node (.inl .phi) []],
          .node (.inr ()) [.node (.inl .gamma) []]]) := by decide
  have c₂ : exTree.filterMap (keep {.phi, .alpha, .beta})
      = some (.node (.inr ()) [.node (.inr ()) [.node (.inl .phi) [],
          .node (.inl .alpha) []], .node (.inr ()) [.node (.inl .beta) []]]) := by
    decide
  rw [restrict, Nonplanar.filterMap_mk, c₁, Option.map_some,
    Option.some.injEq] at e₁
  rw [restrict, Nonplanar.filterMap_mk, c₂, Option.map_some,
    Option.some.injEq] at e₂
  subst e₁ e₂
  rw [fuse, Nonplanar.node_pair_mk]
  intro hcontra
  have := congrArg Nonplanar.numLeaves hcontra
  rw [Nonplanar.numLeaves_mk, Nonplanar.numLeaves_mk] at this
  exact absurd this (by decide)

/-! ### The syntax-morphology correspondence and morphosyntactic trees

A morphosyntactic tree inserts morphological objects at the leaves of a
syntactic tree, constrained by a matching rule between the bundle at the
root of the inserted object and the syntactic datum at the leaf
([senturia-marcolli-2025] Definitions 2.4 and 3.4). We keep the
insertion as a leaf label — syntactic datum paired with the inserted
object — which carries the same data as splicing the object below the
leaf. -/

/-- The syntax-morphology feature correspondence: which feature bundles
can be matched with which lexical items and syntactic features
([senturia-marcolli-2025] Definition 2.4). Matching is multivalued in
both directions, but every syntactic datum carries some bundle. -/
structure FeatureCorrespondence (F Λ : Type*) [DecidableEq F] where
  /-- `matching B lex` iff the bundle `B` can decorate a leaf carrying
  the syntactic datum `lex`. -/
  matching : Finset F → Λ → Prop
  /-- Every syntactic datum carries some bundle. -/
  matching_surjective : ∀ lex : Λ, ∃ B, matching B lex

/-- A morphosyntactic tree in labeled form: each syntactic leaf carries
its datum together with the inserted morphological object, `none` where
morphology was obliterated ([senturia-marcolli-2025] Definition 3.4; the
empty insertion is Remark 5.12). -/
abbrev Morphosyntactic (F Λ : Type*) :=
  Nonplanar ((Λ × Option (Nonplanar (F ⊕ Unit))) ⊕ Unit)

variable {Λ : Type*}

/-- A leaf of a morphosyntactic tree: a syntactic datum with an optional
morphological insertion. -/
def insertion (lex : Λ) (mo : Option (Nonplanar (F ⊕ Unit))) :
    Morphosyntactic F Λ :=
  Nonplanar.leaf (.inl (lex, mo))

/-- The forgetful projection to the syntactic tree: drop the inserted
morphology. This is [senturia-marcolli-2025] Definition 3.9's morphism
of algebras over the Merge operad, in labeled form. -/
def toSyntactic : Morphosyntactic F Λ → Nonplanar (Λ ⊕ Unit) :=
  Nonplanar.map (Sum.map Prod.fst id)

omit [DecidableEq F] in
@[simp] theorem toSyntactic_insertion (lex : Λ)
    (mo : Option (Nonplanar (F ⊕ Unit))) :
    toSyntactic (insertion lex mo) = Nonplanar.leaf (.inl lex) :=
  Nonplanar.map_leaf _ _

/-- The feature content of one leaf label. -/
def insertionFeatures : (Λ × Option (Nonplanar (F ⊕ Unit))) ⊕ Unit → Multiset F
  | .inl (_, some S) => features S
  | .inl (_, none) => 0
  | .inr _ => 0

omit [DecidableEq F] in
@[simp] theorem insertionFeatures_inl (lex : Λ)
    (mo : Option (Nonplanar (F ⊕ Unit))) :
    insertionFeatures (.inl (lex, mo)) = mo.elim 0 features := by
  cases mo <;> rfl

/-- The total feature content of a morphosyntactic tree: everything its
inserted morphological objects carry, with multiplicity. -/
def msFeatures (T : Morphosyntactic F Λ) : Multiset F :=
  (T.leaves.map insertionFeatures).sum

omit [DecidableEq F] in
@[simp] theorem msFeatures_insertion (lex : Λ)
    (mo : Option (Nonplanar (F ⊕ Unit))) :
    msFeatures (insertion lex mo) = mo.elim 0 features := by
  simp [msFeatures, insertion]

/-- Every inserted morphological object matches its leaf's syntactic
datum. -/
def Matched (Γ : FeatureCorrespondence F Λ) (T : Morphosyntactic F Λ) : Prop :=
  ∀ lex S, .inl (lex, some S) ∈ T.leaves → Γ.matching (bundle S) lex

theorem matched_insertion_iff (Γ : FeatureCorrespondence F Λ) (lex : Λ)
    (S : Nonplanar (F ⊕ Unit)) :
    Matched Γ (insertion lex (some S)) ↔ Γ.matching (bundle S) lex := by
  constructor
  · exact fun h => h lex S (by simp [insertion])
  · intro h lex' S' hmem
    simp only [insertion, Nonplanar.leaves_leaf, Multiset.mem_singleton,
      Sum.inl.injEq, Prod.mk.injEq, Option.some.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact h

/-! ### The DM operations at their application site

The four DM operations transform the assembly of a morphosyntactic tree
at one site ([senturia-marcolli-2025] §5–§6). Fusion turns a syntactic
cherry over two insertions into a single insertion of the magma product;
fission turns one insertion into a cherry over its two restrictions.
Under `toSyntactic` the first collapses a cherry and the second grows
one — the movable syntax-morphology boundary — while `msFeatures`
records what happens to the feature content. -/

private theorem leaves_node_pair_leaf {α : Type*} (a x y : α) :
    (Nonplanar.node a {Nonplanar.leaf x, Nonplanar.leaf y}).leaves = {x, y} := by
  rw [show (Nonplanar.leaf x : Nonplanar α) = Nonplanar.mk (.node x []) from rfl,
    show (Nonplanar.leaf y : Nonplanar α) = Nonplanar.mk (.node y []) from rfl,
    Nonplanar.node_pair_mk, Nonplanar.leaves_mk, leaves_node_cons]
  simp

/-- The application site of fusion: a syntactic cherry with insertions
at both leaves. -/
noncomputable def fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    Morphosyntactic F Λ :=
  Nonplanar.node (.inr ()) {insertion lex₁ (some S₁), insertion lex₂ (some S₂)}

/-- The application site of fission on `S` along the kept sets `C₁, C₂`:
a syntactic cherry whose leaves carry the two restrictions; an empty
restriction is an empty insertion. -/
noncomputable def fissionSite (lex₁ lex₂ : Λ) (C₁ C₂ : Finset F)
    (S : Nonplanar (F ⊕ Unit)) : Morphosyntactic F Λ :=
  Nonplanar.node (.inr ())
    {insertion lex₁ (restrict C₁ S), insertion lex₂ (restrict C₂ S)}

omit [DecidableEq F] in
theorem msFeatures_fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    msFeatures (fusionSite lex₁ lex₂ S₁ S₂) = features S₁ + features S₂ := by
  rw [msFeatures, fusionSite, insertion, insertion, leaves_node_pair_leaf]
  simp

omit [DecidableEq F] in
/-- Fusion preserves the total feature content at the site: the fused
insertion, under whichever of the two data projects (the head function's
choice in [senturia-marcolli-2025] Definition 5.2), carries exactly what
the cherry carried. -/
theorem msFeatures_fuse (lexHead lex₁ lex₂ : Λ)
    (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    msFeatures (insertion lexHead (some (fuse S₁ S₂)))
      = msFeatures (fusionSite lex₁ lex₂ S₁ S₂) := by
  rw [msFeatures_insertion, Option.elim_some, features_fuse,
    msFeatures_fusionSite]

omit [DecidableEq F] in
/-- Fusion raises the syntax-morphology boundary: the syntactic
projection collapses from a cherry to a single leaf while the feature
content stays constant (`msFeatures_fuse`). -/
theorem toSyntactic_fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    toSyntactic (fusionSite lex₁ lex₂ S₁ S₂)
      = Nonplanar.node (.inr ())
          {Nonplanar.leaf (.inl lex₁), Nonplanar.leaf (.inl lex₂)} := by
  rw [fusionSite,
    show (insertion lex₁ (some S₁) : Morphosyntactic F Λ)
      = Nonplanar.mk (.node (.inl (lex₁, some S₁)) []) from rfl,
    show (insertion lex₂ (some S₂) : Morphosyntactic F Λ)
      = Nonplanar.mk (.node (.inl (lex₂, some S₂)) []) from rfl,
    Nonplanar.node_pair_mk, toSyntactic, Nonplanar.map_mk,
    show RoseTree.map (Sum.map Prod.fst id)
        (.node (.inr ()) [.node (.inl (lex₁, some S₁)) [],
          .node (.inl (lex₂, some S₂)) []])
      = .node (.inr ()) [.node (.inl lex₁) [], .node (.inl lex₂) []] from rfl,
    show (Nonplanar.leaf (.inl lex₁) : Nonplanar (Λ ⊕ Unit))
      = Nonplanar.mk (.node (.inl lex₁) []) from rfl,
    show (Nonplanar.leaf (.inl lex₂) : Nonplanar (Λ ⊕ Unit))
      = Nonplanar.mk (.node (.inl lex₂) []) from rfl,
    Nonplanar.node_pair_mk]

/-- The necessary condition for fusion: the fused site is matched exactly
when the union of the two bundles matches the projecting datum
([senturia-marcolli-2025]'s condition `(B_{v₁} ∪ B_{v₂}, α_v) ∈ Γ_SM`
following Definition 5.2). -/
theorem matched_fused_iff (Γ : FeatureCorrespondence F Λ) (lexHead : Λ)
    (S₁ S₂ : Nonplanar (F ⊕ Unit)) :
    Matched Γ (insertion lexHead (some (fuse S₁ S₂)))
      ↔ Γ.matching (bundle S₁ ∪ bundle S₂) lexHead := by
  rw [matched_insertion_iff, bundle_fuse]

theorem msFeatures_fissionSite (lex₁ lex₂ : Λ) (C₁ C₂ : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    msFeatures (fissionSite lex₁ lex₂ C₁ C₂ (Nonplanar.mk t))
      = (features (Nonplanar.mk t)).filter (· ∈ C₁)
        + (features (Nonplanar.mk t)).filter (· ∈ C₂) := by
  rw [msFeatures, fissionSite, insertion, insertion, leaves_node_pair_leaf]
  simp [features_restrict _ ht]

/-- Fission along a disjoint cover of the bundle preserves the feature
multiset: the boundary moves down (`toSyntactic` grows a cherry) with no
change in feature content. An overlapping partition instead duplicates
the shared residue (`restrict_copies_shared`), which is how the copied
features of discontinuous agreement come to be pronounced twice. -/
theorem msFeatures_fission_partition (lex₁ lex₂ : Λ) {C₁ C₂ : Finset F}
    (hdisj : Disjoint C₁ C₂) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t)
    (hcover : ∀ f ∈ features (Nonplanar.mk t), f ∈ C₁ ∪ C₂) :
    msFeatures (fissionSite lex₁ lex₂ C₁ C₂ (Nonplanar.mk t))
      = features (Nonplanar.mk t) := by
  rw [msFeatures_fissionSite _ _ _ _ ht, Multiset.filter_add_filter]
  have h₁ : (features (Nonplanar.mk t)).filter (fun f => f ∈ C₁ ∨ f ∈ C₂)
      = features (Nonplanar.mk t) :=
    Multiset.filter_eq_self.mpr fun f hf => by
      simpa [Finset.mem_union] using hcover f hf
  have h₂ : (features (Nonplanar.mk t)).filter (fun f => f ∈ C₁ ∧ f ∈ C₂)
      = 0 :=
    Multiset.filter_eq_nil.mpr fun f _ hf =>
      Finset.disjoint_left.mp hdisj hf.1 hf.2
  rw [h₁, h₂, add_zero]

/-- Impoverishment at a leaf only removes features: keeping one fission
output ([senturia-marcolli-2025] Proposition 5.20, first case) bounds
the feature content by the original. -/
theorem msFeatures_impoverish_le (lex : Λ) (kept : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    msFeatures (insertion lex (restrict kept (Nonplanar.mk t)))
      ≤ msFeatures (insertion lex (some (Nonplanar.mk t))) := by
  rw [msFeatures_insertion, msFeatures_insertion, Option.elim_some,
    features_restrict _ ht]
  exact Multiset.filter_le _ _

omit [DecidableEq F] in
/-- Obliteration removes the entire insertion while the syntactic leaf
and its datum stay in place — [senturia-marcolli-2025]'s reading of
Proposition 5.13, on which no morphology is inserted and the syntactic
tree is untouched. -/
theorem toSyntactic_obliterate (lex : Λ) (S : Nonplanar (F ⊕ Unit)) :
    toSyntactic (insertion lex none : Morphosyntactic F Λ)
      = toSyntactic (insertion lex (some S)) := by
  rw [toSyntactic_insertion, toSyntactic_insertion]

omit [DecidableEq F] in
@[simp] theorem msFeatures_obliterate (lex : Λ) :
    msFeatures (insertion lex none : Morphosyntactic F Λ) = 0 := by
  rw [msFeatures_insertion, Option.elim_none]

/-! ### One-step transformations and the post-syntactic semigroup

The DM operations act anywhere in a morphosyntactic tree: a step applies
a site transformation at the root of some subtree. Compositions of such
steps form [senturia-marcolli-2025] Definition 6.1's semigroups — the
post-syntactic semigroup generated by fusion and fission, and the full
Distributed Morphology semigroup adding impoverishment and obliteration.
Their action is the movable syntax-morphology boundary: `PostSyntactic`
preserves the total feature set exactly, and `Derivation` can only
shrink it. -/

/-- Close a site relation under congruence: apply it at the root or
inside one subtree. -/
inductive Step (R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop) :
    Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | here {T T'} : R T T' → Step R T T'
  | congr {x} {cs : Multiset (Morphosyntactic F Λ)} {T T'} : Step R T T' →
      Step R (Nonplanar.node x (T ::ₘ cs)) (Nonplanar.node x (T' ::ₘ cs))

/-- The fusion site relation: a syntactic cherry over two insertions
rewrites to a single insertion of the magma product, projecting one of
the two data. -/
inductive FuseAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lexHead lex₁ lex₂ : Λ) (S₁ S₂ : Nonplanar (F ⊕ Unit))
      (hhead : lexHead = lex₁ ∨ lexHead = lex₂) :
      FuseAt (fusionSite lex₁ lex₂ S₁ S₂) (insertion lexHead (some (fuse S₁ S₂)))

/-- The fission site relation: an insertion rewrites to a syntactic
cherry over the two restrictions determined by a partition
`B ∖ A = B₁ ⊔ B₂` of its bundle with copied residue `A`
([senturia-marcolli-2025] Definition 5.6). -/
inductive FissAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex lex₁ lex₂ : Λ) (A B₁ B₂ : Finset F) {t : RoseTree (F ⊕ Unit)}
      (ht : IsMorphological t) (hlex : lex = lex₁ ∨ lex = lex₂)
      (h₁ : Disjoint A B₁) (h₂ : Disjoint A B₂) (h₁₂ : Disjoint B₁ B₂)
      (hcover : ∀ f ∈ features (Nonplanar.mk t), f ∈ A ∪ B₁ ∪ B₂) :
      FissAt (insertion lex (some (Nonplanar.mk t)))
        (fissionSite lex₁ lex₂ (B₁ ∪ A) (B₂ ∪ A) (Nonplanar.mk t))

/-- The impoverishment site relation: the insertion is replaced by one
of its fission outputs. -/
inductive ImpovAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex : Λ) (kept : Finset F) {t : RoseTree (F ⊕ Unit)}
      (ht : IsMorphological t) :
      ImpovAt (insertion lex (some (Nonplanar.mk t)))
        (insertion lex (restrict kept (Nonplanar.mk t)))

/-- The obliteration site relation: the insertion is emptied, the
syntactic leaf and its datum staying in place. -/
inductive OblitAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex : Λ) (mo : Option (Nonplanar (F ⊕ Unit))) :
      OblitAt (insertion lex mo) (insertion lex none)

/-- Fission duplicates exactly the copied residue: with `B ∖ A`
partitioned into `B₁ ⊔ B₂` and `A` copied to both sides, the site's
feature multiset grows by precisely the `A`-part. `A = ∅` recovers
content invariance (`msFeatures_fission_partition`). -/
theorem msFeatures_fissionSite_copy (lex₁ lex₂ : Λ) {A B₁ B₂ : Finset F}
    (h₁ : Disjoint A B₁) (h₂ : Disjoint A B₂) (h₁₂ : Disjoint B₁ B₂)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t)
    (hcover : ∀ f ∈ features (Nonplanar.mk t), f ∈ A ∪ B₁ ∪ B₂) :
    msFeatures (fissionSite lex₁ lex₂ (B₁ ∪ A) (B₂ ∪ A) (Nonplanar.mk t))
      = features (Nonplanar.mk t)
        + (features (Nonplanar.mk t)).filter (· ∈ A) := by
  rw [msFeatures_fissionSite _ _ _ _ ht]
  refine Multiset.ext.mpr fun f => ?_
  have hcnt : f ∉ A → f ∉ B₁ → f ∉ B₂ →
      Multiset.count f (features (Nonplanar.mk t)) = 0 := by
    intro nA nB₁ nB₂
    refine Multiset.count_eq_zero.mpr fun hf => ?_
    rcases Finset.mem_union.mp (hcover f hf) with h | h
    · rcases Finset.mem_union.mp h with h | h
      exacts [nA h, nB₁ h]
    · exact nB₂ h
  simp only [Multiset.count_add, Multiset.count_filter, Finset.mem_union]
  by_cases hfA : f ∈ A
  · have nB₁ : f ∉ B₁ := fun hf => Finset.disjoint_left.mp h₁ hfA hf
    have nB₂ : f ∉ B₂ := fun hf => Finset.disjoint_left.mp h₂ hfA hf
    simp [hfA, nB₁, nB₂]
  · by_cases hfB₁ : f ∈ B₁
    · have nB₂ : f ∉ B₂ := fun hf => Finset.disjoint_left.mp h₁₂ hfB₁ hf
      simp [hfA, hfB₁, nB₂]
    · by_cases hfB₂ : f ∈ B₂
      · simp [hfA, hfB₁, hfB₂]
      · have h0 := hcnt hfA hfB₁ hfB₂
        simp only [features_mk] at h0
        simp [hfA, hfB₁, hfB₂, h0]

/-! ### Feature bookkeeping along the semigroups -/

omit [DecidableEq F] in
private theorem msFeatures_node_cons (x : (Λ × Option (Nonplanar (F ⊕ Unit))) ⊕ Unit)
    (T : Morphosyntactic F Λ) (cs : Multiset (Morphosyntactic F Λ)) :
    msFeatures (Nonplanar.node x (T ::ₘ cs))
      = msFeatures T
        + (((cs.map Nonplanar.leaves).sum).map insertionFeatures).sum := by
  rw [msFeatures, Nonplanar.leaves_node_cons, Multiset.map_add,
    Multiset.sum_add, msFeatures]

omit [DecidableEq F] in
private theorem numLeaves_node_cons (x : (Λ × Option (Nonplanar (F ⊕ Unit))) ⊕ Unit)
    (T : Morphosyntactic F Λ) (cs : Multiset (Morphosyntactic F Λ)) :
    (Nonplanar.node x (T ::ₘ cs)).numLeaves
      = T.numLeaves + Multiset.card ((cs.map Nonplanar.leaves).sum) := by
  rw [← Nonplanar.card_leaves, Nonplanar.leaves_node_cons, Multiset.card_add,
    Nonplanar.card_leaves]

omit [DecidableEq F] in
theorem FuseAt.msFeatures_eq {T T' : Morphosyntactic F Λ} (h : FuseAt T T') :
    msFeatures T' = msFeatures T := by
  cases h with
  | mk lexHead lex₁ lex₂ S₁ S₂ hhead => exact msFeatures_fuse ..

theorem FissAt.toFinset_msFeatures_eq {T T' : Morphosyntactic F Λ}
    (h : FissAt T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  cases h with
  | mk lex lex₁ lex₂ A B₁ B₂ ht hlex h₁ h₂ h₁₂ hcover =>
    rw [msFeatures_fissionSite_copy _ _ h₁ h₂ h₁₂ ht hcover,
      msFeatures_insertion, Option.elim_some, Multiset.toFinset_add,
      Multiset.toFinset_filter]
    exact Finset.union_eq_left.mpr (Finset.filter_subset _ _)

theorem ImpovAt.msFeatures_le {T T' : Morphosyntactic F Λ} (h : ImpovAt T T') :
    msFeatures T' ≤ msFeatures T := by
  cases h with
  | mk lex kept ht => exact msFeatures_impoverish_le _ _ ht

omit [DecidableEq F] in
theorem OblitAt.msFeatures_le {T T' : Morphosyntactic F Λ} (h : OblitAt T T') :
    msFeatures T' ≤ msFeatures T := by
  cases h with
  | mk lex mo =>
    rw [msFeatures_insertion, msFeatures_insertion, Option.elim_none]
    exact Multiset.zero_le _

omit [DecidableEq F] in
/-- A site-level feature-content identity transfers through the
congruence closure. -/
theorem Step.msFeatures_eq {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' → msFeatures T' = msFeatures T)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    msFeatures T' = msFeatures T := by
  induction h with
  | here h => exact hR h
  | congr _ ih => rw [msFeatures_node_cons, msFeatures_node_cons, ih]

omit [DecidableEq F] in
theorem Step.msFeatures_le {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' → msFeatures T' ≤ msFeatures T)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    msFeatures T' ≤ msFeatures T := by
  induction h with
  | here h => exact hR h
  | congr _ ih =>
    rw [msFeatures_node_cons, msFeatures_node_cons]
    exact add_le_add ih le_rfl

theorem Step.toFinset_msFeatures_eq
    {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' →
      (msFeatures T').toFinset = (msFeatures T).toFinset)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  induction h with
  | here h => exact hR h
  | congr _ ih =>
    rw [msFeatures_node_cons, msFeatures_node_cons, Multiset.toFinset_add,
      Multiset.toFinset_add, ih]

omit [DecidableEq F] in
/-- Fusion moves the boundary up: one syntactic leaf fewer, wherever it
applies. -/
theorem Step.numLeaves_fuse {T T' : Morphosyntactic F Λ}
    (h : Step FuseAt T T') : T'.numLeaves + 1 = T.numLeaves := by
  induction h with
  | here h =>
    cases h with
    | mk lexHead lex₁ lex₂ S₁ S₂ hhead =>
      rw [show (insertion lexHead (some (fuse S₁ S₂)) : Morphosyntactic F Λ).numLeaves
          = 1 from rfl, ← Nonplanar.card_leaves, fusionSite, insertion, insertion,
        leaves_node_pair_leaf]
      rfl
  | congr _ ih => rw [numLeaves_node_cons, numLeaves_node_cons]; omega

/-- Fission moves the boundary down: one syntactic leaf more, wherever
it applies. -/
theorem Step.numLeaves_fiss {T T' : Morphosyntactic F Λ}
    (h : Step FissAt T T') : T.numLeaves + 1 = T'.numLeaves := by
  induction h with
  | here h =>
    cases h with
    | mk lex lex₁ lex₂ A B₁ B₂ ht hlex h₁ h₂ h₁₂ hcover =>
      rw [show (insertion lex (some (Nonplanar.mk _)) : Morphosyntactic F Λ).numLeaves
          = 1 from rfl, ← Nonplanar.card_leaves, fissionSite, insertion, insertion,
        leaves_node_pair_leaf]
      rfl
  | congr _ ih => rw [numLeaves_node_cons, numLeaves_node_cons]; omega

/-! ### The two semigroups and the movable boundary -/

/-- The post-syntactic semigroup: compositions of fusion and fission
steps ([senturia-marcolli-2025] Definition 6.1). -/
def PostSyntactic : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop :=
  Relation.ReflTransGen fun T T' => Step FuseAt T T' ∨ Step FissAt T T'

/-- A derivation of the full Distributed Morphology semigroup:
post-syntactic steps together with impoverishment and obliteration
([senturia-marcolli-2025] Definition 6.1). -/
def Derivation : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop :=
  Relation.ReflTransGen fun T T' =>
    (Step FuseAt T T' ∨ Step FissAt T T') ∨
      (Step ImpovAt T T' ∨ Step OblitAt T T')

/-- The movable boundary, feature side: the post-syntactic semigroup
never creates or destroys a feature. Any composition of fusions and
fissions leaves the total feature set invariant — the operations only
move the boundary between syntax and morphology. -/
theorem PostSyntactic.toFinset_msFeatures_eq {T T' : Morphosyntactic F Λ}
    (h : PostSyntactic T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
    rcases step with hf | hs
    · rw [Step.msFeatures_eq (fun h => h.msFeatures_eq) hf, ih]
    · rw [Step.toFinset_msFeatures_eq (fun h => h.toFinset_msFeatures_eq) hs, ih]

/-- Along the full Distributed Morphology semigroup the feature set can
only shrink: fusion and fission preserve it, impoverishment and
obliteration delete. -/
theorem Derivation.toFinset_msFeatures_subset {T T' : Morphosyntactic F Λ}
    (h : Derivation T T') :
    (msFeatures T').toFinset ⊆ (msFeatures T).toFinset := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ step ih =>
    refine Finset.Subset.trans ?_ ih
    rcases step with (hf | hs) | (hi | ho)
    · rw [Step.msFeatures_eq (fun h => h.msFeatures_eq) hf]
    · rw [Step.toFinset_msFeatures_eq (fun h => h.toFinset_msFeatures_eq) hs]
    · exact Multiset.toFinset_subset.mpr
        (Multiset.subset_of_le (Step.msFeatures_le (fun h => h.msFeatures_le) hi))
    · exact Multiset.toFinset_subset.mpr
        (Multiset.subset_of_le (Step.msFeatures_le (fun h => h.msFeatures_le) ho))

/-! ### The economy of bivalent features

[senturia-marcolli-2025] Remark 2.3: with `n` feature categories and
three valuations (+, −, unvalued), the bivalent inventory has `n + 3`
generating objects against the `3 n` features a privative encoding
needs, strictly fewer for more than one category. -/

theorem bivalent_economy {n : ℕ} (h : 1 < n) : n + 3 < 3 * n := by omega

end SenturiaMarcolli2025
