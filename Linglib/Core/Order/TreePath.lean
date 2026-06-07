import Mathlib.Data.List.Infix
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.Atoms
import Mathlib.Order.SuccPred.Tree

/-!
# Tree Positions: `TreePath` and the Rooted-Tree Order Stack

A `TreePath` is a position in a rose tree, encoded as a list of child
indices (a Gorn address). Under the prefix order (dominance), `TreePath`
instantiates mathlib's order-theoretic rooted-tree stack
(`Mathlib.Order.SuccPred.Tree`):

| instance              | linguistic reading                          |
|-----------------------|---------------------------------------------|
| `OrderBot`            | the root position `⟨[]⟩`                    |
| `PredOrder`           | parent (mother-of): drop the last index     |
| `IsPredArchimedean`   | finite ancestor chains                      |
| `SemilatticeInf`      | least common ancestor — the smallest        |
|                       | constituent position containing both        |

`TreePath` itself is the *full* ℕ-branching tree of positions; a
concrete tree's valid positions form a prefix-closed subset (see
`Core/Order/Branching.lean`), which inherits the stack.

Moved here from `Syntax/Tree/Basic.lean`: positions are pure
combinatorics, instantiable by any rose-tree carrier (CFG derivation
trees via Gorn addresses, Hopf-algebra rooted trees, constituency
trees) without importing linguistic theory.
-/

/-! ### Generic list API: longest common prefix

Upstream-shaped for `Mathlib/Data/List/Prefix.lean` (no
`commonPrefix` exists in mathlib or Batteries as of 2026-06). -/

namespace List

/-- Longest common prefix of two lists. -/
def commonPrefix {α : Type*} [DecidableEq α] : List α → List α → List α
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

theorem commonPrefix_prefix_left {α : Type*} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), commonPrefix l₁ l₂ <+: l₁
  | [], _ => by simp [commonPrefix]
  | _ :: _, [] => by simp [commonPrefix]
  | a :: as, b :: bs => by
    by_cases h : a = b
    · simpa [commonPrefix, h] using commonPrefix_prefix_left as bs
    · simp [commonPrefix, h]

theorem commonPrefix_prefix_right {α : Type*} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), commonPrefix l₁ l₂ <+: l₂
  | [], _ => by simp [commonPrefix]
  | _ :: _, [] => by simp [commonPrefix]
  | a :: as, b :: bs => by
    by_cases h : a = b
    · subst h
      simpa [commonPrefix] using commonPrefix_prefix_right as bs
    · simp [commonPrefix, h]

theorem prefix_commonPrefix {α : Type*} [DecidableEq α] :
    ∀ {r l₁ l₂ : List α}, r <+: l₁ → r <+: l₂ → r <+: commonPrefix l₁ l₂
  | [], _, _, _, _ => List.nil_prefix
  | x :: rs, l₁, l₂, h₁, h₂ => by
    obtain ⟨s₁, hs₁⟩ := h₁
    obtain ⟨s₂, hs₂⟩ := h₂
    subst hs₁ hs₂
    simpa [commonPrefix] using
      prefix_commonPrefix (r := rs) (List.prefix_append _ _) (List.prefix_append _ _)

theorem commonPrefix_comm {α : Type*} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), commonPrefix l₁ l₂ = commonPrefix l₂ l₁
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    by_cases h : a = b
    · subst h
      simp [commonPrefix, commonPrefix_comm as bs]
    · simp [commonPrefix, h, Ne.symm h]

/-- A prefix agrees with its extension below its length. -/
theorem IsPrefix.getElem?_eq_of_lt {α : Type*} {l₁ l₂ : List α}
    (h : l₁ <+: l₂) {i : Nat} (hi : i < l₁.length) : l₂[i]? = l₁[i]? := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getElem?_append_left hi]

/-- A prefix extends by the element sitting at its length. -/
theorem append_singleton_prefix_of_getElem? {α : Type*} {cp l : List α}
    (h : cp <+: l) {i : α} (hi : l[cp.length]? = some i) :
    cp ++ [i] <+: l := by
  obtain ⟨s, rfl⟩ := h
  rcases s with _ | ⟨x, s'⟩
  · simp at hi
  · rw [List.getElem?_append_right (le_refl _)] at hi
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨s', by simp⟩

/-- The lists genuinely diverge just past their common prefix. -/
theorem getElem?_commonPrefix_ne {α : Type*} [DecidableEq α] :
    ∀ {l₁ l₂ : List α} {i j : α},
      l₁[(commonPrefix l₁ l₂).length]? = some i →
      l₂[(commonPrefix l₁ l₂).length]? = some j → i ≠ j
  | [], _, i, j => by simp
  | _ :: _, [], i, j => by simp [commonPrefix]
  | a :: as, b :: bs, i, j => by
    by_cases h : a = b
    · subst h
      simp only [commonPrefix, if_pos rfl, List.length_cons,
        List.getElem?_cons_succ]
      exact getElem?_commonPrefix_ne
    · simp only [commonPrefix, if_neg h, List.length_nil,
        List.getElem?_cons_zero, Option.some.injEq]
      rintro rfl rfl
      exact h

end List

namespace Core.Order

/-- A position (Gorn address) in a rose tree: a list of child indices.
The empty path is the root. -/
structure TreePath where
  /-- The underlying list of child indices. -/
  toList : List Nat
  deriving DecidableEq, Repr

namespace TreePath

/-- Dominance order: `p ≤ q` iff `p` is a prefix of `q` (p dominates q). -/
instance : LE TreePath := ⟨fun p q => p.toList <+: q.toList⟩

theorem le_def {p q : TreePath} : p ≤ q ↔ p.toList <+: q.toList := Iff.rfl

instance : PartialOrder TreePath where
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm a b h₁ h₂ := by
    cases a; cases b
    have := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le
    simpa using this

/-- Two prefixes of the same list are comparable: the **Connected
Ancestor Condition (CAC)** for the prefix order ([barker-pullum-1990]'s
Definition 15). Delegates to `List.prefix_or_prefix_of_prefix`. -/
theorem prefix_or_prefix {p q r : TreePath} (hp : p ≤ r) (hq : q ≤ r) :
    p ≤ q ∨ q ≤ p :=
  List.prefix_or_prefix_of_prefix hp hq

/-! ### The root: `OrderBot` -/

instance : OrderBot TreePath where
  bot := ⟨[]⟩
  bot_le _ := List.nil_prefix

@[simp] theorem bot_toList : (⊥ : TreePath).toList = [] := rfl

theorem length_strictMono {p q : TreePath} (h : p < q) :
    p.toList.length < q.toList.length := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp h
  refine lt_of_le_of_ne hle.length_le fun hlen => hne ?_
  cases p; cases q
  simpa using hle.eq_of_length hlen

/-! ### Parent: `PredOrder`

`Order.pred` is mother-of: drop the last child index. The root is its
own predecessor (`pred ⊥ = ⊥`), matching mathlib's convention that
`pred` of a minimal element is itself. -/

/-- The parent position: drop the last index. Root's parent is itself. -/
def parent (p : TreePath) : TreePath := ⟨p.toList.dropLast⟩

@[simp] theorem parent_toList (p : TreePath) :
    p.parent.toList = p.toList.dropLast := rfl

theorem parent_le (p : TreePath) : p.parent ≤ p := by
  simpa [parent, le_def] using List.dropLast_prefix p.toList

/-- A non-root position is properly dominated by its parent — the
**Single Mother Condition** reading: every node except the root has a
mother that is a proper ancestor. (`Order.pred ⊥ = ⊥` is mathlib's
convention; linguistic axioms quantifying over mothers need this
`≠ ⊥` guard.) -/
theorem parent_lt_of_ne_bot {p : TreePath} (hp : p ≠ ⊥) : p.parent < p := by
  refine lt_of_le_of_ne (parent_le p) fun heq => hp ?_
  have := congrArg (List.length ∘ TreePath.toList) heq
  simp only [Function.comp, parent_toList, List.length_dropLast] at this
  cases p with | mk l =>
  cases l with
  | nil => rfl
  | cons a as => simp at this

theorem le_parent_of_lt {p q : TreePath} (h : p < q) : p ≤ q.parent := by
  obtain ⟨⟨s, hs⟩, hne⟩ := lt_iff_le_and_ne.mp h
  have hslen : s ≠ [] := by
    rintro rfl
    exact hne (by cases p; cases q; simpa using hs)
  refine le_def.mpr ?_
  rw [parent_toList, ← hs, List.dropLast_append_of_ne_nil hslen]
  exact List.prefix_append _ _

instance : PredOrder TreePath where
  pred := parent
  pred_le := parent_le
  min_of_le_pred {p} h := by
    rcases eq_or_ne p ⊥ with rfl | hne
    · exact isMin_bot
    · exfalso
      have hlt : p.parent < p := by
        refine lt_of_le_of_ne (parent_le p) fun heq => hne ?_
        have := congrArg (List.length ∘ TreePath.toList) heq
        simp only [Function.comp, parent_toList, List.length_dropLast] at this
        cases p with | mk l =>
        cases l with
        | nil => rfl
        | cons a as => simp at this
      exact absurd (le_antisymm h hlt.le) hlt.ne'
  le_pred_of_lt := le_parent_of_lt

@[simp] theorem pred_eq_parent (p : TreePath) : Order.pred p = p.parent := rfl

/-! ### Finite depth: `IsPredArchimedean` -/

instance : IsPredArchimedean TreePath where
  exists_pred_iterate_of_le {p q} h := by
    refine ⟨q.toList.length - p.toList.length, ?_⟩
    obtain ⟨s, hs⟩ := h
    induction s using List.reverseRecOn generalizing q with
    | nil =>
      cases p; cases q
      simp_all
    | append_singleton s a ih =>
      have hq : q.parent = ⟨p.toList ++ s⟩ := by
        cases q with | mk l =>
        simp only [parent]
        congr 1
        have hs' : p.toList ++ (s ++ [a]) = l := hs
        rw [← hs', ← List.append_assoc, List.dropLast_concat]
      have hlen : q.toList.length = p.toList.length + s.length + 1 := by
        have hs' : p.toList ++ (s ++ [a]) = q.toList := hs
        rw [← hs']; simp [List.length_append]; omega
      have hstep : q.toList.length - p.toList.length
          = (p.toList.length + s.length - p.toList.length) + 1 := by omega
      rw [hstep, Function.iterate_succ_apply, pred_eq_parent, hq]
      have := ih (q := ⟨p.toList ++ s⟩) rfl
      simpa [List.length_append] using this

/-! ### Least common ancestor: `SemilatticeInf`

`p ⊓ q` is the longest common prefix — the deepest position dominating
both, i.e. the smallest constituent position containing both.
(`List.commonPrefix` and its lemmas live in the `_root_.List`
namespace at the top of this file; they are generic list API,
upstream-shaped for `Mathlib/Data/List/Prefix.lean`.) -/

instance : SemilatticeInf TreePath where
  inf p q := ⟨List.commonPrefix p.toList q.toList⟩
  inf_le_left p q := List.commonPrefix_prefix_left p.toList q.toList
  inf_le_right p q := List.commonPrefix_prefix_right p.toList q.toList
  le_inf _ _ _ h₁ h₂ := List.prefix_commonPrefix h₁ h₂

/-- Least common ancestor, by its linguistic name. `lca p q` is the
deepest position dominating both `p` and `q` — the smallest constituent
position containing both. -/
abbrev lca (p q : TreePath) : TreePath := p ⊓ q

/-! ### Sisterhood -/

/-- Sisters: distinct positions with the same parent. -/
def IsSister (p q : TreePath) : Prop := p ≠ q ∧ p.parent = q.parent

theorem isSister_symm {p q : TreePath} (h : IsSister p q) : IsSister q p :=
  ⟨h.1.symm, h.2.symm⟩

/-! ### Linear precedence

The PF-side order that dominance forgets: `p` precedes `q` iff their
paths diverge at some common prefix with `p` taking an earlier branch.
Defined only between dominance-incomparable positions
(`Precedes.not_le`, `Precedes.not_ge`) — a node neither precedes nor
follows its ancestors, the ID/LP division of labor. -/

/-- `p` linearly precedes `q`: at some shared position `r`, `p`
continues into an earlier child than `q`. -/
def Precedes (p q : TreePath) : Prop :=
  ∃ (r : List Nat) (i j : Nat), i < j ∧
    (r ++ [i]) <+: p.toList ∧ (r ++ [j]) <+: q.toList

namespace Precedes

/-- Two extensions of the same position by single indices that are both
prefixes of one path carry the same index. -/
private theorem branch_unique {r : List Nat} {i j : Nat} {l : List Nat}
    (hi : (r ++ [i]) <+: l) (hj : (r ++ [j]) <+: l) : i = j := by
  have hcomp := List.prefix_or_prefix_of_prefix hi hj
  have hlen : (r ++ [i]).length = (r ++ [j]).length := by simp
  rcases hcomp with h | h
  · simpa using List.append_inj_right (h.eq_of_length hlen) rfl
  · simpa using (List.append_inj_right (h.eq_of_length hlen.symm) rfl).symm

theorem irrefl (p : TreePath) : ¬ Precedes p p := by
  rintro ⟨r, i, j, hij, hi, hj⟩
  exact absurd (branch_unique hi hj) (Nat.ne_of_lt hij)

/-- Precedence excludes dominance. -/
theorem not_le {p q : TreePath} (h : Precedes p q) : ¬ p ≤ q := by
  rintro hle
  obtain ⟨r, i, j, hij, hi, hj⟩ := h
  exact absurd (branch_unique (hi.trans hle) hj) (Nat.ne_of_lt hij)

/-- Precedence excludes being dominated. -/
theorem not_ge {p q : TreePath} (h : Precedes p q) : ¬ q ≤ p := by
  rintro hle
  obtain ⟨r, i, j, hij, hi, hj⟩ := h
  exact absurd (branch_unique hi (hj.trans hle)) (Nat.ne_of_lt hij)

/-- **Nontangling** (downward inheritance; the third clause of Wall's
tree definition, [barker-pullum-1990] Definition 1): precedence is
inherited by descendants. -/
theorem mono {p q p' q' : TreePath} (h : Precedes p q)
    (hp : p ≤ p') (hq : q ≤ q') : Precedes p' q' := by
  obtain ⟨r, i, j, hij, hi, hj⟩ := h
  exact ⟨r, i, j, hij, hi.trans hp, hj.trans hq⟩

/-- If `r ++ [i]` is a prefix of `l`, then `l` carries `i` at index
`r.length`. -/
private theorem getElem?_of_append_singleton_prefix {r : List Nat} {i : Nat}
    {l : List Nat} (h : (r ++ [i]) <+: l) : l[r.length]? = some i := by
  obtain ⟨s, rfl⟩ := h
  rw [List.append_assoc, List.getElem?_append_right (le_refl _)]
  simp

/-- The divergence index of `Precedes` is exactly the common-prefix
length: `p` precedes `q` iff at index `(commonPrefix p q).length` both
paths continue and `p`'s branch index is smaller. The computable
characterization behind `Decidable (Precedes p q)`. -/
theorem precedes_iff {p q : TreePath} :
    Precedes p q ↔
    ∃ i j, p.toList[(List.commonPrefix p.toList q.toList).length]? = some i ∧
      q.toList[(List.commonPrefix p.toList q.toList).length]? = some j ∧ i < j := by
  set cp := List.commonPrefix p.toList q.toList with hcp
  constructor
  · rintro ⟨r, i, j, hij, hi, hj⟩
    have hrp : r <+: p.toList := (List.prefix_append r [i]).trans hi
    have hrq : r <+: q.toList := (List.prefix_append r [j]).trans hj
    have hrcp : r <+: cp := List.prefix_commonPrefix hrp hrq
    have hd : cp.length = r.length := by
      refine le_antisymm ?_ hrcp.length_le
      by_contra hlt
      push_neg at hlt
      have hpi := getElem?_of_append_singleton_prefix hi
      have hqj := getElem?_of_append_singleton_prefix hj
      have h1 := (List.commonPrefix_prefix_left p.toList q.toList).getElem?_eq_of_lt hlt
      have h2 := (List.commonPrefix_prefix_right p.toList q.toList).getElem?_eq_of_lt hlt
      rw [hpi] at h1
      rw [hqj] at h2
      exact absurd (Option.some_injective _ (h1.trans h2.symm))
        (Nat.ne_of_lt hij)
    rw [hd]
    exact ⟨i, j, getElem?_of_append_singleton_prefix hi,
      getElem?_of_append_singleton_prefix hj, hij⟩
  · rintro ⟨i, j, hpi, hqj, hij⟩
    refine ⟨cp, i, j, hij, ?_, ?_⟩
    · have := List.commonPrefix_prefix_left p.toList q.toList
      exact List.append_singleton_prefix_of_getElem? this hpi
    · have := List.commonPrefix_prefix_right p.toList q.toList
      exact List.append_singleton_prefix_of_getElem? this hqj

instance (p q : TreePath) : Decidable (Precedes p q) := by
  rcases hp : p.toList[(List.commonPrefix p.toList q.toList).length]? with _ | i
  · exact .isFalse fun h => by
      obtain ⟨i, _, hpi, _, _⟩ := precedes_iff.mp h
      rw [hp] at hpi
      simp at hpi
  · rcases hq : q.toList[(List.commonPrefix p.toList q.toList).length]? with _ | j
    · exact .isFalse fun h => by
        obtain ⟨_, j, _, hqj, _⟩ := precedes_iff.mp h
        rw [hq] at hqj
        simp at hqj
    · refine decidable_of_iff (i < j) ⟨fun hij => precedes_iff.mpr ⟨i, j, hp, hq, hij⟩,
        fun h => ?_⟩
      obtain ⟨i', j', hpi, hqj, hij⟩ := precedes_iff.mp h
      rw [hp] at hpi
      rw [hq] at hqj
      obtain rfl := Option.some_injective _ hpi
      obtain rfl := Option.some_injective _ hqj
      exact hij

/-- Precedence is asymmetric. -/
theorem asymm {p q : TreePath} (h : Precedes p q) : ¬ Precedes q p := by
  intro h'
  obtain ⟨i, j, hpi, hqj, hij⟩ := precedes_iff.mp h
  obtain ⟨i', j', hqi', hpj', hij'⟩ := precedes_iff.mp h'
  rw [List.commonPrefix_comm] at hqi' hpj'
  rw [hpi] at hpj'
  rw [hqj] at hqi'
  obtain rfl := Option.some_injective _ hpj'
  obtain rfl := Option.some_injective _ hqi'
  omega

/-- Prepending a shared child index preserves precedence. -/
theorem cons {p q : TreePath} (i : Nat) (h : Precedes p q) :
    Precedes ⟨i :: p.toList⟩ ⟨i :: q.toList⟩ := by
  obtain ⟨r, a, b, hab, ha, hb⟩ := h
  exact ⟨i :: r, a, b, hab,
    (List.cons_prefix_cons).mpr ⟨rfl, ha⟩, (List.cons_prefix_cons).mpr ⟨rfl, hb⟩⟩

/-- Positions under distinct child indices are precedence-ordered by
those indices (divergence at the root). -/
theorem of_index_lt {i j : Nat} (hij : i < j) (p q : TreePath) :
    Precedes ⟨i :: p.toList⟩ ⟨j :: q.toList⟩ :=
  ⟨[], i, j, hij, by simpa using List.cons_prefix_cons.mpr ⟨rfl, p.toList.nil_prefix⟩,
    by simpa using List.cons_prefix_cons.mpr ⟨rfl, q.toList.nil_prefix⟩⟩

/-- **Totality over the dominance remainder**: any two positions are
dominance-comparable or precedence-ordered — the exhaustiveness that
linear-precedence statements need. -/
theorem trichotomy (p q : TreePath) :
    p ≤ q ∨ q ≤ p ∨ Precedes p q ∨ Precedes q p := by
  set cp := List.commonPrefix p.toList q.toList with hcp
  rcases hpd : p.toList[cp.length]? with _ | i
  · -- `p` ends at or before the divergence: `p = cp ≤ q`.
    left
    have hple : p.toList.length ≤ cp.length := by
      by_contra hlt
      push_neg at hlt
      exact absurd hpd (by simp [List.getElem?_eq_some_iff, hlt])
    have : p.toList = cp :=
      (List.commonPrefix_prefix_left p.toList q.toList).eq_of_length
        (le_antisymm (List.commonPrefix_prefix_left p.toList q.toList).length_le hple) |>.symm
    exact le_def.mpr (this ▸ List.commonPrefix_prefix_right p.toList q.toList)
  · rcases hqd : q.toList[cp.length]? with _ | j
    · right; left
      have hqle : q.toList.length ≤ cp.length := by
        by_contra hlt
        push_neg at hlt
        exact absurd hqd (by simp [List.getElem?_eq_some_iff, hlt])
      have : q.toList = cp :=
        (List.commonPrefix_prefix_right p.toList q.toList).eq_of_length
          (le_antisymm (List.commonPrefix_prefix_right p.toList q.toList).length_le hqle) |>.symm
      exact le_def.mpr (this ▸ List.commonPrefix_prefix_left p.toList q.toList)
    · have hne : i ≠ j := List.getElem?_commonPrefix_ne hpd hqd
      rcases Nat.lt_or_ge i j with hij | hge
      · right; right; left
        exact precedes_iff.mpr ⟨i, j, hpd, hqd, hij⟩
      · right; right; right
        exact precedes_iff.mpr ⟨j, i, by rwa [List.commonPrefix_comm],
          by rwa [List.commonPrefix_comm], lt_of_le_of_ne hge (Ne.symm hne)⟩

end Precedes

/-! ### The bundled mathlib rooted tree

`TreePath` carries all four classes of `Mathlib.Order.SuccPred.Tree`'s
`RootedTree`; the bundling makes the alignment true by construction
and opens mathlib's `findAtom`/`subtree` API. -/

/-- `TreePath` as a mathlib `RootedTree`. -/
def rootedTree : RootedTree := ⟨TreePath⟩

end TreePath

end Core.Order
