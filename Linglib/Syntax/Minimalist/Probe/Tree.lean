import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Minimalist.HeadFunction

/-!
# Probe search, grounded in the tree via the head function
[marcolli-chomsky-berwick-2025]

`Probe.search` (`Probe/Basic.lean`) is relativized search over a flat goal
sequence `List α`. This file supplies the *missing canonical linearization* that
`Agree.lean` flags as non-definitional: the goal sequence a probe searches over a
`SyntacticObject` is **derived from the tree by the head function `h`** — the
head tokens of `T`'s accessible terminal positions, in the planar (c-command)
order MCB's section `σ_L` induces. So `Probe` stops floating free of the Merge
algebra: search reads the same `h`-ordered tree-walk that linearization and head
selection do.

The keystone is `indiscriminate_searchTree_eq_head`: bare-minimality search
([halpert-2012]'s `L⁰`, `Probe.indiscriminate`) over a tree recovers
`HeadFunction.head` — the structural fact that a probe with no relativization
finds the head the Externalization section computes.

The leaf-level goal sequence (`accessibleHeads = leafTokens`) is the realization
that suffices for terminal-head probing; the phrasal-goal generalization
(probing over all accessible subtrees via `head`) is the natural extension.
-/

namespace Minimalist

/-! ### Planar-yield head lemmas -/

private theorem leafTokensPlanar_ne_nil (fm : FreeMagma (LIToken ⊕ Nat)) :
    leafTokensPlanar fm ≠ [] := by
  induction fm with
  | ih1 x => cases x <;> simp [leafTokensPlanar]
  | ih2 l r ihl _ =>
    intro hcontra
    rw [leafTokensPlanar_mul] at hcontra
    exact ihl (List.append_eq_nil_iff.mp hcontra).1

/-- The first leaf in planar order is the leftmost leaf — `head?` of the
    planar leaf list is the harmonic head-initial head. -/
private theorem head?_leafTokensPlanar (fm : FreeMagma (LIToken ⊕ Nat)) :
    (leafTokensPlanar fm).head? = some (leftmostLeafPlanar fm) := by
  induction fm with
  | ih1 x => cases x <;> rfl
  | ih2 l r ihl _ =>
    show (leafTokensPlanar l ++ leafTokensPlanar r).head? = some (leftmostLeafPlanar l)
    cases hl : leafTokensPlanar l with
    | nil => exact absurd hl (leafTokensPlanar_ne_nil l)
    | cons x xs => rw [hl] at ihl; simpa using ihl

/-! ### The goal sequence and tree search -/

/-- The goal sequence a probe searches over `T`: the head tokens of `T`'s
    accessible terminal positions, in the planar (c-command) order induced by
    the head function `h`. The flat `List` that `Probe.search` consumes, now
    *derived* from the tree rather than stipulated. (Leaf-level realization;
    the phrasal-goal generalization over all accessible subtrees is the natural
    extension.) -/
def HeadFunction.accessibleHeads (h : HeadFunction) (T : SyntacticObject) :
    List LIToken :=
  h.leafTokens T

/-- Searching a syntactic object: a probe searches its `h`-induced goal
    sequence. The list-vs-tree bridge made definitional via the head function. -/
def Probe.searchTree (p : Probe LIToken) (h : HeadFunction) (T : SyntacticObject) :
    Option LIToken :=
  p.search (h.accessibleHeads T)

@[simp] theorem Probe.searchTree_eq (p : Probe LIToken) (h : HeadFunction)
    (T : SyntacticObject) :
    p.searchTree h T = p.search (h.leafTokens T) := rfl

/-- A goal found by tree search is one of the tree's accessible heads. -/
theorem Probe.searchTree_mem {p : Probe LIToken} {h : HeadFunction}
    {T : SyntacticObject} {a : LIToken} (hfound : p.searchTree h T = some a) :
    a ∈ h.accessibleHeads T :=
  Probe.mem_of_search_eq_some hfound

/-- The accessible heads of a single leaf are just that leaf's token. -/
theorem HeadFunction.accessibleHeads_leaf (h : HeadFunction) (tok : LIToken) :
    h.accessibleHeads (.leaf tok) = [tok] := by
  rw [HeadFunction.accessibleHeads, HeadFunction.leafTokens,
    show (SyntacticObject.leaf tok : SyntacticObject) = FreeCommMagma.of (.inl tok)
      from rfl, h.section_.σ_of]
  rfl

/-- Probing a single leaf finds its token iff the probe sees it. -/
theorem Probe.searchTree_leaf (p : Probe LIToken) (h : HeadFunction)
    (tok : LIToken) :
    p.searchTree h (.leaf tok) = if p.vis tok then some tok else none := by
  rw [Probe.searchTree, h.accessibleHeads_leaf, Probe.search, List.find?_cons,
    List.find?_nil]
  cases p.vis tok <;> rfl

/-! ### Keystone: bare-minimality search finds the head -/

/-- The indiscriminate probe searches by `head?` (it sees every goal, so the
    closest one is the first). -/
theorem Probe.indiscriminate_search_eq_head? (goals : List LIToken) :
    (Probe.indiscriminate : Probe LIToken).search goals = goals.head? := by
  cases goals with
  | nil => rfl
  | cons x xs => rfl

/-- **Keystone.** Bare-minimality search ([halpert-2012]'s `L⁰`,
    `Probe.indiscriminate`) over a tree recovers the head function's head
    (harmonic head-initial): the unrelativized probe, grounded in the tree via
    `h`, finds exactly the head that Externalization's section computes. `Probe`
    search and the Merge algebra read one tree-walk. -/
theorem Probe.indiscriminate_searchTree_eq_head (h : HeadFunction)
    (hinit : h.headSide = .initial) (T : SyntacticObject) :
    (Probe.indiscriminate : Probe LIToken).searchTree h T = some (h.head T) := by
  rw [Probe.searchTree, HeadFunction.accessibleHeads,
    Probe.indiscriminate_search_eq_head?, HeadFunction.leafTokens,
    head?_leafTokensPlanar, HeadFunction.head, HeadFunction.headAtVertex, hinit]

end Minimalist
