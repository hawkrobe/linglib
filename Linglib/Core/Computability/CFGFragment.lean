import Linglib.Core.Computability.CFGTree

/-!
# Partial derivation trees (fragments) for context-free grammars

@cite{odonnell-2015}

A *fragment* of a context-free grammar `g` is a partial derivation
tree some of whose leaves are nonterminal "open slots" rather than
terminal symbols. Fragments are the units of storage in fragment
grammars (@cite{odonnell-2015} §2.3.6) and adaptor grammars
(§2.3.4): a fragment-grammar analysis of an utterance partitions the
full derivation tree into fragments stored in memoized Pitman–Yor
tables.

This file provides the partial-tree data type and the embedding from
`CFGTree` (which represents complete derivations only).

## Main definitions

- `CFGFragment T N` — a derivation tree some of whose leaves are
  open NT slots rather than terminals. Internal nodes carry an `N`,
  leaves carry a `Symbol T N`.
- `CFGFragment.yieldT` / `yieldNT` — terminal yield (ignoring open
  slots) and open-slot list, both left-to-right.
- `CFGFragment.isComplete` — `true` iff the fragment has no open
  slots.
- `CFGFragment.ofCFGTree` — embedding of complete derivations.

## Relation to `CFGTree`

`CFGTree T N` is a derivation tree where every leaf carries a
terminal `T`. `CFGFragment T N` allows leaves to carry either a
terminal `T` or an open nonterminal `N`. Every `CFGTree` embeds as
a complete `CFGFragment` via `ofCFGTree`; the inverse projection
(complete fragment → `CFGTree`) and the round-trip theorems are
deferred to a Phase 3 file when fragment-grammar composition needs
them.

## References

- @cite{odonnell-2015} §2.3.6 (fragment grammars), §3.1.5 (DOP
  prefix function).
- `Mathlib.Computability.ContextFreeGrammar` for the `Symbol T N`
  sum type used at leaves.
-/

/-- A partial derivation tree of a CFG: leaves carry a `Symbol T N`
    (terminal or open nonterminal slot); internal nodes carry an
    `N` and a list of children. -/
inductive CFGFragment (T N : Type) where
  /-- Leaf carrying either a terminal or an open NT slot. -/
  | leaf (s : Symbol T N) : CFGFragment T N
  /-- Internal node with nonterminal label and children. -/
  | node (nt : N) (children : List (CFGFragment T N)) : CFGFragment T N

namespace CFGFragment

variable {T N : Type}

mutual
/-- Terminal yield, ignoring open NT slots, left to right. -/
def yieldT : CFGFragment T N → List T
  | .leaf (.terminal t) => [t]
  | .leaf (.nonterminal _) => []
  | .node _ cs => yieldTList cs

/-- Concatenated terminal yields of a list of fragments. -/
def yieldTList : List (CFGFragment T N) → List T
  | [] => []
  | f :: fs => f.yieldT ++ yieldTList fs
end

mutual
/-- The list of open NT slots at the leaves, left to right. -/
def yieldNT : CFGFragment T N → List N
  | .leaf (.terminal _) => []
  | .leaf (.nonterminal n) => [n]
  | .node _ cs => yieldNTList cs

/-- Concatenated open-slot lists of a list of fragments. -/
def yieldNTList : List (CFGFragment T N) → List N
  | [] => []
  | f :: fs => f.yieldNT ++ yieldNTList fs
end

mutual
/-- `true` iff the fragment has no open NT slots — i.e. it is a
    complete derivation tree. -/
def isComplete : CFGFragment T N → Bool
  | .leaf (.terminal _) => true
  | .leaf (.nonterminal _) => false
  | .node _ cs => isCompleteList cs

/-- `true` iff every fragment in the list is complete. -/
def isCompleteList : List (CFGFragment T N) → Bool
  | [] => true
  | f :: fs => f.isComplete && isCompleteList fs
end

mutual
/-- Embed a `CFGTree` (which has only terminal leaves) as a complete
    `CFGFragment`. -/
def ofCFGTree : CFGTree T N → CFGFragment T N
  | .leaf t => .leaf (.terminal t)
  | .node nt cs => CFGFragment.node nt (ofCFGTreeList cs)

/-- Pointwise lift of `ofCFGTree` to lists. -/
def ofCFGTreeList : List (CFGTree T N) → List (CFGFragment T N)
  | [] => []
  | t :: ts => ofCFGTree t :: ofCFGTreeList ts
end

mutual
/-- `ofCFGTree` always produces a complete fragment. -/
theorem ofCFGTree_isComplete (t : CFGTree T N) :
    (ofCFGTree t).isComplete = true := by
  match t with
  | .leaf _ => rfl
  | .node _ cs =>
    show isCompleteList (ofCFGTreeList cs) = true
    exact ofCFGTreeList_isCompleteList cs

/-- List version of `ofCFGTree_isComplete`. -/
theorem ofCFGTreeList_isCompleteList (ts : List (CFGTree T N)) :
    isCompleteList (ofCFGTreeList ts) = true := by
  match ts with
  | [] => rfl
  | t :: rest =>
    show ((ofCFGTree t).isComplete && isCompleteList (ofCFGTreeList rest)) = true
    rw [ofCFGTree_isComplete t, ofCFGTreeList_isCompleteList rest]
    rfl
end

mutual
/-- Yields agree under the `ofCFGTree` embedding. -/
theorem yieldT_ofCFGTree (t : CFGTree T N) :
    (ofCFGTree t).yieldT = t.yield := by
  match t with
  | .leaf _ => rfl
  | .node _ cs =>
    show yieldTList (ofCFGTreeList cs) = CFGTree.yieldList cs
    exact yieldTList_ofCFGTreeList cs

/-- List version of `yieldT_ofCFGTree`. -/
theorem yieldTList_ofCFGTreeList (ts : List (CFGTree T N)) :
    yieldTList (ofCFGTreeList ts) = CFGTree.yieldList ts := by
  match ts with
  | [] => rfl
  | t :: rest =>
    show (ofCFGTree t).yieldT ++ yieldTList (ofCFGTreeList rest) =
         t.yield ++ CFGTree.yieldList rest
    rw [yieldT_ofCFGTree t, yieldTList_ofCFGTreeList rest]
end

mutual
/-- The embedding produces no open slots. -/
theorem yieldNT_ofCFGTree (t : CFGTree T N) :
    (ofCFGTree t).yieldNT = [] := by
  match t with
  | .leaf _ => rfl
  | .node _ cs =>
    show yieldNTList (ofCFGTreeList cs) = []
    exact yieldNTList_ofCFGTreeList cs

/-- List version of `yieldNT_ofCFGTree`. -/
theorem yieldNTList_ofCFGTreeList (ts : List (CFGTree T N)) :
    yieldNTList (ofCFGTreeList ts) = [] := by
  match ts with
  | [] => rfl
  | t :: rest =>
    show (ofCFGTree t).yieldNT ++ yieldNTList (ofCFGTreeList rest) = []
    rw [yieldNT_ofCFGTree t, yieldNTList_ofCFGTreeList rest]
    rfl
end

end CFGFragment
