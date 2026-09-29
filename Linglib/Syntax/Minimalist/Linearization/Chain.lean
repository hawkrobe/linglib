/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.Economy.Basic
public import Linglib.Syntax.Question
public import Linglib.Core.Data.RoseTree.Get

/-!
# Chains, sharing and PF reduction on planar syntactic objects

A planar syntactic object whose traces remember the token that moved carries the two ways one
token comes to occupy several positions. Internal Merge leaves a trace, the cancellation `T/T_v`
of [marcolli-chomsky-berwick-2025] with `T_v` remembered, so a token's chain is its occurrence
with its traces, and a trace no occurrence of its token c-commands is unbound: seen from its own
conjunct, a copy without its antecedent. A token occurring twice is *shared*, dominated by two
mothers — [citko-2005]'s Parallel Merge, which MCB §1.1.3.2 places outside Merge as a grafting
away from the root — and a shared constituent is an identical subtree at two positions. At PF a
token is pronounced once, at its last occurrence, so shared material follows all unshared material
([wilder-1999], [de-vries-2009]). An [E] feature on a head silences the head's complement
([merchant-2001]), and since a shared token is one token, eliding either of its occurrences
silences it everywhere. An [E] head applies once per distinct complement, and an application that
silences no pronounceable token an earlier one had not already silenced is vacuous, the
configuration [citko-gracanin-yuksek-2025]'s Pronunciation Economy bans. A `v` or `C` projection
whose edge hosts several wh-specifiers, wh-tokens or their traces, receives the asterisk of the
multiple-wh-fronting parameter and crashes at PF unless its head is silenced. The cost of the
object is read off its terms, the distinct subtrees as MCB's `subtrees` taken each once: the lexical
leaves are the items drawn and the internal vertices the Merges, so a shared constituent is built
once.

## Main definitions

* `tokenList`, `occurrences`, `unboundTraces`, `IsShared`: occurrences and chains.
* `terms`: the distinct subtrees, a shared constituent's once.
* `elidedDomains`, `IsSilenced`, `pfPhon`: pronunciation under [E].
* `IsVacuous`, `PronunciationEconomy`: the ban on vacuous ellipsis.
* `projection`, `phaseAt`, `IsAsterisked`, `Converges`: the multiple-wh-fronting asterisk.
* `planarCost`: the object's `DerivationCost`.

## References

* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic Merge*
  (2025)][marcolli-chomsky-berwick-2025]
* [B. Citko, *On the nature of Merge* (2005)][citko-2005]
* [C. Wilder, *Right node raising and the LCA* (1999)][wilder-1999]
* [M. de Vries, *On multidominance and linearization* (2009)][de-vries-2009]
* [J. Merchant, *The Syntax of Silence* (2001)][merchant-2001]
* [B. Citko and M. Gračanin-Yuksek, *Economy in PF reduction* (2025)][citko-gracanin-yuksek-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order.Branching

/-! ### Occurrences and chains -/

mutual
/-- The positions whose label `f` accepts, with their paths, left to right. -/
def positions (f : Vertex → Option LIToken) : RoseTree Vertex → List (List ℕ × LIToken)
  | .node a cs => match f a with
    | some tok => [([], tok)]
    | none => positionsAux f 0 cs
/-- `positionsAux f i cs` lists the positions in the forest `cs`, numbering its trees from `i`. -/
def positionsAux (f : Vertex → Option LIToken) :
    ℕ → List (RoseTree Vertex) → List (List ℕ × LIToken)
  | _, [] => []
  | i, c :: cs => (positions f c).map (fun x ↦ (i :: x.1, x.2)) ++ positionsAux f (i + 1) cs
end

/-- The tokens with their paths, left to right. -/
def tokenList : RoseTree Vertex → List (List ℕ × LIToken) := positions (Sum.elim some fun _ ↦ none)

/-- The traces with their paths, left to right. -/
def traceList : RoseTree Vertex → List (List ℕ × LIToken) := positions (Sum.elim (fun _ ↦ none) id)

variable (t : PlanarSyntacticObject)

/-- The occurrences of `tok`. -/
def occurrences (tok : LIToken) : List (List ℕ) :=
  (tokenList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The tokens of `t`, each once. -/
def tokens : Finset LIToken := ((tokenList t.val).map (·.2)).toFinset

/-- The terms of `t` are its subtrees, a shared constituent counted once. -/
def terms : Finset (RoseTree Vertex) := ((vertices t.val).filterMap (subtreeAt t.val)).toFinset

/-- `tok` is shared, dominated by two mothers, when it occurs twice. -/
def IsShared (tok : LIToken) : Prop := 2 ≤ (occurrences t tok).length

instance (tok : LIToken) : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-- `p` c-commands `q` when the mother of `p` dominates `q` and `p` does not. -/
def CCommands (p q : List ℕ) : Prop := p.dropLast <+: q ∧ ¬ p <+: q

instance (p q : List ℕ) : Decidable (CCommands p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The trace `x` is bound when an occurrence of its token c-commands it. -/
def IsBound (x : List ℕ × LIToken) : Prop := ∃ q ∈ occurrences t x.2, CCommands q x.1

instance (x : List ℕ × LIToken) : Decidable (IsBound t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The unbound traces are, seen from their positions, copies without their antecedents. -/
def unboundTraces : List (List ℕ × LIToken) := (traceList t.val).filter (¬ IsBound t ·)

/-- `tok` is pronounced at its last occurrence. -/
def pronouncedAt (tok : LIToken) : Option (List ℕ) := (occurrences t tok).getLast?

/-! ### Ellipsis -/

/-- The complement of the head at `p` is its sister. -/
def complementPath (p : List ℕ) : List ℕ := p.dropLast ++ [1 - p.getLastD 0]

/-- The [E] heads. -/
def eHeads : List (List ℕ) :=
  (tokenList t.val).filterMap fun x ↦ if x.2.item.outerEllipsis then some x.1 else none

/-- The elided domains are the distinct complements of the [E] heads, in the order of the heads,
so a shared head over one shared complement applies once and over two complements twice. -/
def elidedDomains : List (List ℕ) :=
  ((eHeads t).map complementPath).foldl
    (fun acc p ↦
      if acc.any (fun q ↦ subtreeAt t.val q = subtreeAt t.val p) then acc else acc ++ [p]) []

/-- `tok` is silenced when one of its occurrences lies in an elided domain. -/
def IsSilenced (tok : LIToken) : Prop :=
  ∃ K ∈ elidedDomains t, ∃ p ∈ occurrences t tok, K <+: p

instance (tok : LIToken) : Decidable (IsSilenced t tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The pronounced tokens, left to right, each at its last occurrence unless silenced. -/
def pfYield : List LIToken :=
  (tokenList t.val).filterMap fun x ↦
    if pronouncedAt t x.2 = some x.1 ∧ ¬ IsSilenced t x.2 then some x.2 else none

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap LIToken.phonForm?

/-- The pronounceable tokens the application at the domain `K` silences. -/
def silencedBy (K : List ℕ) : Finset LIToken :=
  (tokens t).filter fun s ↦ s.phonForm?.isSome ∧ (occurrences t s).any (decide <| K <+: ·)

/-- The application at `K` is vacuous when the earlier applications already silenced every token
it silences. -/
def IsVacuous (K : List ℕ) : Prop :=
  silencedBy t K ⊆ ((elidedDomains t).takeWhile (· ≠ K)).toFinset.biUnion (silencedBy t)

instance (K : List ℕ) : Decidable (IsVacuous t K) := by unfold IsVacuous; infer_instance

/-- **Pronunciation Economy** ([citko-gracanin-yuksek-2025] (39)) says that no application of
ellipsis is vacuous. -/
def PronunciationEconomy : Prop := ∀ K ∈ elidedDomains t, ¬ IsVacuous t K

instance : Decidable (PronunciationEconomy t) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Phase edges and the multiple-wh-fronting asterisk -/

/-- `projection c t` finds the specifiers and head of the projection of a head of category `c`.
Going down the right spine, the specifiers are the left daughters above the head, which is the first
selecting item met; the result is `none` when that item has another category or the spine ends
first. -/
def projection (c : Cat) : RoseTree Vertex → Option (List (RoseTree Vertex) × LIToken)
  | .node (.inr none) [.node (.inl tok) [], r] =>
      if tok.item.outerSel = [] then
        (projection c r).map fun x ↦ (.node (.inl tok) [] :: x.1, x.2)
      else if tok.item.outerCat = c then some ([], tok) else none
  | .node (.inr none) [l, r] => (projection c r).map fun x ↦ (l :: x.1, x.2)
  | _ => none

/-- The head of a constituent is the token or trace at a leaf, else the first selecting item down
the right spine. -/
def headToken? : RoseTree Vertex → Option LIToken
  | .node (.inl tok) _ | .node (.inr (some tok)) _ => some tok
  | .node (.inr none) [.node (.inl tok) [], r] =>
      if tok.item.outerSel = [] then headToken? r else some tok
  | .node (.inr none) [_, r] => headToken? r
  | .node (.inr none) _ => none

/-- A constituent is a wh-specifier when its head is a wh-token or its trace. -/
def IsWhSpecifier (s : RoseTree Vertex) : Prop :=
  ∃ tok ∈ (headToken? s).toList, tok.item.outerWh = true

instance (s : RoseTree Vertex) : Decidable (IsWhSpecifier s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `phaseAt t p` is the phase at `p`, a `v` or `C` projection, with its edge, specifiers and
head. -/
def phaseAt (p : List ℕ) : Option (PhaseEdge × List (RoseTree Vertex) × LIToken) :=
  (subtreeAt t.val p).bind fun s ↦
    ((projection .v s).map fun x ↦ (PhaseEdge.vP, x)).or
      ((projection .C s).map fun x ↦ (PhaseEdge.CP, x))

/-- The phase at `p` receives the asterisk of the parameter ([citko-gracanin-yuksek-2025] (27))
when its edge hosts more wh-specifiers than the parameter allows there. -/
def IsAsterisked (param : MWFParameter) (p : List ℕ) : Prop :=
  ∃ x ∈ (phaseAt t p).toList, param.EdgeAsterisk x.1 (x.2.1.countP (decide <| IsWhSpecifier ·))

instance (param : MWFParameter) (p : List ℕ) : Decidable (IsAsterisked t param p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The object converges at PF when the head of every asterisked phase is silenced. -/
def Converges (param : MWFParameter) : Prop :=
  ∀ p ∈ vertices t.val, IsAsterisked t param p → ∀ x ∈ (phaseAt t p).toList, IsSilenced t x.2.2

instance (param : MWFParameter) : Decidable (Converges t param) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Cost -/

/-- The cost of the object counts its tokens as the lexical items drawn, its internal terms as the
Merges, and its elided domains as the applications of ellipsis. -/
def planarCost : DerivationCost
  | .lexicalItems => (tokens t).card
  | .mergeOps => ((terms t).filter fun s ↦ s.arity ≠ 0).card
  | .agreeOps => 0
  | .ellipsisOps => (elidedDomains t).length

end Minimalist
