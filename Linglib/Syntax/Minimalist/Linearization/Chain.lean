import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Syntax.Minimalist.Economy.Basic
import Linglib.Syntax.Question
import Linglib.Core.Algebra.RootedTree.PreLie.Path
import Linglib.Core.Data.RoseTree.Get

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

namespace Minimalist

open RoseTree RoseTree.Pathed SyntacticObject
open Syntax.Question (MWFParameter PhaseEdge)

/-! ### Occurrences and chains -/

mutual
/-- The positions whose label `f` accepts, with their paths, left to right. -/
def positions (f : SOLabel → Option LIToken) : RoseTree SOLabel → List (Path × LIToken)
  | .node a cs => match f a with
    | some tok => [([], tok)]
    | none => positionsAux f 0 cs
/-- Auxiliary: the positions in a children list from index `i`. -/
def positionsAux (f : SOLabel → Option LIToken) :
    ℕ → List (RoseTree SOLabel) → List (Path × LIToken)
  | _, [] => []
  | i, c :: cs => (positions f c).map (λ x => (i :: x.1, x.2)) ++ positionsAux f (i + 1) cs
end

/-- The tokens with their paths, left to right. -/
def tokenList : RoseTree SOLabel → List (Path × LIToken) := positions (Sum.elim some λ _ => none)

/-- The traces with their paths, left to right. -/
def traceList : RoseTree SOLabel → List (Path × LIToken) := positions (Sum.elim (λ _ => none) id)

variable (t : RoseTree SOLabel)

/-- The occurrences of `tok`. -/
def occurrences (tok : LIToken) : List Path :=
  (tokenList t).filterMap λ x => if x.2 = tok then some x.1 else none

/-- The tokens of `t`, each once. -/
def tokens : Finset LIToken := ((tokenList t).map (·.2)).toFinset

/-- The terms of `t`: its subtrees, a shared constituent's once. -/
def terms : Finset (RoseTree SOLabel) := ((vertices t).filterMap t.subtreeAt).toFinset

/-- `tok` is shared, dominated by two mothers: it occurs twice. -/
def IsShared (tok : LIToken) : Prop := 2 ≤ (occurrences t tok).length

instance (tok : LIToken) : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-- `p` c-commands `q`: the mother of `p` dominates `q` while `p` does not. -/
def CCommands (p q : Path) : Prop := p.dropLast <+: q ∧ ¬ p <+: q

instance (p q : Path) : Decidable (CCommands p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The trace `x` is bound: an occurrence of its token c-commands it. -/
def IsBound (x : Path × LIToken) : Prop := ∃ q ∈ occurrences t x.2, CCommands q x.1

instance (x : Path × LIToken) : Decidable (IsBound t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The unbound traces: seen from their positions, copies without their antecedents. -/
def unboundTraces : List (Path × LIToken) := (traceList t).filter (¬ IsBound t ·)

/-- The occurrence at which `tok` is pronounced: its last. -/
def pronouncedAt (tok : LIToken) : Option Path := (occurrences t tok).getLast?

/-! ### Ellipsis -/

/-- The complement of the head at `p`: its sister. -/
def complementPath (p : Path) : Path := p.dropLast ++ [1 - p.getLastD 0]

/-- The [E] heads. -/
def eHeads : List Path :=
  (tokenList t).filterMap λ x => if x.2.item.outerEllipsis then some x.1 else none

/-- The elided domains, one per distinct complement of an [E] head, in the order of the heads:
a shared head over one shared complement applies once, over two complements twice. -/
def elidedDomains : List Path :=
  ((eHeads t).map complementPath).foldl
    (λ acc p => if acc.any (λ q => t.subtreeAt q = t.subtreeAt p) then acc else acc ++ [p]) []

/-- `tok` is silenced: one of its occurrences lies in an elided domain. -/
def IsSilenced (tok : LIToken) : Prop :=
  ∃ K ∈ elidedDomains t, ∃ p ∈ occurrences t tok, K <+: p

instance (tok : LIToken) : Decidable (IsSilenced t tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The pronounced tokens, left to right: each at its last occurrence, unless silenced. -/
def pfYield : List LIToken :=
  (tokenList t).filterMap λ x =>
    if pronouncedAt t x.2 = some x.1 ∧ ¬ IsSilenced t x.2 then some x.2 else none

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap LIToken.phonForm?

/-- The pronounceable tokens the application at the domain `K` silences. -/
def silencedBy (K : Path) : Finset LIToken :=
  (tokens t).filter λ s => s.phonForm?.isSome ∧ (occurrences t s).any (decide <| K <+: ·)

/-- The application at `K` has no effect on pronunciation: the earlier applications silenced
every token it silences. -/
def IsVacuous (K : Path) : Prop :=
  silencedBy t K ⊆ ((elidedDomains t).takeWhile (· ≠ K)).toFinset.biUnion (silencedBy t)

instance (K : Path) : Decidable (IsVacuous t K) := by unfold IsVacuous; infer_instance

/-- **Pronunciation Economy** ([citko-gracanin-yuksek-2025] (39)): no application of ellipsis is
vacuous. -/
def PronunciationEconomy : Prop := ∀ K ∈ elidedDomains t, ¬ IsVacuous t K

instance : Decidable (PronunciationEconomy t) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Phase edges and the multiple-wh-fronting asterisk -/

/-- The specifiers and head of the projection of a head of category `c`: down the right spine,
the left daughters above the head, which is the first selecting item met; `none` when that item
has another category or the spine ends first. -/
def projection (c : Cat) : RoseTree SOLabel → Option (List (RoseTree SOLabel) × LIToken)
  | .node (.inr none) [.node (.inl tok) [], r] =>
      if tok.item.outerSel = [] then
        (projection c r).map λ x => (leafP tok :: x.1, x.2)
      else if tok.item.outerCat = c then some ([], tok) else none
  | .node (.inr none) [l, r] => (projection c r).map λ x => (l :: x.1, x.2)
  | _ => none

/-- The head of a constituent: the token or trace at a leaf, else the first selecting item down
the right spine. -/
def headToken? : RoseTree SOLabel → Option LIToken
  | .node (.inl tok) _ | .node (.inr (some tok)) _ => some tok
  | .node (.inr none) [.node (.inl tok) [], r] =>
      if tok.item.outerSel = [] then headToken? r else some tok
  | .node (.inr none) [_, r] => headToken? r
  | .node (.inr none) _ => none

/-- The constituent is a wh-specifier: its head is a wh-token or its trace. -/
def IsWhSpecifier (s : RoseTree SOLabel) : Prop :=
  ∃ tok ∈ (headToken? s).toList, tok.item.outerWh = true

instance (s : RoseTree SOLabel) : Decidable (IsWhSpecifier s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The phase at `p`, a `v` or `C` projection: its edge, specifiers and head. -/
def phaseAt (p : Path) : Option (PhaseEdge × List (RoseTree SOLabel) × LIToken) :=
  (t.subtreeAt p).bind λ s =>
    ((projection .v s).map λ x => (PhaseEdge.vP, x)).or
      ((projection .C s).map λ x => (PhaseEdge.CP, x))

/-- The phase at `p` receives the asterisk of the parameter ([citko-gracanin-yuksek-2025] (27)):
its edge hosts more wh-specifiers than the parameter allows there. -/
def IsAsterisked (param : MWFParameter) (p : Path) : Prop :=
  ∃ x ∈ (phaseAt t p).toList, param.EdgeAsterisk x.1 (x.2.1.countP (decide <| IsWhSpecifier ·))

instance (param : MWFParameter) (p : Path) : Decidable (IsAsterisked t param p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The object converges at PF: the head of every asterisked phase is silenced. -/
def Converges (param : MWFParameter) : Prop :=
  ∀ p ∈ vertices t, IsAsterisked t param p → ∀ x ∈ (phaseAt t p).toList, IsSilenced t x.2.2

instance (param : MWFParameter) : Decidable (Converges t param) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Cost -/

/-- The cost of the object: its tokens are the lexical items drawn, its internal terms the Merges,
and its elided domains the applications of ellipsis. -/
def planarCost : DerivationCost
  | .lexicalItems => (tokens t).card
  | .mergeOps => ((terms t).filter λ s => s.isLeaf = false).card
  | .agreeOps => 0
  | .ellipsisOps => (elidedDomains t).length

end Minimalist
