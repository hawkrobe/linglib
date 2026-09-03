import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Syntax.Minimalist.Economy.Basic
import Linglib.Syntax.Question
import Linglib.Core.Algebra.RootedTree.PreLie.Path
import Linglib.Core.Data.RoseTree.Get

/-!
# Chains, sharing and PF reduction on planar syntactic objects

A planar syntactic object in which a token occurs at several positions carries its chains: the
copies that the CI interface sees ([marcolli-chomsky-berwick-2025], Lemma 1.2.7). An occurrence is
a chain head when no other occurrence of the token c-commands it. Movement leaves one head, the
highest copy; a constituent with two mothers — [citko-2005]'s Parallel Merge, which MCB §1.1.3.2
places outside Merge as a grafting away from the root — leaves several, mutually incomparable
heads, one per mother, and is *shared*. At PF a token is pronounced once, at its last chain head,
so shared material follows all unshared material ([wilder-1999], [de-vries-2009]), and an [E]
feature on a head silences every token with a chain head in the head's complement
([merchant-2001]): eliding either occurrence of a shared constituent silences it everywhere,
while a moved phrase survives the ellipsis of its launching site. An [E] head applies once per
distinct complement, and an application whose tokens an earlier one already silenced is vacuous,
the configuration [citko-gracanin-yuksek-2025]'s Pronunciation Economy bans. A `v` or `C`
projection whose edge hosts several wh-specifiers receives the asterisk of the multiple-wh-fronting
parameter and crashes at PF unless its head is silenced. The cost of the object is read off its
distinct nodes and tokens: a shared constituent is built once.

## Main definitions

* `occurrenceList`, `CCommands`, `chainHeads`, `IsShared`, `pronouncedAt`: the chains.
* `elidedDomains`, `IsSilenced`, `pfYield`, `pfPhon`: pronunciation under [E].
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
* [B. Citko and M. Gračanin-Yuksek, *Economy in PF Reduction*
  (2025)][citko-gracanin-yuksek-2025]
-/

namespace Minimalist

open RoseTree RoseTree.Pathed SyntacticObject
open Syntax.Question (MWFParameter PhaseEdge)

/-! ### Occurrences and chains -/

mutual
/-- The leaf tokens with their paths, left to right. -/
def occurrenceList : RoseTree SOLabel → List (Path × LIToken)
  | .node (.inl tok) _ => [([], tok)]
  | .node (.inr ()) cs => occurrenceListAux 0 cs
/-- Auxiliary: the occurrences of a children list from index `i`. -/
def occurrenceListAux : ℕ → List (RoseTree SOLabel) → List (Path × LIToken)
  | _, [] => []
  | i, c :: cs => (occurrenceList c).map (λ x => (i :: x.1, x.2)) ++ occurrenceListAux (i + 1) cs
end

variable (t : RoseTree SOLabel)

/-- The tokens of `t`, each once. -/
def distinctTokens : List LIToken := ((occurrenceList t).map (·.2)).eraseDups

/-- The occurrences of `tok`. -/
def occurrences (tok : LIToken) : List Path :=
  (occurrenceList t).filterMap λ x => if x.2 = tok then some x.1 else none

/-- `p` c-commands `q`: the sister of `p` dominates `q`, that is `p`'s mother is an ancestor of
`q` while `p` itself is not. -/
def CCommands (p q : Path) : Prop := p.dropLast <+: q ∧ ¬ p <+: q

instance (p q : Path) : Decidable (CCommands p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The chain heads of `tok`: its occurrences not c-commanded by another. -/
def chainHeads (tok : LIToken) : List Path :=
  (occurrences t tok).filter λ p => (occurrences t tok).all λ q => !decide (CCommands q p)

/-- `tok` is shared, dominated by two mothers: it has several chain heads. -/
def IsShared (tok : LIToken) : Prop := 2 ≤ (chainHeads t tok).length

instance (tok : LIToken) : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-- The occurrence at which `tok` is pronounced: its last chain head. -/
def pronouncedAt (tok : LIToken) : Option Path := (chainHeads t tok).getLast?

/-! ### Ellipsis -/

/-- The complement of the head at `p`: its sister in a binary node. -/
def complementPath (p : Path) : Path := p.dropLast ++ [1 - p.getLastD 0]

/-- The paths of the [E] heads. -/
def eHeads : List Path :=
  (occurrenceList t).filterMap λ x => if x.2.item.outerEllipsis then some x.1 else none

/-- The domains ellipsis deletes, one per distinct complement of an [E] head, in the order of
the heads: a shared head over one shared complement applies once, over two complements twice. -/
def elidedDomains : List Path :=
  ((eHeads t).map complementPath).foldl
    (λ acc p => if acc.any (λ q => t.subtreeAt q = t.subtreeAt p) then acc else acc ++ [p]) []

/-- `tok` is silenced: one of its chain heads lies in an elided domain. -/
def IsSilenced (tok : LIToken) : Prop :=
  ∃ p ∈ eHeads t, ∃ h ∈ chainHeads t tok, complementPath p <+: h

instance (tok : LIToken) : Decidable (IsSilenced t tok) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The pronounced tokens, left to right: each at its last chain head, unless silenced. -/
def pfYield : List LIToken :=
  (occurrenceList t).filterMap λ x =>
    if pronouncedAt t x.2 = some x.1 ∧ ¬ IsSilenced t x.2 then some x.2 else none

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap LIToken.phonForm?

/-- The tokens the application at the domain `K` silences: those with a chain head in `K`. -/
def silencedBy (K : Path) : List LIToken :=
  (distinctTokens t).filter λ s => (chainHeads t s).any λ h => decide (K <+: h)

/-- The application at `K` is vacuous: every token it silences was silenced by an earlier
application. -/
def IsVacuous (K : Path) : Prop :=
  ∀ s ∈ silencedBy t K, ∃ K' ∈ (elidedDomains t).takeWhile (· ≠ K), s ∈ silencedBy t K'

instance (K : Path) : Decidable (IsVacuous t K) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Pronunciation Economy** ([citko-gracanin-yuksek-2025] (39)): no application of ellipsis is
vacuous. -/
def PronunciationEconomy : Prop := ∀ K ∈ elidedDomains t, ¬ IsVacuous t K

instance : Decidable (PronunciationEconomy t) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Phase edges and the multiple-wh-fronting asterisk -/

/-- The specifiers and head of a projection of a head of category `c`: the left daughters down
the right spine above the head, `none` when the spine reaches no such head. -/
def projection (c : Cat) : RoseTree SOLabel → Option (List (RoseTree SOLabel) × LIToken)
  | .node (.inr ()) [.node (.inl tok) [], r] =>
      if tok.item.outerCat = c then some ([], tok)
      else (projection c r).map λ x => (.node (.inl tok) [] :: x.1, x.2)
  | .node (.inr ()) [l, r] => (projection c r).map λ x => (l :: x.1, x.2)
  | _ => none

/-- The constituent contains a wh-token. -/
def IsWhPhrase (s : RoseTree SOLabel) : Prop := ∃ x ∈ occurrenceList s, x.2.item.outerWh = true

instance (s : RoseTree SOLabel) : Decidable (IsWhPhrase s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The phase at `p`, a `v` or `C` projection: its edge, specifiers and head. -/
def phaseAt (p : Path) : Option (PhaseEdge × List (RoseTree SOLabel) × LIToken) :=
  (t.subtreeAt p).bind λ s =>
    ((projection .v s).map λ x => (PhaseEdge.vP, x)).or
      ((projection .C s).map λ x => (PhaseEdge.CP, x))

/-- The phase at `p` receives the asterisk of the parameter: its edge hosts as many
wh-specifiers as the parameter forbids there ([citko-gracanin-yuksek-2025] (27)). -/
def IsAsterisked (param : MWFParameter) (p : Path) : Prop :=
  ∃ x ∈ (phaseAt t p).toList, param.EdgeAsterisk x.1 (x.2.1.countP λ s => decide (IsWhPhrase s))

instance (param : MWFParameter) (p : Path) : Decidable (IsAsterisked t param p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The object converges at PF: every asterisked phase is elided, its head silenced. -/
def Converges (param : MWFParameter) : Prop :=
  ∀ p ∈ vertices t, ∀ x ∈ (phaseAt t p).toList,
    param.EdgeAsterisk x.1 (x.2.1.countP λ s => decide (IsWhPhrase s)) → IsSilenced t x.2.2

instance (param : MWFParameter) : Decidable (Converges t param) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Cost -/

/-- The internal nodes of `t`, a shared constituent's once. -/
def distinctNodes : List (RoseTree SOLabel) :=
  ((vertices t).filterMap t.subtreeAt).filter (λ s => !s.isLeaf) |>.eraseDups

/-- The cost of the object: its distinct tokens are the lexical items drawn, its distinct
internal nodes the Merges, and its elided domains the applications of ellipsis. -/
def planarCost : DerivationCost where
  lexicalItems := (distinctTokens t).length
  mergeOps := (distinctNodes t).length
  agreeOps := 0
  ellipsisOps := (elidedDomains t).length

end Minimalist
