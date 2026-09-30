/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Chain

/-!
# Spell-out of planar syntactic objects

PF pronounces the pronounced copies of a planar syntactic object (`Chain.lean`) and nothing
else, so a deleted copy, a trace, is silent wherever it stands. A shared token is one token,
pronounced once, at its last occurrence ([wilder-1999], [de-vries-2009]), so that material two
conjuncts share is pronounced in the second. An [E] feature on a head silences the head's
complement ([merchant-2001]), and since a shared token is one token, eliding either of its
occurrences silences it everywhere. An [E] head applies once per distinct complement.

## Main definitions

* `pronouncedAt`, `elidedDomains`, `IsSilenced`: pronunciation under [E].
* `pfYield`, `pfPhon`: the pronounced tokens and forms, left to right.

## References

* [wilder-1999]
* [de-vries-2009]
* [merchant-2001]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order Core.Order.Branching

variable (t : PlanarSyntacticObject)

/-- `tok` is pronounced at its last occurrence. -/
def pronouncedAt (tok : LIToken) : Option TreePath := (occurrences t tok).getLast?

/-! ### Ellipsis -/

/-- The complement of the head at `p` is its sister. -/
def complement (p : TreePath) : TreePath := ⟨p.toList.dropLast ++ [1 - p.toList.getLastD 0]⟩

/-- The [E] heads. -/
def eHeads : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2.item.outerEllipsis then some x.1 else none

/-- The elided domains are the distinct complements of the [E] heads, in the order of the heads,
so a shared head over one shared complement applies once and over two complements twice. -/
def elidedDomains : List TreePath :=
  ((eHeads t).map complement).foldl
    (fun acc p ↦ if acc.any (fun q ↦ subtreeAt t.val q.toList = subtreeAt t.val p.toList) then acc
      else acc ++ [p]) []

/-- `tok` is silenced when one of its occurrences lies in an elided domain. -/
def IsSilenced (tok : LIToken) : Prop := ∃ K ∈ elidedDomains t, ∃ p ∈ occurrences t tok, K ≤ p

instance (tok : LIToken) : Decidable (IsSilenced t tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The pronounced tokens, left to right, each at its last occurrence unless silenced. -/
def pfYield : List LIToken :=
  (tokenList t.val).filterMap fun x ↦
    if pronouncedAt t x.2 = some x.1 ∧ ¬ IsSilenced t x.2 then some x.2 else none

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap LIToken.phonForm?

end Minimalist
