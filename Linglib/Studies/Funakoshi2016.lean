/-!
# @cite{funakoshi-2016} — Verb-Stranding VP Ellipsis in Japanese
@cite{funakoshi-2016}

Funakoshi, Kenshi (2016). Verb-stranding verb phrase ellipsis in Japanese.
*Journal of East Asian Linguistics* 25.2, pp. 113–142.

## Key Generalization

(3) An adjunct can be elided only if no other VP-internal elements are present.

This means that if an overt VP-adjunct remains in the second conjunct,
another adjunct *cannot* be the elided element — only an argument can be.
This provides an **argumenthood diagnostic**: if a constituent can be elided
in the presence of an overt adjunct, it must be an argument.

## Application (@cite{ozaki-2026})

Ozaki uses Funakoshi's generalization to show that the source phrase of
Japanese Alternation Verbs (*hanareru* 'leave', *deru* 'exit') is always
an argument, regardless of whether it is marked ACC *-o* or ABL *kara*.
The source elides even with an overt manner adverb (*suguni* 'quickly'),
which would be impossible if it were an adjunct.
-/

namespace Funakoshi2016

/-- Funakoshi's generalization: adjuncts can be elided under VP ellipsis
    only if no other VP-internal elements are present. -/
structure EllipsisDatum where
  /-- The elided constituent -/
  elidedConstituent : String
  /-- Whether it is an argument or adjunct -/
  isArgument : Bool
  /-- Whether another VP-internal element is overt in the ellipsis site -/
  otherVPInternalOvert : Bool
  /-- Is the ellipsis reading available? -/
  available : Bool
  /-- Example sentence -/
  sentence : String
  deriving DecidableEq, Repr

/-- Adjunct elision is blocked when another VP-internal element is overt. -/
def adjunct_blocked : EllipsisDatum where
  elidedConstituent := "teineini (carefully)"
  isArgument := false
  otherVPInternalOvert := true
  available := false
  sentence := "* ... Hanako-wa subayaku ⟨teineini⟩ hatarakanakatta"

/-- Argument elision succeeds even when another VP-internal element is overt. -/
def argument_ok : EllipsisDatum where
  elidedConstituent := "zibun-no kuruma-o (one's own car)"
  isArgument := true
  otherVPInternalOvert := true
  available := true
  sentence := "Taro-wa teineini zibun-no kuruma-o aratta ga, Hanako-wa teineini ⟨zibun-no kuruma-o⟩ arawanakatta"

/-- Funakoshi's generalization holds: adjunct elision is blocked when another
    VP-internal element is overt, but argument elision is not. -/
theorem generalization_holds :
    adjunct_blocked.available = false ∧
    argument_ok.available = true := ⟨rfl, rfl⟩

/-- The generalization as a decidable predicate: if the elided constituent
    is an adjunct AND another VP-internal element is overt, elision is blocked. -/
def funakoshiPredicts (d : EllipsisDatum) : Bool :=
  if !d.isArgument && d.otherVPInternalOvert then !d.available
  else true

theorem adjunct_blocked_predicted :
    funakoshiPredicts adjunct_blocked = true := rfl

theorem argument_ok_predicted :
    funakoshiPredicts argument_ok = true := rfl

end Funakoshi2016
