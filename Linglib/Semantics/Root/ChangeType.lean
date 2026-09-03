import Linglib.Semantics.Root.Defs

/-!
# Change type

[dixon-1982]'s split between property-concept states and states that result
from an action, taken up at root level by [beavers-etal-2021]: a root either
names a gradable property (√flat, √red) or the state an event brings about
(√crack, √shatter), and only the latter entails a prior change. The change type
of a root is read off its atoms, so it is `result` exactly when the root carries
a `result` atom.

## Main declarations

* `ChangeType` — property-concept or result root
* `ChangeType.EntailsChange` — result roots entail a prior change
* `ChangeType.ofKinds`, `Root.changeType` — the change type of a signature and of
  a root

## References

* [dixon-1982]: Where Have All the Adjectives Gone?
* [beavers-etal-2021]: States and changes of state.
-/

namespace Semantics.Root

/-- The two types of change-of-state root, property-concept roots naming a gradable
property (√flat, √red) and result roots naming the state an event brings about
(√crack, √shatter) ([beavers-etal-2021] §3.1). -/
inductive ChangeType where
  | propertyConcept
  | result
  deriving DecidableEq, Repr

namespace ChangeType

/-- A result root entails a prior change and a property-concept root does not
([beavers-etal-2021] §3.6). -/
def EntailsChange : ChangeType → Prop
  | propertyConcept => False
  | result => True

instance : DecidablePred EntailsChange
  | propertyConcept => isFalse id
  | result => isTrue trivial

/-- The change type of a kind signature, `result` iff the signature carries `result`. -/
def ofKinds (s : Kinds) : ChangeType :=
  if Kind.result ∈ s then result else propertyConcept

end ChangeType

/-- The change type of a root, `result` iff it carries a `result` atom. -/
def changeType (r : Root) : ChangeType := .ofKinds r.kinds

end Semantics.Root
