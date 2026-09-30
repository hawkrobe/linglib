module

public import Mathlib.Tactic.DeriveFintype

/-!
# Wh-dependencies

A wh-phrase takes the scope of its interrogative C by moving to the specifier of C, overtly or
covertly, or by unselective binding, an operator in C binding it in situ ([pesetsky-1987]). Where
the phrase is pronounced does not settle which: a phrase pronounced in situ has moved covertly
on one analysis ([huang-1982]) and is bound on another, and an analysis of a language assigns a
dependency to each position its questions use. The choice has consequences: movement, covert
movement included, is sensitive to islands, and binding is not ([sato-ngui-2017]).

## Implementation notes

Movement and binding are not the only analyses of a phrase in situ; [sato-ngui-2017] mention an
analysis in terms of choice functions, which is not modelled.

## References

* [pesetsky-1987]
* [huang-1982]
* [sato-ngui-2017]
-/

@[expose] public section

namespace Minimalist

/-- How a wh-phrase takes the scope of its interrogative C. -/
inductive WhDependency where
  /-- Movement to the specifier of C, overt or covert. -/
  | movement
  /-- Unselective binding of the phrase in situ by an operator in C ([pesetsky-1987]). -/
  | binding
  deriving DecidableEq, Repr, Fintype

end Minimalist
