module

public import Mathlib.Data.Set.Defs

/-!
# Verb second

This file defines the clause-type heads of the split ForceP and a language's verb-second grammar.
Westergaard splits Rizzi's ForceP into one head per clause type, DeclP, IntP, PolP, ExclP and
ImpP for root declaratives, wh-questions, yes/no-questions, exclamatives and imperatives, beside
FinP for embedded declaratives and WhP for embedded questions. Verb second is then not one
parameter but a setting per head: a language's verb-second grammar is the set of clause-type
heads the finite verb moves to, which the Germanic fragments record and which children acquire
head by head as micro-cues.

## Main definitions

* `Minimalist.ForceHead`: the seven clause-type heads of the split ForceP.
* `Minimalist.V2Grammar`: the set of clause-type heads the finite verb moves to.

## References

* [westergaard-2009]
* [rizzi-1997]
-/

@[expose] public section

namespace Minimalist

/-- The clause-type heads of the split ForceP, each a possible target of verb movement. -/
inductive ForceHead
  /-- Root declaratives. -/
  | Decl
  /-- Root wh-questions. -/
  | Int
  /-- Yes/no-questions. -/
  | Pol
  /-- Exclamatives. -/
  | Excl
  /-- Imperatives. -/
  | Imp
  /-- Embedded declaratives, the finiteness head below the force domain. -/
  | Fin
  /-- Embedded questions. -/
  | Wh
  deriving DecidableEq, Repr

/-- A verb-second grammar is the set of clause-type heads the finite verb moves to. -/
abbrev V2Grammar : Type := Set ForceHead

end Minimalist
