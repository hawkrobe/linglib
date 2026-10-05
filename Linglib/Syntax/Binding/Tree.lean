/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Tree.Command

/-!
# Binding configurations of phrase-structure trees

This file defines the binding configuration of a phrase-structure tree. A position commands
another when it c-commands it in Reinhart's sense, neither dominating the other and every
branching node above the first dominating the second, and the binding domain of a position is
the minimal clause containing it: the positions that every clause node properly dominating it
dominates. This is the configuration of the binding theory of Government and Binding, the
governing category approximated by the minimal clause, and of the clause-mate c-command that
psycholinguistic studies of local anaphors test.

## Main definitions

* `PhraseStructure.Tree.clauseConfiguration`: c-command with the minimal clause as binding domain.

## References

* [T. Reinhart, *The Syntactic Domain of Anaphora* (1976)][reinhart-1976]
* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
-/

@[expose] public section

namespace PhraseStructure.Tree

open Core.Order

variable {W : Type*} (t : Tree Cat W)

/-- The binding configuration of `t` takes c-command as its command relation and the minimal
clause containing a position as that position's binding domain. -/
def clauseConfiguration : Binding.Configuration TreePath where
  commands := CCommands t
  domain b := {a | (b, a) ∈ sCommand t}

instance : DecidableRel (clauseConfiguration t).commands :=
  inferInstanceAs (DecidableRel (CCommands t))

instance (b : TreePath) : DecidablePred (· ∈ (clauseConfiguration t).domain b) :=
  fun a ↦ inferInstanceAs (Decidable ((b, a) ∈ sCommand t))

end PhraseStructure.Tree
