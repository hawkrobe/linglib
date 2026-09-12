/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Linearization.Externalization

/-!
# Marcolli, Chomsky and Berwick (2025): Mathematical Structure of Syntactic Merge

This file formalizes the worked examples of externalization of
[marcolli-chomsky-berwick-2025] on the `SyntacticObject` carrier of the Minimalist
substrate: the harmonic head-initial and head-final orders of a determiner–noun Merge, the
head-side convention flipping the yield, and exocentric elimination, two saturated nouns
determining no head and hence no order. The framework itself is the `Syntax/Minimalist/`
theory layer; the examples are kernel-checked against it.

## TODO

The book's section locators (§1.12.1, §1.13, §1.13.2) are transcribed from an earlier
version of this file and are UNVERIFIED against the published text.

## References

* [marcolli-chomsky-berwick-2025]
-/

namespace MarcolliChomskyBerwick2025

open RoseTree UnorderedTree Minimalist SyntacticObject

/-- A determiner over a noun: `D` selects `N`, so `D` projects. -/
private def theDog : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inr none)
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

/-- Harmonic head-initial: the projecting `D`'s yield comes first. -/
example : (theDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide

/-- Harmonic head-final: the same head function, mirrored. -/
example : (theDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide

example : theDog.phonYield .initial = some ["the", "dog"] := by decide
example : theDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge: two saturated `N`s, neither selecting the other, so no head and no
order. -/
private def exoNN : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inr none)
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : exoNN.linearize .initial = none := by decide
example : exoNN.linearize .final = none := by decide

end MarcolliChomskyBerwick2025
