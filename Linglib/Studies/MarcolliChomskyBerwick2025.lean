/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Linearization.Externalization

/-!
# Externalization examples from Marcolli–Chomsky–Berwick

`decide`-checked worked examples of [marcolli-chomsky-berwick-2025] §1.12.1/§1.13
externalization on the `SyntacticObject` carrier: the harmonic head-initial and
head-final orders of a determiner–noun Merge (the head-side convention flips the
yield), and exocentric elimination — two saturated nouns determine no head and no
order (§1.13.2).

The book's framework itself is the `Syntax/Minimalist/` theory layer; this file
holds its concrete examples, kernel-checked against that substrate.
-/

namespace MarcolliChomskyBerwick2025

open RootedTree Minimalist SyntacticObject

/-- A determiner over a noun: `D` selects `N`, so `D` projects. -/
private def theDog : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

/-- Harmonic head-initial: the projecting `D`'s yield comes first. -/
example : (theDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide

/-- Harmonic head-final: the same head function, mirrored. -/
example : (theDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide

example : theDog.phonYield .initial = some ["the", "dog"] := by decide
example : theDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge: two saturated `N`s, neither selecting the other — no head,
    no order ([marcolli-chomsky-berwick-2025] §1.13.2). -/
private def exoNN : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : exoNN.linearize .initial = none := by decide
example : exoNN.linearize .final = none := by decide

end MarcolliChomskyBerwick2025
