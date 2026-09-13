/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar
import Mathlib.Algebra.Order.Group.Defs

/-!
# Weighted context-free grammars

A weighted context-free grammar over `G` attaches a nonnegative weight to each rule of `G`, with
no normalisation; the normalised specialisations are `PCFG`, whose weights in `ℝ≥0∞` sum to one at
each nonterminal, and `DirichletPCFG`, whose pseudo-counts are positive on the rules of the
grammar. The weight type is a parameter, as for `Polynomial R`, so a consumer chooses `ℝ`,
`ℝ≥0∞` or any ordered type with a zero.
-/

/-- A weighted context-free grammar over `G` with weights in `W`: a nonnegative weight on rules,
with no normalisation. -/
@[ext]
structure WeightedCFG {T : Type*} (G : ContextFreeGrammar T) (W : Type*) [Zero W] [LE W] where
  /-- The weight of a rule. -/
  weight : ContextFreeRule T G.NT → W
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ r, 0 ≤ weight r
