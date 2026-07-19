/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Roots in Distributed Morphology

The abstract Root: a syntactic atom individuated by an arbitrary index,
with no phonological or semantic content ([harley-2014] §2,
[marantz-1997]). It is acategorial — it enters the syntax only by merging
with a categorizing head (the Categorization Assumption; the categorizer
inventory and `RootLicense` interface are `DM/Categorizer.lean`, whose
`RootIdx` parameter this type instantiates) — and receives its form at
Vocabulary Insertion (`DM/VocabularyInsertion.lean`).

This is a different object from the comparative-concept root of
`Morphology/Root/Basic.lean`, which is a contentful *morph*: a DM Root is
not a form but an abstract element realized by forms. Where
[haspelmath-2025-root] treats *hammer* (noun) and *hammer* (verb) as
heterosemous sister roots, DM derives both from one acategorial √ under
different categorizers; that rivalry is study content, this file only
fixes the object.
-/

namespace Morphology.DM

/-- A Root terminal node, individuated by an arbitrary index alone — with
deliberately no form or meaning fields, following [harley-2014]'s answer to
what roots are. -/
structure Root where
  /-- The individuating index. -/
  index : Nat
  deriving DecidableEq, Repr

end Morphology.DM
