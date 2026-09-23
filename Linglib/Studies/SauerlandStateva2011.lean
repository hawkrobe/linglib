/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Granularity

/-!
# Sauerland & Stateva (2011): Two Types of Vagueness

This file formalizes the chapter's argument from the distribution of approximators that
vagueness comes in two kinds. Scalar vagueness belongs to point-denoting scalar terms,
numerals and clock times, interpreted at a contextual granularity after [krifka-2007], and
epistemic vagueness to terms like *heap* whose extension varies across indistinguishable
worlds. Scalar approximators such as *exactly* and *approximately* are granularity setters,
resetting the context's granularity to the finest or the coarsest available level
(`Degree.Granularity.finestWidth`, `coarsestWidth`), while epistemic approximators quantify
over worlds, which is why the two classes distribute complementarily. Within the scalar
class the endpoint approximators *absolutely*, *completely* and *more or less* combine only
with scale endpoints and block plain *exactly* and *approximately* there. The chapter's
example expressions and approximators are classified accordingly (`Item.itemClass`,
`Approximator.selects`), and the classification reproduces every cited judgment
(`classification_predicts_distribution`); the reset targets bound every available
interpretation (`exactly_narrowest`, `approximately_widest`), and a second scalar
approximator is vacuous because the first reset leaves a single granularity
(`second_reset_vacuous`).

## Implementation notes

The chapter is not available for verification here, so the judgments are as the file found
them; the granularity intervals are those of `Semantics/Degree/Granularity`.

## References

* [sauerland-stateva-2011]
* [krifka-2007]
* [lasersohn-1999]
-/

@[expose] public section

namespace SauerlandStateva2011

open Degree.Granularity

/-! ### The two-vagueness classification (§6.3) -/

/-- Their example expressions ((4)–(6), (35), (37), (44)–(45)). -/
inductive Item where
  | fifty
  | three
  | dry
  | full
  | beefStroganoff
  deriving DecidableEq, Repr

/-- The classification the dualistic theory assigns: scalar terms denote
scale points — non-endpoints (numerals) or endpoints (*dry*, *full*, their
§6.4 closed-scale adjectives) — while epistemically vague terms denote no
point at all. -/
inductive ItemClass where
  | scalarNonEndpoint
  | scalarEndpoint
  | epistemic
  deriving DecidableEq, Repr

/-- Their classification of the example items. -/
def Item.itemClass : Item → ItemClass
  | .fifty | .three => .scalarNonEndpoint
  | .dry | .full => .scalarEndpoint
  | .beefStroganoff => .epistemic

/-- The approximators whose distribution they cite. -/
inductive Approximator where
  | exactly
  | approximately
  | absolutely
  | completely
  | moreOrLess
  deriving DecidableEq, Repr

/-- The item class each approximator selects: plain scalar approximators
take non-endpoints, the specialized endpoint approximators take endpoints
(§6.4, (32): *absolutely*/*completely*/*more or less* make endpoints
more or less precise and block *exactly*/*approximately* there). -/
def Approximator.selects : Approximator → ItemClass
  | .exactly | .approximately => .scalarNonEndpoint
  | .absolutely | .completely | .moreOrLess => .scalarEndpoint

/-- The theory's compatibility prediction: an approximator combines with an
item iff the item is of the class it selects. -/
def compatible (a : Approximator) (i : Item) : Prop :=
  a.selects = i.itemClass

instance (a : Approximator) (i : Item) : Decidable (compatible a i) :=
  inferInstanceAs (Decidable (_ = _))

/-- One cited acceptability judgment. -/
structure Judgment where
  approximator : Approximator
  item : Item
  acceptable : Bool
  deriving Repr

/-- Their cited judgments: (4a)/(4b) *exactly/approximately fifty* vs
`#`…*Beef Stroganoff*; (6a)/(6b) `*`*absolutely fifty* vs *absolutely*
+ endpoint; (35a)/(35b) `#`*exactly dry/full* vs *exactly three*; (37)
*completely dry* vs `#`*completely three*; (44) *approximately three* vs
`#`…*dry*; (45) *more or less dry* vs `#`…*three*. -/
def Judgment.rows : List Judgment :=
  [⟨.exactly, .fifty, true⟩, ⟨.approximately, .fifty, true⟩,
   ⟨.exactly, .beefStroganoff, false⟩, ⟨.approximately, .beefStroganoff, false⟩,
   ⟨.absolutely, .fifty, false⟩, ⟨.absolutely, .full, true⟩,
   ⟨.exactly, .dry, false⟩, ⟨.exactly, .full, false⟩, ⟨.exactly, .three, true⟩,
   ⟨.completely, .dry, true⟩, ⟨.completely, .three, false⟩,
   ⟨.approximately, .three, true⟩, ⟨.approximately, .dry, false⟩,
   ⟨.moreOrLess, .dry, true⟩, ⟨.moreOrLess, .three, false⟩]

/-- **The dualism argument**: the two-type classification reproduces every
cited judgment — approximator acceptability is class match. -/
theorem classification_predicts_distribution :
    ∀ j ∈ Judgment.rows, (compatible j.approximator j.item ↔ j.acceptable) := by
  decide

/-! ### Granularity setting (18)–(19)

Scalar approximators reset the context's granularity parameter:
*exactly* to the finest available level, *approximately* to the coarsest.
The reset targets bound every available interpretation — at the finest
width the denotation interval (12)–(13), `mkGranInterval` is
contained in all others. -/

variable (𝒢 : Finset ℚ) (h𝒢 : 𝒢.Nonempty)

/-- (19a): *exactly* yields the narrowest available interpretation —
its denotation interval sits inside every available one. -/
theorem exactly_narrowest {ε : ℚ} (hε : ε ∈ 𝒢) (d : ℚ) :
    (mkGranInterval ε d).lo ≤ (mkGranInterval (finestWidth 𝒢 h𝒢) d).lo ∧
    (mkGranInterval (finestWidth 𝒢 h𝒢) d).hi ≤ (mkGranInterval ε d).hi :=
  finer_contained _ _ d (finestWidth_le 𝒢 h𝒢 hε)

/-- (19b): *approximately* yields the widest available
interpretation. -/
theorem approximately_widest {ε : ℚ} (hε : ε ∈ 𝒢) (d : ℚ) :
    (mkGranInterval (coarsestWidth 𝒢 h𝒢) d).lo ≤ (mkGranInterval ε d).lo ∧
    (mkGranInterval ε d).hi ≤ (mkGranInterval (coarsestWidth 𝒢 h𝒢) d).hi :=
  finer_contained _ _ d (le_coarsestWidth 𝒢 h𝒢 hε)

/-- A second scalar approximator is vacuous: the first reset leaves a single granularity, on
which resetting in either direction returns the same width. -/
theorem second_reset_vacuous (ε : ℚ) :
    finestWidth {ε} (Finset.singleton_nonempty ε) = ε ∧
    coarsestWidth {ε} (Finset.singleton_nonempty ε) = ε :=
  ⟨finestWidth_singleton ε, coarsestWidth_singleton ε⟩

end SauerlandStateva2011
