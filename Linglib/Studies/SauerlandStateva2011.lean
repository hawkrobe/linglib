/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Degree.Granularity
import Linglib.Fragments.English.NumeralModifiers

/-!
# [sauerland-stateva-2011]: Two Types of Vagueness
[sauerland-stateva-2011] [krifka-2007] [lasersohn-1999]

[sauerland-stateva-2011] argue from the distribution of *approximators* that
vagueness comes in two kinds: **scalar** (point-denoting scalar terms —
numerals, *6 o'clock* — interpreted at a contextual granularity, following
[krifka-2007]) and **epistemic** (*heap*, *Beef Stroganoff* — extension
varies across indistinguishable worlds). Scalar approximators (*exactly*,
*approximately*, *completely*, *more or less*) are granularity *setters*:
their (19) resets the context's granularity parameter to the finest
(*exactly*) or coarsest (*approximately*) available level — here
`Degree.Granularity.finestWidth`/`coarsestWidth`. Epistemic approximators
(*definitely*, *maybe*) quantify over worlds instead, which is why the two
classes distribute complementarily (their §6.2, §6.4) — the argument the
distribution table below reproduces. Their §6.3.5: stacked scalar
approximators are vacuous, since the first reset leaves a singleton
granularity set — `second_reset_vacuous`.

Within the scalar class, endpoint-approximators (*absolutely*,
*completely*, *more or less*) combine only with scale endpoints, blocking
plain *exactly*/*approximately* there (their §6.4, (32), (35)–(45)).

## Main definitions

- `Item`, `ItemClass`: their example expressions and the two-vagueness
  classification
- `Approximator`, `Approximator.selects`: the approximator inventory and
  which item class each selects
- `Judgment.rows`: their cited acceptability judgments ((4)–(6), (35),
  (37), (44)–(45))

## Main results

- `classification_predicts_distribution`: the two-type theory reproduces
  every cited judgment
- `exactly_narrowest`, `approximately_widest`: the reset targets bound all
  available interpretations (their (19), via `finestWidth_le`/
  `le_coarsestWidth` and `finer_contained`)
- `second_reset_vacuous`: approximator stacking is vacuous (their §6.3.5)
- `fragment_setter_directions`: the `English.NumeralModifiers` entries
  carry the setter classification
-/

namespace SauerlandStateva2011

open Degree.Granularity

/-! ### The two-vagueness classification (their §6.3) -/

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
(their §6.4, (32): *absolutely*/*completely*/*more or less* make endpoints
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

/-! ### Granularity setting (their (18)–(19))

Scalar approximators reset the context's granularity parameter:
*exactly* to the finest available level, *approximately* to the coarsest.
The reset targets bound every available interpretation — at the finest
width the denotation interval (their (12)–(13), `mkGranInterval`) is
contained in all others. -/

variable (𝒢 : Finset ℚ) (h𝒢 : 𝒢.Nonempty)

/-- Their (19a): *exactly* yields the narrowest available interpretation —
its denotation interval sits inside every available one. -/
theorem exactly_narrowest {ε : ℚ} (hε : ε ∈ 𝒢) (d : ℚ) :
    (mkGranInterval ε d).lo ≤ (mkGranInterval (finestWidth 𝒢 h𝒢) d).lo ∧
    (mkGranInterval (finestWidth 𝒢 h𝒢) d).hi ≤ (mkGranInterval ε d).hi :=
  finer_contained _ _ d (finestWidth_le 𝒢 h𝒢 hε)

/-- Their (19b): *approximately* yields the widest available
interpretation. -/
theorem approximately_widest {ε : ℚ} (hε : ε ∈ 𝒢) (d : ℚ) :
    (mkGranInterval (coarsestWidth 𝒢 h𝒢) d).lo ≤ (mkGranInterval ε d).lo ∧
    (mkGranInterval ε d).hi ≤ (mkGranInterval (coarsestWidth 𝒢 h𝒢) d).hi :=
  finer_contained _ _ d (le_coarsestWidth 𝒢 h𝒢 hε)

-- Their (12): at grain ½ m, *5 meters* denotes [4.50 m, 5.50 m]; at the
-- finer grain 0.05 m, [4.95 m, 5.05 m].
example : mkGranInterval (1/2 : ℚ) 5 = ⟨9/2, 11/2⟩ := by
  simp only [mkGranInterval]; norm_num
example : mkGranInterval (1/20 : ℚ) 5 = ⟨99/20, 101/20⟩ := by
  simp only [mkGranInterval]; norm_num

/-- Their §6.3.5: a second scalar approximator is vacuous — the first reset
leaves a singleton granularity set, on which resetting (in either
direction) returns the same width. Hence `#exactly approximately 30`. -/
theorem second_reset_vacuous (ε : ℚ) :
    finestWidth {ε} (Finset.singleton_nonempty ε) = ε ∧
    coarsestWidth {ε} (Finset.singleton_nonempty ε) = ε :=
  ⟨finestWidth_singleton ε, coarsestWidth_singleton ε⟩

/-! ### Fragment bridge

The `English.NumeralModifiers` entries carry the setter classification:
exactifiers signal a point distribution and set the finest grain;
tolerance modifiers signal a peaked distribution and set a coarser one. -/

open English.NumeralModifiers in
/-- The fragment's *exactly*/*precisely* are finest-setters (pointSignal
exactifiers) and its *about*/*around*/*approximately*/*roughly* are
coarse-setters (peakedSignal tolerance modifiers). -/
theorem fragment_setter_directions :
    exactly.modType = .exactifier ∧ exactly.pragFunction = .pointSignal ∧
    precisely.modType = .exactifier ∧ precisely.pragFunction = .pointSignal ∧
    approximately.modType = .tolerance ∧
    approximately.pragFunction = .peakedSignal ∧
    about.modType = .tolerance ∧ about.pragFunction = .peakedSignal := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SauerlandStateva2011
