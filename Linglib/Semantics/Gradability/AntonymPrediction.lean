import Linglib.Semantics.Gradability.Basic
import Linglib.Semantics.Gradability.Antonymy
import Linglib.Semantics.Gradability.AntonymQuadruplet
/-!
# Antonym Prediction — Two Extensional Denotations + Prediction Skeleton

[cruse-1986] [horn-1989] [krifka-2007b]

For the four-form quadruplet of a negated antonymic adjective pair (see
`AntonymQuadruplet.lean`), the literature contests two extensional
denotations:

- **Contradictory denotation** — single threshold `θ`. Both poles share `θ`;
  *not unhappy* reduces (DNE) to *happy*. Captured by
  `AntonymForm.contradictoryDenot`.

- **Strengthened denotation** — two thresholds with `tp.neg ≤ tp.pos`. The
  borderline region `[tp.neg, tp.pos]` lifts *not unhappy* away from *happy*,
  creating the polarity asymmetry. Captured by
  `AntonymForm.strengthenedDenot`.

The two denotations are anchored by the substrate theorems
`contradictoryDenot_synonymy` (DNE collapse) and
`strengthenedDenot_breaks_synonymy` (gap exists).

The **prediction skeleton** `predictionForAntonymy : NegationType →
Asymmetry` reads off Fragment-level antonymy classification (contrary
vs contradictory) to predict the polarity-behaviour direction. It is
anchored in the two denotation theorems: contradictory antonymy entails
DNE (symmetric) and contrary antonymy admits the strengthened gap
(asymmetric).

Per-paper analyses (Krifka's BiOT derivation, Tessler-Franke's RSA scoring,
Alexandropoulou-Gotzner's three-case typology) consume these substrate
primitives via `Iff.rfl` bridges that survive substrate transparency
(both denotations are `abbrev`s).
-/

namespace Semantics.Gradability

open Core.Scale (Degree Threshold)
open Features (NegationType Asymmetry)
open Semantics.Degree (positiveMeaning negativeMeaning antonymMeaning)

-- ============================================================================
-- § 1. Two Extensional Denotations
-- ============================================================================

/-- **Contradictory denotation** of an antonym form on a single threshold `θ`.
    Both poles share `θ`; the four forms collapse to two distinct truth
    values (positive/notNegative ≡ `d > θ`; notPositive/negative ≡ `d ≤ θ`).
    This is the literal-semantic position [krifka-2007b] attributes to
    antonyms before pragmatic strengthening. -/
abbrev AntonymForm.contradictoryDenot {max : Nat} (θ : Threshold max)
    (q : AntonymForm) (d : Degree max) : Prop :=
  match q with
  | .positive    => positiveMeaning d θ      -- d > θ
  | .notPositive => ¬ positiveMeaning d θ    -- d ≤ θ
  | .negative    => ¬ positiveMeaning d θ    -- d ≤ θ (same! contradictory antonym)
  | .notNegative => positiveMeaning d θ      -- d > θ (DNE restores positive)

/-- **Strengthened denotation** of an antonym form on a `ThresholdPair`. Two
    thresholds `tp.neg ≤ tp.pos`; the borderline region `[tp.neg, tp.pos]`
    lifts notNegative ("not unhappy") away from positive ("happy") and
    notPositive ("not happy") away from negative ("unhappy"). This is the
    effective-semantic position post-pragmatic-strengthening (Krifka 2007 §4)
    or the lexically-encoded position (Alexandropoulou-Gotzner 2024). -/
abbrev AntonymForm.strengthenedDenot {max : Nat} (tp : ThresholdPair max)
    (q : AntonymForm) (d : Degree max) : Prop :=
  match q with
  | .positive    => positiveMeaning' d tp        -- d > tp.pos
  | .notPositive => contradictoryNeg d tp.pos    -- d ≤ tp.pos
  | .negative    => contraryNegMeaning d tp      -- d < tp.neg
  | .notNegative => notContraryNegMeaning d tp   -- d ≥ tp.neg

-- ============================================================================
-- § 2. Anchor Theorems
-- ============================================================================

/-- Under the contradictory denotation, the `negative`-`notPositive` and
    `notNegative`-`positive` form pairs are extensionally identical. This is
    the formal puzzle [krifka-2007b] solves pragmatically: literal
    contradictory semantics predicts *not unhappy* ≡ *happy*. -/
theorem contradictoryDenot_synonymy {max : Nat}
    (θ : Threshold max) (d : Degree max) :
    (AntonymForm.contradictoryDenot θ .negative d ↔
     AntonymForm.contradictoryDenot θ .notPositive d) ∧
    (AntonymForm.contradictoryDenot θ .notNegative d ↔
     AntonymForm.contradictoryDenot θ .positive d) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Under the strengthened denotation with strict gap (`tp.neg < tp.pos`),
    the `notNegative` and `positive` extensions come apart: there exists a
    degree (the negative threshold itself) where *not unhappy* holds but
    *happy* does not. This is the witness for the polarity asymmetry. -/
theorem strengthenedDenot_breaks_synonymy {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max,
      AntonymForm.strengthenedDenot tp .notNegative d ∧
      ¬ AntonymForm.strengthenedDenot tp .positive d :=
  Antonymy.contrary_gap_exists tp h

-- ============================================================================
-- § 3. Prediction Skeleton
-- ============================================================================

/-- **Anchored prediction skeleton.** Map an antonymy type to predicted
    polarity-asymmetry direction:

    - `.contradictory ↦ .symmetric` — anchored by `contradictoryDenot_synonymy`
      (the contradictory base collapses notPositive and negative; no asymmetry
      to derive).
    - `.contrary ↦ .asymmetric` — anchored by `strengthenedDenot_breaks_synonymy`
      (the strengthened semantics admits a witness where notNegative holds but
      positive does not).

    Consumed by per-paper prediction signatures (Horn 1989, Krifka 2007,
    Alexandropoulou-Gotzner 2024 JoS) which read this map via
    `predictionForEntry` against a Fragment lexical entry's
    `antonymRelation` field. -/
def predictionForAntonymy : NegationType → Asymmetry
  | .contradictory => .symmetric
  | .contrary      => .asymmetric

/-- Read prediction off a Fragment lexical entry's `antonymRelation`. Defaults
    to `.symmetric` for entries without an explicit antonymy classification. -/
def predictionForEntry (e : GradableAdjEntry) : Asymmetry :=
  e.antonymRelation.elim .symmetric predictionForAntonymy

end Semantics.Gradability
