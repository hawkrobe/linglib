import Mathlib.Data.Rat.Defs

/-!
# @cite{schlotterbeck-wang-2023} — Incremental RSA for Adjective Ordering

Schlotterbeck, F. & Wang, H. (2023). An incremental RSA model for adjective
ordering preferences in referential visual context. *Proceedings of the Society
for Computation in Linguistics (SCiL)* 6, 121–132.

## The Model

The incremental sequence speaker (S1^seq) produces adjective–noun sequences
word-by-word. At each step the utility is the incremental listener's posterior.
The trajectory score accumulates utility across all prefixes:

  S1^seq(w₁,...,wₙ | r) ∝ ∏ₖ U(w₁,...,wₖ; r)

where U(w⃗; r) = exp(β · log L0^inc(r | w⃗)) and the paper sets β = 1 in all
reported simulations. With β = 1, no cost, and uniform language prior, this
simplifies to:

  S1^seq(w₁,...,wₙ | r) = ∏ₖ L0(r | w₁,...,wₖ)

The model uses continuous/noisy semantics (@cite{degen-etal-2020}) where each
word applies with reliability v (correct application) or 1 − v (noise).

**Key insight** (Proposition 1 in the paper): With strictly positive noisy
semantics, the batch L0 (normalize once after all words) equals the incremental
L0 (normalize after each word). Since the batch L0 is a product of word
meanings divided by its normalizer, and ℚ multiplication commutes, L0 is
order-independent: L0(r | w₁, w₂) = L0(r | w₂, w₁). Therefore S1^seq ordering
preference reduces entirely to first-word informativity.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | L0 is order-independent | `l0_swap_A`, `l0_swap_B` |
| 2 | Ordering ratio = first-word informativity ratio | `trajectory_ratio_A`, `trajectory_ratio_B` |
| 3 | Size discriminatory → size-first preferred | `size_first_when_size_discriminates` |
| 4 | Equal discrimination + color reliable → color-first | `color_first_when_color_reliable` |
| 5 | Both orderings identify the target | `both_orderings_identify_target_A` |
| 6 | Both orderings identify the target | `both_orderings_identify_target_B` |

## Note on Parameters

The paper's actual model uses Gaussian perception with Weber fractions for size
and a noise parameter ε for color (@cite{degen-etal-2020}). Our formalization
uses a simplified noise model with reliability parameters sizeRel and colorRel.
The specific parameter values are chosen to demonstrate the qualitative
predictions — they are not taken from the paper.
-/

set_option autoImplicit false

namespace Phenomena.WordOrder.Studies.SchlotterbeckWang2023

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Object size in the reference game. -/
inductive Size where
  | big | small
  deriving DecidableEq, BEq, Repr

/-- Object color in the reference game. -/
inductive Color where
  | blue | green | red
  deriving DecidableEq, BEq, Repr

/-- A referent has a size and a color. -/
structure Referent where
  size : Size
  color : Color
  deriving DecidableEq, BEq, Repr

/-- Words available to the speaker: size adjectives, color adjectives, noun. -/
inductive Word where
  | big | small | blue | green | red | sticker
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. Scene Configuration
-- ============================================================================

/-- A reference game scene: objects, target, and perceptual reliability. -/
structure SceneConfig where
  /-- Objects in the visual display. -/
  refs : List Referent
  /-- The target referent the speaker wants to identify. -/
  target : Referent
  /-- Perceptual reliability for size adjectives (0 < v < 1). -/
  sizeRel : ℚ
  /-- Perceptual reliability for color adjectives (0 < v < 1). -/
  colorRel : ℚ

-- ============================================================================
-- §3. Noisy / Continuous Semantics
-- ============================================================================

/-- Noisy word meaning: P(word correctly applies to referent).
    If the word is true of the referent, returns the reliability v;
    otherwise returns the noise floor 1 − v. The noun "sticker" applies
    universally (all referents are stickers).
    Simplified from @cite{degen-etal-2020}'s continuous semantics. -/
def wordMeaning (sRel cRel : ℚ) (w : Word) (r : Referent) : ℚ :=
  match w with
  | .big     => if r.size == .big then sRel else 1 - sRel
  | .small   => if r.size == .small then sRel else 1 - sRel
  | .blue    => if r.color == .blue then cRel else 1 - cRel
  | .green   => if r.color == .green then cRel else 1 - cRel
  | .red     => if r.color == .red then cRel else 1 - cRel
  | .sticker => 1

-- ============================================================================
-- §4. Incremental Literal Listener
-- ============================================================================

/-- L0 posterior: P(r | w₁,...,wₙ) under uniform prior.

    With strictly positive noisy semantics, the incremental L0 (normalize
    after each word) equals the batch L0 (normalize once after all words).
    The intermediate normalizations cancel because all word meanings are
    strictly positive — no referent is ever zeroed out. -/
def l0 (cfg : SceneConfig) (words : List Word) (r : Referent) : ℚ :=
  let score := words.foldl (λ acc w => acc * wordMeaning cfg.sizeRel cfg.colorRel w r) 1
  let total := cfg.refs.foldl (λ acc r' =>
    acc + words.foldl (λ a w => a * wordMeaning cfg.sizeRel cfg.colorRel w r') 1) 0
  if total == 0 then 0 else score / total

-- ============================================================================
-- §5. Incremental Sequence Speaker (S1^seq)
-- ============================================================================

/-- S1^seq trajectory score (unnormalized, accumulator version).

    Computes ∏ₖ₌₁ⁿ L0(r | w₁,...,wₖ)^β by walking through the utterance
    word by word, extending the context prefix at each step. -/
def s1seqScoreAux (cfg : SceneConfig) (ctx : List Word)
    (remaining : List Word) (β : Nat) (acc : ℚ) : ℚ :=
  match remaining with
  | [] => acc
  | w :: ws =>
    let pfx := ctx ++ [w]
    let score := (l0 cfg pfx cfg.target) ^ β
    s1seqScoreAux cfg pfx ws β (acc * score)

/-- S1^seq trajectory score for a complete utterance. -/
def s1seqScore (cfg : SceneConfig) (utt : List Word) (β : Nat) : ℚ :=
  s1seqScoreAux cfg [] utt β 1

-- ============================================================================
-- §6. Experimental Scenes
-- ============================================================================

/-- **Scene A**: Size-discriminatory scene.

    Objects: {big-blue, small-blue, small-green, small-red}
    Target: big-blue

    "big" uniquely identifies the target (1/4 objects are big).
    "blue" only partially identifies (2/4 objects are blue).
    With sizeRel > colorRel, the size adjective is both more discriminatory
    and more reliable — strongly favoring size-first ordering. -/
def sceneA : SceneConfig where
  refs := [⟨.big, .blue⟩, ⟨.small, .blue⟩, ⟨.small, .green⟩, ⟨.small, .red⟩]
  target := ⟨.big, .blue⟩
  sizeRel := 99/100
  colorRel := 95/100

/-- **Scene B**: Equal-discrimination scene with color more reliable.

    Objects: {big-blue, big-green, small-blue, small-green}
    Target: big-blue

    Both "big" and "blue" narrow to 2/4 referents (equal discrimination).
    But color is more reliable: colorRel (95/100) > sizeRel (80/100).
    So "blue" is the more informative first word, favoring color-first. -/
def sceneB : SceneConfig where
  refs := [⟨.big, .blue⟩, ⟨.big, .green⟩, ⟨.small, .blue⟩, ⟨.small, .green⟩]
  target := ⟨.big, .blue⟩
  sizeRel := 80/100
  colorRel := 95/100

-- Helper: construct orderings for a target
private def sizeFirstUtt (r : Referent) : List Word :=
  let sizeAdj := match r.size with | .big => Word.big | .small => .small
  let colorAdj := match r.color with | .blue => .blue | .green => .green | .red => .red
  [sizeAdj, colorAdj, .sticker]

private def colorFirstUtt (r : Referent) : List Word :=
  let sizeAdj := match r.size with | .big => Word.big | .small => .small
  let colorAdj := match r.color with | .blue => .blue | .green => .green | .red => .red
  [colorAdj, sizeAdj, .sticker]

-- ============================================================================
-- §7. Findings
-- ============================================================================

/-- Qualitative findings from the incremental RSA adjective ordering model. -/
inductive Finding where
  /-- L0 is order-independent for the adjective pair in each scene. -/
  | l0_order_independent
  /-- When size has high discriminatory power, size-first ordering is
      preferred: S1^seq("big blue sticker") > S1^seq("blue big sticker"). -/
  | size_first_when_size_discriminates
  /-- When both properties discriminate equally but color is more
      reliable, color-first is preferred. -/
  | color_first_when_color_reliable
  /-- L0 correctly identifies the target after both adjectives (scene A). -/
  | both_orderings_identify_target_A
  /-- L0 correctly identifies the target after both adjectives (scene B). -/
  | both_orderings_identify_target_B
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §8. L0 Order Independence
-- ============================================================================

/-- L0 is order-independent for the adjective pair [big, blue] in Scene A.
    This follows from commutativity of ℚ multiplication: both the numerator
    (product of word meanings for one referent) and each summand of the
    denominator are commutative products. -/
theorem l0_swap_A :
    ∀ r ∈ sceneA.refs,
      l0 sceneA [.big, .blue] r = l0 sceneA [.blue, .big] r := by
  native_decide

/-- L0 is order-independent for the adjective pair [big, blue] in Scene B. -/
theorem l0_swap_B :
    ∀ r ∈ sceneB.refs,
      l0 sceneB [.big, .blue] r = l0 sceneB [.blue, .big] r := by
  native_decide

-- ============================================================================
-- §9. First-Word Informativity Determines Ordering
-- ============================================================================

/-- The paper sets β = 1 in all reported simulations. -/
private def β : Nat := 1

section FirstWordInformativity

/-- In Scene A, "big" is more informative than "blue" about the target. -/
theorem big_more_informative_A :
    l0 sceneA [.big] sceneA.target > l0 sceneA [.blue] sceneA.target := by
  native_decide

/-- In Scene B, "blue" is more informative than "big" about the target. -/
theorem blue_more_informative_B :
    l0 sceneB [.blue] sceneB.target > l0 sceneB [.big] sceneB.target := by
  native_decide

/-- **Trajectory ratio reduction (Scene A)**: the ratio of trajectory scores
    for the two orderings equals the ratio of first-word informativity.

    Since L0 is order-independent, the trajectory scores differ only in their
    first factor. In cross-multiplication form:
      s1seq([big,blue,sticker]) · L0(target|blue) =
      s1seq([blue,big,sticker]) · L0(target|big)

    This is the paper's central theoretical result: the entire 3-word trajectory
    comparison collapses to a single-word informativity comparison. -/
theorem trajectory_ratio_A :
    s1seqScore sceneA (sizeFirstUtt sceneA.target) β *
      l0 sceneA [.blue] sceneA.target =
    s1seqScore sceneA (colorFirstUtt sceneA.target) β *
      l0 sceneA [.big] sceneA.target := by
  native_decide

/-- **Trajectory ratio reduction (Scene B)**: same structure, color-first
    side has the higher first-word informativity. -/
theorem trajectory_ratio_B :
    s1seqScore sceneB (colorFirstUtt sceneB.target) β *
      l0 sceneB [.big] sceneB.target =
    s1seqScore sceneB (sizeFirstUtt sceneB.target) β *
      l0 sceneB [.blue] sceneB.target := by
  native_decide

end FirstWordInformativity

-- ============================================================================
-- §10. Verified Predictions
-- ============================================================================

section Predictions

/-- **Finding**: When size has high discriminatory power (Scene A),
    S1^seq prefers size-first ordering. -/
theorem size_first_when_size_discriminates :
    s1seqScore sceneA (sizeFirstUtt sceneA.target) β >
    s1seqScore sceneA (colorFirstUtt sceneA.target) β := by
  native_decide

/-- **Finding**: When both properties discriminate equally but color is
    more reliable (Scene B), S1^seq prefers color-first ordering. -/
theorem color_first_when_color_reliable :
    s1seqScore sceneB (colorFirstUtt sceneB.target) β >
    s1seqScore sceneB (sizeFirstUtt sceneB.target) β := by
  native_decide

/-- After hearing both adjectives, L0 assigns highest probability to the
    target in Scene A. -/
theorem both_orderings_identify_target_A :
    ∀ r ∈ sceneA.refs, r ≠ sceneA.target →
      l0 sceneA [.big, .blue] sceneA.target > l0 sceneA [.big, .blue] r := by
  native_decide

/-- After hearing both adjectives, L0 assigns highest probability to the
    target in Scene B. -/
theorem both_orderings_identify_target_B :
    ∀ r ∈ sceneB.refs, r ≠ sceneB.target →
      l0 sceneB [.big, .blue] sceneB.target > l0 sceneB [.big, .blue] r := by
  native_decide

/-- The ordering preference flips between scenes: Scene A prefers size-first,
    Scene B prefers color-first. This captures @cite{schlotterbeck-wang-2023}'s
    key prediction: the preferred ordering depends on the discriminatory
    structure of the scene, not a fixed ordering rule. -/
theorem ordering_preference_flips :
    s1seqScore sceneA (sizeFirstUtt sceneA.target) β >
    s1seqScore sceneA (colorFirstUtt sceneA.target) β ∧
    s1seqScore sceneB (colorFirstUtt sceneB.target) β >
    s1seqScore sceneB (sizeFirstUtt sceneB.target) β := by
  exact ⟨size_first_when_size_discriminates, color_first_when_color_reliable⟩

end Predictions

-- ============================================================================
-- §11. Verification
-- ============================================================================

/-- Map each finding to the model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .l0_order_independent =>
      (∀ r ∈ sceneA.refs, l0 sceneA [.big, .blue] r = l0 sceneA [.blue, .big] r) ∧
      (∀ r ∈ sceneB.refs, l0 sceneB [.big, .blue] r = l0 sceneB [.blue, .big] r)
  | .size_first_when_size_discriminates =>
      s1seqScore sceneA (sizeFirstUtt sceneA.target) β >
      s1seqScore sceneA (colorFirstUtt sceneA.target) β
  | .color_first_when_color_reliable =>
      s1seqScore sceneB (colorFirstUtt sceneB.target) β >
      s1seqScore sceneB (sizeFirstUtt sceneB.target) β
  | .both_orderings_identify_target_A =>
      ∀ r ∈ sceneA.refs, r ≠ sceneA.target →
        l0 sceneA [.big, .blue] sceneA.target > l0 sceneA [.big, .blue] r
  | .both_orderings_identify_target_B =>
      ∀ r ∈ sceneB.refs, r ≠ sceneB.target →
        l0 sceneB [.big, .blue] sceneB.target > l0 sceneB [.big, .blue] r

/-- All 5 findings verified. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact ⟨l0_swap_A, l0_swap_B⟩
  · exact size_first_when_size_discriminates
  · exact color_first_when_color_reliable
  · exact both_orderings_identify_target_A
  · exact both_orderings_identify_target_B

end Phenomena.WordOrder.Studies.SchlotterbeckWang2023
