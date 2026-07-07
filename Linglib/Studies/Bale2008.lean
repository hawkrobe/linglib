import Linglib.Semantics.Degree.Hom
import Linglib.Semantics.Degree.Basic

/-!
# Bale (2008): A Universal Scale of Comparison
[bale-2008]

Direct comparisons (*Seymour is taller than he is wide*) and indirect
comparisons (*Esme is more beautiful than Einstein is intelligent*)
unified through a Universal Scale Ω ≅ ℚ ∩ (0, 1]: individuals map to a
primary scale built from an adjectival quasi-order restricted to a
comparison class ([cresswell-1976]-style equivalence classes), and the
homomorphism ℌ maps each class to the universal degree encoding its
relative position (`Degree.relativeRank`). `MORE` compares universal
degrees (`λμ λd λx. μ(x) ≻ d`), so cross-scale comparison is
well-typed; direct comparison is the special case where a measurement
system structures both primary scales identically.

Formalized: the ten-member committee model with the beauty and
intelligence orders, the (19a)/(19b) truth-value contrast, preservation
of the primary order under ℌ, robustness of universal degrees under
adding equally-ranked members (degrees count equivalence classes, not
individuals), and the for-clause prediction that class-relative ranks
can invert raw measurements (*taller for a boy than wide for a boy*
false for a Seymour who is extremely wide but average in height).
-/

namespace Bale2008

open Degree

/-! ### The committee model (§4.2, Figs. 4–5) -/

/-- The ten committee members `a`–`j`. -/
inductive Member where
  | a | b | c | d | e | f | g | h | i | j
  deriving DecidableEq, Repr

/-- Position in the beauty primary scale, bottom = 0: the order
    a → b → c → d → e → f → g → h → i → j from most to least beautiful. -/
def beautyPos : Member → Fin 10
  | .a => 9 | .b => 8 | .c => 7 | .d => 6 | .e => 5
  | .f => 4 | .g => 3 | .h => 2 | .i => 1 | .j => 0

/-- Position in the intelligence primary scale: the order
    i → f → j → g → h → a → d → b → e → c from most to least intelligent. -/
def intelligencePos : Member → Fin 10
  | .i => 9 | .f => 8 | .j => 7 | .g => 6 | .h => 5
  | .a => 4 | .d => 3 | .b => 2 | .e => 1 | .c => 0

/-- Universal beauty degree: ℌ applied to the member's class in the
    beauty scale. Betty (`b`) receives `d_{9/10}` as in Fig. 4. -/
def universalBeauty (m : Member) : ℚ := relativeRank (beautyPos m)

/-- Universal intelligence degree; Heather (`h`) receives `d_{6/10}`
    as in Fig. 5. -/
def universalIntelligence (m : Member) : ℚ := relativeRank (intelligencePos m)

/-- ℌ on a ten-class scale: position `k` from the bottom receives
    `d_{(k+1)/10}` (Figs. 4–5's degree labels). -/
theorem relativeRank_fin10 (k : Fin 10) : relativeRank k = (k.1 + 1 : ℚ) / 10 := by
  have h : (Finset.univ.filter (· ≤ k)).card = k.1 + 1 := by revert k; decide
  unfold relativeRank
  rw [h, Fintype.card_fin]
  push_cast
  ring

example : universalBeauty .b = 9/10 := by
  simp [universalBeauty, beautyPos, relativeRank_fin10]
  norm_num
example : universalIntelligence .h = 6/10 := by
  simp [universalIntelligence, intelligencePos, relativeRank_fin10]
  norm_num

/-- (19a) *Betty is more beautiful for a committee member than Heather
    is intelligent* — true: `d_{9/10} ≻ d_{6/10}`. -/
theorem betty_beautiful_gt_heather_intelligent :
    universalIntelligence .h < universalBeauty .b := by
  simp [universalBeauty, universalIntelligence, beautyPos, intelligencePos,
        relativeRank_fin10]
  norm_num

/-- (19b) *Betty is more intelligent for a committee member than Evelin
    is beautiful* — false: `d_{3/10} ⊁ d_{6/10}`. -/
theorem betty_intelligent_not_gt_evelin_beautiful :
    ¬ universalBeauty .e < universalIntelligence .b := by
  simp [universalBeauty, universalIntelligence, beautyPos, intelligencePos,
        relativeRank_fin10]
  norm_num

/-- Indirect comparison IS the point-standard comparative over universal
    degrees: Bale's `MORE = λμ λd λx. μ(x) ≻ d` instantiated at the
    than-clause degree. -/
theorem more_eq_comparativeSem (x y : Member) :
    universalIntelligence y < universalBeauty x ↔
      (universalBeauty x > universalIntelligence y) :=
  Iff.rfl

/-- ℌ preserves the primary scale (§3.2): within one scale, indirect
    comparison agrees with direct rank comparison. -/
theorem universalBeauty_lt_iff (x y : Member) :
    universalBeauty x < universalBeauty y ↔ beautyPos x < beautyPos y :=
  relativeRank_strictMono.lt_iff_lt

/-! ### Robustness (§4.2, Figs. 6–9): degrees count classes -/

/-- The expanded committee: five extra members, each exactly as
    beautiful as an original member (`b' ≈ b`, `a' ≈ b`, `c' ≈ c`,
    `d' ≈ d`, `e' ≈ e` per Fig. 6). -/
inductive Member' where
  | old (m : Member) | a' | b' | c' | d' | e'
  deriving DecidableEq, Repr

/-- Beauty class in the expanded model: equivalent members share a
    class, so the scale still has ten positions. -/
def beautyPos' : Member' → Fin 10
  | .old m => beautyPos m
  | .a' => 8 | .b' => 8 | .c' => 7 | .d' => 6 | .e' => 5

/-- Universal degrees are unchanged by adding equally-ranked members:
    the assignment "is based on the number of equivalence classes in
    the domain rather than the number of individuals". -/
theorem universalBeauty_stable (m : Member) :
    relativeRank (beautyPos' (.old m)) = universalBeauty m := rfl

/-! ### For-clauses strip measurements (§1, §4.1) -/

/-- Five boys with height and width measurements (in feet): Seymour is
    5 ft tall — dead average — but 4 ft wide — the widest by far. -/
inductive Boy where
  | seymour | huey | dewey | louie | webby
  deriving DecidableEq, Repr

def heightFt : Boy → ℚ
  | .seymour => 5 | .huey => 6 | .dewey => 55/10 | .louie => 45/10 | .webby => 4

def widthFt : Boy → ℚ
  | .seymour => 4 | .huey => 2 | .dewey => 15/10 | .louie => 1 | .webby => 1/2

/-- Class-relative height position among the boys (Seymour: middle). -/
def heightPos : Boy → Fin 5
  | .huey => 4 | .dewey => 3 | .seymour => 2 | .louie => 1 | .webby => 0

/-- Class-relative width position among the boys (Seymour: top). -/
def widthPos : Boy → Fin 5
  | .seymour => 4 | .huey => 3 | .dewey => 2 | .louie => 1 | .webby => 0

/-- *Seymour is taller for a boy than he is wide for a boy* is FALSE
    "despite the fact that the measurement of his height is greater
    than the measurement of his width": for-clauses restrict the
    primary scales to measurement-free class-relative ones, on which
    Seymour's width position exceeds his height position. -/
theorem seymour_for_a_boy :
    widthFt .seymour < heightFt .seymour ∧
      ¬ relativeRank (widthPos .seymour) < relativeRank (heightPos .seymour) := by
  have h5 : ∀ k : Fin 5, relativeRank k = (k.1 + 1 : ℚ) / 5 := by
    intro k
    have h : (Finset.univ.filter (· ≤ k)).card = k.1 + 1 := by revert k; decide
    unfold relativeRank
    rw [h, Fintype.card_fin]
    push_cast
    ring
  refine ⟨by norm_num [widthFt, heightFt], ?_⟩
  simp [widthPos, heightPos, h5]
  norm_num

end Bale2008
