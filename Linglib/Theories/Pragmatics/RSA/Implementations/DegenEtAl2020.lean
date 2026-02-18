/-
Degen, Hawkins, Graf, Kreiss & Goodman (2020).
*When redundancy is useful*. Psychological Review 127(4).

cs-RSA: continuous semantics (φ ∈ [0,1]) explains "overinformative" referring expressions
via asymmetric noise across feature types (color reliable, size noisy).
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Core.ProductOfExperts
import Mathlib.Data.Rat.Defs

namespace RSA.ContinuousSemantics

/-- Colors for reference game objects. -/
inductive Color where
  | blue | green | red | yellow | purple | orange
  deriving DecidableEq, BEq, Repr

/-- Size categories -/
inductive Size where
  | small | medium | large
  deriving DecidableEq, BEq, Repr

/-- Object types (nominals) -/
inductive ObjType where
  | pin | banana | apple | carrot | tomato | ball
  deriving DecidableEq, BEq, Repr

/-- An object in the reference game has type, color, and size -/
structure Object where
  objType : ObjType
  color : Color
  size : Size
  deriving DecidableEq, BEq, Repr

/-- Components of a referring expression -/
structure ReferringExpression where
  /-- Nominal (type word): "pin", "banana", etc. -/
  nominal : Option ObjType
  /-- Color adjective: "blue", "red", etc. -/
  colorAdj : Option Color
  /-- Size adjective: "small", "large", etc. -/
  sizeAdj : Option Size
  deriving DecidableEq, BEq, Repr

/-- Smart constructor for common utterance patterns -/
def RE.bare (t : ObjType) : ReferringExpression :=
  { nominal := some t, colorAdj := none, sizeAdj := none }

def RE.withColor (t : ObjType) (c : Color) : ReferringExpression :=
  { nominal := some t, colorAdj := some c, sizeAdj := none }

def RE.withSize (t : ObjType) (s : Size) : ReferringExpression :=
  { nominal := some t, colorAdj := none, sizeAdj := some s }

def RE.withBoth (t : ObjType) (c : Color) (s : Size) : ReferringExpression :=
  { nominal := some t, colorAdj := some c, sizeAdj := some s }

/-- Typicality prior P(color | type). -/
def typicality : ObjType → Color → ℚ
  -- Bananas: typically yellow
  | .banana, .yellow => 9/10
  | .banana, .green => 1/20    -- unripe
  | .banana, .blue => 1/100    -- very atypical
  | .banana, _ => 1/100
  -- Apples: red or green
  | .apple, .red => 45/100
  | .apple, .green => 45/100
  | .apple, .yellow => 8/100
  | .apple, _ => 1/100
  -- Carrots: typically orange
  | .carrot, .orange => 85/100
  | .carrot, _ => 3/100
  -- Tomatoes: typically red
  | .tomato, .red => 9/10
  | .tomato, .green => 8/100   -- unripe
  | .tomato, _ => 1/100
  -- Pins & balls: uniform
  | .pin, _ => 1/5
  | .ball, _ => 1/5

/-- Noise parameters for continuous semantics. Color is more reliable than size. -/
structure SemanticParams where
  /-- Semantic value when color matches -/
  colorMatch : ℚ := 99/100
  /-- Semantic value when color doesn't match -/
  colorMismatch : ℚ := 1/100
  /-- Semantic value when size matches -/
  sizeMatch : ℚ := 8/10
  /-- Semantic value when size doesn't match -/
  sizeMismatch : ℚ := 2/10
  /-- Semantic value when type matches -/
  typeMatch : ℚ := 1
  /-- Semantic value when type doesn't match -/
  typeMismatch : ℚ := 0
  deriving Repr

/-- Default parameters from Degen et al. (2020) -/
def defaultParams : SemanticParams := {}

/-- High-noise size parameter (for comparison) -/
def highNoiseSizeParams : SemanticParams :=
  { sizeMatch := 7/10, sizeMismatch := 3/10 }

/-- Hypothetical material parameters (Kursat & Degen 2021): lower discrimination than size. -/
def materialParams : SemanticParams :=
  { colorMatch := 99/100
  , colorMismatch := 1/100
  , sizeMatch := 8/10
  , sizeMismatch := 2/10
  -- Material would need to be added to SemanticParams to use directly
  -- For now, we note the hypothetical values:
  -- materialMatch := 7/10
  -- materialMismatch := 3/10
  -- Discrimination = 0.40 (lower than size's 0.60)
  }

/-- Continuous semantic value φ(u, o) = φ_type × φ_color × φ_size ∈ [0, 1].
Product of Experts: each feature acts as an independent noisy channel. -/
def φ (params : SemanticParams) (u : ReferringExpression) (o : Object) : ℚ :=
  let typeVal := match u.nominal with
    | none => 1  -- No type constraint
    | some t => if t == o.objType then params.typeMatch else params.typeMismatch
  let colorVal := match u.colorAdj with
    | none => 1  -- No color constraint
    | some c => if c == o.color then params.colorMatch else params.colorMismatch
  let sizeVal := match u.sizeAdj with
    | none => 1  -- No size constraint
    | some s => if s == o.size then params.sizeMatch else params.sizeMismatch
  typeVal * colorVal * sizeVal

/-- φ is the unnormalized PoE of three feature experts. -/
theorem φ_is_product_of_experts (params : SemanticParams)
    (u : ReferringExpression) (o : Object) :
    φ params u o = Core.ProductOfExperts.unnormalizedProduct
      [λ _ => match u.nominal with
         | none => 1
         | some t => if t == o.objType then params.typeMatch else params.typeMismatch,
       λ _ => match u.colorAdj with
         | none => 1
         | some c => if c == o.color then params.colorMatch else params.colorMismatch,
       λ _ => match u.sizeAdj with
         | none => 1
         | some s => if s == o.size then params.sizeMatch else params.sizeMismatch]
      () := by
  simp only [φ, Core.ProductOfExperts.unnormalizedProduct, List.foldl, one_mul]

/-- Utterance cost = word count. -/
def utteranceCost (u : ReferringExpression) : ℚ :=
  let nominal := if u.nominal.isSome then 1 else 0
  let color := if u.colorAdj.isSome then 1 else 0
  let size := if u.sizeAdj.isSome then 1 else 0
  nominal + color + size

structure CSRSAParams where
  utterances : List ReferringExpression
  objects : List Object
  params : SemanticParams := defaultParams
  α : ℕ := 1
  costWeight : ℚ := 1/10

def csRSAScenario
    (utterances : List ReferringExpression)
    (objects : List Object)
    (params : SemanticParams := defaultParams)
    (α : ℕ := 1)
    (costWeight : ℚ := 1/10) : CSRSAParams :=
  { utterances, objects, params, α, costWeight }

/-- Compute S1 distribution for a cs-RSA scenario -/
def csRSA_S1 (scenario : CSRSAParams) (target : Object) : List (ReferringExpression × ℚ) :=
  RSA.Eval.basicS1
    scenario.utterances
    scenario.objects
    (λ u w => φ scenario.params u w)
    (λ _ => 1)  -- Uniform object prior
    scenario.α
    (λ u => scenario.costWeight * utteranceCost u)
    target

/-- Scene 1: Color-sufficient discrimination (blue pin vs red pin) -/
def scene1_objects : List Object := [
  ⟨.pin, .blue, .small⟩,   -- Target
  ⟨.pin, .red, .small⟩     -- Distractor (same size, different color)
]

/-- Scene 2: Size-sufficient discrimination (small pin vs large pin) -/
def scene2_objects : List Object := [
  ⟨.pin, .blue, .small⟩,   -- Target
  ⟨.pin, .blue, .large⟩    -- Distractor (same color, different size)
]

/-- Scene 3: Both needed (small blue pin vs large blue pin vs small red pin) -/
def scene3_objects : List Object := [
  ⟨.pin, .blue, .small⟩,   -- Target
  ⟨.pin, .blue, .large⟩,   -- Same color, different size
  ⟨.pin, .red, .small⟩     -- Same size, different color
]

/-- Scene 4: Typicality scene (yellow banana vs blue banana) -/
def scene4_objects : List Object := [
  ⟨.banana, .yellow, .medium⟩,  -- Typical
  ⟨.banana, .blue, .medium⟩     -- Atypical
]

/-- Utterances for pin scenes -/
def pinUtterances : List ReferringExpression := [
  RE.bare .pin,
  RE.withColor .pin .blue,
  RE.withColor .pin .red,
  RE.withSize .pin .small,
  RE.withSize .pin .large,
  RE.withBoth .pin .blue .small,
  RE.withBoth .pin .blue .large,
  RE.withBoth .pin .red .small
]

/-- Utterances for banana scene -/
def bananaUtterances : List ReferringExpression := [
  RE.bare .banana,
  RE.withColor .banana .yellow,
  RE.withColor .banana .blue
]

/-- cs-RSA scenario for Scene 1 -/
def csScenario1 := csRSAScenario pinUtterances scene1_objects

/-- cs-RSA scenario for Scene 2 -/
def csScenario2 := csRSAScenario pinUtterances scene2_objects

/-- cs-RSA scenario for Scene 3 -/
def csScenario3 := csRSAScenario pinUtterances scene3_objects

/-- cs-RSA scenario for banana typicality -/
def csScenario4 := csRSAScenario bananaUtterances scene4_objects

-- Scene 1: Color-sufficient (blue pin among blue & red pins)
def target1 : Object := ⟨.pin, .blue, .small⟩

/-- S1 distribution for target in Scene 1 -/
def s1_scene1 : List (ReferringExpression × ℚ) :=
  csRSA_S1 csScenario1 target1

-- Scene 2: Size-sufficient (small pin among small & large pins)
def target2 : Object := ⟨.pin, .blue, .small⟩

/-- S1 distribution for target in Scene 2 -/
def s1_scene2 : List (ReferringExpression × ℚ) :=
  csRSA_S1 csScenario2 target2

-- Scene 4: Typicality (typical yellow vs atypical blue)
def target4_typical : Object := ⟨.banana, .yellow, .medium⟩
def target4_atypical : Object := ⟨.banana, .blue, .medium⟩

/-- S1 for typical banana -/
def s1_typical_banana : List (ReferringExpression × ℚ) :=
  csRSA_S1 csScenario4 target4_typical

/-- S1 for atypical banana -/
def s1_atypical_banana : List (ReferringExpression × ℚ) :=
  csRSA_S1 csScenario4 target4_atypical

#eval s1_scene1  -- Color-sufficient scene
#eval s1_scene2  -- Size-sufficient scene
#eval s1_typical_banana   -- Typical banana (should use bare more)
#eval s1_atypical_banana  -- Atypical banana (should use color more)

/-- In Scene 1 (color-sufficient), "blue pin" has nonzero S1 probability -/
theorem scene1_blue_pin_nonzero :
    RSA.Eval.getScore s1_scene1 (RE.withColor .pin .blue) > 0 := by
  native_decide

/-- In Scene 2 (size-sufficient), "small pin" has nonzero S1 probability -/
theorem scene2_small_pin_nonzero :
    RSA.Eval.getScore s1_scene2 (RE.withSize .pin .small) > 0 := by
  native_decide

/-- For atypical banana, color mention gets higher probability than bare nominal -/
theorem atypical_banana_prefers_color :
    RSA.Eval.getScore s1_atypical_banana (RE.withColor .banana .blue) >
    RSA.Eval.getScore s1_atypical_banana (RE.bare .banana) := by
  native_decide

/-- Boolean semantics: φ ∈ {0, 1}, for comparison with cs-RSA. -/
def booleanParams : SemanticParams :=
  { colorMatch := 1
  , colorMismatch := 0
  , sizeMatch := 1
  , sizeMismatch := 0
  , typeMatch := 1
  , typeMismatch := 0 }

/-- Boolean RSA scenario for Scene 1 -/
def boolScenario1 := csRSAScenario pinUtterances scene1_objects booleanParams

/-- Boolean RSA scenario for Scene 2 -/
def boolScenario2 := csRSAScenario pinUtterances scene2_objects booleanParams

/-- S1 with Boolean semantics for Scene 1 -/
def s1_bool_scene1 : List (ReferringExpression × ℚ) :=
  csRSA_S1 boolScenario1 target1

/-- S1 with Boolean semantics for Scene 2 -/
def s1_bool_scene2 : List (ReferringExpression × ℚ) :=
  csRSA_S1 boolScenario2 target2

#eval s1_bool_scene1  -- Boolean Scene 1
#eval s1_bool_scene2  -- Boolean Scene 2

/-- P(size mentioned | color sufficient): size overmodification rate. -/
def colorOvermodificationRate (s1dist : List (ReferringExpression × ℚ)) : ℚ :=
  -- Sum probability of utterances that include size
  s1dist.foldl (λ acc (re, p) =>
    if re.sizeAdj.isSome then acc + p else acc) 0

/-- P(color mentioned | size sufficient): color overmodification rate. -/
def sizeOvermodificationRate (s1dist : List (ReferringExpression × ℚ)) : ℚ :=
  -- Sum probability of utterances that include color
  s1dist.foldl (λ acc (re, p) =>
    if re.colorAdj.isSome then acc + p else acc) 0

#eval colorOvermodificationRate s1_scene1  -- Color-sufficient → size overmodification
#eval sizeOvermodificationRate s1_scene2   -- Size-sufficient → color overmodification

/-- High-variation scene: 3 sizes. Predicts more redundant modification. -/
def scene_high_variation : List Object := [
  ⟨.pin, .blue, .small⟩,   -- Target
  ⟨.pin, .blue, .medium⟩,  -- Distractor 1
  ⟨.pin, .blue, .large⟩    -- Distractor 2
]

def csScenario_high_var := csRSAScenario pinUtterances scene_high_variation

def s1_high_var : List (ReferringExpression × ℚ) :=
  csRSA_S1 csScenario_high_var ⟨.pin, .blue, .small⟩

#eval s1_high_var
#eval colorOvermodificationRate s1_high_var  -- Should be higher than s1_scene2

-- Decomposition: cs-RSA = Boolean semantics × independent noise channels
def noiseChannel := RSA.Noise.noiseChannel

/-- Boolean type feature value. -/
def booleanTypeVal (u : ReferringExpression) (o : Object) : ℚ :=
  match u.nominal with
  | none => 1
  | some t => if t == o.objType then 1 else 0

/-- Boolean color feature value. -/
def booleanColorVal (u : ReferringExpression) (o : Object) : ℚ :=
  match u.colorAdj with
  | none => 1
  | some c => if c == o.color then 1 else 0

/-- Boolean size feature value. -/
def booleanSizeVal (u : ReferringExpression) (o : Object) : ℚ :=
  match u.sizeAdj with
  | none => 1
  | some s => if s == o.size then 1 else 0

-- Use theorems from RSA.Noise
#check RSA.Noise.noiseChannel_one
#check RSA.Noise.noiseChannel_zero

/-- Product of {0,1}-valued rationals is {0,1}-valued. -/
theorem mul_mem_zero_one {a b : ℚ} (ha : a ∈ ({0, 1} : Set ℚ)) (hb : b ∈ ({0, 1} : Set ℚ)) :
    a * b ∈ ({0, 1} : Set ℚ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- Each feature channel is a noisy Boolean: `if-then-else = affine on {0,1}`. -/
theorem feature_channel_is_noisy_boolean
    (onMatch onMismatch : ℚ) (isMatch : Bool) :
    (if isMatch then onMatch else onMismatch) =
    onMatch * (if isMatch then 1 else 0) +
    onMismatch * (if isMatch then 0 else 1) := by
  cases isMatch <;> simp

/-- Boolean semantics is the zero-noise limit of cs-RSA. -/
theorem boolean_is_zero_noise_limit (u : ReferringExpression) (o : Object) :
    φ booleanParams u o ∈ ({0, 1} : Set ℚ) := by
  simp only [φ, booleanParams]
  apply mul_mem_zero_one
  · apply mul_mem_zero_one
    · cases u.nominal with
      | none => simp [Set.mem_insert_iff]
      | some t => simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; split_ifs <;> simp
    · cases u.colorAdj with
      | none => simp [Set.mem_insert_iff]
      | some c => simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; split_ifs <;> simp
  · cases u.sizeAdj with
    | none => simp [Set.mem_insert_iff]
    | some s => simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; split_ifs <;> simp

/-- Degen decomposition (specified features): φ = Π noiseChannel(booleanVal). -/
theorem degen_is_boolean_times_noise_specified
    (params : SemanticParams)
    (u : ReferringExpression) (o : Object)
    (h_type : u.nominal.isSome)
    (h_color : u.colorAdj.isSome)
    (h_size : u.sizeAdj.isSome) :
    φ params u o =
    noiseChannel params.typeMatch params.typeMismatch (booleanTypeVal u o) *
    noiseChannel params.colorMatch params.colorMismatch (booleanColorVal u o) *
    noiseChannel params.sizeMatch params.sizeMismatch (booleanSizeVal u o) := by
  unfold φ booleanTypeVal booleanColorVal booleanSizeVal noiseChannel RSA.Noise.noiseChannel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h_type
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h_color
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h_size
  simp only [ht, hc, hs]
  split_ifs <;> ring

/-- Degen decomposition (general): unspecified features contribute 1. -/
theorem degen_is_boolean_times_noise_full
    (params : SemanticParams)
    (u : ReferringExpression) (o : Object) :
    φ params u o =
    (match u.nominal with
     | none => 1
     | some _ => noiseChannel params.typeMatch params.typeMismatch (booleanTypeVal u o)) *
    (match u.colorAdj with
     | none => 1
     | some _ => noiseChannel params.colorMatch params.colorMismatch (booleanColorVal u o)) *
    (match u.sizeAdj with
     | none => 1
     | some _ => noiseChannel params.sizeMatch params.sizeMismatch (booleanSizeVal u o)) := by
  unfold φ booleanTypeVal booleanColorVal booleanSizeVal noiseChannel RSA.Noise.noiseChannel
  cases u.nominal <;> cases u.colorAdj <;> cases u.sizeAdj <;>
    simp only [] <;> (try split_ifs) <;> ring

/-- With Boolean parameters, noise channels are identity on {0,1}. -/
theorem noise_channel_boolean (b : ℚ) (hb : b ∈ ({0, 1} : Set ℚ)) :
    noiseChannel 1 0 b = b := by
  simp only [noiseChannel, RSA.Noise.noiseChannel]
  rcases hb with rfl | rfl <;> ring

end RSA.ContinuousSemantics
