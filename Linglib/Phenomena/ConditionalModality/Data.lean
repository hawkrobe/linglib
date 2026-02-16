import Linglib.Theories.Semantics.Modality.Kratzer

/-!
# Conditional Modality Data — Rain and Wet Streets (Kratzer 2012 §2.9)

Four worlds with two properties (rain, wet street) and a causal regularity:

| World | Rain | Wet Street | Notes                      |
|-------|------|------------|----------------------------|
| w0    | yes  | yes        | Normal causation           |
| w1    | yes  | no         | Broken drainage (anomalous)|
| w2    | no   | yes        | Sprinkler                  |
| w3    | no   | no         | Normal non-rain            |

Two time points: yesterday (t = −1) and now (t = 0). Rain occurs yesterday;
wetness holds now. The function `atTime` projects `World → ℤ → Bool` to
`BProp World` at a specific time, bridging the temporal and modal type systems.

Reference: Kratzer, A. (2012). Modals and Conditionals. Oxford University Press. Ch. 2 §2.9.
-/

namespace Phenomena.ConditionalModality

open IntensionalSemantics.Attitude.Intensional (World allWorlds)
open IntensionalSemantics.Modal.Kratzer

/-! ## Atemporal propositions -/

/-- It rained: true at w0 (normal rain) and w1 (rain + broken drainage). -/
def rained : BProp World := λ w =>
  match w with | .w0 => true | .w1 => true | .w2 => false | .w3 => false

/-- The street is wet: true at w0 (rain → wet) and w2 (sprinkler). -/
def streetWet : BProp World := λ w =>
  match w with | .w0 => true | .w1 => false | .w2 => true | .w3 => false

/-! ## Temporal propositions and the type bridge -/

/-- Rain as a temporal proposition: it rained yesterday (t = −1). -/
def rainedAt : World → ℤ → Bool := λ w t =>
  match t with | -1 => rained w | _ => false

/-- Wet street as a temporal proposition: the street is wet now (t = 0). -/
def wetStreetAt : World → ℤ → Bool := λ w t =>
  match t with | 0 => streetWet w | _ => false

/-- **The type bridge**: project a temporal proposition at a specific time
    to a world proposition `BProp World`. This is what allows a past-tense
    antecedent to enter a Kratzer modal base. -/
def atTime (p : World → ℤ → Bool) (t : ℤ) : BProp World := λ w => p w t

/-! ## Conversational backgrounds -/

/-- Totally realistic modal base: ∩f(w) = {w} for each world.
    Each world's fact set contains the proposition "being exactly that world." -/
def totallyRealisticBg : ModalBase := λ w => [λ w' => w' == w]

/-- Normalcy ordering source: ranks worlds where rain-without-wet-street is
    abnormal. The ordering proposition penalizes w1 (rained ∧ ¬streetWet). -/
def normalcySource : OrderingSource := λ _ => [λ w' => !(rained w' && !streetWet w')]

/-! ## Theory-neutral facts -/

theorem w0_rained_wet : rained .w0 = true ∧ streetWet .w0 = true := ⟨rfl, rfl⟩
theorem w1_rained_dry : rained .w1 = true ∧ streetWet .w1 = false := ⟨rfl, rfl⟩
theorem w2_dry_wet    : rained .w2 = false ∧ streetWet .w2 = true := ⟨rfl, rfl⟩
theorem w3_dry_dry    : rained .w3 = false ∧ streetWet .w3 = false := ⟨rfl, rfl⟩

/-- Temporal projection at yesterday recovers the atemporal `rained`. -/
theorem atTime_rainedAt_yesterday : atTime rainedAt (-1) = rained := by
  funext w; simp [atTime, rainedAt]

/-- Temporal projection at now recovers the atemporal `streetWet`. -/
theorem atTime_wetStreetAt_now : atTime wetStreetAt 0 = streetWet := by
  funext w; simp [atTime, wetStreetAt]

end Phenomena.ConditionalModality
