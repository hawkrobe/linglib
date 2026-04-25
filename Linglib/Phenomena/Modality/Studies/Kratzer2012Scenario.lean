import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Mathlib.Data.Fin.Basic

/-!
# Conditional Modality Data — Rain and Wet Streets (@cite{kratzer-2012} §2.9)

Four worlds with two properties (rain, wet street) and a causal regularity:

| World | Rain | Wet Street | Notes                      |
|-------|------|------------|----------------------------|
| w0    | yes  | yes        | Normal causation           |
| w1    | yes  | no         | Broken drainage (anomalous)|
| w2    | no   | yes        | Sprinkler                  |
| w3    | no   | no         | Normal non-rain            |

Two time points: yesterday (t = −1) and now (t = 0). Rain occurs yesterday;
wetness holds now. The function `atTime` projects `World → ℤ → Prop` to
`(World → Prop)` at a specific time, bridging the temporal and modal type systems.

Reference: Kratzer, A. (2012). Modals and Conditionals. Oxford University Press. Ch. 2 §2.9.
-/

namespace Phenomena.Modality.ConditionalModality

abbrev World := Fin 4

def allWorlds : List World := [0, 1, 2, 3]

open Semantics.Modality.Kratzer

/-! ## Atemporal propositions -/

/-- It rained: true at w0 (normal rain) and w1 (rain + broken drainage). -/
def rained : World → Prop
  | 0 => True
  | 1 => True
  | 2 => False
  | 3 => False

instance : DecidablePred rained := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable True)
  | 2 => inferInstanceAs (Decidable False)
  | 3 => inferInstanceAs (Decidable False)

/-- The street is wet: true at w0 (rain → wet) and w2 (sprinkler). -/
def streetWet : World → Prop
  | 0 => True
  | 1 => False
  | 2 => True
  | 3 => False

instance : DecidablePred streetWet := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable False)
  | 2 => inferInstanceAs (Decidable True)
  | 3 => inferInstanceAs (Decidable False)

/-! ## Temporal propositions and the type bridge -/

/-- Rain as a temporal proposition: it rained yesterday (t = −1). -/
def rainedAt : World → ℤ → Prop := λ w t =>
  match t with | -1 => rained w | _ => False

/-- Wet street as a temporal proposition: the street is wet now (t = 0). -/
def wetStreetAt : World → ℤ → Prop := λ w t =>
  match t with | 0 => streetWet w | _ => False

/-- **The type bridge**: project a temporal proposition at a specific time
    to a world proposition `(World → Prop)`. This is what allows a past-tense
    antecedent to enter a Kratzer modal base. -/
def atTime (p : World → ℤ → Prop) (t : ℤ) : World → Prop := λ w => p w t

/-! ## Conversational backgrounds -/

/-- Totally realistic modal base: ∩f(w) = {w} for each world.
    Each world's fact set contains the proposition "being exactly that world." -/
def totallyRealisticBg : ModalBase World := λ w => [λ w' => w' = w]

/-- Normalcy ordering source: ranks worlds where rain-without-wet-street is
    abnormal. The ordering proposition penalizes w1 (rained ∧ ¬streetWet). -/
def normalcySource : OrderingSource World := λ _ => [λ w' => ¬ (rained w' ∧ ¬ streetWet w')]

/-! ## Theory-neutral facts -/

theorem w0_rained_wet : rained (0 : World) ∧ streetWet (0 : World) := ⟨trivial, trivial⟩
theorem w1_rained_dry : rained (1 : World) ∧ ¬ streetWet (1 : World) := ⟨trivial, id⟩
theorem w2_dry_wet    : ¬ rained (2 : World) ∧ streetWet (2 : World) := ⟨id, trivial⟩
theorem w3_dry_dry    : ¬ rained (3 : World) ∧ ¬ streetWet (3 : World) := ⟨id, id⟩

/-- Temporal projection at yesterday recovers the atemporal `rained`. -/
theorem atTime_rainedAt_yesterday : atTime rainedAt (-1) = rained := by
  funext w; rfl

/-- Temporal projection at now recovers the atemporal `streetWet`. -/
theorem atTime_wetStreetAt_now : atTime wetStreetAt 0 = streetWet := by
  funext w; rfl

end Phenomena.Modality.ConditionalModality
