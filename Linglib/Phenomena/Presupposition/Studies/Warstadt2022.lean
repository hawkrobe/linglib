import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Presupposition

/-!
# Warstadt (2022): Presupposition Triggering and Utterance Utility @cite{warstadt-2022}

Empirical domain types and truth conditions for Warstadt's genus-species
presupposition model. Two examples demonstrate that presupposition triggering
emerges from pragmatic reasoning about utterance utility.

## Green Card Example (Table 1)

Three worlds, five utterances, two QUDs. The central prediction:
under the "need visa?" QUD, "not green card" triggers the genus inference
(Tom is non-US), but under "free drink?" QUD, no such inference arises.

## Family-Genus-Species Example (Table 2)

Four worlds in a taxonomic hierarchy (Olympic sprinter ⊂ runner ⊂ athlete),
seven utterances, non-uniform priors. Species-level negation ("not Olympic
sprinter") triggers stronger accommodation than genus-level ("not runner").

## Reference

Warstadt, A. (2022). Presupposition triggering reflects pragmatic reasoning
about utterance utility. Proceedings of the 23rd Amsterdam Colloquium, 444–451.
-/

namespace Phenomena.Presupposition.Studies.Warstadt2022

open Core.Presupposition


/-! ## Green Card Example (Table 1) -/

/-- World states for the green card scenario.

- `usCitizen`: Tom is a US citizen (no green card possible)
- `gcHolder`: Tom is a non-US citizen with a green card
- `nonUS`: Tom is a non-US citizen without a green card -/
inductive GCWorld where
  | usCitizen
  | gcHolder
  | nonUS
  deriving DecidableEq, BEq, Repr, Inhabited

def allGCWorlds : List GCWorld := [.usCitizen, .gcHolder, .nonUS]

instance : Fintype GCWorld where
  elems := {.usCitizen, .gcHolder, .nonUS}
  complete := λ w => by cases w <;> simp

/-- Utterances for the green card scenario.

- `us` / `notUS`: genus-level descriptions
- `greenCard` / `notGreenCard`: species-level descriptions
- `silence`: null utterance -/
inductive GCUtterance where
  | us
  | notUS
  | greenCard
  | notGreenCard
  | silence
  deriving DecidableEq, BEq, Repr, Inhabited

def allGCUtterances : List GCUtterance :=
  [.us, .notUS, .greenCard, .notGreenCard, .silence]

instance : Fintype GCUtterance where
  elems := {.us, .notUS, .greenCard, .notGreenCard, .silence}
  complete := λ u => by cases u <;> simp

/-- QUDs for the green card scenario.

- `needVisa`: Does Tom need a visa? Partition: {usCitizen, gcHolder} vs {nonUS}
- `freeDrink`: Can Tom get a free drink? Partition: {gcHolder} vs {usCitizen, nonUS} -/
inductive GCQUD where
  | needVisa
  | freeDrink
  deriving DecidableEq, BEq, Repr, Inhabited

def allGCQUDs : List GCQUD := [.needVisa, .freeDrink]

instance : Fintype GCQUD where
  elems := {.needVisa, .freeDrink}
  complete := λ q => by cases q <;> simp

/-- Truth conditions from Table 1. All negations are Boolean. -/
def gcMeaning : GCUtterance → GCWorld → Bool
  | .us, .usCitizen => true
  | .us, _ => false
  | .notUS, .usCitizen => false
  | .notUS, _ => true
  | .greenCard, .gcHolder => true
  | .greenCard, _ => false
  | .notGreenCard, .gcHolder => false
  | .notGreenCard, _ => true
  | .silence, _ => true

/-- QUD answer function: maps each QUD to a world's answer. -/
def gcQUDAnswer : GCQUD → GCWorld → Bool
  | .needVisa, .nonUS => true
  | .needVisa, _ => false
  | .freeDrink, .gcHolder => true
  | .freeDrink, _ => false

/-- QUD projection: two worlds are equivalent iff they give the same QUD answer. -/
def gcQUDProject (q : GCQUD) (w1 w2 : GCWorld) : Bool :=
  gcQUDAnswer q w1 == gcQUDAnswer q w2

/-- Uniform world prior. -/
def gcWorldPrior (_w : GCWorld) : ℚ := 1 / 3

/-- PrProp decomposition of "green card": presupposes non-US, asserts has GC.

This captures the traditional presupposition analysis. The paper's key
contribution is showing that this presupposition structure EMERGES from
RSA reasoning over Boolean truth conditions, without being stipulated. -/
def greenCardPrProp : PrProp GCWorld where
  presup := λ w => match w with | .usCitizen => false | _ => true
  assertion := λ w => match w with | .gcHolder => true | _ => false

/-- The Boolean meaning of "green card" decomposes as presupposition ∧ assertion. -/
theorem gcMeaning_greenCard_eq_prprop (w : GCWorld) :
    gcMeaning .greenCard w = (greenCardPrProp.presup w && greenCardPrProp.assertion w) := by
  cases w <;> rfl

/-- "not green card" is Boolean negation of "green card". -/
theorem gcMeaning_notGreenCard_eq_neg (w : GCWorld) :
    gcMeaning .notGreenCard w = !gcMeaning .greenCard w := by
  cases w <;> rfl

/-- "not US" is Boolean negation of "US". -/
theorem gcMeaning_notUS_eq_neg (w : GCWorld) :
    gcMeaning .notUS w = !gcMeaning .us w := by
  cases w <;> rfl

/-- needVisa QUD partition: {usCitizen, gcHolder} (no) vs {nonUS} (yes). -/
theorem gcQUD_needVisa_partition :
    gcQUDProject .needVisa .usCitizen .gcHolder = true ∧
    gcQUDProject .needVisa .usCitizen .nonUS = false := by
  exact ⟨rfl, rfl⟩

/-- freeDrink QUD partition: {usCitizen, nonUS} (no) vs {gcHolder} (yes). -/
theorem gcQUD_freeDrink_partition :
    gcQUDProject .freeDrink .usCitizen .nonUS = true ∧
    gcQUDProject .freeDrink .usCitizen .gcHolder = false := by
  exact ⟨rfl, rfl⟩


/-! ## Family-Genus-Species Example (Table 2) -/

/-- World states for the family-genus-species hierarchy.

- `olympicSprinter`: species (⊂ runner ⊂ athlete)
- `runner`: genus (⊂ athlete)
- `otherAthlete`: family level
- `nonAthlete`: outside the hierarchy -/
inductive FGSWorld where
  | olympicSprinter
  | runner
  | otherAthlete
  | nonAthlete
  deriving DecidableEq, BEq, Repr, Inhabited

def allFGSWorlds : List FGSWorld :=
  [.olympicSprinter, .runner, .otherAthlete, .nonAthlete]

instance : Fintype FGSWorld where
  elems := {.olympicSprinter, .runner, .otherAthlete, .nonAthlete}
  complete := λ w => by cases w <;> simp

/-- Utterances for the family-genus-species scenario.

Seven utterances: three positive descriptions at each taxonomic level,
their Boolean negations, plus silence. -/
inductive FGSUtterance where
  | olympicSprinter
  | notOlympicSprinter
  | runner
  | notRunner
  | athlete
  | notAthlete
  | silence
  deriving DecidableEq, BEq, Repr, Inhabited

def allFGSUtterances : List FGSUtterance :=
  [.olympicSprinter, .notOlympicSprinter, .runner, .notRunner,
   .athlete, .notAthlete, .silence]

instance : Fintype FGSUtterance where
  elems := {.olympicSprinter, .notOlympicSprinter, .runner, .notRunner,
            .athlete, .notAthlete, .silence}
  complete := λ u => by cases u <;> simp

/-- Truth conditions from Table 2.

Respects the taxonomic hierarchy: Olympic sprinter ⊂ runner ⊂ athlete. -/
def fgsMeaning : FGSUtterance → FGSWorld → Bool
  | .olympicSprinter, .olympicSprinter => true
  | .olympicSprinter, _ => false
  | .notOlympicSprinter, .olympicSprinter => false
  | .notOlympicSprinter, _ => true
  | .runner, .olympicSprinter => true
  | .runner, .runner => true
  | .runner, _ => false
  | .notRunner, .olympicSprinter => false
  | .notRunner, .runner => false
  | .notRunner, _ => true
  | .athlete, .nonAthlete => false
  | .athlete, _ => true
  | .notAthlete, .nonAthlete => true
  | .notAthlete, _ => false
  | .silence, _ => true

/-- Non-uniform world prior from Table 2 (percentages). -/
def fgsWorldPrior : FGSWorld → ℚ
  | .olympicSprinter => 1 / 100
  | .runner => 5 / 100
  | .otherAthlete => 10 / 100
  | .nonAthlete => 84 / 100

/-- Max QUD (full world identification). -/
def fgsQUDProject (w1 w2 : FGSWorld) : Bool := w1 == w2

-- Genus-species hierarchy verification

/-- Olympic sprinter entails runner. -/
theorem olympicSprinter_entails_runner (w : FGSWorld) :
    fgsMeaning .olympicSprinter w = true → fgsMeaning .runner w = true := by
  cases w <;> simp [fgsMeaning]

/-- Runner entails athlete. -/
theorem runner_entails_athlete (w : FGSWorld) :
    fgsMeaning .runner w = true → fgsMeaning .athlete w = true := by
  cases w <;> simp [fgsMeaning]

/-- Olympic sprinter entails athlete (transitivity). -/
theorem olympicSprinter_entails_athlete (w : FGSWorld) :
    fgsMeaning .olympicSprinter w = true → fgsMeaning .athlete w = true := by
  cases w <;> simp [fgsMeaning]

/-- Boolean negation: not Olympic sprinter = ¬ Olympic sprinter. -/
theorem fgsMeaning_notOS_eq_neg (w : FGSWorld) :
    fgsMeaning .notOlympicSprinter w = !fgsMeaning .olympicSprinter w := by
  cases w <;> rfl

/-- Boolean negation: not runner = ¬ runner. -/
theorem fgsMeaning_notRunner_eq_neg (w : FGSWorld) :
    fgsMeaning .notRunner w = !fgsMeaning .runner w := by
  cases w <;> rfl

/-- Boolean negation: not athlete = ¬ athlete. -/
theorem fgsMeaning_notAthlete_eq_neg (w : FGSWorld) :
    fgsMeaning .notAthlete w = !fgsMeaning .athlete w := by
  cases w <;> rfl

/-- FGS priors sum to 1. -/
theorem fgsWorldPrior_sum :
    fgsWorldPrior .olympicSprinter + fgsWorldPrior .runner +
    fgsWorldPrior .otherAthlete + fgsWorldPrior .nonAthlete = 1 := by
  native_decide

end Phenomena.Presupposition.Studies.Warstadt2022
