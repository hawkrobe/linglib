import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Linglib.Pragmatics.RSA.Silence
import Linglib.Semantics.Presupposition.Basic

/-!
# [warstadt-2022]: Presupposition Triggering and Utterance Utility [warstadt-2022]

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

-/

namespace Warstadt2022

open Semantics.Presupposition
open RSA (WithSilence liftMeaning)


/-! ## Green Card Example (Table 1) -/

/-- World states for the green card scenario.

- `usCitizen`: Tom is a US citizen (no green card possible)
- `gcHolder`: Tom is a non-US citizen with a green card
- `nonUS`: Tom is a non-US citizen without a green card -/
inductive GCWorld where
  | usCitizen
  | gcHolder
  | nonUS
  deriving DecidableEq, Repr, Inhabited

def allGCWorlds : List GCWorld := [.usCitizen, .gcHolder, .nonUS]

instance : Fintype GCWorld where
  elems := {.usCitizen, .gcHolder, .nonUS}
  complete := λ w => by cases w <;> simp

/-- Assertable content for the green card scenario (silence is added
separately via `RSA.WithSilence`).

- `us` / `notUS`: genus-level descriptions
- `greenCard` / `notGreenCard`: species-level descriptions -/
inductive GCAssertion where
  | us
  | notUS
  | greenCard
  | notGreenCard
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterances for the green card scenario: `none` is the null utterance,
`some a` a paper-utterance. -/
abbrev GCUtterance := WithSilence GCAssertion

def allGCUtterances : List GCUtterance :=
  [none, some .us, some .notUS, some .greenCard, some .notGreenCard]

/-- QUDs for the green card scenario.

- `needVisa`: Does Tom need a visa? Partition: {usCitizen, gcHolder} vs {nonUS}
- `freeDrink`: Can Tom get a free drink? Partition: {gcHolder} vs {usCitizen, nonUS} -/
inductive GCQUD where
  | needVisa
  | freeDrink
  deriving DecidableEq, Repr, Inhabited

def allGCQUDs : List GCQUD := [.needVisa, .freeDrink]

instance : Fintype GCQUD where
  elems := {.needVisa, .freeDrink}
  complete := λ q => by cases q <;> simp

/-- Truth conditions from Table 1. All negations are Boolean. -/
def gcAssertionMeaning : GCAssertion → GCWorld → Prop
  | .us, .usCitizen => True
  | .us, _ => False
  | .notUS, .usCitizen => False
  | .notUS, _ => True
  | .greenCard, .gcHolder => True
  | .greenCard, _ => False
  | .notGreenCard, .gcHolder => False
  | .notGreenCard, _ => True

instance (a : GCAssertion) : DecidablePred (gcAssertionMeaning a) := fun w => by
  cases a <;> cases w <;> first | exact isTrue trivial | exact isFalse id

/-- Utterance-level meaning: silence is universally true. -/
def gcMeaning : GCUtterance → GCWorld → Prop := liftMeaning gcAssertionMeaning

instance : ∀ u : GCUtterance, DecidablePred (gcMeaning u) :=
  inferInstanceAs (∀ u, DecidablePred (liftMeaning gcAssertionMeaning u))

/-- QUD answer function: maps each QUD to a world's answer. -/
def gcQUDAnswer : GCQUD → GCWorld → Prop
  | .needVisa, .nonUS => True
  | .needVisa, _ => False
  | .freeDrink, .gcHolder => True
  | .freeDrink, _ => False

instance (q : GCQUD) : DecidablePred (gcQUDAnswer q) := fun w => by
  cases q <;> cases w <;> first | exact isTrue trivial | exact isFalse id

/-- QUD projection: two worlds are equivalent iff they give the same QUD answer. -/
def gcQUDProject (q : GCQUD) (w1 w2 : GCWorld) : Prop :=
  gcQUDAnswer q w1 ↔ gcQUDAnswer q w2

instance (q : GCQUD) (w1 w2 : GCWorld) : Decidable (gcQUDProject q w1 w2) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- Uniform world prior. -/
def gcWorldPrior (_w : GCWorld) : ℚ := 1 / 3

/-- PartialProp decomposition of "green card": presupposes non-US, asserts has GC.

This captures the traditional presupposition analysis. The paper's key
contribution is showing that this presupposition structure EMERGES from
RSA reasoning over Boolean truth conditions, without being stipulated. -/
def greenCardPartialProp : PartialProp GCWorld where
  presup := λ w => match w with | .usCitizen => False | _ => True
  assertion := λ w => match w with | .gcHolder => True | _ => False

/-- The meaning of "green card" decomposes as presupposition ∧ assertion. -/
theorem gcMeaning_greenCard_iff_prprop (w : GCWorld) :
    gcMeaning (some .greenCard) w ↔
      greenCardPartialProp.presup w ∧ greenCardPartialProp.assertion w := by
  cases w <;> simp [gcMeaning, gcAssertionMeaning, greenCardPartialProp]

/-- "not green card" is Boolean negation of "green card". -/
theorem gcMeaning_notGreenCard_iff_not (w : GCWorld) :
    gcMeaning (some .notGreenCard) w ↔ ¬ gcMeaning (some .greenCard) w := by
  cases w <;> decide

/-- "not US" is Boolean negation of "US". -/
theorem gcMeaning_notUS_iff_not (w : GCWorld) :
    gcMeaning (some .notUS) w ↔ ¬ gcMeaning (some .us) w := by
  cases w <;> decide

/-- needVisa QUD partition: {usCitizen, gcHolder} (no) vs {nonUS} (yes). -/
theorem gcQUD_needVisa_partition :
    gcQUDProject .needVisa .usCitizen .gcHolder ∧
    ¬ gcQUDProject .needVisa .usCitizen .nonUS := by
  decide

/-- freeDrink QUD partition: {usCitizen, nonUS} (no) vs {gcHolder} (yes). -/
theorem gcQUD_freeDrink_partition :
    gcQUDProject .freeDrink .usCitizen .nonUS ∧
    ¬ gcQUDProject .freeDrink .usCitizen .gcHolder := by
  decide


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
  deriving DecidableEq, Repr, Inhabited

def allFGSWorlds : List FGSWorld :=
  [.olympicSprinter, .runner, .otherAthlete, .nonAthlete]

instance : Fintype FGSWorld where
  elems := {.olympicSprinter, .runner, .otherAthlete, .nonAthlete}
  complete := λ w => by cases w <;> simp

/-- Assertable content for the family-genus-species scenario (silence is
added separately via `RSA.WithSilence`).

Six utterances: three positive descriptions at each taxonomic level plus
their Boolean negations. -/
inductive FGSAssertion where
  | olympicSprinter
  | notOlympicSprinter
  | runner
  | notRunner
  | athlete
  | notAthlete
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterances for the family-genus-species scenario: `none` is the null
utterance, `some a` a paper-utterance. -/
abbrev FGSUtterance := WithSilence FGSAssertion

def allFGSUtterances : List FGSUtterance :=
  [none, some .olympicSprinter, some .notOlympicSprinter, some .runner,
   some .notRunner, some .athlete, some .notAthlete]

/-- Truth conditions from Table 2.

Respects the taxonomic hierarchy: Olympic sprinter ⊂ runner ⊂ athlete. -/
def fgsAssertionMeaning : FGSAssertion → FGSWorld → Prop
  | .olympicSprinter, .olympicSprinter => True
  | .olympicSprinter, _ => False
  | .notOlympicSprinter, .olympicSprinter => False
  | .notOlympicSprinter, _ => True
  | .runner, .olympicSprinter => True
  | .runner, .runner => True
  | .runner, _ => False
  | .notRunner, .olympicSprinter => False
  | .notRunner, .runner => False
  | .notRunner, _ => True
  | .athlete, .nonAthlete => False
  | .athlete, _ => True
  | .notAthlete, .nonAthlete => True
  | .notAthlete, _ => False

instance (a : FGSAssertion) : DecidablePred (fgsAssertionMeaning a) := fun w => by
  cases a <;> cases w <;> first | exact isTrue trivial | exact isFalse id

/-- Utterance-level meaning: silence is universally true. -/
def fgsMeaning : FGSUtterance → FGSWorld → Prop := liftMeaning fgsAssertionMeaning

instance : ∀ u : FGSUtterance, DecidablePred (fgsMeaning u) :=
  inferInstanceAs (∀ u, DecidablePred (liftMeaning fgsAssertionMeaning u))

/-- Non-uniform world prior from Table 2 (percentages). -/
def fgsWorldPrior : FGSWorld → ℚ
  | .olympicSprinter => 1 / 100
  | .runner => 5 / 100
  | .otherAthlete => 10 / 100
  | .nonAthlete => 84 / 100

/-- Max QUD (full world identification). -/
def fgsQUDProject (w1 w2 : FGSWorld) : Prop := w1 = w2

instance (w1 w2 : FGSWorld) : Decidable (fgsQUDProject w1 w2) :=
  inferInstanceAs (Decidable (w1 = w2))

-- Genus-species hierarchy verification

/-- Olympic sprinter entails runner. -/
theorem olympicSprinter_entails_runner (w : FGSWorld) :
    fgsMeaning (some .olympicSprinter) w → fgsMeaning (some .runner) w := by
  cases w <;> decide

/-- Runner entails athlete. -/
theorem runner_entails_athlete (w : FGSWorld) :
    fgsMeaning (some .runner) w → fgsMeaning (some .athlete) w := by
  cases w <;> decide

/-- Olympic sprinter entails athlete (transitivity). -/
theorem olympicSprinter_entails_athlete (w : FGSWorld) :
    fgsMeaning (some .olympicSprinter) w → fgsMeaning (some .athlete) w := by
  cases w <;> decide

/-- Boolean negation: not Olympic sprinter = ¬ Olympic sprinter. -/
theorem fgsMeaning_notOS_iff_not (w : FGSWorld) :
    fgsMeaning (some .notOlympicSprinter) w ↔ ¬ fgsMeaning (some .olympicSprinter) w := by
  cases w <;> decide

/-- Boolean negation: not runner = ¬ runner. -/
theorem fgsMeaning_notRunner_iff_not (w : FGSWorld) :
    fgsMeaning (some .notRunner) w ↔ ¬ fgsMeaning (some .runner) w := by
  cases w <;> decide

/-- Boolean negation: not athlete = ¬ athlete. -/
theorem fgsMeaning_notAthlete_iff_not (w : FGSWorld) :
    fgsMeaning (some .notAthlete) w ↔ ¬ fgsMeaning (some .athlete) w := by
  cases w <;> decide

/-- FGS priors sum to 1. -/
theorem fgsWorldPrior_sum :
    fgsWorldPrior .olympicSprinter + fgsWorldPrior .runner +
    fgsWorldPrior .otherAthlete + fgsWorldPrior .nonAthlete = 1 := by
  norm_num [fgsWorldPrior]

-- ============================================================================
-- Part II: RSA Context Types and PartialProp Connection
-- ============================================================================


/-! ## Green Card: Context Types -/

/-- A context is a subset of GCWorlds. -/
structure GCContext where
  usCitizen : Bool
  gcHolder : Bool
  nonUS : Bool
  deriving DecidableEq, Repr, Inhabited

/-- All 2³ = 8 contexts (subsets of GCWorld). -/
def allGCContexts : List GCContext :=
  [false, true].flatMap λ a =>
    [false, true].flatMap λ b =>
      [false, true].map λ c =>
        ⟨a, b, c⟩

theorem allGCContexts_length : allGCContexts.length = 8 := rfl

/-- A world is compatible with a context iff the context includes it. -/
def gcCompatible (c : GCContext) (w : GCWorld) : Prop :=
  match w with
  | .usCitizen => c.usCitizen
  | .gcHolder => c.gcHolder
  | .nonUS => c.nonUS

instance (c : GCContext) : DecidablePred (gcCompatible c) := fun w => by
  cases w <;> exact inferInstanceAs (Decidable (_ = true))

def gcContextPrior (_c : GCContext) : ℚ := 1 / 8

/-! ## Family-Genus-Species: Context Types -/

/-- A context is a subset of FGSWorlds. -/
structure FGSContext where
  olympicSprinter : Bool
  runner : Bool
  otherAthlete : Bool
  nonAthlete : Bool
  deriving DecidableEq, Repr, Inhabited

/-- All 2⁴ = 16 contexts. -/
def allFGSContexts : List FGSContext :=
  [false, true].flatMap λ a =>
    [false, true].flatMap λ b =>
      [false, true].flatMap λ c =>
        [false, true].map λ d =>
          ⟨a, b, c, d⟩

theorem allFGSContexts_length : allFGSContexts.length = 16 := rfl

def fgsCompatible (c : FGSContext) (w : FGSWorld) : Prop :=
  match w with
  | .olympicSprinter => c.olympicSprinter
  | .runner => c.runner
  | .otherAthlete => c.otherAthlete
  | .nonAthlete => c.nonAthlete

instance (c : FGSContext) : DecidablePred (fgsCompatible c) := fun w => by
  cases w <;> exact inferInstanceAs (Decidable (_ = true))

def fgsContextPrior (_c : FGSContext) : ℚ := 1 / 16

inductive FGSQUD where
  | identity
  deriving DecidableEq, Repr, Inhabited

def allFGSQUDs : List FGSQUD := [.identity]

def fgsQUDProjectBridge : FGSQUD → FGSWorld → FGSWorld → Prop
  | .identity, w1, w2 => fgsQUDProject w1 w2

instance (q : FGSQUD) (w1 w2 : FGSWorld) : Decidable (fgsQUDProjectBridge q w1 w2) :=
  match q with
  | .identity => inferInstanceAs (Decidable (fgsQUDProject w1 w2))

/-! ## PartialProp Connection -/

/-- The meaning of "green card" decomposes as presupposition ∧ assertion. -/
theorem greenCard_meaning_from_prprop (w : GCWorld) :
    gcMeaning (some .greenCard) w ↔
      greenCardPartialProp.presup w ∧ greenCardPartialProp.assertion w :=
  gcMeaning_greenCard_iff_prprop w

/-- "not green card" is Boolean negation — no presupposition in the semantics. -/
theorem notGreenCard_is_boolean_negation (w : GCWorld) :
    gcMeaning (some .notGreenCard) w ↔ ¬ gcMeaning (some .greenCard) w :=
  gcMeaning_notGreenCard_iff_not w

end Warstadt2022
