import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.PolarityItems

/-!
# @cite{israel-2001}: Minimizers, Maximizers, and the Rhetoric of Scalar Reasoning

Formalizes the core contributions of Israel's Scalar Model of Polarity:

1. **The 2×2 taxonomy** (Figure 1): polarity items classified by scalar value
   (high/low) × rhetorical force (emphatic/attenuating)
2. **Inverted polarity items** (§3, Figure 3): maximizer NPIs (*wild horses*,
   *all the tea in China*) and minimizer PPIs (*at the drop of a hat*,
   *for a pittance*) — items whose scalar value is opposite to what the
   basic Scalar Model predicts
3. **The thematic resolution** (§4): inversion tracks propositional role —
   facilitating roles (stimulus, instrument, reward) produce inverted items,
   impeding roles (patient, theme, resource) produce canonical items
4. **The pecuniary paradox**: *a red cent* (NPI, resource = impeding) vs
   *for peanuts* (PPI, reward = facilitating) — same monetary domain,
   different propositional roles

## Connection to linglib infrastructure

- `ScalarValue`, `Canonicity`, `LikelihoodEffect` defined in
  `Core/Lexical/PolarityItem.lean`
- Inverted items added to `Fragments/English/PolarityItems.lean`
- `LikelihoodEffect` is a propositional-role concept, not a theta-role
  function. It connects to proto-role entailments (Dowty 1991) via
  bridge theorems below, but is independently defined: the relevant
  distinction is how a participant affects event likelihood, which
  cross-cuts traditional theta labels.
-/

namespace Phenomena.Polarity.Studies.Israel2001

open Core.Lexical.PolarityItem
open Fragments.English.PolarityItems

-- ════════════════════════════════════════════════════
-- § 1. The Scalar Model (Figure 1)
-- ════════════════════════════════════════════════════

/-! The basic Scalar Model predicts four cells:

| | **Emphatic** | **Attenuating** |
|---------|----------------------|----------------------|
| **NPI** | low: *a wink, inch* | high: *much, long* |
| **PPI** | high: *tons, utterly*| low: *sorta, rather* |

Emphatic items license maximally informative interpretations;
attenuating items license minimally informative interpretations.
NPI contexts are scale-reversing (DE); PPI contexts are scale-preserving (UE). -/

/-- A polarity item datum with its Israel 2001 classification. -/
structure IsraelDatum where
  item : PolarityItemEntry
  /-- Example sentence -/
  sentence : String
  /-- Is the item grammatical in this sentence? -/
  grammatical : Bool
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 2. Canonical items (Figure 1)
-- ════════════════════════════════════════════════════

/-- "I didn't sleep a wink." — canonical emphatic NPI (low, impeding) -/
def sleepAWink : IsraelDatum :=
  { item := { form := "a wink"
            , polarityType := .npiWeak, baseForce := .degree
            , licensingContexts := [.negation]
            , scalarDirection := .strengthening
            , scalarValue := .low, canonicity := .canonical
            , likelihoodEffect := .impeding
            , morphology := .idiomatic }
  , sentence := "I didn't sleep a wink."
  , grammatical := true }

/-- "She didn't budge an inch." — canonical emphatic NPI (low, impeding) -/
def didntBudge : IsraelDatum :=
  { item := budgeAnInch
  , sentence := "She didn't budge an inch."
  , grammatical := true }

/-- "She is insanely good-looking." — canonical emphatic PPI (high) -/
def insanely : IsraelDatum :=
  { item := { form := "insanely"
            , polarityType := .ppi, baseForce := .degree
            , licensingContexts := []
            , scalarDirection := .strengthening
            , scalarValue := .high, canonicity := .canonical }
  , sentence := "She is insanely good-looking."
  , grammatical := true }

/-- "She's sorta clever." — canonical attenuating PPI (low) -/
def sorta : IsraelDatum :=
  { item := { form := "sorta"
            , polarityType := .ppi, baseForce := .degree
            , licensingContexts := []
            , scalarDirection := .attenuating
            , scalarValue := .low, canonicity := .canonical }
  , sentence := "She's sorta clever."
  , grammatical := true }

/-- "He's not all that clever." — canonical attenuating NPI (high) -/
def allThat : IsraelDatum :=
  { item := { form := "all that"
            , polarityType := .npiWeak, baseForce := .degree
            , licensingContexts := [.negation]
            , scalarDirection := .attenuating
            , scalarValue := .high, canonicity := .canonical
            , likelihoodEffect := .impeding }
  , sentence := "He's not all that clever."
  , grammatical := true }

-- ════════════════════════════════════════════════════
-- § 3. Inverted items (Figure 3)
-- ════════════════════════════════════════════════════

/-! Inverted items break the simple correlation between scalar value and
polarity type. They are explained by propositional role (§4). -/

/-- "Wild horses couldn't keep me away." — inverted emphatic NPI (high, facilitating) -/
def wildHorsesDatum : IsraelDatum :=
  { item := wildHorses
  , sentence := "Wild horses couldn't keep me away."
  , grammatical := true }

/-- "I wouldn't do it for all the tea in China." — inverted emphatic NPI (high, facilitating) -/
def teaInChinaDatum : IsraelDatum :=
  { item := allTheTeaInChina
  , sentence := "I wouldn't do it for all the tea in China."
  , grammatical := true }

/-- "I wouldn't touch it with a ten-foot pole." — inverted emphatic NPI (high, facilitating) -/
def tenFootPoleDatum : IsraelDatum :=
  { item := aTenFootPole
  , sentence := "I wouldn't touch it with a ten-foot pole."
  , grammatical := true }

/-- "Godfrey is scared of his own shadow." — inverted emphatic PPI (low, facilitating) -/
def ownShadowDatum : IsraelDatum :=
  { item := { form := "his own shadow"
            , polarityType := .ppi, baseForce := .degree
            , licensingContexts := []
            , scalarDirection := .strengthening
            , scalarValue := .low, canonicity := .inverted
            , likelihoodEffect := .facilitating
            , morphology := .idiomatic }
  , sentence := "Godfrey is scared of his own shadow."
  , grammatical := true }

/-- "You could have knocked me over with a feather." — inverted emphatic PPI (low, facilitating) -/
def withAFeatherDatum : IsraelDatum :=
  { item := { form := "with a feather"
            , polarityType := .ppi, baseForce := .degree
            , licensingContexts := []
            , scalarDirection := .strengthening
            , scalarValue := .low, canonicity := .inverted
            , likelihoodEffect := .facilitating
            , morphology := .idiomatic }
  , sentence := "You could have knocked me over with a feather."
  , grammatical := true }

/-- "We'll be back in a jiffy." — inverted emphatic PPI (low, facilitating) -/
def jiffyDatum : IsraelDatum :=
  { item := inAJiffy
  , sentence := "We'll be back in a jiffy."
  , grammatical := true }

/-- "He got Madonna to play for peanuts." — inverted emphatic PPI (low, facilitating) -/
def peanutsDatum : IsraelDatum :=
  { item := forAPittance  -- same class as "for peanuts"
  , sentence := "He got Madonna to play for peanuts."
  , grammatical := true }

-- ════════════════════════════════════════════════════
-- § 4. The Pecuniary Paradox
-- ════════════════════════════════════════════════════

/-! The pecuniary paradox (§3, examples 15–16): both *a red cent* and
*for peanuts* denote small monetary values, but *a red cent* is an NPI
and *for peanuts* is a PPI. The resolution: they occupy different
propositional roles.

- *a red cent* = Resource (what you spend) → impeding → canonical NPI
- *for peanuts* = Reward (what you gain) → facilitating → inverted PPI -/

/-- "He won't spend a red cent on your wedding." — canonical NPI, resource/expense -/
def redCentDatum : IsraelDatum :=
  { item := { form := "a red cent"
            , polarityType := .npiWeak, baseForce := .degree
            , licensingContexts := [.negation]
            , scalarDirection := .strengthening
            , scalarValue := .low, canonicity := .canonical
            , likelihoodEffect := .impeding  -- resource: bigger cost → less likely
            , morphology := .idiomatic }
  , sentence := "He won't spend a red cent on your wedding."
  , grammatical := true }

/-- "He got Madonna to play for peanuts." — inverted PPI, reward -/
def forPeanutsDatum : IsraelDatum :=
  { item := { form := "for peanuts"
            , polarityType := .ppi, baseForce := .degree
            , licensingContexts := []
            , scalarDirection := .strengthening
            , scalarValue := .low, canonicity := .inverted
            , likelihoodEffect := .facilitating  -- reward: small ask → exchange more likely
            , morphology := .idiomatic }
  , sentence := "He got Madonna to play for peanuts."
  , grammatical := true }

-- The paradox dissolves: same monetary domain, different propositional roles
#guard redCentDatum.item.likelihoodEffect == .impeding
#guard forPeanutsDatum.item.likelihoodEffect == .facilitating
#guard redCentDatum.item.canonicity == .canonical
#guard forPeanutsDatum.item.canonicity == .inverted

-- ════════════════════════════════════════════════════
-- § 5. Verification: predictCanonicity agrees with data
-- ════════════════════════════════════════════════════

/-- All items from this paper with full classification. -/
def allData : List IsraelDatum :=
  [ sleepAWink, didntBudge, insanely, sorta, allThat
  , wildHorsesDatum, teaInChinaDatum, tenFootPoleDatum
  , ownShadowDatum, withAFeatherDatum, jiffyDatum, peanutsDatum
  , redCentDatum, forPeanutsDatum ]

-- Every fully-classified item has consistent canonicity
#guard allData.all (·.item.canonicityConsistent)

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Entailment Profiles
-- ════════════════════════════════════════════════════

/-! @cite{israel-2001} §4 discusses Dowty's proto-roles (fn. 6) as a
possible basis for the canonical/inverted distinction. The connection
to `EntailmentProfile` is:

- **Proto-Agent entailments** (causation, volition, movement,
  independent existence) → participant *facilitates* event realization
- **Proto-Patient entailments** (change of state, incremental theme,
  causally affected, stationary) → participant *impedes* event realization
  (bigger obstacle → less likely)

This is NOT a function on `ThetaRole` (which is a derived convenience
label in linglib). Instead, `LikelihoodEffect` is an independent
propositional-role concept that *correlates* with proto-role entailments
but cross-cuts theta labels in cases like the pecuniary paradox
(where both arguments may be "themes" in a traditional analysis). -/

/-- Proto-Agent dominance predicts facilitating role.

    If an argument position has more P-Agent entailments than P-Patient
    entailments, the participant tends to facilitate event realization.
    This is a heuristic, not a theorem — the pecuniary paradox shows
    that propositional role can diverge from proto-role counts. -/
def pAgentDominant_suggests_facilitating (pAg pPat : Nat) : LikelihoodEffect :=
  if pAg > pPat then .facilitating
  else if pPat > pAg then .impeding
  else .unknown

-- Canonical cases: agent (pAg=5,pPat=0) → facilitating
#guard pAgentDominant_suggests_facilitating 5 0 == .facilitating
-- Canonical cases: patient (pAg=0,pPat=5) → impeding
#guard pAgentDominant_suggests_facilitating 0 5 == .impeding
-- Experiencer (pAg=2,pPat=2) → unknown (requires propositional analysis)
#guard pAgentDominant_suggests_facilitating 2 2 == .unknown

-- ════════════════════════════════════════════════════
-- § 7. Ambiguous Superlatives (§6)
-- ════════════════════════════════════════════════════

/-! Fauconnier (1975b) noted that perception verbs allow dual scalar
readings. "Eve didn't hear even the faintest noise" and "Eve didn't
hear even the loudest noise" are both emphatic, but use different scales:

- *faintest*: existential scale (ranking stimuli by likely existence)
  → canonical impeding role
- *loudest*: perceptual-ability scale (ranking experiencers by acuity)
  → inverted facilitating role

The dual reading arises because perception is bicausal: it depends
both on the stimulus's salience AND the perceiver's acuity. -/

/-- Scale type for the ambiguous-superlative phenomenon -/
inductive PerceptionScaleType where
  | existential       -- scale of stimuli ranked by likely existence
  | perceptualAbility -- scale of experiencers ranked by perceptual acuity
  deriving DecidableEq, BEq, Repr

structure AmbiguousSuperlativeDatum where
  sentence : String
  superlative : String
  scaleType : PerceptionScaleType
  likelihoodEffect : LikelihoodEffect
  notes : String
  deriving Repr

def faintestNoise : AmbiguousSuperlativeDatum :=
  { sentence := "Eve didn't hear even the faintest noise."
  , superlative := "faintest"
  , scaleType := .existential
  , likelihoodEffect := .impeding
  , notes := "Existential scale: if larger things exist, smaller ones do too" }

def loudestNoise : AmbiguousSuperlativeDatum :=
  { sentence := "Eve didn't hear even the loudest noise."
  , superlative := "loudest"
  , scaleType := .perceptualAbility
  , likelihoodEffect := .facilitating
  , notes := "Ability scale: if you can't hear the most perceptible, you can't hear anything" }

-- Both are emphatic in DE contexts, but via different scales
#guard faintestNoise.likelihoodEffect == .impeding
#guard loudestNoise.likelihoodEffect == .facilitating

end Phenomena.Polarity.Studies.Israel2001
