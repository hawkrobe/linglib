import Linglib.Semantics.Polarity.ScalarModel
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Fragments.English.PolarityItems

/-!
# [israel-2001]: Minimizers, Maximizers, and the Rhetoric of Scalar Reasoning

Israel's Scalar Model classifies polarity items by scalar value ×
rhetorical force (Figure 1) and explains the *inverted* items — maximizer
NPIs (*wild horses*) and minimizer PPIs (*for peanuts*) — by
propositional role (§4): facilitating roles produce inverted items,
impeding roles canonical ones. The pecuniary paradox dissolves: *a red
cent* (resource, impeding) and *for peanuts* (reward, facilitating)
share a low monetary value but occupy different roles, hence opposite
canonicity. The paper's items are `ScalarItem`s
(`Semantics/Polarity/ScalarModel.lean`); the classifications of the
`Fragments/English/PolarityItems.lean` entries live here in
`classifiedLexicon`, with the theory that consumes them.

## Main results

* `pecuniary_paradox` — same value and direction, different roles,
  opposite canonicity.
* `paperItems`/`classifiedLexicon` consistency — every classification
  agrees with `predictCanonicity`.
* `suggestedLikelihoodEffect` — the §4 fn. 6 bridge from [dowty-1991]
  proto-role entailments to likelihood effect.
-/

namespace Israel2001

open Semantics.Polarity
open English.PolarityItems

/-! ### Canonical items (Figure 1)

The basic Scalar Model predicts four cells:

| | **Emphatic** | **Attenuating** |
|---------|----------------------|----------------------|
| **NPI** | low: *a wink, inch* | high: *much, long* |
| **PPI** | high: *tons, utterly*| low: *sorta, rather* |

Emphatic items license maximally informative interpretations,
attenuating items minimally informative ones; NPI contexts are
scale-reversing (DE), PPI contexts scale-preserving (UE). -/

/-- *a wink* — canonical emphatic NPI (low, impeding): *I didn't sleep a
    wink.* -/
def aWink : ScalarItem :=
  { form := "a wink"
  , licensor := some .weak, baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , scalarValue := .low, canonicity := .canonical
  , likelihoodEffect := some .impeding
  , morphology := .idiomatic }

/-- *insanely* — canonical emphatic PPI (high): *She is insanely
    good-looking.* -/
def insanely : ScalarItem :=
  { form := "insanely"
  , ppi := true, baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , scalarValue := .high, canonicity := .canonical }

/-- *sorta* — canonical attenuating PPI (low): *She's sorta clever.* -/
def sorta : ScalarItem :=
  { form := "sorta"
  , ppi := true, baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .attenuating
  , scalarValue := .low, canonicity := .canonical }

/-- *all that* — canonical attenuating NPI (high): *He's not all that
    clever.* -/
def allThat : ScalarItem :=
  { form := "all that"
  , licensor := some .weak, baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .attenuating
  , scalarValue := .high, canonicity := .canonical
  , likelihoodEffect := some .impeding }

/-! ### Inverted items (Figure 3)

Inverted items break the simple correlation between scalar value and
polarity type; propositional role (§4) explains them. -/

/-- *his own shadow* — inverted emphatic PPI (low, facilitating):
    *Godfrey is scared of his own shadow.* -/
def ownShadow : ScalarItem :=
  { form := "his own shadow"
  , ppi := true, baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , scalarValue := .low, canonicity := .inverted
  , likelihoodEffect := some .facilitating
  , morphology := .idiomatic }

/-- *with a feather* — inverted emphatic PPI (low, facilitating): *You
    could have knocked me over with a feather.* -/
def withAFeather : ScalarItem :=
  { form := "with a feather"
  , ppi := true, baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , scalarValue := .low, canonicity := .inverted
  , likelihoodEffect := some .facilitating
  , morphology := .idiomatic }

/-! ### The pecuniary paradox

Both *a red cent* and *for peanuts* denote small monetary values (§3,
examples 15–16), but the first is an NPI and the second a PPI: they
occupy different propositional roles — resource (what you spend,
impeding) vs reward (what you gain, facilitating). -/

/-- *a red cent* — canonical NPI, resource role: *He won't spend a red
    cent on your wedding.* -/
def redCent : ScalarItem :=
  { form := "a red cent"
  , licensor := some .weak, baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , scalarValue := .low, canonicity := .canonical
  , likelihoodEffect := some .impeding
  , morphology := .idiomatic }

/-- *for peanuts* — inverted PPI, reward role: *He got Madonna to play
    for peanuts.* -/
def forPeanuts : ScalarItem :=
  { form := "for peanuts"
  , ppi := true, baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , scalarValue := .low, canonicity := .inverted
  , likelihoodEffect := some .facilitating
  , morphology := .idiomatic }

/-- The paradox dissolved: the same low value and emphatic direction,
    but different propositional roles and hence opposite canonicity. -/
theorem pecuniary_paradox :
    redCent.scalarValue = forPeanuts.scalarValue ∧
    redCent.scalarDirection = forPeanuts.scalarDirection ∧
    redCent.likelihoodEffect ≠ forPeanuts.likelihoodEffect ∧
    redCent.canonicity ≠ forPeanuts.canonicity := by decide

/-! ### The classified lexicon -/

/-- The paper's own example items. -/
def paperItems : List ScalarItem :=
  [aWink, insanely, sorta, allThat, ownShadow, withAFeather,
   redCent, forPeanuts]

/-- The paper's classifications of the
    `Fragments/English/PolarityItems.lean` entries (Figure 1 cells; §3
    inverted items; §4 roles where the paper gives them). -/
def classifiedLexicon : List ScalarItem :=
  [ { toItem := any, scalarValue := .low, canonicity := .canonical
    , likelihoodEffect := some .impeding }
  , { toItem := ever, scalarValue := .low, canonicity := .canonical }
  , { toItem := atAll, scalarValue := .low, canonicity := .canonical }
  , { toItem := liftAFinger, scalarValue := .low, canonicity := .canonical
    , likelihoodEffect := some .impeding }
  , { toItem := budgeAnInch, scalarValue := .low, canonicity := .canonical
    , likelihoodEffect := some .impeding }
  , { toItem := wildHorses, scalarValue := .high, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := allTheTeaInChina, scalarValue := .high, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := aTenFootPole, scalarValue := .high, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := inAMillionYears, scalarValue := .high, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := atTheDropOfAHat, scalarValue := .low, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := inAJiffy, scalarValue := .low, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := forAPittance, scalarValue := .low, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := forASong, scalarValue := .low, canonicity := .inverted
    , likelihoodEffect := some .facilitating }
  , { toItem := some_ppi, scalarValue := .low, canonicity := .canonical }
  , { toItem := somewhat, scalarValue := .low, canonicity := .canonical }
  , { toItem := rather, scalarValue := .low, canonicity := .canonical }
  , { toItem := tonsOf, scalarValue := .high, canonicity := .canonical }
  , { toItem := utterly, scalarValue := .high, canonicity := .canonical } ]

/-- Every classification agrees with the role-likelihood prediction. -/
example : ∀ p ∈ paperItems ++ classifiedLexicon, p.canonicityConsistent := by
  decide

/-! ### The proto-role bridge (§4, fn. 6) -/

/-- The suggestion of [dowty-1991] proto-role entailments for likelihood
    effect: Proto-Agent dominance suggests a facilitating role,
    Proto-Patient dominance an impeding one, and a tie suggests nothing —
    a heuristic, not a theorem: the pecuniary paradox shows propositional
    role can diverge from proto-role counts, which is why
    `LikelihoodEffect` is an independent concept rather than a function
    of theta labels. -/
def suggestedLikelihoodEffect (p : ArgumentStructure.EntailmentProfile) :
    Option LikelihoodEffect :=
  if p.pPatientScore < p.pAgentScore then some .facilitating
  else if p.pAgentScore < p.pPatientScore then some .impeding
  else none

-- A pure agent facilitates; a pure patient impedes; a balanced
-- experiencer profile requires propositional analysis.
example : suggestedLikelihoodEffect
    { volition := true, sentience := true, causation := true
    , movement := true, independentExistence := true } =
      some .facilitating := rfl
example : suggestedLikelihoodEffect
    { changeOfState := true, incrementalTheme := true
    , causallyAffected := true, stationary := true
    , dependentExistence := true } = some .impeding := rfl
example : suggestedLikelihoodEffect
    { sentience := true, causallyAffected := true } = none := rfl

/-! ### Ambiguous superlatives (§6)

Perception verbs allow dual scalar readings (Fauconnier 1975b): *Eve
didn't hear even the faintest noise* ranks stimuli by likely existence,
*… even the loudest noise* ranks experiencers by acuity. Perception is
bicausal — it depends on the stimulus's salience and the perceiver's
acuity — and the scale type fixes the role. -/

/-- The two scales a negated perception superlative can invoke. -/
inductive PerceptionScaleType where
  /-- Stimuli ranked by likely existence (*faintest*). -/
  | existential
  /-- Experiencers ranked by perceptual acuity (*loudest*). -/
  | perceptualAbility
  deriving DecidableEq, Repr

/-- The scale type fixes the propositional role: existential scales
    impede (if larger things exist, smaller ones do too), ability scales
    facilitate (missing the most perceptible means missing
    everything). -/
def PerceptionScaleType.role : PerceptionScaleType → LikelihoodEffect
  | .existential => .impeding
  | .perceptualAbility => .facilitating

/-! ### Scale-reversing = DE, scale-preserving = UE

§2 connects the Scalar Model to the Fauconnier–Ladusaw tradition:
scale-reversing contexts are the downward-entailing ones, and
scale-preserving contexts the upward-entailing ones, except that the
relevant inferences may be pragmatic entailments within a scalar model
rather than strictly logical — which is why the Scalar Model handles
cases pure monotonicity misses. -/

/-- Israel's scale directions: reversing (= DE, NPI-licensing) and
    preserving (= UE, PPI-licensing). -/
inductive ScaleDirection where
  | reversing
  | preserving
  deriving DecidableEq, Repr

/-- Expected scale direction in licensing contexts, from the item's
    parameters: strength-licensed items need scale reversal (= DE), PPIs
    scale preservation (= UE), pure FCIs neither (non-veridicality). -/
def expectedScaleDirection (e : Item) : Option ScaleDirection :=
  if e.ppi then some .preserving
  else if e.licensor.isSome then some .reversing
  else none

/-- Non-PPI NPIs need scale-reversing contexts. -/
example : ∀ e : Item, e.isNPI → expectedScaleDirection e = some .reversing ∨
    e.ppi = true := by
  intro e h
  simp only [expectedScaleDirection, Item.isNPI] at *
  split <;> simp_all

end Israel2001
