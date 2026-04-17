/-
# @cite{thomas-2026}: A Probabilistic, Question-Based Approach to Additivity

Empirical data from @cite{thomas-2026} on additive particle felicity,
including the novel argument-building use type where antecedent and
prejacent jointly support a conclusion rather than being focus alternatives.

See also `Ahn2015.lean` in this directory for an independent Boolean
algebra approach to too/either (@cite{ahn-2015}).

## Main definitions

- `ernieIree`: Argument-building "too" from COCA (ex. 1a/14a)
- `trafficTicket`: Argument-building "too" from COCA (ex. 1b/14b)
- `hotelRoom`: Argument-building "too" from COCA (ex. 1c/14c/65)
- `pizzaSpaghetti`: Standard focus-alternative "too" (ex. 5a/10/21)
- `averyInvited`: Standard additive presupposition (ex. 2)
- Infelicitous examples: scalar entailment (11/29a/73), conjunction
  irrelevance (72B), weakening/maximality (30/74),
  cross-product question (13/40/75), reversed argumentative
  orientation (15a/19a), dingy hotel (66)

-/

import Linglib.Phenomena.Focus.AdditiveParticles.Data
import Linglib.Theories.Pragmatics.Particles.Additive

namespace Thomas2026

open Phenomena.Focus.AdditiveParticles

-- Argument-Building Examples (COCA, §1/§3)

/-- Argument-building "too" from COCA (ex. 1a/14a).
ANT = Ernie took Iree in on her own; π = it was a good thing she did.
Both jointly support the conclusion that Ernie helped Iree a great deal. -/
def ernieIree : AdditiveParticleDatum :=
  { sentence := "Ernie [...] just naturally took Iree in with no authority but her own. [...] Good thing she did too because something happened in the birthing time of Iree and she's got epilepsy [...]"
  , antecedent := "Ernie took Iree in with no authority but her own"
  , prejacent := "It was a good thing she did"
  , particle := "too"
  , resolvedQuestion := some "How much has Ernie helped Iree?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. ANT and π jointly evidence the conclusion that Ernie helped Iree a great deal."
  , source := "Thomas (2026), ex. 1a/14a"
  }

/-- Argument-building "too" from COCA (ex. 1b/14b).
ANT = I know a couple people who have gotten tickets;
π = the fine is a hefty one.
Both jointly support the conclusion: you should worry about traffic
enforcement. -/
def trafficTicket : AdditiveParticleDatum :=
  { sentence := "i have never gotten a ticket but i know a cpl people who have.. i guess the fine is a hefty one too. depending on what im driving, i chance it."
  , antecedent := "I know a couple people who have gotten tickets"
  , prejacent := "The fine is a hefty one"
  , particle := "too"
  , resolvedQuestion := some "How much should I worry about traffic enforcement?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. Both provide cumulative evidence that traffic enforcement is serious."
  , source := "Thomas (2026), ex. 1b/14b"
  }

/-- Argument-building "too" from COCA (ex. 1c/14c/65).
ANT = A room just opened up at this hotel;
π = It looks kind of fancy.
Both jointly support the conclusion: this hotel would be a good place
to stay. Primary worked example in §5.3. -/
def hotelRoom : AdditiveParticleDatum :=
  { sentence := "A room just opened up at this hotel. [...] It looks kind of fancy, too."
  , antecedent := "A room just opened up at this hotel"
  , prejacent := "It looks kind of fancy"
  , particle := "too"
  , resolvedQuestion := some "What would be a good hotel for us to stay at?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. Primary worked example in §5.3. ANT = room available, π = fancy, RQ = good hotel?"
  , source := "Thomas (2026), ex. 1c/14c/65"
  }

/-- All argument-building examples from @cite{thomas-2026}. -/
def argumentBuildingExamples : List AdditiveParticleDatum :=
  [ernieIree, trafficTicket, hotelRoom]

-- Standard (Focus-Alternative) Examples

/-- Standard focus-alternative "too" (ex. 5a/10/21).
ANT = "I like pizza", π = "I like spaghetti".
Both are partial answers to "What do you like?" -/
def pizzaSpaghetti : AdditiveParticleDatum :=
  { sentence := "I like [pizza]_F, and I like [spaghetti]_F, too."
  , antecedent := "I like pizza"
  , prejacent := "I like spaghetti"
  , particle := "too"
  , resolvedQuestion := some "What do you like?"
  , felicity := .ok
  , useType := .standard
  , notes := "Standard use. ANT and π are focus alternatives (same property, different objects)."
  , source := "Thomas (2026), ex. 5a/10/21"
  }

/-- Standard additive presupposition example (ex. 2).
Q: Who did Avery invite?
ANT = Avery invited Bailey. π = She invited Cameron. -/
def averyInvited : AdditiveParticleDatum :=
  { sentence := "Q: Who did Avery invite? A: Avery invited Bailey. She invited Cameron, too."
  , antecedent := "Avery invited Bailey"
  , prejacent := "Avery invited Cameron"
  , particle := "too"
  , resolvedQuestion := some "Who did Avery invite?"
  , felicity := .ok
  , useType := .standard
  , notes := "Standard additive presupposition: ANT and π are both partial answers to the same question."
  , source := "Thomas (2026), ex. 2"
  }

/-- Standard focus-alternative examples. -/
def standardExamples : List AdditiveParticleDatum :=
  [pizzaSpaghetti, averyInvited]

-- Infelicitous Examples

/-- Infelicitous: π entails the resolution — violates non-triviality
(ex. 11/29a/73).
ANT = "Sam is happy", π = "He's ecstatic".
Since "ecstatic" entails "happy", ⟦π⟧ ⊆ RQ|_{ANT∩⟦π⟧} = |Sam is ecstatic|,
violating Def. 64c.i. -/
def happyEcstatic : AdditiveParticleDatum :=
  { sentence := "Sam is happy. #He's ecstatic, too."
  , antecedent := "Sam is happy"
  , prejacent := "Sam is ecstatic"
  , particle := "too"
  , resolvedQuestion := some "What is Sam's emotional state?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: π = 'ecstatic' entails the resolution evidenced by ANT∩π — violates Def. 64c.i (non-triviality)."
  , source := "Thomas (2026), ex. 11/29a/73"
  }

/-- Infelicitous: reversed argumentative orientation — no suitable RQ
(ex. 15a/19a).
In the context of (14a) where Ernie's actions are evaluated positively,
replacing "good thing" with "bad thing" reverses the argumentative
direction. No RQ satisfies both the Antecedent and Conjunction Conditions. -/
def badThingSheDidToo : AdditiveParticleDatum :=
  { sentence := "Ernie took Iree in with no authority but her own. It was a bad thing she did, #too."
  , antecedent := "Ernie took Iree in with no authority but her own"
  , prejacent := "It was a bad thing she did"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .argumentBuilding
  , notes := "Infelicitous: ANT evidences a positive conclusion but π evidences a negative one — no RQ satisfies both conditions."
  , source := "Thomas (2026), ex. 15a/19a"
  }

/-- Infelicitous: conjunction provides no additional evidence — fails
Conjunction Condition (ex. 72B).
ANT = "She invited Bailey and Cameron", π = "Dogs are mammals".
π provides no information about who Avery invited. -/
def dogsAreMammals : AdditiveParticleDatum :=
  { sentence := "Q: Who are some people Avery invited? A: She invited Bailey and Cameron. #Dogs are mammals, too."
  , antecedent := "She invited Bailey and Cameron"
  , prejacent := "Dogs are mammals"
  , particle := "too"
  , resolvedQuestion := some "Who are some people Avery invited?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: π provides no information relevant to RQ — ANT∩⟦π⟧ does not Evidence RQ more strongly than ANT alone (fails Conjunction Condition)."
  , source := "Thomas (2026), ex. 72B"
  }

/-- Infelicitous: weaker alternative works just as well — violates
maximality (ex. 30/74).
ANT = "Avery plays an instrument", π = "Bailey plays the cello".
"Bailey plays an instrument" (weaker than π) gives the same evidential
boost to the resolution. -/
def instrumentCello : AdditiveParticleDatum :=
  { sentence := "Q: Who plays an instrument? A: Avery plays an instrument. #Bailey plays the cello, too."
  , antecedent := "Avery plays an instrument"
  , prejacent := "Bailey plays the cello"
  , particle := "too"
  , resolvedQuestion := some "Who plays an instrument?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: 'Bailey plays an instrument' (⊃ ⟦π⟧) evidences the resolution just as strongly — violates Def. 64c.ii (maximality). Note: swapping ANT and π yields felicitous 'too' (ex. 30A')."
  , source := "Thomas (2026), ex. 30/74"
  }

/-- Infelicitous: cross-product question — no single RQ satisfies both
conditions (ex. 13/40/75).
Q: Who ate what? ANT = "Avery ate pizza", π = "Bailey ate spaghetti".
Every resolution to "Who ate what?" specifies what BOTH Avery and Bailey
ate, so ANT alone provides no information about Bailey's food. -/
def whoAteWhat : AdditiveParticleDatum :=
  { sentence := "Q: Who ate what? A: Avery ate pizza. B: #Bailey ate spaghetti, too."
  , antecedent := "Avery ate pizza"
  , prejacent := "Bailey ate spaghetti"
  , particle := "too"
  , resolvedQuestion := some "Who ate what?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: ANT answers 'What did Avery eat?' while π answers 'What did Bailey eat?' — no single RQ has both Antecedent and Conjunction Conditions satisfied."
  , source := "Thomas (2026), ex. 13/40/75"
  }

/-- Infelicitous: reversed argumentative orientation in hotel context
(ex. 66).
ANT = "A room just opened up at this hotel", π = "It looks kind of dingy".
The discourse goal is finding a GOOD hotel, but "dingy" argues AGAINST
the hotel being good. No RQ relevant to the discourse goals has its
felicity conditions satisfied.

Contrast with `hotelRoom` (ex. 65): same ANT but π = "fancy" supports
the "good hotel" conclusion. @cite{thomas-2026} notes that replacing
"fancy" with "dingy" makes "too" unacceptable because ANT ∩ ⟦π⟧ does
not raise the probability of any resolution desirable to the interlocutors. -/
def dingyHotel : AdditiveParticleDatum :=
  { sentence := "A room just opened up at this hotel. It looks kind of dingy, (#too)."
  , antecedent := "A room just opened up at this hotel"
  , prejacent := "It looks kind of dingy"
  , particle := "too"
  , resolvedQuestion := some "What would be a good hotel for us to stay at?"
  , felicity := .odd
  , useType := .argumentBuilding
  , notes := "Infelicitous: 'dingy' argues AGAINST the discourse goal (finding a good hotel). Contrast with hotelRoom (ex. 65) where 'fancy' supports the goal."
  , source := "Thomas (2026), ex. 66"
  }

/-- Infelicitous examples from @cite{thomas-2026}. -/
def infelicitousExamples : List AdditiveParticleDatum :=
  [happyEcstatic, badThingSheDidToo, dogsAreMammals, instrumentCello, whoAteWhat, dingyHotel]

-- Collected Data

/-- All examples. -/
def allExamples : List AdditiveParticleDatum :=
  argumentBuildingExamples ++ standardExamples ++ infelicitousExamples

-- ============================================================================
-- End-to-End Verification: Def. 64 Predicts Felicity
-- ============================================================================

/-! ## End-to-End Verification

Concrete `Fin 4` instantiations of the felicity conditions (Def. 64) from
@cite{thomas-2026}. Five verified scenarios cover the three use types and
all four felicity conditions:

- **Hotel room** (felicitous, argument-building): all four conditions pass
- **Pizza/spaghetti** (felicitous, standard): mention-all partition question
- **Happy/ecstatic** (infelicitous): Def. 64c.i non-triviality failure
- **Instrument/cello** (infelicitous): Def. 64c.ii maximality failure
- **Cross-product** (infelicitous): Def. 64b Conjunction Condition failure -/

section Verification

open Discourse
open Semantics.Questions.ProbabilisticAnswerhood
open Pragmatics.Particles.Additive

-- § Hotel Room (ex. 1c/14c/65) — felicitous argument-building "too"

/-- 4-world model for the hotel room scenario (@cite{thomas-2026}, ex. 65).

| World | Room Available | Fancy | Good Hotel |
|-------|---------------|-------|------------|
| w₀    | ✓             | ✓     | ✓          |
| w₁    | ✓             |       |            |
| w₂    |               | ✓     |            |
| w₃    |               |       |            |

Prior: w₀ = 3/8, w₁ = 1/8, w₂ = 2/8, w₃ = 2/8 (room availability more likely). -/
def roomAvail : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1
def fancyH : Fin 4 → Bool := fun w => w.val == 0 || w.val == 2
def goodHotel : Fin 4 → Bool := fun w => w.val == 0

/-- Non-uniform prior: room availability (w₀, w₁) more likely. -/
def hotelPrior : Prior (Fin 4) where
  mass := fun w => match w.val with | 0 => 3/8 | 1 => 1/8 | 2 => 2/8 | _ => 2/8
  mass_nonneg := by native_decide
  mass_sum_one := by native_decide

def hotelCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Issue.polar goodHotel
  , antecedent := roomAvail
  , prior := hotelPrior }

/-- Hotel room "too" is felicitous: all four conditions of Def. 64 hold.
- **Antecedent Condition**: P(good | room) = 3/4 ≠ P(good) = 3/8
- **Conjunction Condition**: P(good | room ∧ fancy) = 1 > P(good | room) = 3/4
- **Non-triviality**: fancy includes w₂ which is not a good hotel
- **Maximality**: every ANT ∧ good world is also a fancy world -/
theorem hotel_too_felicitous :
    tooFelicitousWith hotelCtx fancyH (List.finRange 4) = true := by native_decide

-- § Happy/Ecstatic (ex. 11/29a/73) — infelicitous: non-triviality failure

/-- 4-world model for the happy/ecstatic scenario.

| World | Ecstatic | Happy (not ecstatic) | Not Happy |
|-------|----------|---------------------|-----------|
| w₀    | ✓        |                     |           |
| w₁    |          | ✓                   |           |
| w₂    |          |                     | ✓         |
| w₃    |          |                     | ✓         |

Prior: uniform 1/4. -/
def happyE : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1
def ecstaticE : Fin 4 → Bool := fun w => w.val == 0

/-- "What is Sam's emotional state?" — three-way partition. -/
def emotionRQ : Issue (Fin 4) :=
  ⟨[ fun w => w.val == 0               -- ecstatic
   , fun w => w.val == 1               -- happy but not ecstatic
   , fun w => w.val == 2 || w.val == 3 -- not happy
   ]⟩

def emotionPrior : Prior (Fin 4) where
  mass := fun _ => 1/4
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

def emotionCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := emotionRQ
  , antecedent := happyE
  , prior := emotionPrior }

/-- "Sam is happy. #He's ecstatic, too." is infelicitous.
Def. 64c.i (non-triviality) fails: the strengthened resolution is
{w₀} = "ecstatic", and ⟦π⟧ = "ecstatic" = {w₀} entails it,
making the conjunction informationally redundant with respect to RQ. -/
theorem ecstatic_too_infelicitous :
    tooFelicitousWith emotionCtx ecstaticE (List.finRange 4) = false := by native_decide

-- § Pizza/Spaghetti (ex. 5a/10/21) — felicitous standard "too"

/-- 4-world model for the standard focus-alternative scenario.

| World | Like Pizza | Like Spaghetti | Partition Cell |
|-------|-----------|----------------|----------------|
| w₀    | ✓         | ✓              | both           |
| w₁    | ✓         |                | pizza only     |
| w₂    |           | ✓              | spaghetti only |
| w₃    |           |                | neither        |

Prior: uniform 1/4. ANT = "I like pizza", π = "I like spaghetti".
RQ = "What do you like?" as a mention-all question with 4-cell partition.

The strengthened resolution under ANT ∧ π is "both" = {w₀}, which π
(= {w₀,w₂}) does NOT entail. This is why standard use passes
non-triviality: the partition cell "both" is strictly stronger than π. -/
def likePizza : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1
def likeSpaghetti : Fin 4 → Bool := fun w => w.val == 0 || w.val == 2

/-- "What do you like?" — mention-all partition. -/
def foodRQ : Issue (Fin 4) :=
  Issue.ofAlternatives
    [ fun w => w.val == 0  -- both
    , fun w => w.val == 1  -- pizza only
    , fun w => w.val == 2  -- spaghetti only
    , fun w => w.val == 3  -- neither
    ]

def foodPrior : Prior (Fin 4) where
  mass := fun _ => 1/4
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

def foodCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := foodRQ
  , antecedent := likePizza
  , prior := foodPrior }

/-- Standard "too" is felicitous: "I like pizza. I like spaghetti, too."
- **Antecedent Condition**: P("both" | pizza) = 1/2 > P("both") = 1/4
- **Conjunction Condition**: P("both" | pizza ∧ spaghetti) = 1 > P("both" | pizza) = 1/2
- **Non-triviality**: spaghetti = {w₀,w₂} ⊄ "both" = {w₀}
- **Maximality**: every pizza ∧ "both" world (= {w₀}) has spaghetti true -/
theorem pizza_spaghetti_too_felicitous :
    tooFelicitousWith foodCtx likeSpaghetti (List.finRange 4) = true := by native_decide

-- § Instrument/Cello (ex. 30/74) — infelicitous: maximality failure

/-- 4-world model for the maximality failure scenario.

| World | Avery Plays | Bailey Plays Cello | Bailey Plays (any) |
|-------|------------|--------------------|--------------------|
| w₀    | ✓          | ✓                  | ✓                  |
| w₁    | ✓          |                    | ✓ (non-cello)      |
| w₂    | ✓          |                    |                    |
| w₃    |            |                    |                    |

Prior: uniform 1/4. ANT = "Avery plays an instrument".
π = "Bailey plays the cello". RQ = "Who plays an instrument?"
(polar: does Bailey play?).

Maximality fails: "Bailey plays an instrument" (S ⊃ π) gives the
same evidential boost as "Bailey plays the cello" (π), since both
make P(Bailey plays | ANT ∧ ·) = 1. The specific instrument is
irrelevant to RQ. -/
def averyPlays : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1 || w.val == 2
def baileyPlaysCello : Fin 4 → Bool := fun w => w.val == 0
def baileyPlays : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1

def instrumentPrior : Prior (Fin 4) where
  mass := fun _ => 1/4
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

def instrumentCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Issue.polar baileyPlays
  , antecedent := averyPlays
  , prior := instrumentPrior }

/-- "Avery plays an instrument. #Bailey plays the cello, too." is infelicitous.
Def. 64c.ii (maximality) fails: w₁ is an ANT ∧ baileyPlays world but
not a baileyPlaysCello world, so a weaker proposition (baileyPlays)
gives the same evidential boost to RQ. -/
theorem cello_too_infelicitous :
    tooFelicitousWith instrumentCtx baileyPlaysCello (List.finRange 4) = false := by native_decide

-- § Cross-Product Question (ex. 13/40/75) — infelicitous: Conjunction Condition failure

/-- 4-world model for the cross-product question scenario.

| World | Avery Eats  | Bailey Eats  |
|-------|------------|--------------|
| w₀    | pizza      | pizza        |
| w₁    | pizza      | spaghetti    |
| w₂    | spaghetti  | pizza        |
| w₃    | spaghetti  | spaghetti    |

Prior: uniform 1/4. ANT = "Avery ate pizza", π = "Bailey ate spaghetti".

@cite{thomas-2026} §5.5.1 (pp. 40-41) argues that for "Who ate what?",
no single RQ simultaneously satisfies both the Antecedent and Conjunction
Conditions. We verify this for RQ = "What did Avery eat?" ((76a)):
ANT already determines the resolution (P(Avery pizza | ANT) = 1), so
learning π = "Bailey ate spaghetti" adds nothing about Avery — the
Conjunction Condition fails because no alternative is strengthened. -/
def averyPizzaCP : Fin 4 → Bool := fun w => w.val == 0 || w.val == 1
def baileySpaghetti : Fin 4 → Bool := fun w => w.val == 1 || w.val == 3

def crossPrior : Prior (Fin 4) where
  mass := fun _ => 1/4
  mass_nonneg := by intro _; norm_num
  mass_sum_one := by native_decide

/-- RQ = "What did Avery eat?" (polar: did Avery eat pizza?). -/
def crossCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Issue.polar averyPizzaCP
  , antecedent := averyPizzaCP
  , prior := crossPrior }

/-- "Avery ate pizza. #Bailey ate spaghetti, too." is infelicitous
when RQ = "What did Avery eat?"
Conjunction Condition fails: P(Avery pizza | ANT∩π) = 1 = P(Avery pizza | ANT),
so π provides no additional evidence about what Avery ate. -/
theorem cross_product_too_infelicitous :
    tooFelicitousWith crossCtx baileySpaghetti (List.finRange 4) = false := by native_decide

end Verification

end Thomas2026
