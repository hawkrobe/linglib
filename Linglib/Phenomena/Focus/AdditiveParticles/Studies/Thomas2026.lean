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
import Linglib.Core.Probability.PMFFin
import Mathlib.Algebra.BigOperators.Fin

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
- **Cross-product** (infelicitous): Def. 64b Conjunction Condition failure

After the Set/Prop migration, the felicity predicates are `noncomputable`
and `Prop`-valued. Each scenario provides per-set `DecidablePred` instances
+ named probability/conditional-probability lemmas (computed via
`Fin.sum_univ_four`) + an `alt`-characterisation lemma
(`Question.alt_polar_of_nontrivial` for polar contexts;
`Question.alt_ofList_of_pairwise_disjoint_nonempty` for partition contexts);
felicity proofs then reduce to `convert`-bridged inequalities. -/

section Verification

open Semantics.Questions.ProbabilisticAnswerhood
open Pragmatics.Particles.Additive
open Core

-- § Hotel Room (ex. 1c/14c/65) — felicitous argument-building "too"

/-- 4-world model for the hotel room scenario (@cite{thomas-2026}, ex. 65).

| World | Room Available | Fancy | Good Hotel |
|-------|---------------|-------|------------|
| w₀    | ✓             | ✓     | ✓          |
| w₁    | ✓             |       |            |
| w₂    |               | ✓     |            |
| w₃    |               |       |            |

Prior: w₀ = 3/8, w₁ = 1/8, w₂ = 2/8, w₃ = 2/8 (room availability more likely). -/
def roomAvail : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1}
def fancyH : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 2}
def goodHotel : Set (Fin 4) := {w | w.val = 0}

/-- Non-uniform prior: room availability (w₀, w₁) more likely. -/
noncomputable def hotelPrior : Prior (Fin 4) :=
  PMF.ofFintype
    (fun w => match w.val with | 0 => 3/8 | 1 => 1/8 | 2 => 2/8 | _ => 2/8)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

noncomputable def hotelCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Core.Question.polar goodHotel
  , antecedent := roomAvail
  , prior := hotelPrior }

instance instRoomAvailDec : DecidablePred (· ∈ roomAvail) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance instFancyHDec : DecidablePred (· ∈ fancyH) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 2))
instance instGoodHotelDec : DecidablePred (· ∈ goodHotel) := fun w =>
  inferInstanceAs (Decidable (w.val = 0))

private lemma goodHotel_ne_empty : goodHotel ≠ ∅ := by
  intro h; exact (h ▸ (rfl : (0 : Fin 4).val = 0) : (0 : Fin 4) ∈ (∅ : Set (Fin 4)))

private lemma goodHotel_ne_univ : goodHotel ≠ Set.univ := by
  intro h
  exact absurd (h ▸ Set.mem_univ (1 : Fin 4) : (1 : Fin 4) ∈ goodHotel) (by decide)

private lemma hotel_prob_room : hotelPrior.probOfSet roomAvail = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [hotelPrior, roomAvail]; ennreal_arith

private lemma hotel_prob_good : hotelPrior.probOfSet goodHotel = 3/8 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [hotelPrior, goodHotel]

private lemma hotel_prob_room_inter_good :
    hotelPrior.probOfSet (roomAvail ∩ goodHotel) = 3/8 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [hotelPrior, roomAvail, goodHotel]

private lemma hotel_prob_room_inter_goodC :
    hotelPrior.probOfSet (roomAvail ∩ goodHotelᶜ) = 1/8 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [hotelPrior, roomAvail, goodHotel, Set.mem_inter_iff]

private lemma hotel_prob_roomFancy :
    hotelPrior.probOfSet (roomAvail ∩ fancyH) = 3/8 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [hotelPrior, roomAvail, fancyH]

private lemma hotel_prob_roomFancy_inter_good :
    hotelPrior.probOfSet (roomAvail ∩ fancyH ∩ goodHotel) = 3/8 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [hotelPrior, roomAvail, fancyH, goodHotel]

private lemma hotel_prob_roomFancy_inter_goodC :
    hotelPrior.probOfSet (roomAvail ∩ fancyH ∩ goodHotelᶜ) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [roomAvail, fancyH, goodHotel, Set.mem_inter_iff]

private lemma hotel_cond_room_good :
    hotelPrior.condProbSet roomAvail goodHotel = 3/4 := by
  rw [PMF.condProbSet_eq_div,
      hotel_prob_room_inter_good, hotel_prob_room]
  ennreal_arith

private lemma hotel_cond_room_goodC :
    hotelPrior.condProbSet roomAvail goodHotelᶜ = 1/4 := by
  rw [PMF.condProbSet_eq_div,
      hotel_prob_room_inter_goodC, hotel_prob_room]
  ennreal_arith

private lemma hotel_cond_roomFancy_good :
    hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotel = 1 := by
  rw [PMF.condProbSet_eq_div,
      hotel_prob_roomFancy_inter_good, hotel_prob_roomFancy]
  ennreal_arith

private lemma hotel_cond_roomFancy_goodC :
    hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotelᶜ = 0 := by
  rw [PMF.condProbSet_eq_div,
      hotel_prob_roomFancy_inter_goodC, hotel_prob_roomFancy]
  ennreal_arith

/-- Hotel room "too" is felicitous: all four conditions of Def. 64 hold.
- **Antecedent Condition**: P(good | room) = 3/4 > P(good) = 3/8
- **Conjunction Condition**: P(good | room ∧ fancy) = 1 > P(good | room) = 3/4
- **Non-triviality**: fancy includes w₂ which is not a good hotel
- **Maximality**: every ANT ∧ good world (w₀) is also fancy. -/
theorem hotel_too_felicitous : tooFelicitous hotelCtx fancyH := by
  have hCtxAnt : hotelCtx.antecedent = roomAvail := rfl
  have hCtxRQ : hotelCtx.resolvedQuestion = Question.polar goodHotel := rfl
  have hCtxPrior : hotelCtx.prior = hotelPrior := rfl
  have hAltMem : goodHotel ∈ Question.alt (Question.polar goodHotel) := by
    rw [Question.alt_polar_of_nontrivial goodHotel_ne_empty goodHotel_ne_univ]
    exact Set.mem_insert _ _
  refine ⟨?ant, ⟨?conjA, ?conjS⟩, ?nontrv, ?max⟩
  · show probAnswersS hotelCtx.antecedent hotelCtx.resolvedQuestion hotelCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨goodHotel, hAltMem, ?_⟩
    have h : hotelPrior.condProbSet roomAvail goodHotel >
             hotelPrior.probOfSet goodHotel := by
      rw [hotel_cond_room_good, hotel_prob_good]; ennreal_arith
    convert h
  · show probAnswersS (hotelCtx.antecedent ∩ fancyH) hotelCtx.resolvedQuestion
         hotelCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨goodHotel, hAltMem, ?_⟩
    have h : hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotel >
             hotelPrior.probOfSet goodHotel := by
      rw [hotel_cond_roomFancy_good, hotel_prob_good]; ennreal_arith
    convert h
  · show someResolutionStrengthenedS hotelCtx.antecedent fancyH
         hotelCtx.resolvedQuestion hotelCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨goodHotel, hAltMem, ?_⟩
    have h : hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotel >
             hotelPrior.condProbSet roomAvail goodHotel := by
      rw [hotel_cond_roomFancy_good, hotel_cond_room_good]; ennreal_arith
    convert h
  · show nonTrivialityCondition hotelCtx fancyH
    unfold nonTrivialityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨goodHotel, hAltMem, ?_, ?_⟩
    · intro hsub
      exact absurd (hsub (Or.inr rfl : (2 : Fin 4) ∈ fancyH)) (by decide)
    · have h : hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotel >
               hotelPrior.condProbSet roomAvail goodHotel := by
        rw [hotel_cond_roomFancy_good, hotel_cond_room_good]; ennreal_arith
      convert h
  · show maximalityCondition hotelCtx fancyH
    unfold maximalityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro a haAlt hStrengthen w _ _ haW
    rw [Question.alt_polar_of_nontrivial goodHotel_ne_empty goodHotel_ne_univ] at haAlt
    rcases haAlt with rfl | haAlt
    · have : w = 0 := Fin.ext (haW : w.val = 0)
      rw [this]; exact Or.inl rfl
    · rw [Set.mem_singleton_iff] at haAlt
      subst haAlt
      have hno : ¬ (hotelPrior.condProbSet (roomAvail ∩ fancyH) goodHotelᶜ >
                    hotelPrior.condProbSet roomAvail goodHotelᶜ) := by
        rw [hotel_cond_roomFancy_goodC, hotel_cond_room_goodC]; ennreal_arith
      exact absurd (by convert hStrengthen) hno

-- § Happy/Ecstatic (ex. 11/29a/73) — infelicitous: non-triviality failure

/-- 4-world model for the happy/ecstatic scenario.

| World | Ecstatic | Happy (not ecstatic) | Not Happy |
|-------|----------|---------------------|-----------|
| w₀    | ✓        |                     |           |
| w₁    |          | ✓                   |           |
| w₂    |          |                     | ✓         |
| w₃    |          |                     | ✓         |

Prior: uniform 1/4. -/
def happyE : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1}
def ecstaticE : Set (Fin 4) := {w | w.val = 0}

/-- "What is Sam's emotional state?" — three-way partition. -/
def emotionRQ : Core.Question (Fin 4) :=
  Core.Question.ofList
    [ {w | w.val = 0}                    -- ecstatic
    , {w | w.val = 1}                    -- happy but not ecstatic
    , {w | w.val = 2 ∨ w.val = 3}        -- not happy
    ]

noncomputable def emotionPrior : Prior (Fin 4) :=
  PMF.ofFintype (fun _ => 1/4)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

noncomputable def emotionCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := emotionRQ
  , antecedent := happyE
  , prior := emotionPrior }

instance instEmCellEDec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 0} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 0))
instance instEmCellHDec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 1} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 1))
instance instEmCellNDec :
    DecidablePred (· ∈ ({w : Fin 4 | w.val = 2 ∨ w.val = 3} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 2 ∨ w.val = 3))
instance instHappyEDec : DecidablePred (· ∈ happyE) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance instEcstaticEDec : DecidablePred (· ∈ ecstaticE) :=
  fun w => inferInstanceAs (Decidable (w.val = 0))

private lemma em_prob_happy : emotionPrior.probOfSet happyE = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior, happyE]; ennreal_arith

private lemma em_prob_happy_ecst :
    emotionPrior.probOfSet (happyE ∩ ecstaticE) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior, happyE, ecstaticE]

private lemma em_prob_happy_inter_h :
    emotionPrior.probOfSet (happyE ∩ {w | w.val = 1}) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior, happyE]

private lemma em_prob_happyEcst_inter_h :
    emotionPrior.probOfSet (happyE ∩ ecstaticE ∩ {w | w.val = 1}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [happyE, ecstaticE]

private lemma em_prob_happy_inter_n :
    emotionPrior.probOfSet (happyE ∩ {w | w.val = 2 ∨ w.val = 3}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [happyE]

private lemma em_prob_happyEcst_inter_n :
    emotionPrior.probOfSet (happyE ∩ ecstaticE ∩ {w | w.val = 2 ∨ w.val = 3}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [happyE, ecstaticE]

private lemma em_cond_happy_h :
    emotionPrior.condProbSet happyE {w | w.val = 1} = 1/2 := by
  rw [PMF.condProbSet_eq_div,
      em_prob_happy_inter_h, em_prob_happy]
  ennreal_arith

private lemma em_cond_happyEcst_h :
    emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 1} = 0 := by
  rw [PMF.condProbSet_eq_div,
      em_prob_happyEcst_inter_h, em_prob_happy_ecst]
  ennreal_arith

private lemma em_cond_happy_n :
    emotionPrior.condProbSet happyE {w | w.val = 2 ∨ w.val = 3} = 0 := by
  rw [PMF.condProbSet_eq_div,
      em_prob_happy_inter_n, em_prob_happy]
  ennreal_arith

private lemma em_cond_happyEcst_n :
    emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 2 ∨ w.val = 3} = 0 := by
  rw [PMF.condProbSet_eq_div,
      em_prob_happyEcst_inter_n, em_prob_happy_ecst]
  ennreal_arith

private lemma emotion_alt :
    Question.alt emotionRQ =
    {p | p ∈ ([{w | w.val = 0}, {w | w.val = 1}, {w | w.val = 2 ∨ w.val = 3}]
              : List (Set (Fin 4)))} := by
  apply Question.alt_ofList_of_pairwise_disjoint_nonempty
  · decide
  · intro p₁ hp₁ p₂ hp₂ hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | (rw [Set.disjoint_left]; intro w hw1 hw2;
         simp only [Set.mem_setOf_eq] at hw1 hw2; omega)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · intro h
      exact absurd (h ▸ (rfl : (0 : Fin 4).val = 0) :
        (0 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)
    · intro h
      exact absurd (h ▸ (rfl : (1 : Fin 4).val = 1) :
        (1 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)
    · intro h
      exact absurd (h ▸ (Or.inl rfl : (2 : Fin 4).val = 2 ∨ (2 : Fin 4).val = 3) :
        (2 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)

/-- "Sam is happy. #He's ecstatic, too." is infelicitous.
Def. 64c.i (non-triviality) fails: the only strengthened resolution is
{w₀} = "ecstatic", and ⟦π⟧ = "ecstatic" = {w₀} entails it. -/
theorem ecstatic_too_infelicitous : ¬ tooFelicitous emotionCtx ecstaticE := by
  have hCtxAnt : emotionCtx.antecedent = happyE := rfl
  have hCtxRQ : emotionCtx.resolvedQuestion = emotionRQ := rfl
  have hCtxPrior : emotionCtx.prior = emotionPrior := rfl
  intro hFel
  obtain ⟨_, _, hNT, _⟩ := hFel
  have hNT' : nonTrivialityCondition emotionCtx ecstaticE := hNT
  unfold nonTrivialityCondition at hNT'
  rw [hCtxAnt, hCtxRQ, hCtxPrior] at hNT'
  obtain ⟨a, haAlt, hNotSub, hStr⟩ := hNT'
  rw [emotion_alt] at haAlt
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at haAlt
  rcases haAlt with rfl | rfl | rfl
  · exact hNotSub (fun _ h => h)
  · have hno : ¬ (emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 1} >
                  emotionPrior.condProbSet happyE {w | w.val = 1}) := by
      rw [em_cond_happyEcst_h, em_cond_happy_h]; ennreal_arith
    exact hno (by convert hStr)
  · have hno : ¬ (emotionPrior.condProbSet (happyE ∩ ecstaticE)
                    {w | w.val = 2 ∨ w.val = 3} >
                  emotionPrior.condProbSet happyE {w | w.val = 2 ∨ w.val = 3}) := by
      rw [em_cond_happyEcst_n, em_cond_happy_n]; ennreal_arith
    exact hno (by convert hStr)

-- § Pizza/Spaghetti (ex. 5a/10/21) — felicitous standard "too"

/-- 4-world model for the standard focus-alternative scenario.

| World | Like Pizza | Like Spaghetti | Partition Cell |
|-------|-----------|----------------|----------------|
| w₀    | ✓         | ✓              | both           |
| w₁    | ✓         |                | pizza only     |
| w₂    |           | ✓              | spaghetti only |
| w₃    |           |                | neither        |

Prior: uniform 1/4. ANT = "I like pizza", π = "I like spaghetti".
RQ = "What do you like?" as a mention-all question with 4-cell partition. -/
def likePizza : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1}
def likeSpaghetti : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 2}

/-- "What do you like?" — mention-all partition. -/
def foodRQ : Core.Question (Fin 4) :=
  Core.Question.ofList
    [ {w | w.val = 0}    -- both
    , {w | w.val = 1}    -- pizza only
    , {w | w.val = 2}    -- spaghetti only
    , {w | w.val = 3}    -- neither
    ]

noncomputable def foodPrior : Prior (Fin 4) :=
  PMF.ofFintype (fun _ => 1/4)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

noncomputable def foodCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := foodRQ
  , antecedent := likePizza
  , prior := foodPrior }

instance instLikePizzaDec : DecidablePred (· ∈ likePizza) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance instLikeSpaghettiDec : DecidablePred (· ∈ likeSpaghetti) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 2))
instance instFood0Dec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 0} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 0))
instance instFood1Dec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 1} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 1))
instance instFood2Dec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 2} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 2))
instance instFood3Dec : DecidablePred (· ∈ ({w : Fin 4 | w.val = 3} : Set (Fin 4))) :=
  fun w => inferInstanceAs (Decidable (w.val = 3))

private lemma fd_prob_pizza : foodPrior.probOfSet likePizza = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [foodPrior, likePizza]; ennreal_arith

private lemma fd_prob_pizza_spag :
    foodPrior.probOfSet (likePizza ∩ likeSpaghetti) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [foodPrior, likePizza, likeSpaghetti]

private lemma fd_prob_0 : foodPrior.probOfSet {w : Fin 4 | w.val = 0} = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [foodPrior]

private lemma fd_prob_pizza_inter_0 :
    foodPrior.probOfSet (likePizza ∩ {w | w.val = 0}) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [foodPrior, likePizza]

private lemma fd_prob_pizzaSpag_inter_0 :
    foodPrior.probOfSet (likePizza ∩ likeSpaghetti ∩ {w | w.val = 0}) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [foodPrior, likePizza, likeSpaghetti]

private lemma fd_prob_pizza_inter_1 :
    foodPrior.probOfSet (likePizza ∩ {w | w.val = 1}) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [foodPrior, likePizza]

private lemma fd_prob_pizzaSpag_inter_1 :
    foodPrior.probOfSet (likePizza ∩ likeSpaghetti ∩ {w | w.val = 1}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [likePizza, likeSpaghetti]

private lemma fd_prob_pizza_inter_2 :
    foodPrior.probOfSet (likePizza ∩ {w | w.val = 2}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [likePizza]

private lemma fd_prob_pizzaSpag_inter_2 :
    foodPrior.probOfSet (likePizza ∩ likeSpaghetti ∩ {w | w.val = 2}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [likePizza, likeSpaghetti]

private lemma fd_prob_pizza_inter_3 :
    foodPrior.probOfSet (likePizza ∩ {w | w.val = 3}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [likePizza]

private lemma fd_prob_pizzaSpag_inter_3 :
    foodPrior.probOfSet (likePizza ∩ likeSpaghetti ∩ {w | w.val = 3}) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [likePizza, likeSpaghetti]

private lemma fd_cond_pizza_0 :
    foodPrior.condProbSet likePizza {w | w.val = 0} = 1/2 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizza_inter_0, fd_prob_pizza]
  ennreal_arith

private lemma fd_cond_pizzaSpag_0 :
    foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 0} = 1 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizzaSpag_inter_0, fd_prob_pizza_spag]
  ennreal_arith

private lemma fd_cond_pizza_1 :
    foodPrior.condProbSet likePizza {w | w.val = 1} = 1/2 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizza_inter_1, fd_prob_pizza]
  ennreal_arith

private lemma fd_cond_pizzaSpag_1 :
    foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 1} = 0 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizzaSpag_inter_1, fd_prob_pizza_spag]
  ennreal_arith

private lemma fd_cond_pizza_2 :
    foodPrior.condProbSet likePizza {w | w.val = 2} = 0 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizza_inter_2, fd_prob_pizza]
  ennreal_arith

private lemma fd_cond_pizzaSpag_2 :
    foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 2} = 0 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizzaSpag_inter_2, fd_prob_pizza_spag]
  ennreal_arith

private lemma fd_cond_pizza_3 :
    foodPrior.condProbSet likePizza {w | w.val = 3} = 0 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizza_inter_3, fd_prob_pizza]
  ennreal_arith

private lemma fd_cond_pizzaSpag_3 :
    foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 3} = 0 := by
  rw [PMF.condProbSet_eq_div,
      fd_prob_pizzaSpag_inter_3, fd_prob_pizza_spag]
  ennreal_arith

private lemma food_alt :
    Question.alt foodRQ =
    {p | p ∈ ([{w | w.val = 0}, {w | w.val = 1}, {w | w.val = 2}, {w | w.val = 3}]
              : List (Set (Fin 4)))} := by
  apply Question.alt_ofList_of_pairwise_disjoint_nonempty
  · decide
  · intro p₁ hp₁ p₂ hp₂ hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with rfl | rfl | rfl | rfl <;>
      rcases hp₂ with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | (rw [Set.disjoint_left]; intro w hw1 hw2;
         simp only [Set.mem_setOf_eq] at hw1 hw2; omega)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · intro h
      exact absurd (h ▸ (rfl : (0 : Fin 4).val = 0) :
        (0 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)
    · intro h
      exact absurd (h ▸ (rfl : (1 : Fin 4).val = 1) :
        (1 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)
    · intro h
      exact absurd (h ▸ (rfl : (2 : Fin 4).val = 2) :
        (2 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)
    · intro h
      exact absurd (h ▸ (rfl : (3 : Fin 4).val = 3) :
        (3 : Fin 4) ∈ (∅ : Set (Fin 4))) (by simp)

/-- Standard "too" is felicitous: "I like pizza. I like spaghetti, too."
- **Antecedent Condition**: P({w₀} | likePizza) = 1/2 > P({w₀}) = 1/4
- **Conjunction Condition**: P({w₀} | likePizza ∩ likeSpaghetti) = 1 > 1/2
- **Non-triviality**: π = likeSpaghetti contains w₂ ∉ {w₀}
- **Maximality**: only {w₀} is strengthened, and ANT ∩ {w₀} = {w₀} ⊆ π. -/
theorem pizza_spaghetti_too_felicitous : tooFelicitous foodCtx likeSpaghetti := by
  have hCtxAnt : foodCtx.antecedent = likePizza := rfl
  have hCtxRQ : foodCtx.resolvedQuestion = foodRQ := rfl
  have hCtxPrior : foodCtx.prior = foodPrior := rfl
  have hAltMem0 : ({w : Fin 4 | w.val = 0}) ∈ Question.alt foodRQ := by
    rw [food_alt]; exact List.mem_cons_self
  refine ⟨?ant, ⟨?conjA, ?conjS⟩, ?nontrv, ?max⟩
  · show probAnswersS foodCtx.antecedent foodCtx.resolvedQuestion foodCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨{w | w.val = 0}, hAltMem0, ?_⟩
    have h : foodPrior.condProbSet likePizza {w | w.val = 0} >
             foodPrior.probOfSet {w | w.val = 0} := by
      rw [fd_cond_pizza_0, fd_prob_0]; ennreal_arith
    convert h
  · show probAnswersS (foodCtx.antecedent ∩ likeSpaghetti)
         foodCtx.resolvedQuestion foodCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨{w | w.val = 0}, hAltMem0, ?_⟩
    have h : foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 0} >
             foodPrior.probOfSet {w | w.val = 0} := by
      rw [fd_cond_pizzaSpag_0, fd_prob_0]; ennreal_arith
    convert h
  · show someResolutionStrengthenedS foodCtx.antecedent likeSpaghetti
         foodCtx.resolvedQuestion foodCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨{w | w.val = 0}, hAltMem0, ?_⟩
    have h : foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 0} >
             foodPrior.condProbSet likePizza {w | w.val = 0} := by
      rw [fd_cond_pizzaSpag_0, fd_cond_pizza_0]; ennreal_arith
    convert h
  · show nonTrivialityCondition foodCtx likeSpaghetti
    unfold nonTrivialityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨{w | w.val = 0}, hAltMem0, ?_, ?_⟩
    · intro hsub
      have h2 : (2 : Fin 4) ∈ likeSpaghetti := Or.inr rfl
      exact absurd (hsub h2) (by decide)
    · have h : foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 0} >
               foodPrior.condProbSet likePizza {w | w.val = 0} := by
        rw [fd_cond_pizzaSpag_0, fd_cond_pizza_0]; ennreal_arith
      convert h
  · show maximalityCondition foodCtx likeSpaghetti
    unfold maximalityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro a haAlt hStr w _ _ hwA
    rw [food_alt] at haAlt
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at haAlt
    rcases haAlt with rfl | rfl | rfl | rfl
    · have : w = 0 := Fin.ext (hwA : w.val = 0)
      rw [this]; exact Or.inl rfl
    · exfalso
      have hno : ¬ (foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 1} >
                    foodPrior.condProbSet likePizza {w | w.val = 1}) := by
        rw [fd_cond_pizzaSpag_1, fd_cond_pizza_1]; ennreal_arith
      exact hno (by convert hStr)
    · exfalso
      have hno : ¬ (foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 2} >
                    foodPrior.condProbSet likePizza {w | w.val = 2}) := by
        rw [fd_cond_pizzaSpag_2, fd_cond_pizza_2]; ennreal_arith
      exact hno (by convert hStr)
    · exfalso
      have hno : ¬ (foodPrior.condProbSet (likePizza ∩ likeSpaghetti) {w | w.val = 3} >
                    foodPrior.condProbSet likePizza {w | w.val = 3}) := by
        rw [fd_cond_pizzaSpag_3, fd_cond_pizza_3]; ennreal_arith
      exact hno (by convert hStr)

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
(polar: does Bailey play?). -/
def averyPlays : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1 ∨ w.val = 2}
def baileyPlaysCello : Set (Fin 4) := {w | w.val = 0}
def baileyPlays : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1}

noncomputable def instrumentPrior : Prior (Fin 4) :=
  PMF.ofFintype (fun _ => 1/4)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

noncomputable def instrumentCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Core.Question.polar baileyPlays
  , antecedent := averyPlays
  , prior := instrumentPrior }

instance instAveryPlaysDec : DecidablePred (· ∈ averyPlays) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1 ∨ w.val = 2))
instance instBaileyPlaysCelloDec : DecidablePred (· ∈ baileyPlaysCello) := fun w =>
  inferInstanceAs (Decidable (w.val = 0))
instance instBaileyPlaysDec : DecidablePred (· ∈ baileyPlays) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))

private lemma baileyPlays_ne_empty : baileyPlays ≠ ∅ := by
  intro h; exact (h ▸ (Or.inl rfl) : (0 : Fin 4) ∈ (∅ : Set (Fin 4)))

private lemma baileyPlays_ne_univ : baileyPlays ≠ Set.univ := by
  intro h
  exact absurd (h ▸ Set.mem_univ (2 : Fin 4) : (2 : Fin 4) ∈ baileyPlays) (by decide)

private lemma instr_prob_avery : instrumentPrior.probOfSet averyPlays = 3/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [instrumentPrior, averyPlays]; ennreal_arith

private lemma instr_prob_avery_inter_bplays :
    instrumentPrior.probOfSet (averyPlays ∩ baileyPlays) = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [instrumentPrior, averyPlays, baileyPlays]; ennreal_arith

private lemma instr_prob_avery_cello :
    instrumentPrior.probOfSet (averyPlays ∩ baileyPlaysCello) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [instrumentPrior, averyPlays, baileyPlaysCello]

private lemma instr_prob_avery_cello_inter_bplays :
    instrumentPrior.probOfSet (averyPlays ∩ baileyPlaysCello ∩ baileyPlays) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [instrumentPrior, averyPlays, baileyPlaysCello, baileyPlays]

private lemma instr_cond_avery_cello_bplays :
    instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays = 1 := by
  rw [PMF.condProbSet_eq_div,
      instr_prob_avery_cello_inter_bplays, instr_prob_avery_cello]
  ennreal_arith

/-- "Avery plays an instrument. #Bailey plays the cello, too." is infelicitous.
Maximality (Def. 64c.ii) fails: the strengthened resolution is `baileyPlays`
({w₀, w₁}); world `w₁ ∈ averyPlays ∩ baileyPlays` has positive prior but
`w₁ ∉ baileyPlaysCello`, so prejacent does not capture all witnesses. -/
theorem cello_too_infelicitous : ¬ tooFelicitous instrumentCtx baileyPlaysCello := by
  have hCtxAnt : instrumentCtx.antecedent = averyPlays := rfl
  have hCtxRQ : instrumentCtx.resolvedQuestion = Question.polar baileyPlays := rfl
  have hCtxPrior : instrumentCtx.prior = instrumentPrior := rfl
  intro hFel
  obtain ⟨_, _, _, hMax⟩ := hFel
  have hMax' : maximalityCondition instrumentCtx baileyPlaysCello := hMax
  unfold maximalityCondition at hMax'
  rw [hCtxAnt, hCtxRQ, hCtxPrior] at hMax'
  have hAltMem : baileyPlays ∈ Question.alt (Question.polar baileyPlays) := by
    rw [Question.alt_polar_of_nontrivial baileyPlays_ne_empty baileyPlays_ne_univ]
    exact Set.mem_insert _ _
  have hStr : instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays >
              instrumentPrior.condProbSet averyPlays baileyPlays := by
    rw [instr_cond_avery_cello_bplays,
        PMF.condProbSet_eq_div,
        instr_prob_avery, instr_prob_avery_inter_bplays]
    ennreal_arith
  have h1in : (1 : Fin 4) ∈ averyPlays := Or.inr (Or.inl rfl)
  have h1bp : (1 : Fin 4) ∈ baileyPlays := Or.inr rfl
  have hPos : instrumentPrior 1 > 0 := by
    simp [instrumentPrior, PMF.ofFintype_apply]
  have h1bpc : (1 : Fin 4) ∈ baileyPlaysCello := by
    refine hMax' baileyPlays hAltMem ?_ 1 hPos h1in h1bp
    convert hStr
  exact absurd h1bpc (by decide)

-- § Cross-Product Question (ex. 13/40/75) — infelicitous: Conjunction Condition failure

/-- 4-world model for the cross-product question scenario.

| World | Avery Eats  | Bailey Eats  |
|-------|------------|--------------|
| w₀    | pizza      | pizza        |
| w₁    | pizza      | spaghetti    |
| w₂    | spaghetti  | pizza        |
| w₃    | spaghetti  | spaghetti    |

Prior: uniform 1/4. ANT = "Avery ate pizza", π = "Bailey ate spaghetti". -/
def averyPizzaCP : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1}
def baileySpaghetti : Set (Fin 4) := {w | w.val = 1 ∨ w.val = 3}

noncomputable def crossPrior : Prior (Fin 4) :=
  PMF.ofFintype (fun _ => 1/4)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

/-- RQ = "What did Avery eat?" (polar: did Avery eat pizza?). -/
noncomputable def crossCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := Core.Question.polar averyPizzaCP
  , antecedent := averyPizzaCP
  , prior := crossPrior }

instance instAveryPizzaCPDec : DecidablePred (· ∈ averyPizzaCP) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance instBaileySpaghettiDec : DecidablePred (· ∈ baileySpaghetti) := fun w =>
  inferInstanceAs (Decidable (w.val = 1 ∨ w.val = 3))

private lemma averyPizzaCP_ne_empty : averyPizzaCP ≠ ∅ := by
  intro h; exact (h ▸ (Or.inl rfl) : (0 : Fin 4) ∈ (∅ : Set (Fin 4)))

private lemma averyPizzaCP_ne_univ : averyPizzaCP ≠ Set.univ := by
  intro h
  exact absurd (h ▸ Set.mem_univ (2 : Fin 4) : (2 : Fin 4) ∈ averyPizzaCP) (by decide)

private lemma cross_prob_apc : crossPrior.probOfSet averyPizzaCP = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [crossPrior, averyPizzaCP]; ennreal_arith

private lemma cross_prob_apc_inter_bs :
    crossPrior.probOfSet (averyPizzaCP ∩ baileySpaghetti) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [crossPrior, averyPizzaCP, baileySpaghetti]

private lemma cross_prob_apc_inter_bs_inter_apc :
    crossPrior.probOfSet (averyPizzaCP ∩ baileySpaghetti ∩ averyPizzaCP) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [crossPrior, averyPizzaCP, baileySpaghetti]

private lemma cross_prob_apc_inter_bs_inter_apcC :
    crossPrior.probOfSet (averyPizzaCP ∩ baileySpaghetti ∩ averyPizzaCPᶜ) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [averyPizzaCP, baileySpaghetti, Set.mem_inter_iff]

private lemma cross_prob_apc_inter_apc :
    crossPrior.probOfSet (averyPizzaCP ∩ averyPizzaCP) = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [crossPrior, averyPizzaCP]; ennreal_arith

private lemma cross_prob_apc_inter_apcC :
    crossPrior.probOfSet (averyPizzaCP ∩ averyPizzaCPᶜ) = 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [averyPizzaCP]

private lemma cross_cond_apc_apc :
    crossPrior.condProbSet averyPizzaCP averyPizzaCP = 1 := by
  rw [PMF.condProbSet_eq_div, cross_prob_apc_inter_apc, cross_prob_apc]
  ennreal_arith

private lemma cross_cond_apc_apcC :
    crossPrior.condProbSet averyPizzaCP averyPizzaCPᶜ = 0 := by
  rw [PMF.condProbSet_eq_div, cross_prob_apc_inter_apcC, cross_prob_apc]
  ennreal_arith

private lemma cross_cond_apcbs_apc :
    crossPrior.condProbSet (averyPizzaCP ∩ baileySpaghetti) averyPizzaCP = 1 := by
  rw [PMF.condProbSet_eq_div,
      cross_prob_apc_inter_bs_inter_apc, cross_prob_apc_inter_bs]
  ennreal_arith

private lemma cross_cond_apcbs_apcC :
    crossPrior.condProbSet (averyPizzaCP ∩ baileySpaghetti) averyPizzaCPᶜ = 0 := by
  rw [PMF.condProbSet_eq_div,
      cross_prob_apc_inter_bs_inter_apcC, cross_prob_apc_inter_bs]
  ennreal_arith

/-- "Avery ate pizza. #Bailey ate spaghetti, too." is infelicitous.
Conjunction Condition (Def. 64b, strengthening half) fails: no resolution
of the polar question is strengthened by adding `baileySpaghetti` to
`averyPizzaCP`. For `averyPizzaCP` itself the conditional probability
stays at 1; for its complement it stays at 0. -/
theorem cross_product_too_infelicitous :
    ¬ tooFelicitous crossCtx baileySpaghetti := by
  have hCtxAnt : crossCtx.antecedent = averyPizzaCP := rfl
  have hCtxRQ : crossCtx.resolvedQuestion = Question.polar averyPizzaCP := rfl
  have hCtxPrior : crossCtx.prior = crossPrior := rfl
  intro hFel
  obtain ⟨_, ⟨_, hStr⟩, _, _⟩ := hFel
  have hStr' : someResolutionStrengthenedS crossCtx.antecedent baileySpaghetti
                 crossCtx.resolvedQuestion crossCtx.prior := hStr
  unfold someResolutionStrengthenedS at hStr'
  rw [hCtxAnt, hCtxRQ, hCtxPrior] at hStr'
  obtain ⟨a, haAlt, hgt⟩ := hStr'
  rw [Question.alt_polar_of_nontrivial averyPizzaCP_ne_empty averyPizzaCP_ne_univ] at haAlt
  rcases haAlt with rfl | haAlt
  · have hno : ¬ (crossPrior.condProbSet (averyPizzaCP ∩ baileySpaghetti) averyPizzaCP >
                  crossPrior.condProbSet averyPizzaCP averyPizzaCP) := by
      rw [cross_cond_apcbs_apc, cross_cond_apc_apc]; ennreal_arith
    exact absurd (by convert hgt) hno
  · rw [Set.mem_singleton_iff] at haAlt
    subst haAlt
    have hno : ¬ (crossPrior.condProbSet (averyPizzaCP ∩ baileySpaghetti) averyPizzaCPᶜ >
                  crossPrior.condProbSet averyPizzaCP averyPizzaCPᶜ) := by
      rw [cross_cond_apcbs_apcC, cross_cond_apc_apcC]; ennreal_arith
    exact absurd (by convert hgt) hno

end Verification

end Thomas2026
