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

/-- Worked mention-some example from @cite{thomas-2026} §5.4 (ex. 68).
ANT = "Avery invited Bailey AND Cameron"; π = "Avery invited Dana".
Distinct from `averyInvited` (ex. 2) which uses just Bailey + Cameron.
This is the felicity proof Thomas walks through step-by-step in PDF
lines 1750-1880, verified in `averyInvited_too_felicitous` below. -/
def averyInvitedDana : AdditiveParticleDatum :=
  { sentence :=
      "Q: Who are some people Avery invited?\n" ++
      "A: She invited Bailey and Cameron.\n" ++
      "B: She invited Dana, too."
  , antecedent := "Avery invited Bailey and Cameron"
  , prejacent := "Avery invited Dana"
  , particle := "too"
  , resolvedQuestion := some "Who are some people Avery invited?"
  , felicity := .ok
  , useType := .standard
  , notes :=
      "Mention-some additive use. Resolution `RQ|_{ANT∩π}` = " ++
      "|Avery invited Bailey AND Cameron AND Dana|; the conjunction of " ++
      "ANT and π evidences this resolution maximally."
  , source := "Thomas (2026), ex. 68 (worked example, PDF pp. 33-34)"
  }

/-- Standard focus-alternative examples. -/
def standardExamples : List AdditiveParticleDatum :=
  [pizzaSpaghetti, averyInvited, averyInvitedDana]

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

private lemma hotel_AntPi_eq : roomAvail ∩ fancyH = goodHotel := by
  ext w
  simp only [roomAvail, fancyH, goodHotel, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0 | h0, h0' | h0'⟩ <;> first | exact h0 | exact h0' | omega
  · intro h0; exact ⟨Or.inl h0, Or.inl h0⟩

/-- Characterisation: the unique conditional answer for `R = roomAvail ∩ fancyH`
in the polar(goodHotel) question is `T = {goodHotel}`. -/
private lemma hotel_cond_answer_eq (T : Set (Set (Fin 4)))
    (hT : Semantics.Questions.ProbabilisticAnswerhood.IsConditionalAnswer
      (roomAvail ∩ fancyH) (Question.polar goodHotel) hotelPrior T) :
    T = {goodHotel} := by
  obtain ⟨⟨hNeT, _hFinT, hAltT, hStr⟩, _⟩ := hT
  have hAltSet : Question.alt (Question.polar goodHotel) =
      insert goodHotel {goodHotelᶜ} :=
    Question.alt_polar_of_nontrivial goodHotel_ne_empty goodHotel_ne_univ
  -- Helper: if A = goodHotelᶜ ∈ T, derive contradiction from hStr
  have h_no_GHC : goodHotelᶜ ∉ T := by
    intro hGHCT
    have h_sub : ⋂₀ T ⊆ goodHotelᶜ := Set.sInter_subset_of_mem hGHCT
    have h_inter_empty : (roomAvail ∩ fancyH) ∩ ⋂₀ T = ∅ := by
      rw [hotel_AntPi_eq]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hgh, hint⟩
      exact (h_sub hint) hgh
    have h_cond_zero :
        hotelPrior.condProbSet (roomAvail ∩ fancyH) (⋂₀ T) = 0 := by
      rw [PMF.condProbSet_eq_div, h_inter_empty, PMF.probOfSet_empty,
          ENNReal.zero_div]
    have h_cond_zero' :
        hotelPrior.condProbSet (roomAvail ∩ fancyH) (⋂₀ T) = 0 := by
      convert h_cond_zero
    rw [h_cond_zero'] at hStr
    exact absurd hStr (not_lt.mpr (zero_le _))
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA⟩ := hNeT
    have hA_alt : A ∈ (insert goodHotel {goodHotelᶜ} : Set (Set (Fin 4))) := by
      rw [← hAltSet]; exact hAltT A hA
    rcases hA_alt with rfl | hAc
    · exact hA
    · rw [Set.mem_singleton_iff] at hAc; subst hAc
      exact absurd hA h_no_GHC
  · intro y hy
    have hy_alt : y ∈ (insert goodHotel {goodHotelᶜ} : Set (Set (Fin 4))) := by
      rw [← hAltSet]; exact hAltT y hy
    rcases hy_alt with rfl | hyc
    · rfl
    · rw [Set.mem_singleton_iff] at hyc; subst hyc
      exact absurd hy h_no_GHC

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
    intro T hT
    rw [hotel_cond_answer_eq T hT, Set.sInter_singleton]
    -- Goal: ¬ fancyH ⊆ goodHotel. fancyH contains w₂ ∉ goodHotel.
    intro hsub
    exact absurd (hsub (Or.inr rfl : (2 : Fin 4) ∈ fancyH)) (by decide)
  · show maximalityCondition hotelCtx fancyH
    unfold maximalityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro T hT S hSS hPos
    rw [hotel_cond_answer_eq T hT, Set.sInter_singleton]
    have h_gh_sub_AntPi : goodHotel ⊆ roomAvail ∩ fancyH := by rw [hotel_AntPi_eq]
    have h_gh_sub_AntS : goodHotel ⊆ roomAvail ∩ S :=
      h_gh_sub_AntPi.trans (Set.inter_subset_inter_right _ hSS.le)
    have h_pos_gh : hotelPrior.probOfSet goodHotel > 0 := by
      rw [hotel_prob_good]; ennreal_arith
    classical
    have h_lt := PMF.condProbSet_strict_anti_of_probOfSet_lt hotelPrior goodHotel
      (roomAvail ∩ fancyH) (roomAvail ∩ S) h_gh_sub_AntPi h_gh_sub_AntS h_pos_gh hPos
    convert h_lt

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

private lemma em_AntPi_eq :
    happyE ∩ ecstaticE = ({w | w.val = 0} : Set (Fin 4)) := by
  ext w
  simp only [happyE, ecstaticE, Set.mem_inter_iff, Set.mem_setOf_eq]
  omega

/-- T = {{w | w.val = 0}} (the singleton ecstatic alt) is a conditional answer
for `R = happyE ∩ ecstaticE = {w₀}` in `emotionRQ`. -/
private lemma em_isCondAns :
    Semantics.Questions.ProbabilisticAnswerhood.IsConditionalAnswer
      (happyE ∩ ecstaticE) emotionRQ emotionPrior
      ({({w : Fin 4 | w.val = 0} : Set (Fin 4))} : Set (Set (Fin 4))) := by
  refine ⟨⟨Set.singleton_nonempty _, Set.finite_singleton _, ?alts, ?strengthen⟩,
          ?max⟩
  case alts =>
    intro A hA
    rw [Set.mem_singleton_iff] at hA; subst hA
    rw [emotion_alt]; simp [List.mem_cons]
  case strengthen =>
    rw [Set.sInter_singleton]
    -- condProbSet (happyE ∩ ecstaticE) {w | w.val = 0} = 1 (since (h∩e) = {w₀} ⊆ {w₀}).
    -- probOfSet {w | w.val = 0} = 1/4.
    have h_cond_eq_one :
        emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 0} = 1 := by
      rw [PMF.condProbSet_eq_div, em_AntPi_eq, Set.inter_self]
      have h_prob :
          emotionPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
        rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior]
      rw [h_prob]; ennreal_arith
    have h_cond_eq_one' :
        emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 0} = 1 := by
      convert h_cond_eq_one
    rw [h_cond_eq_one']
    -- Goal: 1 > probOfSet {w | w.val = 0} = 1/4
    have h_prob :
        emotionPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
      rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior]
    have h_prob' : emotionPrior.probOfSet {w | w.val = 0} = 1/4 := by convert h_prob
    rw [h_prob']; ennreal_arith
  case max =>
    -- For all T' ⊆ alt with ¬ {{w₀}} ⊆ T' (i.e., {w₀} ∉ T'),
    -- impactRatio of {{w₀}} (= 4) > impactRatio of T'.
    -- alt = {{w₀}, {w₁}, {w₂∨w₃}}; non-{w₀}-containing T' ⊆ {{w₁}, {w₂∨w₃}}.
    -- For each such T', condProbSet ({w₀}) (⋂T') = 0 (R = {w₀} disjoint from
    -- any subset of {{w₁}, {w₂∨w₃}}'s intersection).
    intro T' _hNeT' _hFinT' hAltT' hNotSub
    rw [Set.sInter_singleton]
    -- Show: condProbSet R {w₀} / probOfSet {w₀} > condProbSet R (⋂T') / probOfSet (⋂T')
    -- LHS = 1 / (1/4) = 4. RHS: need condProbSet R (⋂T') = 0.
    have h_no_zero : ({w : Fin 4 | w.val = 0} : Set (Fin 4)) ∉ T' := by
      intro h; exact hNotSub (Set.singleton_subset_iff.mpr h)
    have h_w0_not_in_inter : (0 : Fin 4) ∉ ⋂₀ T' := by
      intro h_in
      -- 0 ∈ ⋂₀T' means 0 ∈ A for all A ∈ T'. But each A ∈ alt = 3 sets, only {w₀} contains 0.
      -- So all A ∈ T' equal {w₀}. By Nonempty, T' = {{w₀}}, contradicting h_no_zero.
      obtain ⟨A, hA⟩ := _hNeT'
      have h0A : (0 : Fin 4) ∈ A := Set.mem_sInter.mp h_in A hA
      have hA_alt := hAltT' A hA
      rw [emotion_alt] at hA_alt
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hA_alt
      rcases hA_alt with rfl | rfl | rfl
      · exact h_no_zero hA
      · exact absurd (h0A : (0 : Fin 4).val = 1) (by decide)
      · rcases (h0A : (0 : Fin 4).val = 2 ∨ (0 : Fin 4).val = 3) with h | h <;> exact absurd h (by decide)
    have h_inter_empty : (happyE ∩ ecstaticE) ∩ ⋂₀ T' = ∅ := by
      rw [em_AntPi_eq]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hw0, hwint⟩
      have : w = 0 := Fin.ext hw0
      subst this; exact h_w0_not_in_inter hwint
    have h_cond_R_T' : emotionPrior.condProbSet (happyE ∩ ecstaticE) (⋂₀ T') = 0 := by
      rw [PMF.condProbSet_eq_div, h_inter_empty, PMF.probOfSet_empty, ENNReal.zero_div]
    -- impactRatios
    unfold PMF.impactRatio
    have h_cond_R_W0 :
        emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 0} = 1 := by
      rw [PMF.condProbSet_eq_div, em_AntPi_eq, Set.inter_self]
      have h_prob :
          emotionPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
        rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior]
      rw [h_prob]; ennreal_arith
    have h_prob_W0 :
        emotionPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
      rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [emotionPrior]
    have hcr : emotionPrior.condProbSet (happyE ∩ ecstaticE) {w | w.val = 0} = 1 := by
      convert h_cond_R_W0
    have hpr : emotionPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
      convert h_prob_W0
    have h_cond_R_T'_typed :
        emotionPrior.condProbSet (happyE ∩ ecstaticE) (⋂₀ T') = 0 := by
      convert h_cond_R_T'
    rw [hcr, hpr, h_cond_R_T'_typed, ENNReal.zero_div]
    ennreal_arith

/-- "Sam is happy. #He's ecstatic, too." is infelicitous.
Def. 64c.i (non-triviality) fails under the literal form: take
`T = {{w | w.val = 0}}`, the unique conditional answer. Then
`⋂₀T = {w₀} = ecstaticE = ⟦π⟧`, so π ⊆ ⋂₀T, contradicting the
nonTrivialityCondition's requirement π ⊄ ⋂₀T. -/
theorem ecstatic_too_infelicitous : ¬ tooFelicitous emotionCtx ecstaticE := by
  have hCtxAnt : emotionCtx.antecedent = happyE := rfl
  have hCtxRQ : emotionCtx.resolvedQuestion = emotionRQ := rfl
  have hCtxPrior : emotionCtx.prior = emotionPrior := rfl
  intro hFel
  obtain ⟨_, _, hNT, _⟩ := hFel
  unfold nonTrivialityCondition at hNT
  rw [hCtxAnt, hCtxRQ, hCtxPrior] at hNT
  -- Apply hNT to T = {{w | w.val = 0}} (the conditional answer)
  have h_no_sub :=
    hNT ({({w : Fin 4 | w.val = 0} : Set (Fin 4))} : Set (Set (Fin 4))) em_isCondAns
  -- h_no_sub : ¬ ecstaticE ⊆ ⋂₀ {{w | w.val = 0}}
  rw [Set.sInter_singleton] at h_no_sub
  -- ecstaticE = {w | w.val = 0}, so ecstaticE ⊆ {w | w.val = 0} trivially
  exact h_no_sub (fun _ h => h)

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

private lemma food_AntPi_eq :
    likePizza ∩ likeSpaghetti = ({w | w.val = 0} : Set (Fin 4)) := by
  ext w
  simp only [likePizza, likeSpaghetti, Set.mem_inter_iff, Set.mem_setOf_eq]
  omega

/-- Characterisation: the unique conditional answer for `R = likePizza ∩ likeSpaghetti`
in the 4-cell partition `foodRQ` is `T = {{w | w.val = 0}}`. -/
private lemma food_cond_answer_eq (T : Set (Set (Fin 4)))
    (hT : Semantics.Questions.ProbabilisticAnswerhood.IsConditionalAnswer
      (likePizza ∩ likeSpaghetti) foodRQ foodPrior T) :
    T = ({({w : Fin 4 | w.val = 0} : Set (Fin 4))} : Set (Set (Fin 4))) := by
  obtain ⟨⟨hNeT, _hFinT, hAltT, hStr⟩, _⟩ := hT
  -- Step 1: 0 ∈ ⋂₀T
  have h_w0_in_inter : (0 : Fin 4) ∈ ⋂₀ T := by
    by_contra h0
    have h_inter_empty : (likePizza ∩ likeSpaghetti) ∩ ⋂₀ T = ∅ := by
      rw [food_AntPi_eq]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hw0, hwint⟩
      have : w = 0 := Fin.ext hw0
      subst this
      exact h0 hwint
    have h_cond_zero :
        foodPrior.condProbSet (likePizza ∩ likeSpaghetti) (⋂₀ T) = 0 := by
      rw [PMF.condProbSet_eq_div, h_inter_empty, PMF.probOfSet_empty, ENNReal.zero_div]
    have h_cond_zero' :
        foodPrior.condProbSet (likePizza ∩ likeSpaghetti) (⋂₀ T) = 0 := by
      convert h_cond_zero
    rw [h_cond_zero'] at hStr
    exact absurd hStr (not_lt.mpr (zero_le _))
  -- Step 2: each A ∈ T equals {w | w.val = 0}
  have h_T_subset : ∀ A ∈ T, A = ({w : Fin 4 | w.val = 0} : Set (Fin 4)) := by
    intro A hA
    have hA_alt := hAltT A hA
    rw [food_alt] at hA_alt
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hA_alt
    have h0_in_A : (0 : Fin 4) ∈ A := Set.mem_sInter.mp h_w0_in_inter A hA
    rcases hA_alt with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (h0_in_A : (0 : Fin 4).val = 1) (by decide)
    · exact absurd (h0_in_A : (0 : Fin 4).val = 2) (by decide)
    · exact absurd (h0_in_A : (0 : Fin 4).val = 3) (by decide)
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, h_T_subset⟩
  obtain ⟨A, hA⟩ := hNeT
  rwa [h_T_subset A hA] at hA

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
    intro T hT
    rw [food_cond_answer_eq T hT, Set.sInter_singleton]
    -- Goal: ¬ likeSpaghetti ⊆ {w | w.val = 0}. likeSpaghetti contains w₂.
    intro hsub
    have h2 : (2 : Fin 4) ∈ likeSpaghetti := Or.inr rfl
    exact absurd (hsub h2) (by decide)
  · show maximalityCondition foodCtx likeSpaghetti
    unfold maximalityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro T hT S hSS hPos
    rw [food_cond_answer_eq T hT, Set.sInter_singleton]
    classical
    have hA_sub_R : ({w : Fin 4 | w.val = 0} : Set (Fin 4)) ⊆ likePizza ∩ likeSpaghetti := by
      rw [food_AntPi_eq]
    have hA_sub_R' : ({w : Fin 4 | w.val = 0} : Set (Fin 4)) ⊆ likePizza ∩ S :=
      hA_sub_R.trans (Set.inter_subset_inter_right _ hSS.le)
    have h_pos : foodPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) > 0 := by
      rw [fd_prob_0]; ennreal_arith
    have h_lt := PMF.condProbSet_strict_anti_of_probOfSet_lt foodPrior _
      (likePizza ∩ likeSpaghetti) (likePizza ∩ S) hA_sub_R hA_sub_R' h_pos hPos
    convert h_lt

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

private lemma instr_prob_baileyPlays :
    instrumentPrior.probOfSet baileyPlays = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [instrumentPrior, baileyPlays]; ennreal_arith

private lemma instr_prob_baileyPlaysCompl :
    instrumentPrior.probOfSet baileyPlaysᶜ = 1/2 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [instrumentPrior, baileyPlays, Set.mem_compl_iff, Set.mem_setOf_eq]
  ennreal_arith

private lemma instr_subset_AntPi_BPlays :
    averyPlays ∩ baileyPlaysCello ⊆ baileyPlays := by
  intro w hw
  exact Or.inl hw.2

private lemma instr_subset_AntS_BPlays :
    averyPlays ∩ baileyPlays ⊆ baileyPlays := Set.inter_subset_right

private lemma instr_inter_AntPi_BPlaysC_empty :
    (averyPlays ∩ baileyPlaysCello) ∩ baileyPlaysᶜ = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨⟨_, hwc⟩, hwn⟩
  exact hwn (Or.inl hwc)

/-- "Avery plays an instrument. #Bailey plays the cello, too." is infelicitous.
Maximality (Def. 64c.ii) fails under the literal weakening-comparison form:
take `S = baileyPlays ⊋ baileyPlaysCello`. Then
`P(averyPlays ∩ baileyPlays) = 1/2 > 1/4 = P(averyPlays ∩ baileyPlaysCello)`
satisfies the implicit non-trivial-weakening precondition. The unique
conditional answer is `T = {baileyPlays}` (singleton, since
`alt(polar baileyPlays)` has only `baileyPlays` and `baileyPlaysᶜ`,
and only `{baileyPlays}` is impact-ratio-maximal at `R = {w₀}`).
With `⋂₀ T = baileyPlays`, both
`P(baileyPlays | averyPlays ∩ baileyPlaysCello) = 1` and
`P(baileyPlays | averyPlays ∩ baileyPlays) = 1` — so the strict
inequality required by Def. 64c.ii fails (1 ≯ 1). -/
theorem cello_too_infelicitous : ¬ tooFelicitous instrumentCtx baileyPlaysCello := by
  intro hFel
  obtain ⟨_, _, _, hMax⟩ := hFel
  have hCtxAnt : instrumentCtx.antecedent = averyPlays := rfl
  have hCtxRQ : instrumentCtx.resolvedQuestion = Question.polar baileyPlays := rfl
  have hCtxPrior : instrumentCtx.prior = instrumentPrior := rfl
  have hAltSet : Question.alt (Question.polar baileyPlays) =
      insert baileyPlays {baileyPlaysᶜ} :=
    Question.alt_polar_of_nontrivial baileyPlays_ne_empty baileyPlays_ne_univ
  -- (a) Probabilities
  have h_prob_intP_pos :
      instrumentPrior.probOfSet (averyPlays ∩ baileyPlaysCello) > 0 := by
    rw [instr_prob_avery_cello]; ennreal_arith
  have hCondInt_eq_one :
      instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays = 1 := by
    rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr instr_subset_AntPi_BPlays]
    exact ENNReal.div_self h_prob_intP_pos.ne' (PMF.probOfSet_ne_top _ _)
  have hCondInt_BPC_eq_zero :
      instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlaysᶜ = 0 := by
    rw [PMF.condProbSet_eq_div, instr_inter_AntPi_BPlaysC_empty, PMF.probOfSet_empty,
        ENNReal.zero_div]
  -- (b) Build IsConditionalAnswer for {baileyPlays}
  have hCandidate :
      IsConditionalAnswerCandidate (averyPlays ∩ baileyPlaysCello)
        (Question.polar baileyPlays) instrumentPrior {baileyPlays} := by
    refine ⟨Set.singleton_nonempty _, Set.finite_singleton _, ?alts, ?strengthen⟩
    · intro A hA
      rw [Set.mem_singleton_iff] at hA; subst hA
      rw [hAltSet]; exact Set.mem_insert _ _
    · rw [Set.sInter_singleton]
      have h1 : instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays = 1 := by
        convert hCondInt_eq_one
      rw [h1, instr_prob_baileyPlays]
      ennreal_arith
  have hMax_T : ∀ T' : Set (Set (Fin 4)), T'.Nonempty → T'.Finite →
      (∀ A ∈ T', A ∈ Question.alt (Question.polar baileyPlays)) →
      ¬ {baileyPlays} ⊆ T' →
      PMF.impactRatio instrumentPrior (averyPlays ∩ baileyPlaysCello)
        (⋂₀ ({baileyPlays} : Set (Set (Fin 4)))) >
      PMF.impactRatio instrumentPrior (averyPlays ∩ baileyPlaysCello) (⋂₀ T') := by
    intro T' hNeT' _hFinT' hAltT' hNotSub
    have hSubAlt : T' ⊆ insert baileyPlays {baileyPlaysᶜ} := by
      intro A hA; rw [← hAltSet]; exact hAltT' A hA
    have hNotBP : baileyPlays ∉ T' :=
      fun h => hNotSub (Set.singleton_subset_iff.mpr h)
    have hT'eq : T' = {baileyPlaysᶜ} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · obtain ⟨x, hx⟩ := hNeT'
        have hxAlt := hSubAlt hx
        rcases hxAlt with rfl | hxc
        · exact absurd hx hNotBP
        · rwa [Set.mem_singleton_iff.mp hxc] at hx
      · intro y hy
        have hyAlt := hSubAlt hy
        rcases hyAlt with rfl | hyc
        · exact absurd hy hNotBP
        · exact Set.mem_singleton_iff.mp hyc
    rw [hT'eq, Set.sInter_singleton, Set.sInter_singleton]
    unfold PMF.impactRatio
    have h1 : instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays = 1 := by
      convert hCondInt_eq_one
    have h0 : instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlaysᶜ = 0 := by
      convert hCondInt_BPC_eq_zero
    rw [h1, h0, instr_prob_baileyPlays, instr_prob_baileyPlaysCompl]
    ennreal_arith
  have hT : IsConditionalAnswer (averyPlays ∩ baileyPlaysCello)
      (Question.polar baileyPlays) instrumentPrior {baileyPlays} := ⟨hCandidate, hMax_T⟩
  -- Construct the weakening witness
  have hSS : baileyPlaysCello ⊂ baileyPlays := by
    refine ⟨fun w hw => Or.inl hw, ?_⟩
    intro h
    have : (1 : Fin 4) ∈ baileyPlaysCello := h (Or.inr rfl : (1 : Fin 4) ∈ baileyPlays)
    exact absurd this (by decide)
  have hPos_increase :
      instrumentPrior.probOfSet (averyPlays ∩ baileyPlays) >
        instrumentPrior.probOfSet (averyPlays ∩ baileyPlaysCello) := by
    rw [instr_prob_avery_inter_bplays, instr_prob_avery_cello]; ennreal_arith
  -- Apply hMax
  have hMax' : maximalityCondition instrumentCtx baileyPlaysCello := hMax
  unfold maximalityCondition at hMax'
  rw [hCtxAnt, hCtxRQ, hCtxPrior] at hMax'
  have hM := hMax' {baileyPlays} hT baileyPlays hSS hPos_increase
  rw [Set.sInter_singleton] at hM
  -- RHS condProbSet (averyPlays ∩ baileyPlays) baileyPlays = 1
  have h_prob_AB_pos :
      instrumentPrior.probOfSet (averyPlays ∩ baileyPlays) > 0 := by
    rw [instr_prob_avery_inter_bplays]; ennreal_arith
  have hRHS_one :
      instrumentPrior.condProbSet (averyPlays ∩ baileyPlays) baileyPlays = 1 := by
    rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr instr_subset_AntS_BPlays]
    exact ENNReal.div_self h_prob_AB_pos.ne' (PMF.probOfSet_ne_top _ _)
  -- Bridge Classical vs structural Decidable instances on `hM` and conclude.
  have hLHS_one :
      instrumentPrior.condProbSet (averyPlays ∩ baileyPlaysCello) baileyPlays = 1 := by
    convert hCondInt_eq_one
  rw [hLHS_one, hRHS_one] at hM
  exact absurd hM (lt_irrefl _)

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

-- § Avery invited Bailey, Cameron; she invited Dana too (ex. 68)
-- — felicitous canonical additive use, mention-some

/-- 4-world model for the worked example (68) from @cite{thomas-2026}.

| World | Bailey | Cameron | Dana |
|-------|--------|---------|------|
| w₀    | ✓      | ✓       | ✓    |
| w₁    | ✓      | ✓       |      |
| w₂    | ✓      |         | ✓    |
| w₃    |        | ✓       | ✓    |

ANT = "Avery invited Bailey AND Cameron" = aiB ∩ aiC = {w₀, w₁}.
π = "Avery invited Dana" = aiD = {w₀, w₂, w₃}.
ANT ∩ π = {w₀} (Bailey AND Cameron AND Dana all invited).
RQ = mention-some "Who are some people Avery invited?" with alts |B|, |C|, |D|.
Uniform 1/4 prior. -/
def aiB : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1 ∨ w.val = 2}
def aiC : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 1 ∨ w.val = 3}
def aiD : Set (Fin 4) := {w | w.val = 0 ∨ w.val = 2 ∨ w.val = 3}

/-- "Who are some people Avery invited?" — mention-some question. -/
def averyInvitedRQ : Core.Question (Fin 4) :=
  Core.Question.ofList [aiB, aiC, aiD]

noncomputable def averyInvitedPrior : Prior (Fin 4) :=
  PMF.ofFintype (fun _ => 1/4)
    (by rw [Fin.sum_univ_four]; ennreal_arith)

noncomputable def averyInvitedCtx : AdditiveContext (Fin 4) :=
  { resolvedQuestion := averyInvitedRQ
  , antecedent := aiB ∩ aiC
  , prior := averyInvitedPrior }

instance instAiBDec : DecidablePred (· ∈ aiB) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1 ∨ w.val = 2))
instance instAiCDec : DecidablePred (· ∈ aiC) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1 ∨ w.val = 3))
instance instAiDDec : DecidablePred (· ∈ aiD) := fun w =>
  inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 2 ∨ w.val = 3))

private lemma ai_alt :
    Question.alt averyInvitedRQ =
    {p | p ∈ ([aiB, aiC, aiD] : List (Set (Fin 4)))} := by
  apply Question.alt_ofList_of_antichain_nonempty
  · decide
  · intro p₁ hp₁ p₂ hp₂ hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₁ hp₂
    rcases hp₁ with rfl | rfl | rfl
    · rcases hp₂ with rfl | rfl | rfl
      · exact absurd rfl hne
      · intro h
        have := h (show (2 : Fin 4) ∈ aiB from Or.inr (Or.inr rfl))
        simp [aiC] at this
      · intro h
        have := h (show (1 : Fin 4) ∈ aiB from Or.inr (Or.inl rfl))
        simp [aiD] at this
    · rcases hp₂ with rfl | rfl | rfl
      · intro h
        have := h (show (3 : Fin 4) ∈ aiC from Or.inr (Or.inr rfl))
        simp [aiB] at this
      · exact absurd rfl hne
      · intro h
        have := h (show (1 : Fin 4) ∈ aiC from Or.inr (Or.inl rfl))
        simp [aiD] at this
    · rcases hp₂ with rfl | rfl | rfl
      · intro h
        have := h (show (3 : Fin 4) ∈ aiD from Or.inr (Or.inr rfl))
        simp [aiB] at this
      · intro h
        have := h (show (2 : Fin 4) ∈ aiD from Or.inr (Or.inl rfl))
        simp [aiC] at this
      · exact absurd rfl hne
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · intro h
      have h0 : (0 : Fin 4) ∈ aiB := Or.inl rfl
      rw [h] at h0; exact h0
    · intro h
      have h0 : (0 : Fin 4) ∈ aiC := Or.inl rfl
      rw [h] at h0; exact h0
    · intro h
      have h0 : (0 : Fin 4) ∈ aiD := Or.inl rfl
      rw [h] at h0; exact h0

private lemma ai_AntPi_eq : aiB ∩ aiC ∩ aiD = ({w | w.val = 0} : Set (Fin 4)) := by
  ext w
  simp only [aiB, aiC, aiD, Set.mem_inter_iff, Set.mem_setOf_eq]
  omega

-- Probability helpers
private lemma ai_prob_aiB : averyInvitedPrior.probOfSet aiB = 3/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [averyInvitedPrior, aiB]; ennreal_arith

private lemma ai_prob_aiC : averyInvitedPrior.probOfSet aiC = 3/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [averyInvitedPrior, aiC]; ennreal_arith

private lemma ai_prob_aiD : averyInvitedPrior.probOfSet aiD = 3/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [averyInvitedPrior, aiD]; ennreal_arith

private lemma ai_prob_w0 :
    averyInvitedPrior.probOfSet ({w : Fin 4 | w.val = 0} : Set (Fin 4)) = 1/4 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_four]; simp [averyInvitedPrior]

private lemma ai_prob_AntPi :
    averyInvitedPrior.probOfSet (aiB ∩ aiC ∩ aiD) = 1/4 := by
  rw [ai_AntPi_eq, ai_prob_w0]

private lemma ai_AntPi_pos :
    averyInvitedPrior.probOfSet (aiB ∩ aiC ∩ aiD) > 0 := by
  rw [ai_prob_AntPi]; ennreal_arith

private lemma ai_AntPi_sub_aiB : aiB ∩ aiC ∩ aiD ⊆ aiB := fun _ hw => hw.1.1
private lemma ai_AntPi_sub_aiC : aiB ∩ aiC ∩ aiD ⊆ aiC := fun _ hw => hw.1.2
private lemma ai_AntPi_sub_aiD : aiB ∩ aiC ∩ aiD ⊆ aiD := fun _ hw => hw.2

private lemma ai_aiB_aiC_eq :
    aiB ∩ aiC = ({w | w.val = 0 ∨ w.val = 1} : Set (Fin 4)) := by
  ext w; simp only [aiB, aiC, Set.mem_inter_iff, Set.mem_setOf_eq]; omega

private lemma ai_aiB_aiD_eq :
    aiB ∩ aiD = ({w | w.val = 0 ∨ w.val = 2} : Set (Fin 4)) := by
  ext w; simp only [aiB, aiD, Set.mem_inter_iff, Set.mem_setOf_eq]; omega

private lemma ai_aiC_aiD_eq :
    aiC ∩ aiD = ({w | w.val = 0 ∨ w.val = 3} : Set (Fin 4)) := by
  ext w; simp only [aiC, aiD, Set.mem_inter_iff, Set.mem_setOf_eq]; omega

private lemma ai_prob_aiB_aiC : averyInvitedPrior.probOfSet (aiB ∩ aiC) = 1/2 := by
  rw [ai_aiB_aiC_eq, PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [averyInvitedPrior]; ennreal_arith

private lemma ai_pos_ANT : averyInvitedPrior.probOfSet (aiB ∩ aiC) > 0 := by
  rw [ai_prob_aiB_aiC]; ennreal_arith

private lemma ai_prob_aiB_aiD : averyInvitedPrior.probOfSet (aiB ∩ aiD) = 1/2 := by
  rw [ai_aiB_aiD_eq, PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [averyInvitedPrior]; ennreal_arith

private lemma ai_prob_aiC_aiD : averyInvitedPrior.probOfSet (aiC ∩ aiD) = 1/2 := by
  rw [ai_aiC_aiD_eq, PMF.probOfSet_apply, Fin.sum_univ_four]
  simp [averyInvitedPrior]; ennreal_arith

private lemma ai_pos_aiB_aiC : averyInvitedPrior.probOfSet (aiB ∩ aiC) > 0 := by
  rw [ai_prob_aiB_aiC]; ennreal_arith

private lemma ai_pos_aiB_aiD : averyInvitedPrior.probOfSet (aiB ∩ aiD) > 0 := by
  rw [ai_prob_aiB_aiD]; ennreal_arith

private lemma ai_pos_aiC_aiD : averyInvitedPrior.probOfSet (aiC ∩ aiD) > 0 := by
  rw [ai_prob_aiC_aiD]; ennreal_arith

private lemma ai_pos_aiB : averyInvitedPrior.probOfSet aiB > 0 := by
  rw [ai_prob_aiB]; ennreal_arith

private lemma ai_pos_aiC : averyInvitedPrior.probOfSet aiC > 0 := by
  rw [ai_prob_aiC]; ennreal_arith

private lemma ai_pos_aiD : averyInvitedPrior.probOfSet aiD > 0 := by
  rw [ai_prob_aiD]; ennreal_arith

/-- For each `X ∈ {aiB, aiC, aiD}`: `condProbSet AntPi X = 1` (since AntPi ⊆ X). -/
private lemma ai_cond_AntPi_alt_one (X : Set (Fin 4))
    (hX : X = aiB ∨ X = aiC ∨ X = aiD) :
    averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) X = 1 := by
  have h_sub : aiB ∩ aiC ∩ aiD ⊆ X := by
    rcases hX with rfl | rfl | rfl
    · exact ai_AntPi_sub_aiB
    · exact ai_AntPi_sub_aiC
    · exact ai_AntPi_sub_aiD
  rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr h_sub]
  exact ENNReal.div_self ai_AntPi_pos.ne' (PMF.probOfSet_ne_top _ _)

/-- For each pair `X ≠ Y` in `{aiB, aiC, aiD}`: `condProbSet AntPi (X ∩ Y) = 1`. -/
private lemma ai_cond_AntPi_pair_one (X Y : Set (Fin 4))
    (hX : X = aiB ∨ X = aiC ∨ X = aiD)
    (hY : Y = aiB ∨ Y = aiC ∨ Y = aiD) :
    averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) (X ∩ Y) = 1 := by
  have h_sub_X : aiB ∩ aiC ∩ aiD ⊆ X := by
    rcases hX with rfl | rfl | rfl
    · exact ai_AntPi_sub_aiB
    · exact ai_AntPi_sub_aiC
    · exact ai_AntPi_sub_aiD
  have h_sub_Y : aiB ∩ aiC ∩ aiD ⊆ Y := by
    rcases hY with rfl | rfl | rfl
    · exact ai_AntPi_sub_aiB
    · exact ai_AntPi_sub_aiC
    · exact ai_AntPi_sub_aiD
  have h_sub : aiB ∩ aiC ∩ aiD ⊆ X ∩ Y := Set.subset_inter h_sub_X h_sub_Y
  rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr h_sub]
  exact ENNReal.div_self ai_AntPi_pos.ne' (PMF.probOfSet_ne_top _ _)

/-- All three alts contain `w₀`. -/
private lemma ai_w0_in_all (X : Set (Fin 4))
    (hX : X = aiB ∨ X = aiC ∨ X = aiD) : (0 : Fin 4) ∈ X := by
  rcases hX with rfl | rfl | rfl <;> exact Or.inl rfl

-- Distinctness lemmas
private lemma ai_aiB_ne_aiC : aiB ≠ aiC := fun h => by
  have h2 : (2 : Fin 4) ∈ aiB := Or.inr (Or.inr rfl)
  rw [h] at h2; simp [aiC] at h2

private lemma ai_aiB_ne_aiD : aiB ≠ aiD := fun h => by
  have h1 : (1 : Fin 4) ∈ aiB := Or.inr (Or.inl rfl)
  rw [h] at h1; simp [aiD] at h1

private lemma ai_aiC_ne_aiD : aiC ≠ aiD := fun h => by
  have h1 : (1 : Fin 4) ∈ aiC := Or.inr (Or.inl rfl)
  rw [h] at h1; simp [aiD] at h1

/-- All singleton impact ratios equal 4/3 (model symmetry). -/
private lemma ai_impactRatio_singleton (X : Set (Fin 4))
    (hX : X = aiB ∨ X = aiC ∨ X = aiD) :
    PMF.impactRatio averyInvitedPrior
      (aiB ∩ aiC ∩ aiD) X = 4/3 := by
  unfold PMF.impactRatio
  rw [ai_cond_AntPi_alt_one X hX]
  rcases hX with rfl | rfl | rfl
  · rw [ai_prob_aiB]; ennreal_arith
  · rw [ai_prob_aiC]; ennreal_arith
  · rw [ai_prob_aiD]; ennreal_arith

/-- All pair impact ratios equal 2 (model symmetry). -/
private lemma ai_impactRatio_pair (X Y : Set (Fin 4))
    (hX : X = aiB ∨ X = aiC ∨ X = aiD) (hY : Y = aiB ∨ Y = aiC ∨ Y = aiD)
    (hne : X ≠ Y) :
    PMF.impactRatio averyInvitedPrior
      (aiB ∩ aiC ∩ aiD) (X ∩ Y) = 2 := by
  unfold PMF.impactRatio
  rw [ai_cond_AntPi_pair_one X Y hX hY]
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [ai_prob_aiB_aiC]; ennreal_arith
  · rw [ai_prob_aiB_aiD]; ennreal_arith
  · rw [Set.inter_comm, ai_prob_aiB_aiC]; ennreal_arith
  · exact absurd rfl hne
  · rw [ai_prob_aiC_aiD]; ennreal_arith
  · rw [Set.inter_comm, ai_prob_aiB_aiD]; ennreal_arith
  · rw [Set.inter_comm, ai_prob_aiC_aiD]; ennreal_arith
  · exact absurd rfl hne

/-- For any conditional answer T, `aiD ∈ T`. By contradiction: if `aiD ∉ T`,
`T ⊆ {aiB, aiC}`; case-analyse to a swap-construction `T'` (replace one
element with `aiD`); apply `hMaxT` to derive an `impactRatio` tie via
model symmetry, contradicting strict-greater. -/
private lemma ai_T_contains_aiD
    (T : Set (Set (Fin 4)))
    (hT : Semantics.Questions.ProbabilisticAnswerhood.IsConditionalAnswer
      (aiB ∩ aiC ∩ aiD) averyInvitedRQ averyInvitedPrior T) :
    aiD ∈ T := by
  obtain ⟨⟨hNeT, _hFinT, hAltT, _⟩, hMaxT⟩ := hT
  by_contra h_no_aiD
  have h_aiB_alt : aiB ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_aiC_alt : aiC ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_aiD_alt : aiD ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_T_alts : ∀ A ∈ T, A = aiB ∨ A = aiC := fun A hA => by
    have hAlt := hAltT A hA
    rw [ai_alt] at hAlt
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hAlt
    rcases hAlt with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hA h_no_aiD
  -- Case on whether aiB ∈ T and aiC ∈ T (4 sub-cases, last ruled out by Nonempty)
  by_cases h_aiB_in : aiB ∈ T
  · by_cases h_aiC_in : aiC ∈ T
    · -- T = {aiB, aiC}; T' = {aiB, aiD}.
      have h_T_eq : T = ({aiB, aiC} : Set (Set (Fin 4))) := by
        apply Set.eq_of_subset_of_subset
        · intro A hA
          rcases h_T_alts A hA with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · intro A hA
          rcases hA with rfl | hA
          · exact h_aiB_in
          · rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiC_in
      have h_T'_ne : ({aiB, aiD} : Set (Set (Fin 4))).Nonempty := ⟨aiB, Or.inl rfl⟩
      have h_T'_fin : ({aiB, aiD} : Set (Set (Fin 4))).Finite :=
        (Set.finite_singleton _).insert _
      have h_T'_alt : ∀ A ∈ ({aiB, aiD} : Set (Set (Fin 4))),
          A ∈ Question.alt averyInvitedRQ := by
        intro A hA
        rcases hA with rfl | hA
        · exact h_aiB_alt
        · rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiD_alt
      have h_no_sub : ¬ T ⊆ ({aiB, aiD} : Set (Set (Fin 4))) := by
        rw [h_T_eq]
        intro h_sub
        have : aiC ∈ ({aiB, aiD} : Set (Set (Fin 4))) := h_sub (Or.inr rfl)
        rcases this with hCB | hC
        · exact ai_aiB_ne_aiC hCB.symm
        · rw [Set.mem_singleton_iff] at hC; exact ai_aiC_ne_aiD hC
      have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
      rw [h_T_eq] at hM
      have h_inter_BC : ⋂₀ ({aiB, aiC} : Set (Set (Fin 4))) = aiB ∩ aiC := by
        ext w; simp [Set.mem_inter_iff]
      have h_inter_BD : ⋂₀ ({aiB, aiD} : Set (Set (Fin 4))) = aiB ∩ aiD := by
        ext w; simp [Set.mem_inter_iff]
      rw [h_inter_BC, h_inter_BD] at hM
      rw [ai_impactRatio_pair aiB aiC (Or.inl rfl) (Or.inr (Or.inl rfl)) ai_aiB_ne_aiC,
          ai_impactRatio_pair aiB aiD (Or.inl rfl) (Or.inr (Or.inr rfl)) ai_aiB_ne_aiD] at hM
      exact absurd hM (lt_irrefl _)
    · -- T = {aiB}; T' = {aiD}.
      have h_T_eq : T = ({aiB} : Set (Set (Fin 4))) := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨h_aiB_in, ?_⟩
        intro y hy
        rcases h_T_alts y hy with rfl | rfl
        · rfl
        · exact absurd hy h_aiC_in
      have h_T'_ne : ({aiD} : Set (Set (Fin 4))).Nonempty := Set.singleton_nonempty _
      have h_T'_fin : ({aiD} : Set (Set (Fin 4))).Finite := Set.finite_singleton _
      have h_T'_alt : ∀ A ∈ ({aiD} : Set (Set (Fin 4))),
          A ∈ Question.alt averyInvitedRQ := by
        intro A hA; rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiD_alt
      have h_no_sub : ¬ T ⊆ ({aiD} : Set (Set (Fin 4))) := by
        rw [h_T_eq]
        intro h_sub
        have : aiB ∈ ({aiD} : Set (Set (Fin 4))) := h_sub rfl
        rw [Set.mem_singleton_iff] at this
        exact ai_aiB_ne_aiD this
      have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
      rw [h_T_eq, Set.sInter_singleton, Set.sInter_singleton] at hM
      rw [ai_impactRatio_singleton aiB (Or.inl rfl),
          ai_impactRatio_singleton aiD (Or.inr (Or.inr rfl))] at hM
      exact absurd hM (lt_irrefl _)
  · -- aiB ∉ T. Then T ⊆ {aiC}.
    have h_aiC_in : aiC ∈ T := by
      obtain ⟨A, hA⟩ := hNeT
      rcases h_T_alts A hA with rfl | rfl
      · exact absurd hA h_aiB_in
      · exact hA
    have h_T_eq : T = ({aiC} : Set (Set (Fin 4))) := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨h_aiC_in, ?_⟩
      intro y hy
      rcases h_T_alts y hy with rfl | rfl
      · exact absurd hy h_aiB_in
      · rfl
    have h_T'_ne : ({aiD} : Set (Set (Fin 4))).Nonempty := Set.singleton_nonempty _
    have h_T'_fin : ({aiD} : Set (Set (Fin 4))).Finite := Set.finite_singleton _
    have h_T'_alt : ∀ A ∈ ({aiD} : Set (Set (Fin 4))),
        A ∈ Question.alt averyInvitedRQ := by
      intro A hA; rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiD_alt
    have h_no_sub : ¬ T ⊆ ({aiD} : Set (Set (Fin 4))) := by
      rw [h_T_eq]
      intro h_sub
      have : aiC ∈ ({aiD} : Set (Set (Fin 4))) := h_sub rfl
      rw [Set.mem_singleton_iff] at this
      exact ai_aiC_ne_aiD this
    have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
    rw [h_T_eq, Set.sInter_singleton, Set.sInter_singleton] at hM
    rw [ai_impactRatio_singleton aiC (Or.inr (Or.inl rfl)),
        ai_impactRatio_singleton aiD (Or.inr (Or.inr rfl))] at hM
    exact absurd hM (lt_irrefl _)

/-- Symmetric to `ai_T_contains_aiD`: any conditional answer contains `aiC`. -/
private lemma ai_T_contains_aiC
    (T : Set (Set (Fin 4)))
    (hT : Semantics.Questions.ProbabilisticAnswerhood.IsConditionalAnswer
      (aiB ∩ aiC ∩ aiD) averyInvitedRQ averyInvitedPrior T) :
    aiC ∈ T := by
  obtain ⟨⟨hNeT, _hFinT, hAltT, _⟩, hMaxT⟩ := hT
  by_contra h_no_aiC
  have h_aiB_alt : aiB ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_aiC_alt : aiC ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_aiD_alt : aiD ∈ Question.alt averyInvitedRQ := by rw [ai_alt]; simp [List.mem_cons]
  have h_T_alts : ∀ A ∈ T, A = aiB ∨ A = aiD := fun A hA => by
    have hAlt := hAltT A hA
    rw [ai_alt] at hAlt
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hAlt
    rcases hAlt with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hA h_no_aiC
    · exact Or.inr rfl
  by_cases h_aiB_in : aiB ∈ T
  · by_cases h_aiD_in : aiD ∈ T
    · -- T = {aiB, aiD}; T' = {aiB, aiC}.
      have h_T_eq : T = ({aiB, aiD} : Set (Set (Fin 4))) := by
        apply Set.eq_of_subset_of_subset
        · intro A hA
          rcases h_T_alts A hA with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · intro A hA
          rcases hA with rfl | hA
          · exact h_aiB_in
          · rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiD_in
      have h_T'_ne : ({aiB, aiC} : Set (Set (Fin 4))).Nonempty := ⟨aiB, Or.inl rfl⟩
      have h_T'_fin : ({aiB, aiC} : Set (Set (Fin 4))).Finite :=
        (Set.finite_singleton _).insert _
      have h_T'_alt : ∀ A ∈ ({aiB, aiC} : Set (Set (Fin 4))),
          A ∈ Question.alt averyInvitedRQ := by
        intro A hA
        rcases hA with rfl | hA
        · exact h_aiB_alt
        · rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiC_alt
      have h_no_sub : ¬ T ⊆ ({aiB, aiC} : Set (Set (Fin 4))) := by
        rw [h_T_eq]
        intro h_sub
        have : aiD ∈ ({aiB, aiC} : Set (Set (Fin 4))) := h_sub (Or.inr rfl)
        rcases this with hAD | hC
        · exact ai_aiB_ne_aiD hAD.symm
        · rw [Set.mem_singleton_iff] at hC; exact ai_aiC_ne_aiD hC.symm
      have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
      rw [h_T_eq] at hM
      have h_inter_BD : ⋂₀ ({aiB, aiD} : Set (Set (Fin 4))) = aiB ∩ aiD := by
        ext w; simp [Set.mem_inter_iff]
      have h_inter_BC : ⋂₀ ({aiB, aiC} : Set (Set (Fin 4))) = aiB ∩ aiC := by
        ext w; simp [Set.mem_inter_iff]
      rw [h_inter_BD, h_inter_BC] at hM
      rw [ai_impactRatio_pair aiB aiD (Or.inl rfl) (Or.inr (Or.inr rfl)) ai_aiB_ne_aiD,
          ai_impactRatio_pair aiB aiC (Or.inl rfl) (Or.inr (Or.inl rfl)) ai_aiB_ne_aiC] at hM
      exact absurd hM (lt_irrefl _)
    · -- T = {aiB}; T' = {aiC}.
      have h_T_eq : T = ({aiB} : Set (Set (Fin 4))) := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨h_aiB_in, ?_⟩
        intro y hy
        rcases h_T_alts y hy with rfl | rfl
        · rfl
        · exact absurd hy h_aiD_in
      have h_T'_ne : ({aiC} : Set (Set (Fin 4))).Nonempty := Set.singleton_nonempty _
      have h_T'_fin : ({aiC} : Set (Set (Fin 4))).Finite := Set.finite_singleton _
      have h_T'_alt : ∀ A ∈ ({aiC} : Set (Set (Fin 4))),
          A ∈ Question.alt averyInvitedRQ := by
        intro A hA; rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiC_alt
      have h_no_sub : ¬ T ⊆ ({aiC} : Set (Set (Fin 4))) := by
        rw [h_T_eq]
        intro h_sub
        have : aiB ∈ ({aiC} : Set (Set (Fin 4))) := h_sub rfl
        rw [Set.mem_singleton_iff] at this
        exact ai_aiB_ne_aiC this
      have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
      rw [h_T_eq, Set.sInter_singleton, Set.sInter_singleton] at hM
      rw [ai_impactRatio_singleton aiB (Or.inl rfl),
          ai_impactRatio_singleton aiC (Or.inr (Or.inl rfl))] at hM
      exact absurd hM (lt_irrefl _)
  · -- aiB ∉ T → T ⊆ {aiD}; T = {aiD}.
    have h_aiD_in : aiD ∈ T := by
      obtain ⟨A, hA⟩ := hNeT
      rcases h_T_alts A hA with rfl | rfl
      · exact absurd hA h_aiB_in
      · exact hA
    have h_T_eq : T = ({aiD} : Set (Set (Fin 4))) := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨h_aiD_in, ?_⟩
      intro y hy
      rcases h_T_alts y hy with rfl | rfl
      · exact absurd hy h_aiB_in
      · rfl
    have h_T'_ne : ({aiC} : Set (Set (Fin 4))).Nonempty := Set.singleton_nonempty _
    have h_T'_fin : ({aiC} : Set (Set (Fin 4))).Finite := Set.finite_singleton _
    have h_T'_alt : ∀ A ∈ ({aiC} : Set (Set (Fin 4))),
        A ∈ Question.alt averyInvitedRQ := by
      intro A hA; rw [Set.mem_singleton_iff] at hA; subst hA; exact h_aiC_alt
    have h_no_sub : ¬ T ⊆ ({aiC} : Set (Set (Fin 4))) := by
      rw [h_T_eq]
      intro h_sub
      have : aiD ∈ ({aiC} : Set (Set (Fin 4))) := h_sub rfl
      rw [Set.mem_singleton_iff] at this
      exact ai_aiC_ne_aiD this.symm
    have hM := hMaxT _ h_T'_ne h_T'_fin h_T'_alt h_no_sub
    rw [h_T_eq, Set.sInter_singleton, Set.sInter_singleton] at hM
    rw [ai_impactRatio_singleton aiD (Or.inr (Or.inr rfl)),
        ai_impactRatio_singleton aiC (Or.inr (Or.inl rfl))] at hM
    exact absurd hM (lt_irrefl _)

/-- "She invited Bailey and Cameron. She invited Dana, too." (Thomas 2026 ex. 68)
is felicitous as a canonical mention-some additive use.

This is the worked example Thomas walks through at PDF lines 1750-1880. The
felicity-condition discharge:
- **Antecedent Condition** (Def. 64a): `condProbSet ANT |B| = 1 > 3/4 = probOfSet |B|`
- **Conjunction Condition (answers)** (Def. 64b.i): `condProbSet (ANT ∩ π) |D| = 1 > 3/4`
- **Conjunction Condition (strengthens)** (Def. 64b.ii): `condProbSet (ANT ∩ π) |D| = 1 > 1/2 = condProbSet ANT |D|`
- **Non-triviality** (Def. 64c.i): π = `|D|` ⊄ ⋂T = {w₀} (PDF line 1869: "Avery
  invited Dana does not entail that Avery invited Bailey, Cameron, AND Dana").
  Discharged via `ai_T_contains_aiC` (any conditional answer contains `aiC`,
  so `w₂ ∈ aiD` but `w₂ ∉ aiC ⊇ ⋂T`).
- **Maximality** (Def. 64c.ii): for any S ⊋ π with non-trivial weakening,
  `condProbSet (ANT ∩ π) ⋂T = 1 > condProbSet (ANT ∩ S) ⋂T`. Discharged via
  `ai_T_contains_aiD` (any conditional answer contains `aiD`, so `w₁ ∉ ⋂T`)
  + computed `(R ∩ ⋂T) = (R' ∩ ⋂T) = {w₀}` + `ENNReal.div_lt_div_left` with
  `hPos : P(R) < P(R')`.

This is the **first mention-some application** of the `IsConditionalAnswer`
substrate. The 4-world model is the minimum diversity needed for an antichain
of three alternatives whose pairwise intersections all have positive prior.
The two `ai_T_contains_*` lemmas use the Option-1 mathlib idiom (impactRatio
symmetry helpers + per-scenario case enumeration over T's non-empty subsets
of `alt`); each missing-alt assumption derives an `impactRatio`-tie via the
`hMaxT` clause, contradicting strict-greater. -/
theorem averyInvited_too_felicitous :
    tooFelicitous averyInvitedCtx aiD := by
  have hCtxAnt : averyInvitedCtx.antecedent = aiB ∩ aiC := rfl
  have hCtxRQ : averyInvitedCtx.resolvedQuestion = averyInvitedRQ := rfl
  have hCtxPrior : averyInvitedCtx.prior = averyInvitedPrior := rfl
  have hAltMem_aiB : aiB ∈ Question.alt averyInvitedRQ := by
    rw [ai_alt]; simp [List.mem_cons]
  have hAltMem_aiD : aiD ∈ Question.alt averyInvitedRQ := by
    rw [ai_alt]; simp [List.mem_cons]
  have hAltMem_aiC : aiC ∈ Question.alt averyInvitedRQ := by
    rw [ai_alt]; simp [List.mem_cons]
  refine ⟨?ant, ⟨?conjA, ?conjS⟩, ?nontrv, ?max⟩
  · -- Antecedent Condition: ANT = {w₀, w₁} answers RQ via |B|.
    show probAnswersS averyInvitedCtx.antecedent averyInvitedCtx.resolvedQuestion
         averyInvitedCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨aiB, hAltMem_aiB, ?_⟩
    -- Need: condProbSet (aiB ∩ aiC) aiB > probOfSet aiB
    -- (aiB ∩ aiC) ⊆ aiB, so condProbSet = 1. probOfSet aiB = 3/4. 1 > 3/4.
    have h_cond : averyInvitedPrior.condProbSet (aiB ∩ aiC) aiB = 1 := by
      rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr Set.inter_subset_left]
      exact ENNReal.div_self ai_pos_ANT.ne' (PMF.probOfSet_ne_top _ _)
    have h : averyInvitedPrior.condProbSet (aiB ∩ aiC) aiB >
             averyInvitedPrior.probOfSet aiB := by
      rw [h_cond, ai_prob_aiB]; ennreal_arith
    convert h
  · -- Conjunction-Answers: ANT ∩ π = {w₀} answers RQ via |D|.
    show probAnswersS (averyInvitedCtx.antecedent ∩ aiD)
         averyInvitedCtx.resolvedQuestion averyInvitedCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨aiD, hAltMem_aiD, ?_⟩
    -- (aiB ∩ aiC) ∩ aiD ⊆ aiD, so condProbSet = 1. probOfSet aiD = 3/4. 1 > 3/4.
    have h_cond : averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) aiD = 1 := by
      rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr ai_AntPi_sub_aiD]
      exact ENNReal.div_self ai_AntPi_pos.ne' (PMF.probOfSet_ne_top _ _)
    have h : averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) aiD >
             averyInvitedPrior.probOfSet aiD := by
      rw [h_cond, ai_prob_aiD]; ennreal_arith
    convert h
  · -- Conjunction-Strengthens: |D| strengthened by π over ANT alone.
    show someResolutionStrengthenedS averyInvitedCtx.antecedent aiD
         averyInvitedCtx.resolvedQuestion averyInvitedCtx.prior
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    refine ⟨aiD, hAltMem_aiD, ?_⟩
    -- condProbSet (ANT ∩ π) aiD = 1 (computed above).
    -- condProbSet ANT aiD = P(ANT ∩ aiD) / P(ANT) = (1/4)/(1/2) = 1/2.
    have h_cond_AntPi : averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) aiD = 1 := by
      rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr ai_AntPi_sub_aiD]
      exact ENNReal.div_self ai_AntPi_pos.ne' (PMF.probOfSet_ne_top _ _)
    have h_cond_Ant : averyInvitedPrior.condProbSet (aiB ∩ aiC) aiD = 1/2 := by
      rw [PMF.condProbSet_eq_div, ai_prob_aiB_aiC]
      -- (aiB ∩ aiC) ∩ aiD = aiB ∩ aiC ∩ aiD = {w₀}, probOfSet = 1/4.
      have h_inter_eq : (aiB ∩ aiC) ∩ aiD = aiB ∩ aiC ∩ aiD := by ext w; tauto
      rw [h_inter_eq, ai_prob_AntPi]
      ennreal_arith
    have h : averyInvitedPrior.condProbSet (aiB ∩ aiC ∩ aiD) aiD >
             averyInvitedPrior.condProbSet (aiB ∩ aiC) aiD := by
      rw [h_cond_AntPi, h_cond_Ant]; ennreal_arith
    convert h
  · -- Non-triviality (literal): ∀ T cond.ans, π = aiD ⊄ ⋂T.
    -- Use ai_T_contains_aiC: aiC ∈ T → ⋂T ⊆ aiC. Witness w₂ ∈ aiD \ aiC.
    unfold nonTrivialityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro T hT h_pi_sub_inter
    have h_aiC_in : aiC ∈ T := ai_T_contains_aiC T hT
    have h_inter_sub_C : ⋂₀ T ⊆ aiC := Set.sInter_subset_of_mem h_aiC_in
    have h_w2_in_pi : (2 : Fin 4) ∈ aiD := Or.inr (Or.inl rfl)
    have h_w2_in_inter : (2 : Fin 4) ∈ ⋂₀ T := h_pi_sub_inter h_w2_in_pi
    have h_w2_in_aiC : (2 : Fin 4) ∈ aiC := h_inter_sub_C h_w2_in_inter
    simp [aiC] at h_w2_in_aiC
  · -- Maximality (literal): ∀ T cond.ans, ∀ S preconds, strict ineq.
    unfold maximalityCondition
    rw [hCtxAnt, hCtxRQ, hCtxPrior]
    intro T hT S hSS hPos
    have h_aiD_in : aiD ∈ T := ai_T_contains_aiD T hT
    obtain ⟨⟨_, _, hAltT, _⟩, _⟩ := hT
    -- Step 1: w₀ ∈ ⋂T (every alt contains w₀)
    have h_w0_in : (0 : Fin 4) ∈ ⋂₀ T := by
      apply Set.mem_sInter.mpr
      intro A hA
      have hAlt := hAltT A hA
      rw [ai_alt] at hAlt
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hAlt
      rcases hAlt with rfl | rfl | rfl <;> exact Or.inl rfl
    -- ⋂T ⊆ aiD (from aiD ∈ T)
    have h_inter_sub_D : ⋂₀ T ⊆ aiD := Set.sInter_subset_of_mem h_aiD_in
    -- w₁ ∉ ⋂T (since w₁ ∉ aiD)
    have h_w1_not_in : (1 : Fin 4) ∉ ⋂₀ T := fun h => by
      have h_in_D : (1 : Fin 4) ∈ aiD := h_inter_sub_D h
      simp [aiD] at h_in_D
    -- (R ∩ ⋂T) = {w₀} where R = AntPi
    have h_LHS_inter : (aiB ∩ aiC ∩ aiD) ∩ ⋂₀ T = ({w | w.val = 0} : Set (Fin 4)) := by
      rw [ai_AntPi_eq]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · exact And.left
      · intro h0
        refine ⟨h0, ?_⟩
        have : w = 0 := Fin.ext h0
        subst this; exact h_w0_in
    -- (ANT∩S) ∩ ⋂T = {w₀}: ANT∩S ⊆ {w₀, w₁} (= ANT), w₁ ∉ ⋂T, w₀ ∈ both.
    have h_RHS_inter : (aiB ∩ aiC ∩ S) ∩ ⋂₀ T = ({w | w.val = 0} : Set (Fin 4)) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hw_ant_s, hw_inter⟩
        have hw_ant : w ∈ aiB ∩ aiC := hw_ant_s.1
        rw [ai_aiB_aiC_eq] at hw_ant
        rcases hw_ant with h0 | h1
        · exact h0
        · exfalso
          have : w = 1 := Fin.ext h1
          subst this; exact h_w1_not_in hw_inter
      · intro h0
        have : w = 0 := Fin.ext h0
        subst this
        refine ⟨⟨⟨Or.inl rfl, Or.inl rfl⟩, ?_⟩, h_w0_in⟩
        exact hSS.le (Or.inl rfl)
    -- Reduce both condProbSets via h_LHS_inter, h_RHS_inter, then strict-anti
    -- on the explicit ratio.
    rw [PMF.condProbSet_eq_div, PMF.condProbSet_eq_div, h_LHS_inter, h_RHS_inter, ai_prob_w0]
    -- Goal: 1/4 / P(R) > 1/4 / P(R'), where R = aiB ∩ aiC ∩ aiD, R' = aiB ∩ aiC ∩ S.
    -- hPos : P(R) < P(R'). Apply ENNReal.div_lt_div_left.
    have h14_pos : (0 : ENNReal) < 1/4 := by ennreal_arith
    have h14_ne_top : (1/4 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num : (4 : ENNReal) ≠ 0)
    exact ENNReal.div_lt_div_left h14_pos.ne' h14_ne_top hPos

end Verification

-- ============================================================================
-- Abstract Theorems
-- ============================================================================

/-! ## Abstract Theorems

Three abstract characterisations of @cite{thomas-2026}'s framework, stated
schematically over arbitrary `W`:

1. **Standard-use reduction**: when π directly entails an alternative of RQ,
   the Conjunction-Condition strengthening half is trivial.
2. **Heim-style setup**: when ANT and π each entail distinct alternatives of
   RQ, both the Antecedent Condition and the strengthening half of the
   Conjunction Condition are satisfied.
3. **Cumulative-evidence necessity**: if π is conditionally independent of
   every alternative given ANT, no resolution is strengthened, so *too* is
   infelicitous.

These characterisations are paper-anchored claims about Thomas 2026's Def. 64;
they live here rather than in `Theories/Pragmatics/Particles/Additive.lean`
per the linglib study-vs-theory split.

The Heim-style setup is a structural observation by the formaliser, not
a claim Thomas makes literally: Thomas 2026 §2 presents @cite{heim-1992}'s
individual-based formulation `φ[α_F]too_i presupposes x_i ≠ α & φ[x_i]`
(PDF eq. (4)) but does not argue formally that Def. 64 *subsumes* it. The
theorem `heim_subsumption_partial` below records the half-direction that
follows directly from Def. 64a and the strengthening half of 64b under
distinct-alternative assumptions; the full subsumption claim (recovering
non-triviality and maximality) is left open. -/

namespace AbstractTheorems

open Semantics.Questions.ProbabilisticAnswerhood
open Pragmatics.Particles.Additive
open Core

variable {W : Type*} [Fintype W]

/-- π is conditionally independent of `target` given `cond` if
`P(target | cond ∩ π) = P(target | cond)`. -/
noncomputable def conditionallyIndependent
    (cond p target : Set W) (prior : Prior W) : Prop :=
  prior.condProbSet (cond ∩ p) target = prior.condProbSet cond target

/-- π is evidentially irrelevant to Q given ANT if π doesn't change the
conditional probability of any alternative when we already know ANT. -/
noncomputable def evidentiallyIrrelevant
    (ant prejacent : Set W) (q : Core.Question W) (prior : Prior W) : Prop :=
  ∀ a ∈ Core.Question.alt q, conditionallyIndependent ant prejacent a prior

/-- **Predicate: Argument-Building Use** (Thomas 2026 §3, §5.3).

Argument-building use arises exactly when:
1. ANT does not entail any alternative of RQ;
2. π does not entail any alternative of RQ;
3. The Conjunction Condition still holds.

The hotel example (Thomas 2026, ex. 1c/14c/65) is the paradigm case:
RQ = "What would be a good hotel?", ANT = "room just opened up",
π = "looks fancy". Neither alone determines a hotel-goodness alternative;
together they raise the probability that this hotel is good. -/
def isArgumentBuildingUse
    (ctx : AdditiveContext W) (prejacent : Set W) : Prop :=
  (¬ ∃ a ∈ Core.Question.alt ctx.resolvedQuestion, ctx.antecedent ⊆ a) ∧
  (¬ ∃ a ∈ Core.Question.alt ctx.resolvedQuestion, prejacent ⊆ a) ∧
  conjunctionCondition ctx prejacent

/-- **Theorem: Standard-Use Reduction**

When π directly determines an alternative `alt` of RQ, and `alt` isn't
already certain given ANT, the conjunction strengthens evidence for
`alt` over ANT alone.

Captures why standard *too* works: if π = "Mary came" and this IS an
alternative of "Who came?", then learning π guarantees that alternative,
so ANT ∩ π always evidences it more strongly than ANT alone (unless ANT
already entailed it). The probabilistic strengthening reduces to the
simple requirement that ANT and π both be true. -/
theorem standard_use_reduction
    (ctx : AdditiveContext W) (prejacent alt : Set W)
    (hEntails : prejacent ⊆ alt)
    (hNotAlreadyCertain : ctx.prior.condProbSet ctx.antecedent alt < 1)
    (hConjPossible : ctx.prior.probOfSet (ctx.antecedent ∩ prejacent) > 0) :
    ctx.prior.condProbSet (ctx.antecedent ∩ prejacent) alt >
    ctx.prior.condProbSet ctx.antecedent alt := by
  rw [condProb_eq_one_of_entails ctx.prior (ctx.antecedent ∩ prejacent) alt
      (fun _ hw => hEntails hw.2) hConjPossible]
  exact hNotAlreadyCertain

/-- **Theorem: Heim-style setup satisfies 64a + strengthening half of 64b.**

@cite{heim-1992}'s formulation (Thomas 2026 §2 eq. (4)):
`φ[α_F]too_i presupposes x_i ≠ α & φ[x_i]` — i.e. there is a distinct
salient individual of which the same property holds. Lifting this to
the propositional level, the Heim setup corresponds to ANT ⊆ altAnt and
prejacent ⊆ altPi for two distinct alternatives `altAnt, altPi` of RQ.

Under those assumptions plus standard non-degeneracy on the prior, this
theorem proves the **Antecedent Condition** (Def. 64a) and the
**strengthening half** of the Conjunction Condition (Def. 64b). The
*answers-RQ* half of 64b, the non-triviality condition (64c.i), and the
maximality condition (64c.ii) are NOT discharged here and would require
additional hypotheses about the question's alternative structure.

This is therefore a *partial* subsumption result: it shows that the
core informativeness intuition behind Heim's account is recovered by
Def. 64a + 64b-strengthening, not that every Heim-felicitous *too* is
fully Thomas-felicitous. -/
theorem heim_subsumption_partial
    (ctx : AdditiveContext W) (prejacent altAnt altPi : Set W)
    (hAntInQ : altAnt ∈ Core.Question.alt ctx.resolvedQuestion)
    (hPiInQ : altPi ∈ Core.Question.alt ctx.resolvedQuestion)
    (hAntEntails : ctx.antecedent ⊆ altAnt)
    (hPiEntails : prejacent ⊆ altPi)
    (hAntPossible : ctx.prior.probOfSet ctx.antecedent > 0)
    (hConjPossible : ctx.prior.probOfSet (ctx.antecedent ∩ prejacent) > 0)
    (hAntAltNotCertain : ctx.prior.probOfSet altAnt < 1)
    (hPiNotCertainGivenAnt : ctx.prior.condProbSet ctx.antecedent altPi < 1) :
    antecedentCondition ctx ∧
    someResolutionStrengthenedS ctx.antecedent prejacent
      ctx.resolvedQuestion ctx.prior := by
  refine ⟨⟨altAnt, hAntInQ, ?_⟩, ⟨altPi, hPiInQ, ?_⟩⟩
  · rw [condProb_eq_one_of_entails ctx.prior ctx.antecedent altAnt
        hAntEntails hAntPossible]
    exact hAntAltNotCertain
  · rw [condProb_eq_one_of_entails ctx.prior (ctx.antecedent ∩ prejacent) altPi
        (fun _ hw => hPiEntails hw.2) hConjPossible]
    exact hPiNotCertainGivenAnt

/-- **Theorem: Cumulative-Evidence Necessity**

If π is evidentially irrelevant to RQ given ANT (i.e., π doesn't change
the probability of any alternative), then no resolution is strengthened,
so the strengthening half of the Conjunction Condition fails.

Explains why *too* requires the prejacent to contribute something: a
prejacent that is just noise relative to the question at hand cannot
felicitously be marked. Compare the infelicity diagnosed by Winterstein
2011 (PDF lines 195-201) for "Lemmy did not solve all the problems.
Ritchie solved some of them (#too)." -/
theorem cumulative_evidence_necessary
    (ctx : AdditiveContext W) (prejacent : Set W)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    ¬ someResolutionStrengthenedS ctx.antecedent prejacent
        ctx.resolvedQuestion ctx.prior := by
  rintro ⟨a, ha, hgt⟩
  have h := hIrrelevant a ha
  simp only [conditionallyIndependent] at h
  rw [h] at hgt
  exact lt_irrefl _ hgt

/-- Corollary: If π is irrelevant, *too* is infelicitous. -/
theorem irrelevant_prejacent_infelicitous
    (ctx : AdditiveContext W) (prejacent : Set W)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    ¬ tooFelicitous ctx prejacent := by
  intro hFel
  exact cumulative_evidence_necessary ctx prejacent hIrrelevant hFel.2.1.2

end AbstractTheorems

end Thomas2026
