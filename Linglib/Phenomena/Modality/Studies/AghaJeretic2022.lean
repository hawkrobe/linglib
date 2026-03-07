import Linglib.Core.Semantics.Kleene
import Linglib.Phenomena.Plurals.Homogeneity

/-!
# Weak Necessity Modals as Homogeneous Pluralities of Worlds
@cite{agha-jeretic-2022}

Proceedings of SALT 32: 831–851.

## Core Proposal

Weak necessity modals like *should* are **not quantificational**. They denote
definite pluralities of worlds, paralleling the relationship between plural
definite nominals (*the*) and universal quantifiers (*all*/*every*):

- *must p* = all worlds in a given domain are p-worlds  (∀ quantifier)
- *should p* = the worlds in a given domain are p-worlds (plural definite)

This gives weak necessity modals **homogeneity** as an intrinsic feature:
they yield a truth-value gap (neither true nor false) when some but not all
worlds in the domain satisfy the prejacent — exactly paralleling the behavior
of plural definite DPs under negation.

## Key Claims Formalized

1. **Homogeneity** (§3.1): Weak necessity modals take obligatory apparent wide
   scope over negation, unlike strong necessity modals which allow narrow scope.
   "You shouldn't go" is incompatible with "but you can" (wide scope only),
   while "You don't have to go" is compatible (narrow scope available).

2. **Trivalent semantics** (§4.2): `should_D := ⊕D` — the mereological sum
   of the best worlds. Evaluation is trivalent:
   - 1 if all worlds in g(D) satisfy p
   - 0 if no world in g(D) satisfies p
   - ★ (indeterminate) otherwise

3. **Homogeneity removal** (§3.2): The adverb *necessarily* removes
   homogeneity from *should*, just as *all* removes homogeneity from plural
   definites. "You shouldn't necessarily go" ≃ "You don't go in all best
   worlds" — compatible with existential followup.

4. **QUD-sensitive exception tolerance** (§3.3): Weak necessity modals
   tolerate exceptions when irrelevant to the QUD, paralleling plural
   definite non-maximality.

5. **X operator** (§5.1): Derives `should` from `must` compositionally.
   X picks out the unique minimal witness set of a universal quantifier
   and takes its mereological sum: `X(must_D) = ⊕D`.

6. **Cross-linguistic morphological patterns** (§5.2):
   - French: *devoir*+CF (counterfactual) = weak necessity
   - Javanese: *mesthi*+NE (definiteness marker) = weak necessity

7. **Critique of domain restriction** (§6.1): The von Fintel & Iatridou (2008)
   analysis treats *should* as ∀ over a refined set. This predicts that
   *shouldn't* is compatible with an existential claim — but empirically it
   is not (homogeneity).

## Connection to @cite{agha-jeretic-2026}

The 2026 handbook chapter surveys this analysis as one of three competing
accounts of weak necessity (alongside domain restriction and comparative
semantics), and extends it to explain the neg-raising asymmetry between
*should* and *must*.
-/

namespace Phenomena.Modality.Studies.AghaJeretic2022

open Core.Kleene (TVal Prop3)
open Phenomena.Plurals.Homogeneity (HomogeneityJudgment HomogeneityDatum
  HomogeneityRemover HomogeneityRemovalDatum)

-- ============================================================================
-- §1. Trivalent Semantics for Modals (§4.2)
-- ============================================================================

/-! ## Trivalent evaluation

The paper's central formal contribution: *should* gets trivalent semantics
via plural predication over worlds, while *must* remains bivalent (standard
∀ quantification).

We model the modal domain as a `List World` and use `Core.Kleene.TVal`
for the three-valued output. -/

variable {World : Type}

/-- Strong necessity: standard ∀ quantification over the modal domain.
    Bivalent — always true or false, never indeterminate.

    `must_D := λp. ∀w ∈ D. p(w)` (paper eq. 25) -/
def mustEval (domain : List World) (p : World → Bool) : TVal :=
  TVal.ofBool (domain.all p)

/-- Weak necessity: trivalent plural predication over the modal domain.
    Returns tt if all worlds satisfy p, ff if none do, unk otherwise.

    `should_D := ⊕D` — the prejacent is predicated of the plurality
    of worlds, yielding homogeneity (paper eq. 27-28). -/
def shouldEval (domain : List World) (p : World → Bool) : TVal :=
  if domain.isEmpty then TVal.ff  -- empty domain: vacuously false
  else if domain.all p then TVal.tt
  else if domain.all (fun w => !p w) then TVal.ff
  else TVal.unk

-- ============================================================================
-- §2. Core Properties of the Trivalent Semantics
-- ============================================================================

/-! ### must is always bivalent -/

/-- `must` never returns the indeterminate value. -/
theorem must_bivalent (domain : List World) (p : World → Bool) :
    mustEval domain p = TVal.tt ∨ mustEval domain p = TVal.ff := by
  unfold mustEval TVal.ofBool
  cases domain.all p <;> simp

/-! ### should is homogeneous: it can return ★ -/

/-- In a mixed domain, `should` returns ★ (indeterminate). -/
theorem should_mixed :
    shouldEval [true, false] id = TVal.unk := by native_decide

/-- In a uniform-true domain, `should` returns tt. -/
theorem should_all_true :
    shouldEval [true, true, true] id = TVal.tt := by native_decide

/-- In a uniform-false domain, `should` returns ff. -/
theorem should_all_false :
    shouldEval [false, false] id = TVal.ff := by native_decide

/-- `must` returns ff in the mixed case (no gap). -/
theorem must_mixed :
    mustEval [true, false] id = TVal.ff := by native_decide

/-- When positive, `should` and `must` agree. -/
theorem should_must_agree_positive (domain : List World) (p : World → Bool)
    (h : domain.all p = true) (hne : domain.isEmpty = false) :
    shouldEval domain p = mustEval domain p := by
  simp [shouldEval, mustEval, TVal.ofBool, h, hne]

-- ============================================================================
-- §3. Homogeneity Data for Modals (§3.1)
-- ============================================================================

/-! ## Modal homogeneity parallels plural definite homogeneity

The paper demonstrates that weak necessity modals pattern exactly like
plural definites with respect to negation. We encode the key data points
using the `HomogeneityDatum` type from `Plurals.Homogeneity`. -/

/-- *Should* displays homogeneity: under negation, "shouldn't go" is
    incompatible with an existential followup "but you can" — just like
    "The guests aren't here" is incompatible with "but some of them are."

    Paper examples (8-9): "According to the rules, you shouldn't go,
    #but you are allowed to go." -/
def shouldHomogeneity : HomogeneityDatum :=
  { positiveSentence := "According to the rules, you should go."
  , negativeSentence := "According to the rules, you shouldn't go."
  , allScenario := "All best deontic worlds are go-worlds"
  , noneScenario := "No best deontic worlds are go-worlds"
  , gapScenario := "Some but not all best deontic worlds are go-worlds"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

/-- *Have to* does NOT display homogeneity: "don't have to go" is compatible
    with "but you are allowed to go" — narrow scope reading available.

    Paper example (9b): "According to the rules, you don't have to go,
    ✓but you are allowed to go." -/
def haveToNoHomogeneity : HomogeneityDatum :=
  { positiveSentence := "According to the rules, you have to go."
  , negativeSentence := "According to the rules, you don't have to go."
  , allScenario := "All best deontic worlds are go-worlds"
  , noneScenario := "No best deontic worlds are go-worlds"
  , gapScenario := "Some but not all best deontic worlds are go-worlds"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  -- have-to is bivalent: false in gap under wide scope, true under narrow
  , positiveInGap := .clearlyFalse
  , negativeInGap := .clearlyTrue
  }

/-- The gap judgments match: should gets ★, have-to gets a definite value. -/
theorem should_has_gap :
    shouldHomogeneity.positiveInGap = .neitherTrueNorFalse := rfl

theorem haveTo_no_gap :
    haveToNoHomogeneity.negativeInGap = .clearlyTrue := rfl

-- ============================================================================
-- §4. Homogeneity Removal (§3.2)
-- ============================================================================

/-! ## Homogeneity removal by "necessarily"

Inserting *necessarily* into a weak necessity modal sentence removes the
homogeneity gap, just as *all* removes homogeneity from plural definites.

Paper examples (14-15):
- "You shouldn't go" → #but you can go
- "You shouldn't necessarily go" → ✓but you can go

This parallels:
- "The guests aren't here" → #but some are
- "The guests aren't all here" → ✓but some are -/

/-- *Necessarily* removes homogeneity from *should*. -/
def necessarilyRemovesModalHomogeneity : HomogeneityRemovalDatum :=
  { homogeneousSentence := "According to the rules, you shouldn't go."
  , precisesentence := "According to the rules, you shouldn't necessarily go."
  , remover := .all  -- "necessarily" functions like "all" for worlds
  , gapScenario := "Some but not all best worlds are go-worlds"
  , homogeneousJudgment := .neitherTrueNorFalse
  , preciseJudgment := .clearlyFalse
  }

/-- `shouldEval` with homogeneity removal (= quantifier insertion) reduces
    to `mustEval` — the gap disappears. -/
def shouldWithRemoval (domain : List World) (p : World → Bool) : TVal :=
  mustEval domain p  -- "shouldn't necessarily" = ¬∀ = standard bivalent

theorem removal_eliminates_gap :
    shouldWithRemoval [true, false] id = TVal.ff := by native_decide

-- ============================================================================
-- §5. Exception Tolerance (§3.3)
-- ============================================================================

/-! ## QUD-sensitive exception tolerance

Plural predication tolerates exceptions when they are irrelevant to the QUD.
The paper shows the same pattern for weak necessity modals:

Paper example (17):
Context: One can get a perfect grade by doing most exercises correctly;
doing all gives extra credit.
QUD1: What is a way to get a perfect grade?
QUD2: What are the minimal requirements?

(a) "You should do every exercise." → QUD1: ✓; QUD2: #
(b) "You have to do every exercise." → QUD1: #; QUD2: # -/

/-- A QUD-sensitivity datum for modal exception tolerance. -/
structure ModalExceptionDatum where
  modal : String
  sentence : String
  context : String
  qud1 : String
  qud2 : String
  acceptableUnderQUD1 : Bool
  acceptableUnderQUD2 : Bool
  deriving Repr

def shouldExceptionTolerance : ModalExceptionDatum where
  modal := "should"
  sentence := "To get a perfect grade, you should do every exercise."
  context := "One can get a perfect grade by doing most exercises; doing all gives extra credit."
  qud1 := "What is a way to get a perfect grade?"
  qud2 := "What are the minimal requirements to get a perfect grade?"
  acceptableUnderQUD1 := true   -- tolerates exceptions (extra-credit worlds irrelevant)
  acceptableUnderQUD2 := false  -- exceptions relevant → infelicitous

def haveToExceptionTolerance : ModalExceptionDatum where
  modal := "have to"
  sentence := "To get a perfect grade, you have to do every exercise."
  context := "One can get a perfect grade by doing most exercises; doing all gives extra credit."
  qud1 := "What is a way to get a perfect grade?"
  qud2 := "What are the minimal requirements to get a perfect grade?"
  acceptableUnderQUD1 := false  -- no exception tolerance (universal quantifier)
  acceptableUnderQUD2 := false  -- false under any QUD

/-- *Should* tolerates exceptions under a friendly QUD; *have to* does not. -/
theorem should_tolerates_exceptions :
    shouldExceptionTolerance.acceptableUnderQUD1 = true ∧
    haveToExceptionTolerance.acceptableUnderQUD1 = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §6. Responses to Indeterminate Sentences (§3.4)
-- ============================================================================

/-! ## Well-responses in borderline cases

In borderline cases (★), outright denial is infelicitous; *well*-responses
are preferred. This parallels plural definites (Križ 2016).

Paper example (19):
Context: Two doors lead to the living room; both are equally good.
A: #You should take the right door.
B: #{No, That's not true}, you don't have to, but you can.
B: Well, you don't have to, but you can. -/

/-- Response pattern for indeterminate modal sentences. -/
structure IndeterminateResponseDatum where
  sentence : String
  context : String
  noResponseFelicitous : Bool
  wellResponseFelicitous : Bool
  deriving Repr

def shouldIndeterminateResponse : IndeterminateResponseDatum where
  sentence := "You should take the right door to go to the living room."
  context := "Two doors lead to the living room; both are equally good options."
  noResponseFelicitous := false  -- #"No, that's not true"
  wellResponseFelicitous := true -- ✓"Well, you don't have to, but you can."

def mustIndeterminateResponse : IndeterminateResponseDatum where
  sentence := "You must take the right door to go to the living room."
  context := "Two doors lead to the living room; both are equally good options."
  noResponseFelicitous := true   -- ✓"No, that's not true" (bivalent: simply false)
  wellResponseFelicitous := false -- #"Well, ..." (no gap to hedge)

/-- *Should* in borderline cases resists "no" but allows "well";
    *must* allows "no" but resists "well". -/
theorem should_well_not_no :
    shouldIndeterminateResponse.noResponseFelicitous = false ∧
    shouldIndeterminateResponse.wellResponseFelicitous = true := ⟨rfl, rfl⟩

theorem must_no_not_well :
    mustIndeterminateResponse.noResponseFelicitous = true ∧
    mustIndeterminateResponse.wellResponseFelicitous = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §7. The X Operator: Deriving should from must (§5.1)
-- ============================================================================

/-! ## Compositional derivation via the X operator

X picks out the unique smallest set that makes a quantifier true and returns
the mereological sum of its elements:

  X := λM. ⊕ ιW[W ∈ WIT(M)]

where WIT(M) is the set of minimal witness sets for quantifier M.

Applied to `must_D = λp. ∀w ∈ D. p(w)`:
- The unique minimal witness set of ∀ over D is D itself
- So X(must_D) = ⊕D = should_D

This provides a compositional derivation of weak from strong necessity. -/

/-- The minimal witness set of universal quantification over a domain
    is the domain itself — there is no proper subset that still satisfies ∀. -/
def minimalWitnessOfUniversal (domain : List World) : List World := domain

/-- X applied to must yields the domain itself (= should's denotation).
    The resulting plurality is then subject to plural predication semantics. -/
def applyX (domain : List World) (p : World → Bool) : TVal :=
  shouldEval (minimalWitnessOfUniversal domain) p

/-- X(must) = should: the X operator derives trivalent semantics from
    bivalent universal quantification. -/
theorem x_must_eq_should (domain : List World) (p : World → Bool) :
    applyX domain p = shouldEval domain p := rfl

-- ============================================================================
-- §8. Cross-Linguistic Morphological Patterns (§2, §5.2)
-- ============================================================================

/-! ## Morphological composition of weak necessity

Cross-linguistically, weak necessity is expressed in two ways:

1. **Primitive lexical items** (English *should*, *ought*): morphologically
   non-decomposable, weak necessity is the basic meaning.

2. **Morphological derivation from strong necessity**:
   a. French: *devoir* (must) + counterfactual morphology = *devrait* (should)
   b. Javanese: *mesthi* (must) + NE marker = *mesthi-ne* (should)

The paper proposes that the deriving morpheme is a version of the X operator:
- Javanese NE = X (unique minimal witness, only applies to universals)
- French CF = a relaxed version (picks a witness set, not necessarily unique)
-/

/-- Morphological strategy for encoding weak necessity. -/
inductive WeakNecessityMorphology where
  | primitive           -- morphologically non-decomposable (English should)
  | counterfactual      -- strong + counterfactual morphology (French, Hungarian)
  | dedicatedMarker     -- strong + dedicated morpheme (Javanese NE)
  deriving DecidableEq, Repr

/-- Cross-linguistic data on weak necessity morphology. -/
structure WeakNecessityMorphDatum where
  language : String
  strongForm : String
  weakForm : String
  strategy : WeakNecessityMorphology
  glossNote : String
  deriving Repr

def english_should : WeakNecessityMorphDatum where
  language := "English"
  strongForm := "must/have to"
  weakForm := "should/ought"
  strategy := .primitive
  glossNote := "Non-decomposable; no productive morphological relation"

def french_devrais : WeakNecessityMorphDatum where
  language := "French"
  strongForm := "dois (devoir.PRES)"
  weakForm := "devrais (devoir+CF)"
  strategy := .counterfactual
  glossNote := "Counterfactual morphology on strong necessity modal"

def javanese_mesthi : WeakNecessityMorphDatum where
  language := "Javanese"
  strongForm := "mesthi"
  weakForm := "mesthi-ne"
  strategy := .dedicatedMarker
  glossNote := "NE is also a definiteness marker for nominals"

def spanish_deber : WeakNecessityMorphDatum where
  language := "Spanish"
  strongForm := "deber/tener que"
  weakForm := "debería/tendría que (deber/tener que+CF)"
  strategy := .counterfactual
  glossNote := "Counterfactual morphology, parallel to French"

def hungarian_kell : WeakNecessityMorphDatum where
  language := "Hungarian"
  strongForm := "kell"
  weakForm := "kell+CF"
  strategy := .counterfactual
  glossNote := "Counterfactual morphology"

def russian_sledovat : WeakNecessityMorphDatum where
  language := "Russian"
  strongForm := "—"
  weakForm := "sledovat'/stoit'"
  strategy := .primitive
  glossNote := "Shows homogeneity effects under negation"

def swedish_bor : WeakNecessityMorphDatum where
  language := "Swedish"
  strongForm := "—"
  weakForm := "bör"
  strategy := .primitive
  glossNote := "Shows homogeneity effects under negation"

def weakNecessityMorphData : List WeakNecessityMorphDatum :=
  [ english_should, french_devrais, javanese_mesthi, spanish_deber
  , hungarian_kell, russian_sledovat, swedish_bor ]

/-- Three distinct morphological strategies attested. -/
theorem three_strategies :
    (weakNecessityMorphData.map (·.strategy)).eraseDups.length = 3 := by
  native_decide

-- ============================================================================
-- §9. Critique of Domain Restriction (§6.1)
-- ============================================================================

/-! ## Why domain restriction doesn't capture homogeneity

The von Fintel & Iatridou (2008) analysis treats *should* as ∀ over a
refined (smaller) set of best worlds. Under this analysis:

  ⟦shouldn't go⟧ = ¬∀w ∈ D'. go(w)   where D' ⊆ D

This is compatible with ∃w ∈ D. go(w) — predicting that "you shouldn't
go, but you are allowed to go" should be felicitous. But empirically it
is not (#). The ∀-analysis wrongly predicts narrow-scope readings.

The plural predication analysis avoids this: negation of a plural definite
yields the homogeneous gap, blocking the existential followup. -/

/-- The domain restriction analysis predicts narrow scope for negated
    weak necessity — but empirically, only wide scope is available. -/
structure DomainRestrictionPrediction where
  sentence : String
  existentialFollowup : String
  domainRestrictionPredicts : Bool  -- is followup felicitous?
  empiricallyObserved : Bool        -- is it actually felicitous?
  deriving Repr

def domainRestrictionFails : DomainRestrictionPrediction where
  sentence := "According to the rules, you shouldn't go."
  existentialFollowup := "but you are allowed to go"
  domainRestrictionPredicts := true   -- ¬∀ compatible with ∃
  empiricallyObserved := false        -- actually infelicitous (#)

/-- Domain restriction makes the wrong prediction for the core homogeneity
    diagnostic: it predicts felicity where infelicity is observed. -/
theorem domain_restriction_wrong :
    domainRestrictionFails.domainRestrictionPredicts ≠
    domainRestrictionFails.empiricallyObserved := by decide

-- ============================================================================
-- §10. Scopelessness (§3.1, higher negation)
-- ============================================================================

/-! ## Scopelessness persists under higher negation

The apparent wide scope of *should* persists when negation is in a higher
clause, paralleling plural definites:

- "I don't think the guests are here" → #but some are (plural def.)
- "I don't think you should go" → #but you are allowed to go (should)
- "I don't think you have to go" → ✓but you are allowed to go (have to)

This is analyzed as *scopelessness*: plural definites don't actually take
scope; they are predicated directly. The "wide scope" effect is a
consequence of homogeneity, not movement. -/

/-- Modal scopelessness under extra-clausal negation. -/
structure ScopelessnessDatum where
  modal : String
  sentence : String
  existentialFollowup : String
  followupFelicitous : Bool
  deriving Repr

def shouldScopeless : ScopelessnessDatum where
  modal := "should"
  sentence := "According to the rules, I don't think you should go."
  existentialFollowup := "but you are allowed to go"
  followupFelicitous := false  -- wide scope only (homogeneity)

def haveToNotScopeless : ScopelessnessDatum where
  modal := "have to"
  sentence := "According to the rules, I don't think you have to go."
  existentialFollowup := "but you are allowed to go"
  followupFelicitous := true   -- narrow scope available (quantifier)

/-- *Should* is scopeless (homogeneous); *have to* is not. -/
theorem scopelessness_contrast :
    shouldScopeless.followupFelicitous = false ∧
    haveToNotScopeless.followupFelicitous = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §11. Summary: The Parallel
-- ============================================================================

/-! ## The Determiner–Modal Parallel

The paper's central analogy:

| Nominal domain          | Modal domain              |
|------------------------|---------------------------|
| *the* N (plural def.)  | *should* (weak necessity)  |
| *all*/*every* N (∀)    | *must*/*have to* (strong)  |
| homogeneous            | homogeneous                |
| scopeless              | scopeless                  |
| exception-tolerant     | exception-tolerant         |
| *all* removes gap      | *necessarily* removes gap  |
| ★ → "well" response   | ★ → "well" response       |

The proposal: weak necessity *is* to strong necessity what *the* is to *all*.
-/

/-- Summary of the five shared properties between plural definites
    and weak necessity modals. -/
structure PluralModalParallel where
  property : String
  pluralDefiniteExample : String
  weakNecessityExample : String
  sharedBehavior : Bool
  deriving Repr

def sharedProperties : List PluralModalParallel :=
  [ { property := "Homogeneity (obligatory wide scope under negation)"
    , pluralDefiniteExample := "The guests aren't here — #but some are"
    , weakNecessityExample := "You shouldn't go — #but you can"
    , sharedBehavior := true }
  , { property := "Scopelessness (persists under higher negation)"
    , pluralDefiniteExample := "I don't think the guests are here — #but some are"
    , weakNecessityExample := "I don't think you should go — #but you can"
    , sharedBehavior := true }
  , { property := "Homogeneity removal by explicit quantifier"
    , pluralDefiniteExample := "The guests aren't all here — ✓but some are"
    , weakNecessityExample := "You shouldn't necessarily go — ✓but you can"
    , sharedBehavior := true }
  , { property := "QUD-sensitive exception tolerance"
    , pluralDefiniteExample := "The students asked questions (QUD1: ✓; QUD2: #)"
    , weakNecessityExample := "You should do every exercise (QUD1: ✓; QUD2: #)"
    , sharedBehavior := true }
  , { property := "Well-responses to indeterminate sentences"
    , pluralDefiniteExample := "#Mary talked to the girls. / Well, only to some."
    , weakNecessityExample := "#You should take the right door. / Well, you don't have to."
    , sharedBehavior := true }
  ]

/-- All five properties are shared between plural definites and weak
    necessity modals. -/
theorem all_properties_shared :
    sharedProperties.all (·.sharedBehavior) = true := by native_decide

/-- Five parallel properties identified. -/
theorem five_parallels : sharedProperties.length = 5 := rfl

end Phenomena.Modality.Studies.AghaJeretic2022
