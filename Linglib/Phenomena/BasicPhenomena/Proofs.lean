/-
# Proofs that Surface Grammar Captures Basic Phenomena

Formal verification that the surface grammar correctly distinguishes
grammatical from ungrammatical sentences for each phenomenon.
-/

import Linglib.Theories.Surface.Basic
import Linglib.Phenomena.BasicPhenomena.Agreement
import Linglib.Phenomena.BasicPhenomena.Subcategorization
import Linglib.Phenomena.BasicPhenomena.WordOrder
import Linglib.Phenomena.BasicPhenomena.Case
import Linglib.Phenomena.BasicPhenomena.DetNounAgreement
import Linglib.Phenomena.BasicPhenomena.DativeAlternation
import Linglib.Phenomena.BasicPhenomena.Passive

open Lexicon Surface

-- ============================================================================
-- Agreement Proofs
-- ============================================================================

/-- "he sleeps" is grammatical -/
theorem agreement_he_sleeps :
    agreementOk [he, sleeps] = true := rfl

/-- "he sleep" is ungrammatical (agreement violation) -/
theorem agreement_he_sleep_bad :
    agreementOk [he, sleep] = false := rfl

/-- "they sleep" is grammatical -/
theorem agreement_they_sleep :
    agreementOk [they, sleep] = true := rfl

/-- "they sleeps" is ungrammatical -/
theorem agreement_they_sleeps_bad :
    agreementOk [they, sleeps] = false := rfl

/-- "john sleeps" is grammatical (proper name is 3sg) -/
theorem agreement_john_sleeps :
    agreementOk [john, sleeps] = true := rfl

/-- "john sleep" is ungrammatical -/
theorem agreement_john_sleep_bad :
    agreementOk [john, sleep] = false := rfl

-- ============================================================================
-- Subcategorization Proofs
-- ============================================================================

/-- Intransitive verb with no object is grammatical -/
theorem subcat_intransitive_ok :
    subcatOk [john, sleeps] = true := rfl

/-- Intransitive verb with object is ungrammatical -/
theorem subcat_intransitive_with_obj_bad :
    subcatOk [john, sleeps, book] = false := rfl

/-- Transitive verb with object is grammatical -/
theorem subcat_transitive_ok :
    subcatOk [john, devours, pizza] = true := rfl

/-- Transitive verb without object is ungrammatical -/
theorem subcat_transitive_no_obj_bad :
    subcatOk [john, devours] = false := rfl

/-- Ditransitive verb with two objects is grammatical -/
theorem subcat_ditransitive_ok :
    subcatOk [john, gives, mary, book] = true := rfl

/-- Ditransitive verb with one object is ungrammatical -/
theorem subcat_ditransitive_one_obj_bad :
    subcatOk [john, gives, mary] = false := rfl

-- ============================================================================
-- Word Order Proofs
-- ============================================================================

/-- SVO order is grammatical -/
theorem word_order_svo_ok :
    wordOrderOk [john, sees, mary] .declarative = true := rfl

/-- SOV order is ungrammatical -/
theorem word_order_sov_bad :
    wordOrderOk [john, mary, sees] .declarative = false := rfl

-- ============================================================================
-- Case Proofs
-- ============================================================================

/-- Nominative subject, accusative object is grammatical -/
theorem case_nom_subj_acc_obj :
    caseOk [he, sees, her] = true := rfl

/-- Accusative in subject position is ungrammatical -/
theorem case_acc_subj_bad :
    caseOk [him, sees, her] = false := rfl

/-- Nominative in object position is ungrammatical -/
theorem case_nom_obj_bad :
    caseOk [he, sees, she] = false := rfl

/-- Proper names (no case marking) are ok in any position -/
theorem case_proper_names_ok :
    caseOk [john, sees, mary] = true := rfl

-- ============================================================================
-- Determiner-Noun Agreement Proofs
-- ============================================================================

/-- Singular determiner with singular noun is grammatical -/
theorem det_noun_sg_sg_ok :
    detNounAgrOk [a, girl] = true := rfl

/-- Singular determiner with plural noun is ungrammatical -/
theorem det_noun_sg_pl_bad :
    detNounAgrOk [a, girls] = false := rfl

/-- Plural determiner with plural noun is grammatical -/
theorem det_noun_pl_pl_ok :
    detNounAgrOk [these, books] = true := rfl

/-- Plural determiner with singular noun is ungrammatical -/
theorem det_noun_pl_sg_bad :
    detNounAgrOk [these, book] = false := rfl

/-- Number-neutral determiner works with singular -/
theorem det_noun_neutral_sg_ok :
    detNounAgrOk [the, girl] = true := rfl

/-- Number-neutral determiner works with plural -/
theorem det_noun_neutral_pl_ok :
    detNounAgrOk [the, girls] = true := rfl

-- ============================================================================
-- Dative Alternation Proofs
-- ============================================================================

/-- Double object construction is grammatical -/
theorem dative_double_object_ok :
    subcatOk [john, gives, mary, book] = true := rfl

/-- Prepositional dative is grammatical -/
theorem dative_prep_ok :
    subcatOk [john, gives_dat, book, to, mary] = true := rfl

/-- Dative without PP is ungrammatical -/
theorem dative_no_pp_bad :
    subcatOk [john, gives_dat, book] = false := rfl

/-- Locative with PP is grammatical -/
theorem locative_ok :
    subcatOk [john, puts, book, on, table] = true := rfl

/-- Locative without PP is ungrammatical -/
theorem locative_no_pp_bad :
    subcatOk [john, puts, book] = false := rfl

-- ============================================================================
-- Passive Proofs
-- ============================================================================

/-- Short passive is grammatical -/
theorem passive_short_ok :
    passiveOk [the, ball, was, kicked] = true := rfl

/-- Passive with by-phrase is grammatical -/
theorem passive_with_agent_ok :
    passiveOk [the, cat_, was, chased, by_, john] = true := rfl

/-- Passive with direct object is ungrammatical -/
theorem passive_with_obj_bad :
    passiveOk [the, ball, was, kicked, the, dog] = false := rfl

/-- Active sentence passes passiveOk vacuously -/
theorem active_passes_passive_check :
    passiveOk [john, kicks, ball] = true := rfl

-- ============================================================================
-- Combined Check Proofs (Full Grammar)
-- ============================================================================

/-- Complete grammatical sentence passes all checks -/
theorem full_check_grammatical :
    checkSentence defaultGrammar [he, sees, her] .declarative = true := rfl

/-- Agreement violation caught by full check -/
theorem full_check_agreement_bad :
    checkSentence defaultGrammar [he, see, her] .declarative = false := rfl

/-- Case violation caught by full check -/
theorem full_check_case_bad :
    checkSentence defaultGrammar [him, sees, her] .declarative = false := rfl

/-- Passive sentence passes full check -/
theorem full_check_passive_ok :
    checkSentence defaultGrammar [the, ball, was, kicked] .declarative = true := rfl

/-- Passive with by-phrase passes full check -/
theorem full_check_passive_by_ok :
    checkSentence defaultGrammar [the, cat_, was, chased, by_, john] .declarative = true := rfl

-- ============================================================================
-- Meta-theorem: Grammar distinguishes minimal pairs
-- ============================================================================

/-- For a valid minimal pair, grammatical and ungrammatical sentences differ -/
theorem minimal_pair_distinguished
    (grammatical ungrammatical : List Word)
    (ct : ClauseType)
    (h_good : checkSentence defaultGrammar grammatical ct = true)
    (h_bad : checkSentence defaultGrammar ungrammatical ct = false) :
    checkSentence defaultGrammar grammatical ct ≠
    checkSentence defaultGrammar ungrammatical ct := by
  simp [h_good, h_bad]

-- Example instantiation
example : checkSentence defaultGrammar [he, sleeps] .declarative ≠
          checkSentence defaultGrammar [he, sleep] .declarative :=
  minimal_pair_distinguished [he, sleeps] [he, sleep] .declarative rfl rfl

-- ============================================================================
-- Formal Phenomenon Capture Proofs
-- ============================================================================

/-- Surface grammar derives a sentence iff checkSentence returns true -/
theorem derives_iff_check (ws : List Word) (ct : ClauseType) :
    Grammar.derives defaultGrammar ws ct ↔ checkSentence defaultGrammar ws ct = true := by
  constructor <;> intro h <;> exact h

/-- Surface grammar captures a pair: derives grammatical, blocks ungrammatical -/
theorem captures_agreement_pair_1 :
    checkSentence defaultGrammar [he, sleeps] .declarative = true ∧
    checkSentence defaultGrammar [he, sleep] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_case_pair_1 :
    checkSentence defaultGrammar [he, sees, her] .declarative = true ∧
    checkSentence defaultGrammar [him, sees, her] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_det_noun_pair_1 :
    checkSentence defaultGrammar [a, girl] .declarative = true ∧
    checkSentence defaultGrammar [a, girls] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_subcat_pair_trans :
    checkSentence defaultGrammar [john, devours, pizza] .declarative = true ∧
    checkSentence defaultGrammar [john, devours] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_passive_pair :
    checkSentence defaultGrammar [the, ball, was, kicked] .declarative = true ∧
    checkSentence defaultGrammar [the, ball, was, kicked, the, ball] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_word_order_pair :
    checkSentence defaultGrammar [john, sees, mary] .declarative = true ∧
    checkSentence defaultGrammar [john, mary, sees] .declarative = false :=
  ⟨rfl, rfl⟩

theorem captures_dative_pair :
    checkSentence defaultGrammar [john, gives, mary, book] .declarative = true ∧
    checkSentence defaultGrammar [john, gives, mary] .declarative = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Soundness: If grammar accepts, constraints are satisfied
-- ============================================================================

/-- If checkSentence passes, then agreementOk passes -/
theorem check_implies_agreement (ws : List Word) (ct : ClauseType) :
    checkSentence defaultGrammar ws ct = true →
    agreementOk ws = true := by
  intro h
  simp only [checkSentence, defaultGrammar] at h
  cases h_agr : agreementOk ws
  · simp [h_agr] at h
  · rfl

/-- If checkSentence passes, then caseOk passes -/
theorem check_implies_case (ws : List Word) (ct : ClauseType) :
    checkSentence defaultGrammar ws ct = true →
    caseOk ws = true := by
  intro h
  simp only [checkSentence, defaultGrammar] at h
  cases h_case : caseOk ws
  · simp [h_case] at h
  · rfl

/-- If checkSentence passes, then subcatOk passes -/
theorem check_implies_subcat (ws : List Word) (ct : ClauseType) :
    checkSentence defaultGrammar ws ct = true →
    subcatOk ws = true := by
  intro h
  simp only [checkSentence, defaultGrammar] at h
  cases h_sub : subcatOk ws
  · simp [h_sub] at h
  · rfl
