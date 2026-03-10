import Linglib.Theories.Syntax.Minimalism.Core.PersonGeometry
import Linglib.Fragments.Italian.Pronouns

/-!
# Adamson & Zompì (2025): Polite Pronouns and the PCC
@cite{adamson-zompi-2025}

Polite Pronouns and the PCC. *Linguistic Inquiry*, Early Access.

## Summary

The Person-Case Constraint (PCC) bans certain person combinations in
ditransitive clitic clusters. All Italian speakers reject 3>1 and 3>2
IO>DO clitic combinations (Weak PCC); some additionally reject 1>2 and
2>1 (Strong PCC). PCC effects are restricted to clitic clusters —
stressed/tonic pronouns are always licit (§2, (5)).

The polite pronoun LEI is **formally** third person — it triggers 3sg
verbal agreement (§3, (8)), patterns with 3sg.f clitics in ordering
(§3, (11c)), binds 3rd person reflexives (§3, (10)), and triggers
obligatory feminine participle agreement (§3, (14)). Yet LEI triggers
PCC effects like a **second person** pronoun: `*Glie La hanno affidata`
(3.DAT LEI.ACC) is ungrammatical (§4.1, (17)), paralleling `*Glie ti
hanno affidata` (3.DAT 2.ACC), not the licit `Glie la hanno affidata`
(3.DAT 3.F.ACC).

Three independent lines of evidence converge:
1. **PCC** (§4.1): LEI in DO position triggers PCC effects like 2nd person
2. **Fancy Constraint** (§4.2): LEI triggers person hierarchy effects in
   *faire infinitif* causatives like 2nd person
3. **Resolved agreement** (§4.3, (30)): LEI in coordination triggers 2PL
   resolved agreement, unlike imposters which trigger 3PL ((31)-(32))

This falsifies morphosyntactic accounts (@cite{deal-2021},
@cite{coon-keine-2021}, @cite{bjar-rezac-2009}), which predict LEI
should behave like 3rd person for PCC purposes. The data supports a
syntacticosemantic account such as @cite{pancheva-zubizarreta-2018},
where the PCC reads *interpretable* person features.

The same pattern obtains cross-linguistically: Spanish USTED (§6.1) and
German SIE (§6.2) also trigger PCC effects despite 3rd person agreement.
Imposters (e.g., *Vostro Onore*) do NOT trigger PCC effects (§4.3),
confirming the effect depends on syntacticosemantic person features,
not addressee reference per se.
-/

namespace Phenomena.Agreement.Studies.AdamsonZompi2025

open Core.Prominence (PersonLevel)
open Minimalism (DecomposedPerson decomposePerson)

-- ============================================================================
-- § 1: Dual Person Features
-- ============================================================================

/-- A nominal's person features split into two layers.

    @cite{adamson-zompi-2025} argue that polite pronouns carry two distinct
    sets of φ-features (following @cite{smith-2017}, @cite{anagnostopoulou-2017a},
    @cite{wurmbrand-2017}, among others):

    - **`agreementPerson`** (uninterpretable): governs verbal agreement,
      clitic allomorphy, reflexive binding, clitic ordering, participle
      agreement. For LEI, this is 3rd person.
    - **`interpretablePerson`** (interpretable): governs the PCC, Fancy
      Constraint, resolved agreement in coordination. For LEI, this is
      2nd person.

    For ordinary (non-polite) pronouns, both layers coincide. -/
structure DualPersonFeatures where
  agreementPerson : PersonLevel
  interpretablePerson : PersonLevel
  deriving DecidableEq, BEq, Repr

/-- Ordinary pronoun: both layers are the same person. -/
def DualPersonFeatures.ordinary (p : PersonLevel) : DualPersonFeatures :=
  ⟨p, p⟩

-- ============================================================================
-- § 2: Italian Pronouns with Dual Features
-- ============================================================================

/-- *io* — 1sg: agreement 1st, interpretable 1st. -/
def pro1 : DualPersonFeatures := .ordinary .first

/-- *tu* — 2sg familiar: agreement 2nd, interpretable 2nd. -/
def pro2 : DualPersonFeatures := .ordinary .second

/-- *lui/lei* — 3sg: agreement 3rd, interpretable 3rd. -/
def pro3 : DualPersonFeatures := .ordinary .third

/-- *Lei* (polite) — agreement 3rd, interpretable 2nd.

    Morphological evidence for 3rd person agreement features (§3):
    - Morphologically identical to 3sg.f pronominal series (Table 1)
    - Triggers 3sg verbal agreement, not 2sg ((7)–(8))
    - Patterns with 3sg.f clitics in ordering: follows locative, like
      3sg.f `la` and unlike 2sg `ti` which precedes locative ((11))
    - Binds 3rd person reflexive `si`, not 2nd person `ti` ((9)–(10))
    - Triggers obligatory feminine participle agreement matching formal
      (not conceptual) gender, like 3sg.f accusative clitics ((13)–(14)) -/
def lei : DualPersonFeatures := ⟨.third, .second⟩

/-- Imposters (e.g., *Vostro Onore* 'Your Honor', *il signor Duca*):
    agreement 3rd, interpretable 3rd.

    Like LEI, imposters are grammatically 3rd person and are used to
    refer to addressees. Unlike LEI, imposters do not trigger PCC effects
    (§4.3, (27)–(29)), Fancy Constraint effects ((28)–(29)), or 2nd person
    resolved agreement in coordination ((31)–(32)). Their relationship to
    addressee reference is pragmatic, not encoded in interpretable person
    features. -/
def imposter : DualPersonFeatures := .ordinary .third

-- ============================================================================
-- § 3: The PCC — Strong and Weak Variants
-- ============================================================================

/-- The **Weak PCC**: a 3rd person IO clitic cannot co-occur with a 1st or
    2nd person DO clitic.

    All Italian speakers have at least the Weak PCC (§2, p. 4–5).
    The constraint bans 3>1 and 3>2 but allows 1>2, 2>1, and all
    combinations where IO is 1st/2nd or DO is 3rd.

    Note: the person values here are the values the PCC *reads* — the
    central question of the paper is whether these are agreement person
    or interpretable person. -/
def weakPCC (ioPerson doPerson : PersonLevel) : Bool :=
  !(ioPerson == .third && doPerson.isSAP)

/-- The **Strong PCC**: in a ditransitive clitic cluster, the DO must be
    3rd person. Some Italian speakers have the Strong PCC (§2, p. 5),
    which additionally bans 1>2 and 2>1.

    The Strong PCC entails the Weak PCC: anything banned under the Weak
    PCC is also banned under the Strong PCC. -/
def strongPCC (_ioPerson doPerson : PersonLevel) : Bool :=
  doPerson == .third

/-- Strong PCC entails Weak PCC. -/
theorem strong_entails_weak (io do_ : PersonLevel) :
    strongPCC io do_ = true → weakPCC io do_ = true := by
  cases io <;> cases do_ <;> decide

-- Weak PCC judgments
theorem weak_3_3 : weakPCC .third .third = true := rfl
theorem weak_2_3 : weakPCC .second .third = true := rfl
theorem weak_1_3 : weakPCC .first .third = true := rfl
theorem weak_3_2 : weakPCC .third .second = false := rfl
theorem weak_3_1 : weakPCC .third .first = false := rfl
/-- Weak PCC allows 1>2 and 2>1 (unlike Strong PCC). -/
theorem weak_allows_participant_pairs :
    weakPCC .first .second = true ∧ weakPCC .second .first = true := ⟨rfl, rfl⟩

-- Strong PCC judgments
theorem strong_3_2 : strongPCC .third .second = false := rfl
theorem strong_1_2 : strongPCC .first .second = false := rfl

-- ============================================================================
-- § 4: Empirical Data — Italian Clitic Combinations (§2, §4.1)
-- ============================================================================

/-- Acceptability judgments for Italian ditransitive clitic clusters.

    Person values are **interpretable** person — the paper's claim is that
    PCC effects track this layer, not agreement person. For non-polite
    pronouns the distinction is vacuous; for LEI it is crucial.

    PCC effects are restricted to clitic clusters: when one argument is a
    stressed (tonic) pronoun, person restrictions vanish (§2, (5)):
    - `Gli hanno affidato te` (3.DAT entrusted 2SG.STRESS) = ✓
    - `Ti hanno affidato a lui` (2.ACC entrusted to 3SG.STRESS) = ✓
    Similarly for LEI: `Gli hanno affidato Lei` (stressed) is licit (§4.1,
    (21)), and `La hanno affidata a lui` is licit ((21b)). -/
structure CliticJudgment where
  label : String
  ok : Bool
  ioPerson : PersonLevel
  doPerson : PersonLevel
  deriving Repr

-- Standard PCC data (§2, (1)–(3))
/-- (2a) Te la hanno affidata — 2.DAT > 3.F.ACC = ✓ -/
def dat2_acc3 : CliticJudgment := ⟨"2.DAT > 3.F.ACC", true, .second, .third⟩
/-- (2b) Glie la hanno affidata — 3.DAT > 3.F.ACC = ✓ -/
def dat3_acc3 : CliticJudgment := ⟨"3.DAT > 3.F.ACC", true, .third, .third⟩
/-- (3a) *Gli(e)/Le ti/te hanno affidato/affidata — 3.DAT > 2.ACC = ✗ -/
def dat3_acc2 : CliticJudgment := ⟨"3.DAT > 2.ACC", false, .third, .second⟩
/-- (3b) *Ti/Te gli(e)/le hanno affidato/affidata — same combination,
    reversed clitic order, still ✗. PCC is about person combination, not
    linear order. -/
def acc2_dat3 : CliticJudgment := ⟨"2.ACC > 3.DAT (reordered)", false, .third, .second⟩

-- LEI and the PCC (§4.1, (16)–(19))
/-- (16) Glie la hanno affidata — LEI.DAT > 3.F.ACC = ✓
    LEI as dative with 3rd person accusative: not a PCC violation because
    the interpretively-2nd-person argument is the IO, not the DO.
    (The clitic form `glie` is ambiguous between regular 3.DAT and LEI.DAT;
    both readings yield a grammatical sentence.) -/
def leiDat_acc3 : CliticJudgment := ⟨"LEI.DAT > 3.F.ACC", true, .second, .third⟩
/-- (17) *Glie La hanno affidata — 3.DAT > LEI.ACC = ✗
    The paper's central data point. LEI as accusative clitic with a 3rd
    person dative triggers PCC, just like 2nd person accusative `ti`.
    Note: this is string-identical to the licit `Glie la hanno affidata`
    (3.DAT > 3.F.ACC), differing only in whether the accusative is
    polite LEI or ordinary 3sg.f ((17) fn. 9). -/
def dat3_leiAcc : CliticJudgment := ⟨"3.DAT > LEI.ACC", false, .third, .second⟩
/-- (19a) Glie la hanno raccomandata — LEI.DAT > 3.F.ACC = ✓
    Same pattern with *raccomandare* 'recommend'. -/
def leiDat_acc3_racc : CliticJudgment := ⟨"LEI.DAT > 3.F.ACC (racc.)", true, .second, .third⟩
/-- (19b) *Glie La hanno raccomandata — 3.DAT > LEI.ACC = ✗ -/
def dat3_leiAcc_racc : CliticJudgment := ⟨"3.DAT > LEI.ACC (racc.)", false, .third, .second⟩

def italianData : List CliticJudgment :=
  [dat2_acc3, dat3_acc3, dat3_acc2, acc2_dat3,
   leiDat_acc3, dat3_leiAcc, leiDat_acc3_racc, dat3_leiAcc_racc]

-- ============================================================================
-- § 5: Predictions — Morphosyntactic vs. Syntacticosemantic
-- ============================================================================

/-- Morphosyntactic prediction: the PCC reads **agreement** person.

    Under morphosyntactic accounts (@cite{deal-2021}, @cite{coon-keine-2021},
    @cite{bjar-rezac-2009}), LEI's agreement features (3rd person) determine
    PCC behavior. Since 3>3 is licit, `3.DAT > LEI.ACC` should be licit. -/
def morphosyntacticPrediction (d : DualPersonFeatures) : Bool :=
  weakPCC .third d.agreementPerson

/-- Syntacticosemantic prediction: the PCC reads **interpretable** person.

    Under a syntacticosemantic account (@cite{pancheva-zubizarreta-2018}),
    LEI's interpretable features (2nd person) determine PCC behavior.
    Since 3>2 is illicit, `3.DAT > LEI.ACC` should be illicit. -/
def syntacticosemanticPrediction (d : DualPersonFeatures) : Bool :=
  weakPCC .third d.interpretablePerson

/-- Morphosyntactic account WRONGLY predicts 3.DAT > LEI.ACC is licit. -/
theorem morphosyntactic_wrong_for_lei :
    morphosyntacticPrediction lei = true := rfl

/-- Syntacticosemantic account CORRECTLY predicts 3.DAT > LEI.ACC is illicit. -/
theorem syntacticosemantic_correct_for_lei :
    syntacticosemanticPrediction lei = false := rfl

/-- The syntacticosemantic prediction matches the actual judgment. -/
theorem lei_prediction_matches_data :
    syntacticosemanticPrediction lei = dat3_leiAcc.ok := rfl

/-- The morphosyntactic prediction does NOT match the actual judgment. -/
theorem lei_morphosyntactic_mismatch :
    morphosyntacticPrediction lei ≠ dat3_leiAcc.ok := by decide

/-- LEI triggers effects under BOTH PCC variants. The Strong PCC is
    strictly stronger, so if the Weak PCC bans a combination, the Strong
    PCC does too. The LEI data doesn't depend on which variant a speaker has. -/
theorem lei_banned_under_both_variants :
    weakPCC .third lei.interpretablePerson = false ∧
    strongPCC .third lei.interpretablePerson = false := ⟨rfl, rfl⟩

/-- For ordinary pronouns (no mismatch), both accounts agree. -/
theorem ordinary_accounts_agree (p : PersonLevel) :
    morphosyntacticPrediction (.ordinary p) =
    syntacticosemanticPrediction (.ordinary p) := rfl

-- ============================================================================
-- § 6: Fancy Constraint — Independent Evidence (§4.2)
-- ============================================================================

/-- The Fancy Constraint (@cite{postal-1989}): in analytic causative
    constructions (*faire infinitif*), a person hierarchy effect obtains
    between the accusative clitic causee and 1st/2nd person arguments.

    In Italian, the *faire infinitif* construction shows: a 3rd person
    accusative causee is licit ((24) `Micol la fa pettinare a Carlo`),
    but a 1st/2nd person causee triggers a hierarchy effect ((24)
    `*Micol ti fa pettinare a Carlo`). Crucially, this is NOT a
    ditransitive clitic cluster — it involves a causative verb — so it
    constitutes independent evidence for the same person-sensitivity.

    LEI patterns with 2nd person, not 3rd:
    - (25) `*Signor Biagi, Micol La fa pettinare a Carlo` = ✗ (LEI as causee)
    - (26) `Micol fa pettinare {te / Lei} a Carlo` = ✓ (stressed: no effect)

    We model the Fancy Constraint as reading the same interpretable person
    features as the PCC. -/
def fancyConstraint (causeePerson : PersonLevel) : Bool :=
  -- Causee must be 3rd person (non-participant) when co-occurring
  -- with another argument
  causeePerson == .third

/-- 3sg.f causee is licit: `Micol la fa pettinare a Carlo` (24). -/
theorem fancy_3f_ok : fancyConstraint .third = true := rfl

/-- 2sg causee is illicit: `*Micol ti fa pettinare a Carlo` (24). -/
theorem fancy_2_bad : fancyConstraint .second = false := rfl

/-- LEI causee: interpretable 2nd → illicit, like `ti` ((25)). -/
theorem fancy_lei_bad : fancyConstraint lei.interpretablePerson = false := rfl

/-- LEI causee: agreement 3rd → morphosyntactic account wrongly predicts
    licit, like `la`. -/
theorem fancy_lei_morphosyntactic_wrong :
    fancyConstraint lei.agreementPerson = true := rfl

/-- PCC and Fancy Constraint agree for LEI: both read interpretable
    person, both ban LEI. -/
theorem pcc_fancy_converge :
    syntacticosemanticPrediction lei = false ∧
    fancyConstraint lei.interpretablePerson = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Imposters — No PCC Effect (§4.3)
-- ============================================================================

/-- Both accounts predict no PCC effect for imposters, matching the
    data ((27)–(29)). -/
theorem imposter_no_pcc_either_account :
    morphosyntacticPrediction imposter = true ∧
    syntacticosemanticPrediction imposter = true := ⟨rfl, rfl⟩

/-- The contrast between LEI and imposters: LEI triggers PCC, imposters
    don't. Both refer to addressees, but only LEI encodes this in
    interpretable person features. -/
theorem lei_imposter_contrast :
    syntacticosemanticPrediction lei ≠ syntacticosemanticPrediction imposter := by
  decide

/-- Resolved agreement in coordination (§4.3, (30)–(32)).

    When LEI is coordinated with a 3sg nominal, resolved agreement is
    obligatorily 2PL ((30) `Lei e l'ambasciatore... vi incontrerete`),
    consistent with LEI's interpretable 2nd person features. When an
    imposter (*Vostro Onore*, *il signor Duca*) is coordinated with a
    3sg nominal, resolved agreement is 3PL ((31)–(32)), consistent with
    interpretable 3rd person features.

    This is a third line of evidence, independent of both the PCC and
    the Fancy Constraint, showing that LEI's interpretable person surfaces
    in the grammar. -/
inductive ResolvedNumber where
  | pl2  -- 2nd person plural (vi incontrerete)
  | pl3  -- 3rd person plural (si incontreranno)
  deriving DecidableEq, BEq, Repr

def resolvedAgreement (d : DualPersonFeatures) : ResolvedNumber :=
  if d.interpretablePerson.isSAP then .pl2 else .pl3

/-- LEI + 3sg → 2PL resolved agreement ((30)). -/
theorem lei_resolved_2pl : resolvedAgreement lei = .pl2 := rfl

/-- Imposter + 3sg → 3PL resolved agreement ((31)–(32)). -/
theorem imposter_resolved_3pl : resolvedAgreement imposter = .pl3 := rfl

/-- All three lines of evidence (PCC, Fancy Constraint, resolved agreement)
    converge: LEI patterns with 2nd person, imposters pattern with 3rd. -/
theorem three_lines_converge :
    -- PCC: LEI banned, imposter not
    syntacticosemanticPrediction lei = false ∧
    syntacticosemanticPrediction imposter = true ∧
    -- Fancy Constraint: LEI banned, imposter not
    fancyConstraint lei.interpretablePerson = false ∧
    fancyConstraint imposter.interpretablePerson = true ∧
    -- Resolved agreement: LEI → 2PL, imposter → 3PL
    resolvedAgreement lei = .pl2 ∧
    resolvedAgreement imposter = .pl3 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Integration with PersonGeometry — [±participant] Drives the PCC
-- ============================================================================

/-- The PCC's sensitivity to interpretable person is equivalent to
    sensitivity to [+participant] in @cite{preminger-2014}'s decomposition.

    The Weak PCC bans 3rd person IO with [+participant] DO. LEI has
    interpretable [+participant] (2nd person = [+participant, −author]). -/
theorem lei_interpretable_is_participant :
    (decomposePerson lei.interpretablePerson).hasParticipant = true := rfl

/-- LEI's agreement features lack [participant] (3rd = [−participant]). -/
theorem lei_agreement_not_participant :
    (decomposePerson lei.agreementPerson).hasParticipant = false := rfl

/-- The Weak PCC reduces to: if IO is [−participant], then DO must be
    [−participant]. Equivalently: ¬(IO lacks [participant] ∧ DO has
    [participant]). -/
def pccViaParticipant (ioPerson doPerson : PersonLevel) : Bool :=
  !(!((decomposePerson ioPerson).hasParticipant) &&
     (decomposePerson doPerson).hasParticipant)

/-- `pccViaParticipant` is extensionally equivalent to `weakPCC`. -/
theorem pcc_participant_equivalence (io do_ : PersonLevel) :
    weakPCC io do_ = pccViaParticipant io do_ := by
  cases io <;> cases do_ <;> rfl

-- ============================================================================
-- § 9: Consistency with Italian Clitic Paradigm
-- ============================================================================

/-- LEI's agreement features match the 3sg.f clitic `la` in person.

    The fragment entry `la_cl` has `.third` person, matching LEI's
    agreement layer — confirming the paper's morphological evidence
    that LEI is formally 3sg.f (§3, Table 1). -/
theorem lei_matches_la_cl_person :
    lei.agreementPerson = .third ∧
    Fragments.Italian.Pronouns.la_cl.person = .third := ⟨rfl, rfl⟩

/-- LEI's agreement person (3rd) differs from 2sg clitic `ti` (2nd).

    The fragment types are `PersonLevel` (agreement) and `Person` (UD),
    but both encode the same three-way distinction. -/
theorem lei_differs_from_ti :
    lei.agreementPerson = .third ∧
    Fragments.Italian.Pronouns.ti_acc.person = .second := ⟨rfl, rfl⟩

/-- LEI binds 3rd person reflexive `si`, not 2nd person `ti` (§3, (9)–(10)).

    The fragment has `si_refl` (person = .third) and `ti_refl` (person =
    .second). LEI's reflexive matches the 3rd person entry, consistent
    with agreement person, not interpretable person. -/
theorem lei_reflexive_is_3p :
    Fragments.Italian.Pronouns.si_refl.person = .third ∧
    Fragments.Italian.Pronouns.ti_refl.person = .second := ⟨rfl, rfl⟩

/-- The fragment's `lei_formal` records LEI with `person := some .second`,
    which is the INTERPRETABLE person. This is consistent with our dual-
    feature analysis. -/
theorem fragment_lei_is_interpretive :
    Fragments.Italian.Pronouns.lei_formal.person = some .second := rfl

-- ============================================================================
-- § 10: All Data Points Match Syntacticosemantic Predictions
-- ============================================================================

/-- Every Italian judgment matches the Weak PCC evaluated over
    interpretable person. Since `weakPCC` checks both IO and DO person,
    this verifies the full constraint, not just DO. -/
theorem all_data_match_syntacticosemantic :
    italianData.all (λ j => (weakPCC j.ioPerson j.doPerson) == j.ok) = true := by
  native_decide

-- ============================================================================
-- § 11: Cross-Linguistic Extension — Spanish USTED (§6.1)
-- ============================================================================

/-- Spanish USTED: agreement 3rd, interpretable 2nd.

    Like Italian LEI, USTED triggers 3sg verbal agreement but refers to
    an addressee. @cite{rezac-2011} observes PCC effects with USTED:
    the accusative clitic `la` is grammatical in a 3>3 configuration
    if its referent is 3rd person, but ungrammatical if interpreted as
    polite USTED (§6.1, (43)). The paper's own consultants confirm the
    same contrast with *encomendar* 'entrust' ((44)). -/
def usted : DualPersonFeatures := ⟨.third, .second⟩

/-- USTED triggers PCC effects under the syntacticosemantic account. -/
theorem usted_pcc : syntacticosemanticPrediction usted = false := rfl

/-- Morphosyntactic account wrongly predicts no PCC effect. -/
theorem usted_morphosyntactic_wrong : morphosyntacticPrediction usted = true := rfl

/-- Italian LEI and Spanish USTED have the same dual-feature structure:
    both are agreement-3rd, interpretable-2nd. -/
theorem lei_usted_isomorphic : lei = usted := rfl

-- ============================================================================
-- § 12: Cross-Linguistic Extension — German SIE (§6.2)
-- ============================================================================

/-- German polite SIE: agreement 3rd (plural), interpretable 2nd.

    SIE triggers 3pl verbal agreement ((45)) and binds 3rd person reflexive
    *sich* (not 2sg *dich* or 2pl *euch*). In the limited PCC environments
    available in German (Wackernagel clusters), SIE patterns with 2nd person
    in triggering person hierarchy effects ((47)–(48)). -/
def sie : DualPersonFeatures := ⟨.third, .second⟩

/-- SIE triggers PCC effects under the syntacticosemantic account. -/
theorem sie_pcc : syntacticosemanticPrediction sie = false := rfl

/-- German assumed-identity copular constructions (§6.2, (49)–(53)) exhibit
    a DIFFERENT person hierarchy effect — one ameliorated by syncretism of
    verbal forms and therefore attributed to exponence/morphology, not to the
    syntax-semantics interface.

    The paper's key modularity argument: PCC effects (syntacticosemantic
    source) are sensitive to interpretable person, so polite pronouns
    trigger them. Assumed-identity effects (exponence-based source) are
    sensitive to formal features, so polite pronouns do NOT trigger them.

    SIE in assumed-identity contexts: interpretable 2nd → would trigger
    PCC-type effects, but agreement 3rd → does not trigger exponence-
    based effects. The data confirms ((52)–(53)): SIE behaves like 3rd
    for assumed-identity, unlike for PCC.

    PCC reads interpretable person → SIE triggers effect.
    Exponence reads agreement person → SIE does NOT trigger effect. -/
theorem sie_pcc_vs_exponence_contrast :
    syntacticosemanticPrediction sie = false ∧
    (sie.agreementPerson == .third) = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 13: The PCC + Politeness Prediction (§6, (40))
-- ============================================================================

/-- The paper's cross-linguistic prediction (40):

    "If a language displays PCC effects in ditransitives for second person
    arguments and has a third person addressee-referring polite pronoun,
    this pronoun should also give rise to PCC effects."

    Formalized: for any pronoun with interpretable 2nd person, the
    syntacticosemantic account predicts a PCC effect in DO position. -/
theorem pcc_politeness_prediction (pol : DualPersonFeatures)
    (h_int : pol.interpretablePerson = .second) :
    syntacticosemanticPrediction pol = false := by
  unfold syntacticosemanticPrediction weakPCC; rw [h_int]; rfl

/-- The morphosyntactic account wrongly predicts NO PCC effect for
    any polite pronoun with 3rd person agreement features. -/
theorem morphosyntactic_misses_polite (pol : DualPersonFeatures)
    (h_agr : pol.agreementPerson = .third) :
    morphosyntacticPrediction pol = true := by
  unfold morphosyntacticPrediction weakPCC; rw [h_agr]; rfl

/-- All three cross-linguistic polite pronouns (LEI, USTED, SIE) are
    correctly predicted by the syntacticosemantic account. -/
theorem all_polite_pronouns_predicted :
    syntacticosemanticPrediction lei = false ∧
    syntacticosemanticPrediction usted = false ∧
    syntacticosemanticPrediction sie = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 14: Summary — What the Mismatch Tells Us
-- ============================================================================

/-- Only mismatch pronouns distinguish the two accounts. For any pronoun
    where agreement and interpretable person coincide, both accounts make
    the same prediction. Polite pronouns are the crucial test case. -/
theorem mismatch_is_crucial (d : DualPersonFeatures)
    (h : d.agreementPerson = d.interpretablePerson) :
    morphosyntacticPrediction d = syntacticosemanticPrediction d := by
  simp only [morphosyntacticPrediction, syntacticosemanticPrediction, h]

end Phenomena.Agreement.Studies.AdamsonZompi2025
