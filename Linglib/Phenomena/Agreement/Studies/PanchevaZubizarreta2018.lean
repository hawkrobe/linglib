import Linglib.Theories.Syntax.Minimalism.PConstraint
import Linglib.Features.Person
import Linglib.Fragments.Italian.Pronouns
import Linglib.Fragments.Spanish.Clitics

/-!
# Pancheva & Zubizarreta (2018): The Person Case Constraint
@cite{pancheva-zubizarreta-2018} @cite{sells-1987}

The Person Case Constraint: The Syntactic Encoding of Perspective.
*Natural Language and Linguistic Theory* 36: 1291–1337.

## Summary

Empirical predictions of the P-Constraint theory (formalized in
`Theories/Syntax/Minimalism/PConstraint.lean`) for the eight grammar
instances P&Z discuss: five attested PCC varieties (strong, ultra-strong,
weak, super-strong, me-first) plus three predicted varieties (PG1, PG2,
PG3) that the four-parameter space generates.

## Key derivations (beyond per-cell predictions)

- **`personHierarchy_from_features`** — the paper's central claim that the
  Person Hierarchy 1P > 2P > 3P is *derived* from the count of positive
  features in `decomposePerson` (§2.1, p. 1296), not stipulated.
- **`isLicit_imp_io_pov`** — the four parametric clauses are recovered as
  the conditions under which selecting the IO as point-of-view center
  satisfies the P-Constraint semantically (§6.3, eq. 48).
- **`prominence_logophoric_role`** — the explicit
  `PProminence ≃ LogophoricRole` correspondence the paper draws in §6.2.

## Forward references

This study is extended by @cite{adamson-zompi-2025} (study file
`AdamsonZompi2025.lean`), who use the dual-feature distinction to argue
that PCC effects diagnose *interpretable* (not agreement) person.
-/

namespace Phenomena.Agreement.Studies.PanchevaZubizarreta2018

open Features.Prominence (PersonLevel)
open Features.Logophoricity (LogophoricRole pointOfViewPrinciple)
open Minimalism (DecomposedPerson decomposePerson)
open Minimalism.PConstraint

-- ============================================================================
-- § 1: Person Hierarchy as Derived (paper §2.1)
-- ============================================================================

/-- Number of positive features in a person decomposition. By the
    implicational hierarchy of (paper eq. 11), 1P bears all three
    (proximate, participant, author), 2P bears two, 3P bears none. -/
def positiveFeatureCount (dp : DecomposedPerson) : ℕ :=
  (if dp.hasProximate then 1 else 0) +
  (if dp.hasParticipant then 1 else 0) +
  (if dp.hasAuthor then 1 else 0)

/-- The numeric values of `positiveFeatureCount` per person. -/
theorem positiveFeatureCount_values :
    positiveFeatureCount (decomposePerson .first) = 3 ∧
    positiveFeatureCount (decomposePerson .second) = 2 ∧
    positiveFeatureCount (decomposePerson .third) = 0 := by decide

/-- **The Person Hierarchy is derived, not stipulated** (paper §2.1, p. 1296:
    "We seek to derive it from more fundamental principles"). The order
    induced by `PersonLevel.rank` (1P > 2P > 3P) coincides with the order
    induced by the count of positive features in the decomposition.

    Note: The two functions are not pointwise equal (3 vs 2, 2 vs 1, 0 vs 0)
    because `rank` collapses the SAP/non-SAP gap, but the orders match. -/
theorem personHierarchy_from_features (p q : PersonLevel) :
    p.rank ≤ q.rank ↔
    positiveFeatureCount (decomposePerson p) ≤
    positiveFeatureCount (decomposePerson q) := by
  cases p <;> cases q <;> decide

-- ============================================================================
-- § 2: Per-Grammar Empirical Predictions (paper §4)
-- ============================================================================

/-- Strong PCC (paper §4.1.1, eq. 14a): DO must be 3P. -/
theorem strong_predictions :
    licitFinset strongGrammar =
      {(.first, .third), (.second, .third), (.third, .third)} := by decide

/-- Ultra-strong PCC (§4.1.2, eq. 14d): adds P-Primacy, so 1P-IO can rescue
    1P/2P DO. ⟨1,2⟩ allowed but ⟨2,1⟩ banned. -/
theorem ultra_predictions :
    licitFinset ultraStrongGrammar =
      {(.first, .first), (.first, .second), (.first, .third),
       (.second, .third), (.third, .third)} := by decide

/-- Weak PCC (§4.1.3, eq. 14b): drops P-Uniqueness, so any SAP IO licenses
    any DO. Bans only 3P-IO with 1P/2P DO. -/
theorem weak_predictions :
    licitFinset weakGrammar =
      {(.first, .first), (.first, .second), (.first, .third),
       (.second, .first), (.second, .second), (.second, .third),
       (.third, .third)} := by decide

/-- Super-strong PCC (§4.2, eq. 14e): IO must be SAP, DO must be 3P.
    Strictly the most restrictive variety. -/
theorem super_predictions :
    licitFinset superStrongGrammar =
      {(.first, .third), (.second, .third)} := by decide

/-- Me-first PCC (§4.3, eq. 14c): bans 1P DO with non-1P IO; restricted
    domain exempts ⟨2P,2P⟩, ⟨2P,3P⟩, ⟨3P,2P⟩, ⟨3P,3P⟩ entirely.

    NB: The implementation also bans ⟨1P,1P⟩ via P-Uniqueness. The paper
    (§4.3, p. 1314: "allows all other combinations") does not explicitly
    address this case; see `mefirst_one_one_excluded` below. -/
theorem mefirst_predictions :
    licitFinset meFirstGrammar =
      {(.first, .second), (.first, .third),
       (.second, .second), (.second, .third),
       (.third, .second), (.third, .third)} := by decide

/-- PG1 (predicted, §4.5, eq. 32a-ii): [+participant] + P-Primacy. -/
theorem pg1_predictions :
    licitFinset pg1Grammar =
      {(.first, .first), (.first, .second), (.first, .third),
       (.second, .third)} := by decide

/-- PG2 (predicted, §4.5, eq. 32b): [+participant], no P-Uniqueness. -/
theorem pg2_predictions :
    licitFinset pg2Grammar =
      {(.first, .first), (.first, .second), (.first, .third),
       (.second, .first), (.second, .second), (.second, .third)} := by decide

/-- PG3 (predicted, §4.5, eq. 33): [+author] with unrestricted domain.
    Only 1P-IO is licensed; uniqueness then rules out 1P-DO. -/
theorem pg3_predictions :
    licitFinset pg3Grammar =
      {(.first, .second), (.first, .third)} := by decide

-- ============================================================================
-- § 3: Licit Counts (kernel-checkable)
-- ============================================================================

theorem licit_counts :
    licitCount strongGrammar = 3 ∧
    licitCount ultraStrongGrammar = 5 ∧
    licitCount weakGrammar = 7 ∧
    licitCount superStrongGrammar = 2 ∧
    licitCount meFirstGrammar = 6 ∧
    licitCount pg1Grammar = 4 ∧
    licitCount pg2Grammar = 6 ∧
    licitCount pg3Grammar = 2 := by decide

-- ============================================================================
-- § 4: Markedness Table (paper §4.5, eq. 31)
-- ============================================================================

/-- The markedness rank of each grammar as the number of parameter
    departures from the strong PCC default. Strong is the unique 0-rank
    grammar; the four 1-rank grammars (ultra/weak/super/pg3) are the
    "minimal departures"; the three 2-rank grammars (me-first/pg1/pg2)
    are doubly marked. -/
theorem markedness_table :
    parameterDepartures strongGrammar = 0 ∧
    parameterDepartures ultraStrongGrammar = 1 ∧
    parameterDepartures weakGrammar = 1 ∧
    parameterDepartures superStrongGrammar = 1 ∧
    parameterDepartures pg3Grammar = 1 ∧
    parameterDepartures meFirstGrammar = 2 ∧
    parameterDepartures pg1Grammar = 2 ∧
    parameterDepartures pg2Grammar = 2 := by decide

-- ============================================================================
-- § 5: Entailment (Preorder via licit-set containment)
-- ============================================================================

/-- Strong PCC entails Weak PCC: every cell licit in strong is licit in
    weak. Falls out of the `Preorder PCCGrammar` instance. -/
theorem strong_le_weak : strongGrammar ≤ weakGrammar := by decide

/-- Strong PCC entails Ultra-strong PCC. -/
theorem strong_le_ultra : strongGrammar ≤ ultraStrongGrammar := by decide

/-- Super-strong PCC entails Strong PCC: super-strong's prominence on
    [+participant] is strictly more restrictive than strong's on
    [+proximate]. -/
theorem super_le_strong : superStrongGrammar ≤ strongGrammar := by decide

-- ============================================================================
-- § 6: Logophoric Bridge (paper §6.2)
-- ============================================================================

/-- The three P-Prominence settings correspond to the three logophoric
    roles of @cite{sells-1987}: a [+proximate]-grammar IO is interpreted
    as a pivot, [+participant] as a self, [+author] as a source. -/
theorem prominence_logophoric_role :
    PProminence.equivLogophoric .proximate = .pivot ∧
    PProminence.equivLogophoric .participant = .self ∧
    PProminence.equivLogophoric .author = .source := ⟨rfl, rfl, rfl⟩

/-- The five attested grammars and the [+author]-prominence predicted
    family map onto the logophoric hierarchy: strong/ultra/weak ⇒ pivot,
    super ⇒ self, me-first/pg3 ⇒ source. -/
theorem family_logophoric_assignments :
    PProminence.equivLogophoric strongGrammar.prominence = .pivot ∧
    PProminence.equivLogophoric ultraStrongGrammar.prominence = .pivot ∧
    PProminence.equivLogophoric weakGrammar.prominence = .pivot ∧
    PProminence.equivLogophoric superStrongGrammar.prominence = .self ∧
    PProminence.equivLogophoric meFirstGrammar.prominence = .source ∧
    PProminence.equivLogophoric pg3Grammar.prominence = .source := by decide

-- ============================================================================
-- § 7: Point-of-View Derivation (paper §6.3, eq. 48)
-- ============================================================================

/-- Whenever ⟨IO, DO⟩ is licit, selecting the IO as point-of-view center
    yields an Appl domain that semantically satisfies the P-Constraint.
    The four parametric clauses in (12) are not free-standing stipulations:
    they are precisely the conditions on IO-as-POV consistency. -/
theorem isLicit_imp_io_pov (g : PCCGrammar) (io do_ : PersonLevel) :
    IsLicit g io do_ → PConstraintSatisfied g ⟨io, do_, io⟩ := by
  rintro (h | ⟨hprom, hrest⟩)
  · exact Or.inl h
  · exact Or.inr ⟨rfl, hprom, hrest⟩

/-- Conversely, if any Appl domain over ⟨io, do_⟩ with IO as POV center
    satisfies the P-Constraint, the combination is licit. Together with
    `isLicit_imp_io_pov`, this characterizes `IsLicit` semantically. -/
theorem io_pov_imp_isLicit (g : PCCGrammar) (io do_ : PersonLevel) :
    PConstraintSatisfied g ⟨io, do_, io⟩ → IsLicit g io do_ := by
  rintro (h | ⟨_, hprom, hrest⟩)
  · exact Or.inl h
  · exact Or.inr ⟨hprom, hrest⟩

/-- For [+participant] and [+author] grammars, the IO-as-POV semantics
    automatically interprets the IO as an attitude holder (`self` or
    `source`). The Point-of-View Principle (eq. 48) then holds with the
    AH = POV identification. -/
theorem pov_principle_at_io_attitude_grammar :
    pointOfViewPrinciple true true = true := rfl

-- ============================================================================
-- § 8: Cross-Linguistic Anchors (paper §4)
--
-- Where Fragment clitic data exists (Italian, Spanish), the PCC
-- predictions are derived from the actual fragment forms via
-- `PersonLevel.ofUDPerson`. For French, Catalan, Kambera, Bulgarian no
-- ditransitive-clitic fragment is yet defined in linglib, so the
-- predictions cite paper examples but read directly off the parameter
-- settings. Adding `Fragments/{French,Catalan,Bulgarian}/Pronouns.lean`
-- would let those theorems be similarly grounded.
-- ============================================================================

open Features.Prominence (PersonLevel)

/-- Helper: extract a `PersonLevel` from a clitic entry whose `person`
    field is a `UD.Person`. Returns `none` only on `.zero` (impersonal),
    which object clitics never bear. -/
private def cliticLevel? (p : UD.Person) : Option PersonLevel :=
  PersonLevel.ofUDPerson p

-- ── Italian (Romance, weak ∼ strong PCC variation per @cite{adamson-zompi-2025}) ──

/-- Italian dative *gli* is 3rd person; accusative *ti* is 2nd. The weak
    PCC prediction ⟨3,2⟩ ⇒ illicit is therefore satisfied at these two
    actual clitic forms. -/
theorem italian_weak_glidat_tiacc :
    cliticLevel? Fragments.Italian.Pronouns.gli_dat.person = some .third ∧
    cliticLevel? Fragments.Italian.Pronouns.ti_acc.person = some .second ∧
    ¬ IsLicit weakGrammar .third .second := ⟨rfl, rfl, by decide⟩

/-- The Italian licit pair *ti la* (2.DAT > 3.ACC) under weak PCC. -/
theorem italian_weak_tidat_lacl :
    cliticLevel? Fragments.Italian.Pronouns.ti_dat.person = some .second ∧
    cliticLevel? Fragments.Italian.Pronouns.la_cl.person = some .third ∧
    IsLicit weakGrammar .second .third := ⟨rfl, rfl, by decide⟩

-- ── Spanish (weak PCC dialect, paper §4.1.3, ex. 23–24) ──

/-- Spanish *te me* (2.DAT > 1.ACC) is licit under weak PCC. The
    interpretable persons are read off the actual `te_dat`/`me_acc` clitic
    forms in `Fragments/Spanish/Clitics.lean`. -/
theorem spanish_weak_tedat_meacc :
    cliticLevel? Fragments.Spanish.Clitics.te_dat.person = some .second ∧
    cliticLevel? Fragments.Spanish.Clitics.me_acc.person = some .first ∧
    IsLicit weakGrammar .second .first := ⟨rfl, rfl, by decide⟩

/-- Spanish *me te* (1.DAT > 2.ACC) is also licit (weak PCC ⟨1,2⟩). -/
theorem spanish_weak_medat_teacc :
    cliticLevel? Fragments.Spanish.Clitics.me_dat.person = some .first ∧
    cliticLevel? Fragments.Spanish.Clitics.te_acc.person = some .second ∧
    IsLicit weakGrammar .first .second := ⟨rfl, rfl, by decide⟩

/-- Spanish *le me* (3.DAT > 1.ACC) is illicit (paper ex. 24). -/
theorem spanish_weak_ledat_meacc_banned :
    cliticLevel? Fragments.Spanish.Clitics.le_dat.person = some .third ∧
    cliticLevel? Fragments.Spanish.Clitics.me_acc.person = some .first ∧
    ¬ IsLicit weakGrammar .third .first := ⟨rfl, rfl, by decide⟩

-- ── French / Catalan / Kambera / Bulgarian (no Fragment yet) ──

/-- French strong PCC (§4.1.1, ex. 16): *Elle te me présentera.
    No `Fragments/French/Pronouns.lean` exists; theorem reads off the
    parameter settings rather than fragment data. -/
theorem french_strong_examples :
    ¬ IsLicit strongGrammar .third .first ∧            -- *3.DAT > 1.ACC
    IsLicit strongGrammar .second .third ∧             -- 2.DAT > 3.ACC
    IsLicit strongGrammar .third .third := by decide   -- 3.DAT > 3.ACC

/-- Catalan ultra-strong PCC (§4.1.2, ex. 20): the ⟨1,2⟩ vs ⟨2,1⟩
    asymmetry that distinguishes ultra-strong from strong. -/
theorem catalan_ultra_strong_examples :
    IsLicit ultraStrongGrammar .first .second ∧        -- me l' (1.DAT > 3.ACC as ⟨1,2⟩)
    ¬ IsLicit ultraStrongGrammar .second .first := by  -- *me li (2.DAT > 1.ACC)
  decide

/-- Kambera super-strong PCC (§4.2, ex. 27): IO must be SAP, DO must be
    3P; ⟨3,3⟩ is also banned. -/
theorem kambera_super_strong_examples :
    IsLicit superStrongGrammar .first .third ∧         -- ngga (gives it to me)
    IsLicit superStrongGrammar .second .third ∧        -- nggau (gives it to you)
    ¬ IsLicit superStrongGrammar .third .third ∧       -- *(gives it to them)
    ¬ IsLicit superStrongGrammar .first .second := by  -- *(gives you to me)
  decide

/-- Bulgarian me-first PCC (§4.3, ex. 29): only ⟨2,1⟩ and ⟨3,1⟩ banned;
    crucially, ⟨3,2⟩ is licit (where it is illicit in all
    [+proximate] varieties). -/
theorem bulgarian_me_first_examples :
    IsLicit meFirstGrammar .third .second ∧            -- mu te (3.DAT > 2.ACC)
    ¬ IsLicit meFirstGrammar .second .first := by      -- *ti me (2.DAT > 1.ACC)
  decide

-- ============================================================================
-- § 9: Documentation of substantive commitments beyond the paper
-- ============================================================================

/-- The implementation rules out ⟨1P, 1P⟩ in me-first by P-Uniqueness on
    [+author]: both arguments are [+author], so neither can be uniquely
    the perspectival source. The paper (§4.3) explicitly bans only ⟨3,1⟩
    and ⟨2,1⟩, leaving ⟨1,1⟩ unaddressed. The implementation's verdict
    follows from (12c) applied to two coreferential [+author] DPs. -/
theorem mefirst_one_one_excluded : ¬ IsLicit meFirstGrammar .first .first := by
  decide

/-- The me-first family does not show *⟨3,3⟩ effects: 3P-IO with 3P-DO
    is domain-exempt (no [+author] DP triggers the constraint), so the
    spurious-se restriction documented for [+proximate] varieties is
    structurally unavailable here (paper §4.4). -/
theorem mefirst_three_three_exempt :
    IsLicit meFirstGrammar .third .third := by decide

end Phenomena.Agreement.Studies.PanchevaZubizarreta2018
