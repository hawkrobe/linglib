import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Logophoricity
import Linglib.Features.Empathy
import Linglib.Features.Person
import Linglib.Fragments.Spanish.Clitics

/-!
# Charnavel & Mateu (2015): The Clitic Logophoric Restriction
@cite{charnavel-mateu-2015} @cite{sells-1987} @cite{kuno-1987}

The Clitic Binding Restriction Revisited: Evidence for Antilogophoricity.
*The Linguistic Review* 32(4).

## Summary

@cite{charnavel-mateu-2015} (C&M) reanalyze the restriction on accusative
clitics in Romance clitic clusters. Earlier work (Bhatt & Šimík 2009)
attributed the restriction to *binding*; C&M's grammaticality experiment
(97 French + 35 Spanish speakers, 9 conditions) shows that the relevant
factor is **antilogophoricity**, not binding. Their generalization (eq. 26):

> **Clitic Logophoric Restriction (CLR)**: When a third person dative clitic
> and an accusative clitic co-occur in a cluster, the accusative clitic
> cannot corefer with a logophoric center.

## Local apparatus

C&M propose a three-level hierarchy of logophoric centers (eq. 53–54):
discourse participant > empathy locus > attitude holder. Each center is
characterised by a feature subset of `{A, B, C}` (eq. 63):
- discourse participant = `{A, B}`
- empathy locus = `{B, C}`
- attitude holder = `{C}`

Antilogophoric clash occurs when two centers in the same domain share a
feature (equivalent to: two adjacent-or-identical positions on the
hierarchy). PCC and CLR are both instances:
- PCC = discourse participant + empathy locus (share `B`)
- CLR = empathy locus + attitude holder (share `C`)

## Disagreement with @cite{pancheva-zubizarreta-2018}

C&M unify CLR and PCC under one mechanism. P&Z (page 1308) explicitly
disagree: "We do not think the CLR and the PCC should be unified along
the lines suggested by Charnavel and Mateu (2015). The two phenomena are
related but nevertheless distinct." The cross-paper bridge file
`Phenomena/Anaphora/Antilogophoricity.lean` documents this disagreement
explicitly.
-/

namespace Phenomena.Anaphora.Studies.CharnavelMateu2015

open Features.Prominence (PersonLevel)

-- ============================================================================
-- § 1: Logophoric Centers (paper §3.5.2, eq. 53)
-- ============================================================================

/-- Three types of logophoric center, ordered by degree of perspective
    integration in the discourse (paper eq. 54: discourse participant >
    empathy locus > attitude holder). -/
inductive LogoCenter : Type where
  /-- Speaker / addressee — directly defining the discourse. -/
  | discourseParticipant
  /-- Event participant the speaker empathizes with (Kuno's empathy locus).
      In Romance, typically the 3rd-person dative clitic. -/
  | empathyLocus
  /-- Attitude holder whose thoughts/discourse are reported.
      In Romance, typically a 3rd-person accusative clitic read *de se*. -/
  | attitudeHolder
  deriving DecidableEq, Repr, Fintype

-- ============================================================================
-- § 2: Feature System (paper §3.6, eq. 63)
-- ============================================================================

/-- The three abstract logophoric features. `B` expresses the
    speaker-component (shared by discourse participants and empathy loci);
    `C` expresses perspectival distance from the speaker (shared by empathy
    loci and attitude holders). -/
inductive LogoFeature : Type
  | A | B | C
  deriving DecidableEq, Repr, Fintype

/-- Feature decomposition (paper eq. 63). -/
def LogoCenter.features : LogoCenter → Finset LogoFeature
  | .discourseParticipant => {.A, .B}
  | .empathyLocus         => {.B, .C}
  | .attitudeHolder       => {.C}

-- ============================================================================
-- § 3: Antilogophoric Intervention (paper §3.5.2)
-- ============================================================================

/-- Two centers clash iff their feature sets share at least one feature.
    Equivalent to "identical or adjacent on the hierarchy" (paper eq. 54). -/
def Clash (x y : LogoCenter) : Prop := (x.features ∩ y.features).Nonempty

instance (x y : LogoCenter) : Decidable (Clash x y) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- C&M's antilogophoric intervention (paper §3.5.2, generalising eq. 64):
    a configuration of logophoric centers in a single domain is
    antilogophoric iff some pair of distinct centers clash.

    Note: a single center never clashes with itself in this formulation —
    the "identical centers" case of (54) corresponds to multiple *positions*
    bearing the same center type, not the abstract type clashing with
    itself. We model the multi-position case with a `List`. -/
def Antilogophoric (centers : List LogoCenter) : Prop :=
  ∃ i j : Fin centers.length, i ≠ j ∧ Clash centers[i] centers[j]

instance (centers : List LogoCenter) : Decidable (Antilogophoric centers) :=
  inferInstanceAs (Decidable (∃ _ : Fin _, _))

-- ============================================================================
-- § 4: Predictions of Table 3 (paper §3.5.2)
-- ============================================================================

/-- PCC clash: discourse participant (1/2 clitic) + empathy locus
    (3.dat clitic) share feature `B`. -/
theorem pcc_clash : Clash .discourseParticipant .empathyLocus := by decide

/-- CLR clash: empathy locus (3.dat) + attitude holder (3.acc *de se*)
    share feature `C`. -/
theorem clr_clash : Clash .empathyLocus .attitudeHolder := by decide

/-- Discourse participant + attitude holder do **not** clash — no shared
    feature. This is the licit configuration (Table 3 final row). -/
theorem dp_ah_no_clash : ¬ Clash .discourseParticipant .attitudeHolder := by
  decide

/-- The full Table 3 prediction: clash iff the pair shares a feature. -/
theorem table3_predictions :
    Clash .discourseParticipant .discourseParticipant ∧   -- PCC: *me/te me/te
    Clash .discourseParticipant .empathyLocus ∧           -- PCC: *me/te lui
    Clash .empathyLocus .empathyLocus ∧                   -- vacuous configuration
    Clash .attitudeHolder .empathyLocus ∧                 -- CLR
    Clash .attitudeHolder .attitudeHolder ∧               -- CLR
    ¬ Clash .discourseParticipant .attitudeHolder := by   -- licit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 5: Experimental Conditions (paper §2.3, Table 1)
-- ============================================================================

/-- A test condition in C&M's grammaticality experiment, parameterised by
    the three crossed factors (paper Table 1). The 9 conditions enumerate
    {c-command, no c-command} × {logophoric centre as antecedent, not} ×
    {3.dat dative clitic, 1/2.dat dative clitic}, dropping the "bound 3"
    sub-case (their condition 3) for which they collapse the same
    prediction as condition 1. -/
structure Condition where
  /-- Does the antecedent c-command the accusative clitic? -/
  cCommandingAntecedent : Bool
  /-- Is the antecedent a logophoric centre (attitude holder)? -/
  logoCenterAntecedent : Bool
  /-- Is the dative clitic a 3rd-person form (an empathy locus)? -/
  dative3rdPerson : Bool
  deriving DecidableEq, Repr

/-- C&M's hypothesis (paper §2.1): a sentence is ungrammatical iff the
    antecedent of the accusative clitic is a logophoric centre AND the
    dative clitic is 3rd person. C-command is **not** the relevant factor
    (contra Bhatt & Šimík). -/
def predictsUngrammatical (c : Condition) : Prop :=
  c.logoCenterAntecedent = true ∧ c.dative3rdPerson = true

instance (c : Condition) : Decidable (predictsUngrammatical c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Paper Table 2: the experimental result. Conditions 1, 3, 6 (the three
    rows with logo-centre antecedent + 3.dat) received significantly lower
    scores than controls; the other six conditions did not. We collapse
    Table 1's "bound 3" condition into the 3.dat case. -/
theorem table2_results :
    -- Cond 1: c-cmd=yes, logo=yes, dat=3 → *
    predictsUngrammatical ⟨true, true, true⟩ ∧
    -- Cond 2: c-cmd=yes, logo=yes, dat=1/2 → OK
    ¬ predictsUngrammatical ⟨true, true, false⟩ ∧
    -- Cond 4: c-cmd=yes, logo=no, dat=3 → OK
    ¬ predictsUngrammatical ⟨true, false, true⟩ ∧
    -- Cond 5: c-cmd=yes, logo=no, dat=1/2 → OK
    ¬ predictsUngrammatical ⟨true, false, false⟩ ∧
    -- Cond 6: c-cmd=no, logo=yes, dat=3 → * (the key finding: c-cmd irrelevant)
    predictsUngrammatical ⟨false, true, true⟩ ∧
    -- Cond 7: c-cmd=no, logo=yes, dat=1/2 → OK
    ¬ predictsUngrammatical ⟨false, true, false⟩ ∧
    -- Cond 8: c-cmd=no, logo=no, dat=3 → OK
    ¬ predictsUngrammatical ⟨false, false, true⟩ ∧
    -- Cond 9: c-cmd=no, logo=no, dat=1/2 → OK
    ¬ predictsUngrammatical ⟨false, false, false⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The key empirical finding (paper §2.4, conditions 4 vs 6):
    c-command is irrelevant; only logophoric centrehood + 3rd-person
    dative matter. -/
theorem c_command_irrelevant
    (logoCenter dative3rd : Bool) :
    predictsUngrammatical ⟨true, logoCenter, dative3rd⟩ ↔
    predictsUngrammatical ⟨false, logoCenter, dative3rd⟩ := by
  cases logoCenter <;> cases dative3rd <;> decide

-- ============================================================================
-- § 6: CLR as a Special Case of Antilogophoricity (paper eq. 26 + §3.4)
-- ============================================================================

/-- A clitic-cluster configuration as a list of two logophoric centres
    (one for each clitic). The dative is read first, then the accusative. -/
def ClusterConfig : Type := LogoCenter × LogoCenter

/-- The Clitic Logophoric Restriction (paper eq. 26): a configuration is
    blocked when its two centres are antilogophoric. -/
def CLRViolated (cfg : ClusterConfig) : Prop :=
  Clash cfg.1 cfg.2

instance (cfg : ClusterConfig) : Decidable (CLRViolated cfg) :=
  inferInstanceAs (Decidable (Clash _ _))

/-- The canonical CLR configuration: 3.dat (empathy locus) + 3.acc *de se*
    (attitude holder). Violation. -/
theorem canonical_clr : CLRViolated (.empathyLocus, .attitudeHolder) := by decide

/-- The canonical PCC configuration in C&M's terms: 3.dat (empathy locus) +
    1/2.acc (discourse participant). Violation under the same mechanism. -/
theorem canonical_pcc : CLRViolated (.empathyLocus, .discourseParticipant) := by
  decide

/-- C&M's unification claim (paper §3.4): both phenomena are instances of
    `CLRViolated`. The bridge file documents P&Z's dissent. -/
theorem cm_unification :
    CLRViolated (.empathyLocus, .attitudeHolder) ∧
    CLRViolated (.empathyLocus, .discourseParticipant) := ⟨by decide, by decide⟩

-- ============================================================================
-- § 7: Spanish Anchoring (Fragments.Spanish.Clitics)
-- ============================================================================

/-- Spanish *me lo* — 1.DAT.ACC. Under C&M's typology, the 1.dat clitic is
    a discourse participant; *lo* is the accusative. The cluster is licit
    when *lo* is **not** read with an attitude-holder antecedent
    (paper §1.1, ex. 6 type: licit accusative). -/
theorem spanish_me_lo_dat_is_discourse :
    Fragments.Spanish.Clitics.me_dat.person = .first ∧
    Fragments.Spanish.Clitics.lo.person = .third := ⟨rfl, rfl⟩

/-- Spanish *te lo* — 2.DAT + 3.ACC. Same pattern: 2.dat is a discourse
    participant; the cluster is licit on non-attitude-holder readings. -/
theorem spanish_te_lo_dat_is_discourse :
    Fragments.Spanish.Clitics.te_dat.person = .second ∧
    Fragments.Spanish.Clitics.lo.person = .third := ⟨rfl, rfl⟩

/-- Spanish *le lo* (which surfaces as *se lo* by the spurious-se rule):
    3.DAT + 3.ACC. The CLR-relevant configuration — empathy locus +
    attitude holder. Bad under *de se* readings of *lo*
    (paper §1, ex. 2b; §3.4 implementation). -/
theorem spanish_le_lo_is_clr_pair :
    Fragments.Spanish.Clitics.le_dat.person = .third ∧
    Fragments.Spanish.Clitics.lo.person = .third := ⟨rfl, rfl⟩

/-- The clash-yielding cluster for Spanish *se lo* / *le lo* under
    a *de se* reading: empathy + attitude holder. -/
theorem spanish_le_lo_de_se_violates_clr :
    CLRViolated (.empathyLocus, .attitudeHolder) := by decide

/-- The PCC pattern *le me / *le te in Spanish: 3.dat + 1/2.acc — empathy
    locus + discourse participant. -/
theorem spanish_le_me_pcc_violates :
    Fragments.Spanish.Clitics.le_dat.person = .third ∧
    Fragments.Spanish.Clitics.me_acc.person = .first ∧
    CLRViolated (.empathyLocus, .discourseParticipant) := ⟨rfl, rfl, by decide⟩

end Phenomena.Anaphora.Studies.CharnavelMateu2015
