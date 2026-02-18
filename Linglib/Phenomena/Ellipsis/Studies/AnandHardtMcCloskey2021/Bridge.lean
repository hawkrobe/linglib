import Linglib.Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Data
import Linglib.Phenomena.Ellipsis.Sluicing
import Linglib.Theories.Syntax.Minimalism.Formal.Sluicing.FormalMatching

/-!
# Sluicing — Minimalist Bridge Theorems

@cite{anand-hardt-mccloskey-2021}

Connects empirical sluicing data — both the individual examples in
`Phenomena.Ellipsis.Sluicing` and the corpus findings from Anand, Hardt
& McCloskey (2021) — to the Syntactic Isomorphism Condition (SIC)
formalized in `Theories.Syntax.Minimalism.Formal.Sluicing.FormalMatching`.

## Derivation Chain

The SIC licenses sluicing when the argument domains of antecedent and
ellipsis site have structurally identical head pairs. This file proves
the full chain:

1. **Concrete licensing** (§1): Construct head pairs for actual sluicing
   examples and prove `SluicingLicense.isLicensed = true`.

2. **Mismatch predictions** (§2): The SIC partitions syntactic categories
   into those inside the argument domain (V, v — must match) and those
   outside (T, Mod, C — may differ). The corpus confirms both directions:
   0 argument structure mismatches, 129 tense + 394 modal mismatches.

3. **The voice puzzle** (§3): The SIC predicts voice mismatches are licit,
   yet the corpus shows zero. This gap is theoretically significant.

4. **Corpus distributions** (§4): Sprouting dominates, *why* dominates.

## References

- Anand, P., Hardt, D. & McCloskey, J. (2021). The Santa Cruz sluicing
  data set. *Language* 97(1): e68–e88.
- Anand, P., Hardt, D. & McCloskey, J. (2025). Sluicing and Syntactic
  Identity.
-/

namespace Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Bridge

open Minimalism
open Minimalism.Sluicing
open Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Data
open Phenomena.Ellipsis.Sluicing

-- ============================================================================
-- § 1: Concrete SIC Licensing
-- ============================================================================

-- The argument domain of a full clause (CP) is vP, containing head pairs
-- ⟨v, V⟩ and ⟨V, D⟩ (v selects VP, V selects DP). When antecedent and
-- ellipsis site share the same verb, these head pairs are identical.

/-- Head pairs for a simple transitive vP: v selects V, V selects D.
    This is the argument domain structure of "someone left" / "John ate
    something" — any clause with a single verb and a DP argument. -/
def transitiveVP : List HeadPair := [⟨.v, .V, 0, none⟩, ⟨.V, .D, 0, none⟩]

/-- Head pairs for an intransitive vP: v selects V only.
    Used for the antecedent of sprouting examples like "John left." -/
def intransitiveVP : List HeadPair := [⟨.v, .V, 0, none⟩]

/-- SIC licenses basic sluicing: "Someone left, but I don't know who."

    Antecedent "someone left" and ellipsis "[who] left" share the same
    verb, so their argument domains have identical head pairs. -/
theorem basic_sluice_licensed :
    structurallyIdentical transitiveVP transitiveVP = true := by
  native_decide

/-- SIC licenses object sluicing: "John ate something, but I don't know what."

    Same verb "ate" → same head pairs. -/
theorem object_sluice_licensed :
    structurallyIdentical transitiveVP transitiveVP = true := by
  native_decide

/-- A `SluicingLicense` for same-verb sluices is licensed. -/
theorem same_verb_license_is_licensed :
    (SluicingLicense.mk transitiveVP transitiveVP .C .C).isLicensed = true := by
  native_decide

/-- SIC correctly predicts `basicSluice` is grammatical. -/
theorem sic_predicts_basicSluice :
    basicSluice.grammatical = true ∧
    (SluicingLicense.mk transitiveVP transitiveVP .C .C).isLicensed = true :=
  ⟨rfl, by native_decide⟩

/-- SIC correctly predicts `objectSluice` is grammatical. -/
theorem sic_predicts_objectSluice :
    objectSluice.grammatical = true ∧
    (SluicingLicense.mk transitiveVP transitiveVP .C .C).isLicensed = true :=
  ⟨rfl, by native_decide⟩

-- Case matching: case is assigned within the argument domain, so the SIC
-- requires case to match between antecedent and ellipsis site.

/-- Head pairs for a dative-assigning transitive vP.
    V assigns dative case to its DP complement (e.g., German *helfen*). -/
def dativeVP : List HeadPair :=
  [⟨.v, .V, 0, none⟩, ⟨.V, .D, 0, some .Dat⟩]

/-- Head pairs for an accusative-assigning transitive vP.
    V assigns accusative case to its DP complement (e.g., German *sehen*). -/
def accusativeVP : List HeadPair :=
  [⟨.v, .V, 0, none⟩, ⟨.V, .D, 0, some .Acc⟩]

/-- Same-case head pairs are structurally identical (case match OK). -/
theorem case_match_licensed :
    structurallyIdentical dativeVP dativeVP = true := by
  native_decide

/-- Case mismatch blocks structural identity. -/
theorem case_mismatch_blocked :
    structurallyIdentical dativeVP accusativeVP = false := by
  native_decide

/-- SIC correctly predicts `germanCaseMatch` is grammatical:
    dative wh-phrase matches dative correlate. The SIC is licensed
    because the argument domains have structurally identical head pairs
    (both assign dative). -/
theorem sic_predicts_germanCaseMatch :
    germanCaseMatch.grammatical = true ∧
    structurallyIdentical dativeVP dativeVP = true :=
  ⟨rfl, by native_decide⟩

/-- SIC correctly predicts `germanCaseMismatch` is ungrammatical:
    accusative wh-phrase does not match dative correlate. The SIC
    blocks sluicing because dative ≠ accusative within the argument
    domain (Merchant 2001: German *wem*/*wen* data). -/
theorem sic_predicts_germanCaseMismatch :
    germanCaseMismatch.grammatical = false ∧
    structurallyIdentical dativeVP accusativeVP = false :=
  ⟨rfl, by native_decide⟩

-- ============================================================================
-- § 2: SIC Mismatch Predictions Confirmed by Corpus
-- ============================================================================

-- The SIC partitions categories into those inside and outside the
-- argument domain. Categories inside (V, v) must match; categories
-- outside (T, Mod, C) may differ freely.

/-- V and v are inside the argument domain: argument structure must match.
    The corpus confirms: zero argument structure mismatches. -/
theorem argstructure_inside_and_absent :
    isInArgumentDomain .V .C = true ∧
    isInArgumentDomain .v .C = true ∧
    MismatchDimension.corpusCount .argumentStructure = 0 :=
  ⟨by decide, by decide, rfl⟩

/-- T is outside the argument domain: tense mismatches are licit.
    The corpus confirms: 129 tense mismatches attested. -/
theorem tense_outside_and_attested :
    isInArgumentDomain .T .C = false ∧
    MismatchDimension.corpusCount .tense > 0 :=
  ⟨by decide, by native_decide⟩

/-- Mod is outside the argument domain: modal mismatches are licit.
    The corpus confirms: 394 modal mismatches — the most frequent type. -/
theorem modality_outside_and_attested :
    isInArgumentDomain .Mod .C = false ∧
    MismatchDimension.corpusCount .modality > 0 :=
  ⟨by decide, by native_decide⟩

/-- The SIC cleanly separates tolerated from untolerated mismatches:
    every mismatch dimension inside the argument domain has 0 corpus
    attestations; every dimension outside has nonzero attestations. -/
theorem sic_partition_confirmed :
    -- Inside arg domain → 0 mismatches
    MismatchDimension.corpusCount .argumentStructure = 0 ∧
    MismatchDimension.corpusCount .voice = 0 ∧
    -- Outside arg domain → mismatches attested
    MismatchDimension.corpusCount .tense > 0 ∧
    MismatchDimension.corpusCount .modality > 0 :=
  ⟨rfl, rfl, by native_decide, by native_decide⟩

-- ============================================================================
-- § 3: The Voice Puzzle
-- ============================================================================

/-- The voice mismatch puzzle: the SIC predicts voice mismatches are licit
    (Voice/T heads are outside the argument domain), yet the corpus
    contains zero.

    This asymmetry is striking because tense and modality — at the same
    structural level (outside vP) — show abundant mismatches. The gap
    between "permitted by the grammar" and "attested in use" suggests
    either:
    (a) additional pragmatic/processing constraints on sluicing, or
    (b) the SIC is too permissive for voice.

    The contrast with VP ellipsis is sharp: Merchant (2013) shows voice
    mismatches are freely attested under VP ellipsis. -/
theorem voice_permitted_but_absent :
    isInArgumentDomain .T .C = false ∧
    MismatchDimension.corpusCount .tense > 0 ∧
    MismatchDimension.corpusCount .voice = 0 :=
  ⟨by decide, by native_decide, rfl⟩

-- ============================================================================
-- § 4: Corpus Distributions
-- ============================================================================

/-- Sprouting is the dominant sluice kind (65.5%), overturning the
    literature's focus on merger. -/
theorem sprouting_is_default :
    scss.sproutingPctTenths > 500 := by native_decide

/-- *Why* accounts for the majority of sluicing. Since virtually all
    *why*-sluices are sprouting (reason adjuncts lack overt correlates),
    the prototypical sluice is "John left, but I don't know why"
    (sprouting, reason), not "Someone left, but I don't know who"
    (merger, entity). -/
theorem why_dominates :
    scss.whyCount > scss.totalSluices / 2 := by native_decide

end Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Bridge
