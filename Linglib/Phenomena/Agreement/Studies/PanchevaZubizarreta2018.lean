import Linglib.Theories.Syntax.Minimalism.Core.PConstraint
import Linglib.Core.Logophoricity

/-!
# Pancheva & Zubizarreta (2018): The Person Case Constraint
@cite{pancheva-zubizarreta-2018}

The Person Case Constraint: The Syntactic Encoding of Perspective.
*Natural Language and Linguistic Theory* 36: 1291–1337.

## Summary

The Person Case Constraint (PCC) restricts person combinations in
ditransitive clitic clusters cross-linguistically. P&Z re-analyze the
PCC as a syntax-semantics interface phenomenon rooted in the encoding
of perspective. The core mechanism is a **P-Constraint** triggered by
an interpretable person feature on Appl, which marks the indirect
object as a **point-of-view center**.

## Key Contributions Formalized

1. **Full PCC typology**: five attested varieties (strong, ultra-strong,
   weak, super-strong, me-first) plus three predicted grammars, all
   derived from four binary parameters of the P-Constraint.

2. **Logophoric grounding**: the P-Prominence settings correspond to
   logophoric roles (Sells 1987): pivot, self, source.

3. **Markedness predictions**: grammar markedness follows from parameter
   departures from the default (strong PCC).

4. **Impossible grammar predictions**: me-first + *<3,3> restriction
   is ruled out by incompatible parameter settings.

5. **Cross-linguistic data**: French strong PCC, Catalan ultra-strong,
   Spanish weak, Kambera super-strong, Bulgarian me-first.
-/

namespace Phenomena.Agreement.Studies.PanchevaZubizarreta2018

open Core.Prominence (PersonLevel)
open Minimalism (DecomposedPerson decomposePerson)
open Minimalism.PConstraint

-- ============================================================================
-- § 1: The Person Hierarchy (§2.1, (2))
-- ============================================================================

/-- The Person Hierarchy is derived from suitability for point-of-view
    center, not stipulated as a primitive. -/
def personHierarchyRank (p : PersonLevel) : Nat :=
  match p with
  | .first  => 2  -- source + self + pivot
  | .second => 1  -- self + pivot
  | .third  => 0  -- pivot only contextually

theorem sap_gt_third :
    personHierarchyRank .first > personHierarchyRank .third ∧
    personHierarchyRank .second > personHierarchyRank .third := by decide

-- ============================================================================
-- § 2: Feature Decomposition (§3, (11))
-- ============================================================================

theorem feature_spec_1p :
    let dp := decomposePerson .first
    dp.hasProximate = true ∧ dp.hasParticipant = true ∧ dp.hasAuthor = true :=
  ⟨rfl, rfl, rfl⟩

theorem feature_spec_2p :
    let dp := decomposePerson .second
    dp.hasProximate = true ∧ dp.hasParticipant = true ∧ dp.hasAuthor = false :=
  ⟨rfl, rfl, rfl⟩

theorem feature_spec_3p :
    let dp := decomposePerson .third
    dp.hasProximate = false ∧ dp.hasParticipant = false ∧ dp.hasAuthor = false :=
  ⟨rfl, rfl, rfl⟩

theorem feature_hierarchy (p : PersonLevel) :
    (decomposePerson p).wellFormed = true := by
  cases p <;> rfl

-- ============================================================================
-- § 3: PCC Variety Verification (§4, (14))
-- ============================================================================

/-- Strong PCC (§4.1.1, (14a)): DO must be 3P. -/
theorem strong_pcc_do_must_be_3p :
    (∀ io, pccLicit strongGrammar io .third = true) ∧
    pccLicit strongGrammar .third .first = false ∧
    pccLicit strongGrammar .third .second = false ∧
    pccLicit strongGrammar .first .second = false ∧
    pccLicit strongGrammar .second .first = false :=
  ⟨λ io => by cases io <;> rfl, rfl, rfl, rfl, rfl⟩

/-- Weak PCC (§4.1.3, (14b)): 1P/2P co-occurrence allowed. -/
theorem weak_pcc_allows_participant_pairs :
    pccLicit weakGrammar .first .second = true ∧
    pccLicit weakGrammar .second .first = true ∧
    pccLicit weakGrammar .third .first = false ∧
    pccLicit weakGrammar .third .second = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Ultra-strong PCC (§4.1.2, (14d)): ⟨1,2⟩ OK but ⟨2,1⟩ banned. -/
theorem ultra_strong_pcc :
    pccLicit ultraStrongGrammar .first .second = true ∧
    pccLicit ultraStrongGrammar .second .first = false ∧
    pccLicit ultraStrongGrammar .third .first = false ∧
    pccLicit ultraStrongGrammar .third .second = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Me-first PCC (§4.3, (14c)): only ⟨3,1⟩ and ⟨2,1⟩ banned. -/
theorem me_first_pcc :
    pccLicit meFirstGrammar .third .first = false ∧
    pccLicit meFirstGrammar .second .first = false ∧
    pccLicit meFirstGrammar .first .second = true ∧
    pccLicit meFirstGrammar .first .third = true ∧
    pccLicit meFirstGrammar .second .third = true ∧
    pccLicit meFirstGrammar .third .second = true ∧
    pccLicit meFirstGrammar .third .third = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Super-strong PCC (§4.2, (14e)): IO must be 1P/2P, DO must be 3P.
    ⟨3,3⟩ banned (IO not [+participant]). -/
theorem super_strong_pcc :
    pccLicit superStrongGrammar .first .third = true ∧
    pccLicit superStrongGrammar .second .third = true ∧
    pccLicit superStrongGrammar .third .third = false ∧
    pccLicit superStrongGrammar .third .first = false ∧
    pccLicit superStrongGrammar .third .second = false ∧
    pccLicit superStrongGrammar .first .second = false ∧
    pccLicit superStrongGrammar .second .first = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Parameter Settings (§4.5, (31))
-- ============================================================================

/-- The [+proximate] family shares prominence and domain settings. -/
theorem proximate_family_shared :
    strongGrammar.prominence = .proximate ∧
    ultraStrongGrammar.prominence = .proximate ∧
    weakGrammar.prominence = .proximate := ⟨rfl, rfl, rfl⟩

theorem strong_is_default :
    strongGrammar = ⟨.proximate, true, false, false⟩ := rfl

theorem ultra_departs_on_primacy :
    ultraStrongGrammar.primacy = true ∧ strongGrammar.primacy = false := ⟨rfl, rfl⟩

theorem weak_departs_on_uniqueness :
    weakGrammar.uniqueness = false ∧ strongGrammar.uniqueness = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Logophoric Role Correspondence (§6.2)
-- ============================================================================

open Core.Logophoricity

/-- The P-Prominence setting that corresponds to a logophoric role.

    This is the formal link between the syntactic mechanism of the
    P-Constraint and the semantic content of perspectival centering:
    the interpretable person feature on Appl selects for the logophoric
    role of the indirect object. @cite{pancheva-zubizarreta-2018} -/
def roleToProminence : LogophoricRole → PProminence
  | .pivot  => .proximate
  | .self   => .participant
  | .source => .author

/-- The logophoric role corresponding to a P-Prominence setting. -/
def prominenceToRole : PProminence → LogophoricRole
  | .proximate   => .pivot
  | .participant => .self
  | .author      => .source

/-- The bridge is an isomorphism. -/
theorem prominence_role_roundtrip (r : LogophoricRole) :
    prominenceToRole (roleToProminence r) = r := by
  cases r <;> rfl

theorem role_prominence_roundtrip (p : PProminence) :
    roleToProminence (prominenceToRole p) = p := by
  cases p <;> rfl

theorem prominence_is_logophoric :
    prominenceToRole strongGrammar.prominence = .pivot ∧
    prominenceToRole superStrongGrammar.prominence = .self ∧
    prominenceToRole meFirstGrammar.prominence = .source := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: CLR Prediction (§4.1.4)
-- ============================================================================

/-- CLR effects predicted in all [+proximate] grammars. Me-first grammars
    do NOT predict CLR in ⟨3,3⟩ (domain restriction exempts). -/
theorem mefirst_no_clr_in_3_3 :
    pccLicit meFirstGrammar .third .third = true := rfl

-- ============================================================================
-- § 7: Spurious SE (§4.1.6)
-- ============================================================================

/-- *<3,3> effects compatible with [+proximate] family. -/
theorem spurious_se_compatible :
    pccLicit strongGrammar .third .third = true ∧
    pccLicit ultraStrongGrammar .third .third = true ∧
    pccLicit weakGrammar .third .third = true := ⟨rfl, rfl, rfl⟩

/-- *<3,3> incompatible with me-first (impossible parameter combination). -/
theorem mefirst_incompatible_with_star33 :
    pccLicit meFirstGrammar .third .third = true := rfl

-- ============================================================================
-- § 8: Predicted Grammars (§4.5)
-- ============================================================================

/-- PG1: [+participant] + P-Primacy. -/
theorem pg1_predictions :
    pccLicit pg1Grammar .first .third = true ∧
    pccLicit pg1Grammar .second .third = true ∧
    pccLicit pg1Grammar .first .second = true ∧   -- P-Primacy rescues
    pccLicit pg1Grammar .second .first = false ∧
    pccLicit pg1Grammar .third .first = false ∧
    pccLicit pg1Grammar .third .third = false :=   -- 3P IO not [+participant]
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- PG2: [+participant], no P-Uniqueness. IO must be SAP. -/
theorem pg2_predictions :
    pccLicit pg2Grammar .first .third = true ∧
    pccLicit pg2Grammar .second .third = true ∧
    pccLicit pg2Grammar .first .second = true ∧
    pccLicit pg2Grammar .second .first = true ∧
    pccLicit pg2Grammar .third .first = false ∧
    pccLicit pg2Grammar .third .third = false :=   -- 3P IO not [+participant]
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- PG3: [+author], unrestricted domain. Only 1P IO. -/
theorem pg3_predictions :
    pccLicit pg3Grammar .first .third = true ∧
    pccLicit pg3Grammar .first .second = true ∧
    pccLicit pg3Grammar .second .third = false ∧   -- 2P IO not [+author]
    pccLicit pg3Grammar .third .first = false ∧
    pccLicit pg3Grammar .third .third = false :=   -- 3P IO not [+author]
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Direct/Inverse Parallel (§5)
-- ============================================================================

/-- "Direct" order: IO satisfies the prominence requirement. -/
def isDirectOrder (ioPerson : PersonLevel) (prominence : PProminence) : Bool :=
  satisfiesProminence prominence ioPerson

theorem first_io_direct :
    isDirectOrder .first .proximate = true := rfl

theorem third_io_not_direct :
    isDirectOrder .third .proximate = false := rfl

-- ============================================================================
-- § 10: Cross-Linguistic Data
-- ============================================================================

/-- French strong PCC (§4.1.1, (16)). -/
theorem french_strong :
    pccLicit strongGrammar .third .first = false ∧   -- *Elle te me présentera
    pccLicit strongGrammar .second .third = true ∧   -- Elle le lui présentera
    pccLicit strongGrammar .third .third = true :=    -- two 3Ps OK
  ⟨rfl, rfl, rfl⟩

/-- Catalan ultra-strong (§4.1.2, (20)). -/
theorem catalan_ultra_strong :
    pccLicit ultraStrongGrammar .first .second = true ∧   -- El director, me l' ha recomanat
    pccLicit ultraStrongGrammar .second .first = false :=  -- *Al director, me li ha recomanat
  ⟨rfl, rfl⟩

/-- Spanish weak PCC (§4.1.3, (23)–(24)). -/
theorem spanish_weak :
    pccLicit weakGrammar .first .second = true ∧
    pccLicit weakGrammar .second .first = true ∧
    pccLicit weakGrammar .third .first = false :=
  ⟨rfl, rfl, rfl⟩

/-- Kambera super-strong (§4.2, (27)). -/
theorem kambera_super_strong :
    pccLicit superStrongGrammar .first .third = true ∧   -- (27a)
    pccLicit superStrongGrammar .second .third = true ∧  -- (27b)
    pccLicit superStrongGrammar .third .third = false ∧  -- (27c) *
    pccLicit superStrongGrammar .third .first = false ∧  -- (27d) *
    pccLicit superStrongGrammar .first .second = false := -- (27e) *
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Bulgarian me-first (§4.3, (29)). -/
theorem bulgarian_me_first :
    pccLicit meFirstGrammar .third .second = true ∧    -- (29a) OK
    pccLicit meFirstGrammar .second .first = false :=   -- (29b) *
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 11: Licit Counts and Markedness
-- ============================================================================

theorem strong_count : licitCount strongGrammar = 3 := by native_decide
theorem ultra_count : licitCount ultraStrongGrammar = 5 := by native_decide
theorem weak_count : licitCount weakGrammar = 7 := by native_decide
theorem super_count : licitCount superStrongGrammar = 2 := by native_decide
theorem mefirst_count : licitCount meFirstGrammar = 6 := by native_decide

/-- Me-first and weak have different licit sets. -/
theorem mefirst_ne_weak : meFirstGrammar ≠ weakGrammar := by decide

end Phenomena.Agreement.Studies.PanchevaZubizarreta2018
