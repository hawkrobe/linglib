import Linglib.Theories.Phonology.Autosegmental.Defs
import Linglib.Fragments.English.Phonology
import Linglib.Phenomena.Phonology.Alternation

/-!
# Autosegmental Derivations

Connects autosegmental spreading to English nasal place assimilation data.
Where SPE needs a separate rule per trigger place, autosegmental spreading
captures the generalization in one operation: spread the place node from the
stop onto the preceding nasal.

§ 1 demonstrates velar assimilation (/n/ + /k/ → [ŋk]) and § 2 demonstrates
labial assimilation (/n/ + /p/ → [mp]).

@cite{clements-1985}
-/

namespace Clements1985

open Phonology
open Phonology.FeatureGeometry (GeomNode)
open Phonology.Autosegmental
open Fragments.English.Phonology

-- ============================================================================
-- § 1: Velar Assimilation (/n/ + /k/ → [ŋk])
-- ============================================================================

section VelarAssimilation

/-- Underlying representation: /nk/ with no sharing. -/
def ur_nk : AutosegRep where
  segments := [n, k]
  sharing := []

/-- Surface representation: result of spreading place from /k/ onto /n/. -/
def sr_nk : AutosegRep := ur_nk.spreadFeatures 0 .place

/-- /n/ and /k/ disagree at the place node in the UR. -/
theorem n_k_disagree_at_place : agreeAt n k .place = false := by native_decide

/-- After spreading, the modified nasal agrees with /k/ at the place node. -/
theorem spread_nk_agrees_at_place :
    (match sr_nk.segments[0]?, sr_nk.segments[1]? with
    | some s0, some s1 => agreeAt s0 s1 .place
    | _, _ => false) = true := by native_decide

/-- Spreading /k/'s dorsal place onto /n/ produces exactly [ŋ]. -/
theorem spread_nk_equals_ŋ :
    (match sr_nk.segments[0]? with
    | some s => s == ŋ
    | none => false) = true := by native_decide

/-- The surface representation is consistent (sharing matches feature values). -/
theorem sr_nk_consistent : sr_nk.consistent = true := by native_decide

end VelarAssimilation

-- ============================================================================
-- § 2: Labial Assimilation (/n/ + /p/ → [mp])
-- ============================================================================

section LabialAssimilation

/-- Underlying representation: /np/ with no sharing. -/
def ur_np : AutosegRep where
  segments := [n, p]
  sharing := []

/-- Surface representation: result of spreading place from /p/ onto /n/. -/
def sr_np : AutosegRep := ur_np.spreadFeatures 0 .place

/-- /n/ and /p/ disagree at the place node in the UR. -/
theorem n_p_disagree_at_place : agreeAt n p .place = false := by native_decide

/-- After spreading, the modified nasal agrees with /p/ at the place node. -/
theorem spread_np_agrees_at_place :
    (match sr_np.segments[0]?, sr_np.segments[1]? with
    | some s0, some s1 => agreeAt s0 s1 .place
    | _, _ => false) = true := by native_decide

/-- Spreading /p/'s labial place onto /n/ produces exactly [m]. -/
theorem spread_np_equals_m :
    (match sr_np.segments[0]? with
    | some s => s == m
    | none => false) = true := by native_decide

/-- The surface representation is consistent (sharing matches feature values). -/
theorem sr_np_consistent : sr_np.consistent = true := by native_decide

end LabialAssimilation

end Clements1985
