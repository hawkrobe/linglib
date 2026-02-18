import Linglib.Phenomena.Complementation.Studies.Cacchioli2025.Data
import Linglib.Phenomena.Complementation.Studies.Cacchioli2025.SelectionBridge
import Linglib.Fragments.Tigrinya.ClausePrefixes
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Cacchioli (2025) — Bridge Theorems @cite{cacchioli-2025}

Connects Tigrinya clausal prefix data (Data.lean) and Fragment entries
(ClausePrefixes.lean) to the Minimalist extended projection hierarchy
(ExtendedProjection/Basic.lean) and clause-typing features (Agree.lean
via SelectionBridge.lean).

## What this file proves

1. **EP position**: Each prefix spells out a head at the correct position
   in the split-CP / split-IP hierarchy
2. **Fragment-data consistency**: Fragment entries match empirical data
3. **Selection bridge**: CTPClass → [±finite] mapping predicts which
   prefix appears with which verb class
4. **Circumfix**: The negative prefix is correctly typed as discontinuous

## References

- Cacchioli, S. (2025). The Syntax of Clausal Prefixes in Tigrinya.
-/

namespace Phenomena.Complementation.Cacchioli2025.Bridge

open Minimalism
open Fragments.Tigrinya.ClausePrefixes
open Phenomena.Complementation.Cacchioli2025.Data
open Phenomena.Complementation.SelectionBridge

-- ============================================================================
-- Section A: Fragment entries target correct EP positions
-- ============================================================================

/-- zɨ- (Rel) is at the same fValue level as Top (topic field, F5). -/
theorem zi_fvalue_topic_field : fValue zi.headCat = fValue .Top := by decide

/-- kɨ- (Fin) is at the IP/CP boundary (F3). -/
theorem ki_fvalue_boundary : fValue ki.headCat = 3 := by decide

/-- kəmzi- (Force) is at the clause-typing level (F6). -/
theorem kemzi_fvalue_clause_typing : fValue kemzi.headCat = 6 := by decide

/-- ʔay-...-n (Neg) is in the inflectional domain (F2). -/
theorem ay_fvalue_inflectional : fValue ay_n.headCat = 2 := by decide

/-- The four prefixes target four distinct F-levels:
    Neg(2) < Fin(3) < Rel(5) < Force(6). -/
theorem prefixes_distinct_flevels :
    fValue ay_n.headCat < fValue ki.headCat ∧
    fValue ki.headCat < fValue zi.headCat ∧
    fValue zi.headCat < fValue kemzi.headCat := by decide

-- ============================================================================
-- Section B: Fragment-data consistency
-- ============================================================================

/-- Fragment agreement field matches empirical data for each prefix. -/
theorem agreement_matches_data :
    zi.takesAgreementSuffix = false ∧
    ki.takesAgreementSuffix = true ∧
    kemzi.takesAgreementSuffix = false ∧
    ay_n.takesAgreementSuffix = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Only ʔay-...-n is discontinuous. -/
theorem only_neg_discontinuous :
    zi.isDiscontinuous = false ∧
    ki.isDiscontinuous = false ∧
    kemzi.isDiscontinuous = false ∧
    ay_n.isDiscontinuous = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Section C: Selection bridge (CTPClass → prefix)
-- ============================================================================

/-- Knowledge verbs select [+finite] → predicts kəmzi- (factive). -/
theorem knowledge_selects_kemzi :
    ctpToFiniteness .knowledge = some true := rfl

/-- Desiderative verbs select [-finite] → predicts kɨ- (subjunctive). -/
theorem desiderative_selects_ki :
    ctpToFiniteness .desiderative = some false := rfl

/-- Commentative verbs select [+finite] → predicts kəmzi- (factive). -/
theorem commentative_selects_kemzi :
    ctpToFiniteness .commentative = some true := rfl

/-- Manipulative verbs select [-finite] → predicts kɨ- (subjunctive). -/
theorem manipulative_selects_ki :
    ctpToFiniteness .manipulative = some false := rfl

-- ============================================================================
-- Section D: Negative circumfix
-- ============================================================================

/-- The negative circumfix surfaces correctly for a sample verb. -/
theorem neg_circumfix_realize :
    (negCircumfix "mäs'ə").realize = "ʔay-mäs'ə-n" := rfl

/-- The negative circumfix gloss is derived from the fragment entry. -/
theorem neg_circumfix_from_neg :
    (negCircumfix "mäs'ə").gloss = ay_n.gloss := rfl

-- ============================================================================
-- Section E: All four heads are verbal
-- ============================================================================

/-- All four prefix heads are in the verbal extended projection. -/
theorem all_prefixes_verbal :
    catFamily zi.headCat = .verbal ∧
    catFamily ki.headCat = .verbal ∧
    catFamily kemzi.headCat = .verbal ∧
    catFamily ay_n.headCat = .verbal := by decide

end Phenomena.Complementation.Cacchioli2025.Bridge
