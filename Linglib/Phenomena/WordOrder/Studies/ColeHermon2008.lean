import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Derivation
import Linglib.Theories.Syntax.Minimalism.Core.EPP

/-!
# VP Raising in a VOS Language @cite{cole-hermon-2008}

@cite{cole-hermon-2008} argue that VOS word order in Toba Batak derives
from VP-raising to Spec,TP, rather than from rightward subject shift or
base-generation. The key evidence:

1. **Binding**: Objects inside the raised VP can bind into the subject
   (backward binding), because the VP c-commands the subject at surface
   structure. This follows directly from VP-raising but is unexpected
   under rightward movement of the subject.

2. **Same base structure**: Toba Batak and English share the same
   underlying vP-internal structure `[TP T [vP Subj [v' v [VP V Obj]]]]`.
   The only difference is what moves to Spec,TP — the VP (yielding VOS)
   vs the subject DP (yielding SVO).

## Derivation

Bottom-up, both languages build the same pre-movement tree:

    [TP T [vP Subj [v' v [VP V Obj]]]]

Then:
- **Toba Batak** (VP-raising): VP moves to Spec,TP → `[VP V Obj] T Subj v tVP` → VOS
- **English** (subject-raising): Subj moves to Spec,TP → `Subj T tSubj v [VP V Obj]` → SVO
-/

namespace Phenomena.WordOrder.Studies.ColeHermon2008

open Minimalism

-- ============================================================================
-- § 1: Toba Batak Lexical Items
-- ============================================================================

/-- "mangatuk" — ACT-hit (active voice transitive verb). -/
def v_mangatuk := mkLeafPhon .V [] "mangatuk" 1

/-- "biangi" — dog-DEF (definite object DP). -/
def n_biangi := mkLeafPhon .N [] "biangi" 2

/-- "dakdanakan" — child-that (subject DP). -/
def n_dakdanakan := mkLeafPhon .N [] "dakdanakan" 3

/-- Little v (silent, selects VP). -/
def v_head := mkLeaf .v [.V] 4

/-- T (silent, selects vP). -/
def t_head := mkLeaf .T [.v] 5

/-- The VP constituent `[VP V Obj]` — the phrase that raises. -/
def vp : SyntacticObject := .node v_mangatuk n_biangi

-- ============================================================================
-- § 2: Toba Batak VOS Derivation
-- ============================================================================

/-- Toba Batak VOS via VP-raising to Spec,TP.

    Steps (bottom-up):
    1. EM-R Obj → `[VP V Obj]`
    2. EM-L v  → `[v' v VP]`
    3. EM-L Subj → `[vP Subj [v' v VP]]`
    4. EM-L T  → `[TP T [vP Subj [v' v VP]]]`
    5. IM VP   → `[TP VP [T' T [vP Subj [v' v tVP]]]]` -/
def tobaBatakVOS : Derivation :=
  { initial := v_mangatuk
    steps := [
      .emR n_biangi,
      .emL v_head,
      .emL n_dakdanakan,
      .emL t_head,
      .im vp 0
    ] }

-- ============================================================================
-- § 3: English SVO Derivation (Comparison)
-- ============================================================================

def v_saw   := mkLeafPhon .V [] "saw" 11
def n_mary  := mkLeafPhon .N [] "Mary" 12
def n_john  := mkLeafPhon .N [] "John" 13
def v_head2 := mkLeaf .v [.V] 14
def t_head2 := mkLeaf .T [.v] 15

/-- English SVO via subject-raising to Spec,TP.

    Same base as Toba Batak, but the subject (not VP) moves to Spec,TP. -/
def englishSVO : Derivation :=
  { initial := v_saw
    steps := [
      .emR n_mary,
      .emL v_head2,
      .emL n_john,
      .emL t_head2,
      .im n_john 0
    ] }

-- ============================================================================
-- § 4: Word Order Predictions
-- ============================================================================

/-- VP-raising yields Verb-Object-Subject surface order. -/
theorem toba_batak_is_vos :
    tobaBatakVOS.final.phonYield = ["mangatuk", "biangi", "dakdanakan"] := by
  native_decide

/-- Subject-raising yields Subject-Verb-Object surface order. -/
theorem english_is_svo :
    englishSVO.final.phonYield = ["John", "saw", "Mary"] := by
  native_decide

/-- Both derivations have the same tree shape before the movement step
    (stage 4). The only parametric difference is *what* moves in step 5. -/
theorem same_base_shape :
    (tobaBatakVOS.stageAt 4).shape = (englishSVO.stageAt 4).shape := by
  native_decide

/-- Toba Batak moves the VP (one moved item). -/
theorem toba_batak_moves_vp :
    tobaBatakVOS.movedItems.length = 1 := by native_decide

/-- English moves the subject DP (one moved item). -/
theorem english_moves_subject :
    englishSVO.movedItems.length = 1 := by native_decide

-- ============================================================================
-- § 5: C-Command — Backward Binding
-- ============================================================================

/-- After VP-raising, the VP c-commands the subject in the derived tree.

    This is the structural basis for backward binding: elements inside the
    raised VP (including the object) can bind into the subject, because the
    VP is the left daughter of the root and its sister (T') dominates the
    subject. -/
theorem vp_ccommands_subject :
    cCommandsIn tobaBatakVOS.final vp n_dakdanakan := by
  -- Compute the final tree: [TP [VP V Obj] [T' T [vP Subj [v' v tVP]]]]
  have h_final : tobaBatakVOS.final =
    .node vp (.node t_head (.node n_dakdanakan (.node v_head (mkTrace 0)))) := by
    native_decide
  rw [h_final]
  -- VP's sister is T', which dominates the subject
  exact ⟨.node t_head (.node n_dakdanakan (.node v_head (mkTrace 0))),
         ⟨_, self_mem_subterms _, Or.inl rfl, Or.inr rfl, by decide⟩,
         Or.inr (contains.trans _ _ _ (Or.inr rfl) (contains.imm _ _ (Or.inl rfl)))⟩

-- ============================================================================
-- § 6: EPP Parameter
-- ============================================================================

/-- Toba Batak and English instantiate the same EPP parameter space:
    VP-raising → VOS, subject-raising → SVO. -/
theorem epp_predicts_order :
    tobaBatak_wo.eppStrategy = .vpRaising ∧
    english_wo.eppStrategy = .subjectRaising := ⟨rfl, rfl⟩

end Phenomena.WordOrder.Studies.ColeHermon2008
