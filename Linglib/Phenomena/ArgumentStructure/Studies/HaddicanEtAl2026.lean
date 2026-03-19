import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.SmallClause
import Linglib.Phenomena.Constructions.ParticleVerbs.Data

/-!
# PVC–DOC Structural Priming
@cite{haddican-tamminga-dendikken-wade-2026} @cite{dendikken-1995} @cite{halle-marantz-1993} @cite{johnson-1991} @cite{aarts-1989} @cite{bruening-2010a}

English Particle Verbs Prime Double Object Constructions in Production.
*Linguistic Inquiry*. doi:10.1162/LING.a.558

Production priming experiment (N=238) testing whether PVCs prime DOCs.

## Design

Sentence completion task. Two subdesigns (Table 1, p.7):

- **Baseline**: DOC vs PD primes → DOC/PD target completions
- **PV**: PVC vs non-PVC primes → DOC/PD target completions

PVC primes used particle-object order ("put down the vase") to control
for surface string similarity with DOC targets (p.5).

## Results

PVCs prime DOCs (β=0.296, p=.005). PVC and DOC primes do not differ in
priming magnitude (β=−0.069, p=.503). Consistent with identical structural
representations under the SC analysis.

## Cross-references

- `Phenomena.WordOrder.Studies.ArnoldEtAl2000`: The same two constructions
  (dative alternation + particle placement) studied from a processing
  perspective — heaviness drives linearization while abstract structure
  drives priming.
- `Phenomena.ArgumentStructure.DativeAlternation`: Records both DOC and PD
  frames as grammatical — the precondition for the priming study.
-/

namespace Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026

/-- A priming contrast between two prime conditions. -/
structure PrimingContrast where
  primeA        : String   -- test condition
  primeB        : String   -- control condition
  target        : String   -- response measure
  aFavorsTarget : Bool     -- primeA increases target production vs primeB
  significant   : Bool     -- p < .05
  deriving Repr, BEq

/-- DOC production rate by prime condition. Table 1, p.7.
    Percentages are integers (e.g., 59 = 59%). -/
structure CellRate where
  condition : String
  docPct    : Nat       -- DOC production %
  pdPct     : Nat       -- PD production %
  deriving Repr, BEq

/-! ## Table 1 cell rates -/

def baseline_doc : CellRate := { condition := "DOC prime",     docPct := 59, pdPct := 41 }
def baseline_pd  : CellRate := { condition := "PD prime",      docPct := 49, pdPct := 51 }
def pv_pvc       : CellRate := { condition := "PVC prime",     docPct := 58, pdPct := 42 }
def pv_nonpvc    : CellRate := { condition := "non-PVC prime", docPct := 52, pdPct := 48 }

/-! ## Regression contrasts -/

/-- Baseline replication: DOC primes boost DOC production relative to
    PD primes (β=0.569, SE=0.114, p<.001). -/
def baseline : PrimingContrast :=
  { primeA := "DOC", primeB := "PD", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- Key finding: PVC primes boost DOC production relative to non-PVC
    control primes (β=0.296, SE=0.105, p=.005). -/
def pvc_primes_doc : PrimingContrast :=
  { primeA := "PVC", primeB := "non-PVC", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- PVC and DOC primes do not differ in their priming of DOCs
    (β=−0.069, SE=0.104, p=.503; combined 2×4 model, n.9). -/
def pvc_doc_equivalent : PrimingContrast :=
  { primeA := "PVC", primeB := "DOC", target := "DOC"
  , aFavorsTarget := false, significant := false }

/-! ## Verification theorems -/

/-- DOC priming is strictly stronger than PD non-priming (baseline effect). -/
theorem baseline_effect_direction :
    baseline.aFavorsTarget = true ∧ baseline.significant = true := ⟨rfl, rfl⟩

/-- PVC primes DO boost DOC production. -/
theorem pvc_effect :
    pvc_primes_doc.aFavorsTarget = true ∧ pvc_primes_doc.significant = true := ⟨rfl, rfl⟩

/-- PVC and DOC primes yield equivalent magnitude — no significant difference. -/
theorem pvc_doc_equivalence :
    pvc_doc_equivalent.significant = false := rfl

-- ============================================================================
-- Part II: Minimalist Small Clause Analysis
-- ============================================================================

open Minimalism

/-! ## Lexical items -/

def V_give   : SyntacticObject := mkLeafPhon .V [.D, .D] "give" 0
def V_lift   : SyntacticObject := mkLeafPhon .V [.D] "lift" 1
def DP_hsu   : SyntacticObject := mkLeafPhon .D [] "Hsu" 2
def DP_book  : SyntacticObject := mkLeafPhon .D [] "the book" 3
def Prt_up   : SyntacticObject := mkLeafPhon .P [] "up" 4
def Appl_h   : SyntacticObject := mkLeafPhon .Appl [.V] "∅" 5
def P_to     : SyntacticObject := mkLeafPhon .P [.D] "to" 6
def V_hammer : SyntacticObject := mkLeafPhon .V [.D] "hammer" 8
def DP_metal : SyntacticObject := mkLeafPhon .D [] "the metal" 9
def AP_flat  : SyntacticObject := mkLeafPhon .A [] "flat" 10
def V_make   : SyntacticObject := mkLeafPhon .V [.D] "make" 11
def DP_child : SyntacticObject := mkLeafPhon .D [] "the child" 12
def VP_laugh : SyntacticObject := mkLeafPhon .V [] "laugh" 13

/-- Experimental PVC primes derive from the ParticleVerbs inventory. -/
theorem experimental_pvcs_in_inventory :
    (Phenomena.Constructions.ParticleVerbs.inventory.any
      (· == Phenomena.Constructions.ParticleVerbs.lift_up)) = true ∧
    (Phenomena.Constructions.ParticleVerbs.inventory.any
      (· == Phenomena.Constructions.ParticleVerbs.put_down)) = true := by
  constructor <;> native_decide

/-- The ApplP analysis uses a LOW applicative. -/
def doc_appl_type : ApplType := .lowRecipient

/-! ## Structural analyses -/

/-- **DOC, Small Clause**: `[VP V [SC DP_goal DP_theme]]` -/
def doc_sc : SyntacticObject :=
  merge V_give (merge DP_hsu DP_book)

/-- **DOC, Applicative** (@cite{halle-marantz-1993}; @cite{bruening-2010a}):
    `[ApplP DP_goal [Appl' Appl [VP V DP_theme]]]` -/
def doc_appl : SyntacticObject :=
  merge DP_hsu (merge Appl_h (merge V_give DP_book))

/-- **PVC, Small Clause** (@cite{aarts-1989}; @cite{dendikken-1995}):
    `[VP V [SC DP Prt]]` -/
def pvc_sc : SyntacticObject :=
  merge V_lift (merge DP_hsu Prt_up)

/-- **PVC, Complex predicate**: `[VP [V lift+up] DP]` -/
def pvc_complexPred : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D] "lift").combine
                (LexicalItem.simple .P [] "up"), 7⟩) DP_hsu

/-- **PD, Prepositional dative** (control): `[VP [V' V DP_theme] [PP P DP_goal]]` -/
def pd : SyntacticObject :=
  merge (merge V_give DP_book) (merge P_to DP_hsu)

/-- **Non-PVC transitive control**: `[VP V DP]` -/
def transitive_control : SyntacticObject :=
  merge V_lift DP_hsu

/-! ## @cite{dendikken-1995} SC family -/

/-- **Resultative, Small Clause**: `[VP V [SC DP AP]]` -/
def resultative_sc : SyntacticObject :=
  merge V_hammer (merge DP_metal AP_flat)

/-- **Causative, Small Clause**: `[VP V [SC DP VP]]` -/
def causative_sc : SyntacticObject :=
  merge V_make (merge DP_child VP_laugh)

/-! ## Explicit shapes -/

theorem doc_sc_shape :
    doc_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

theorem doc_appl_shape :
    doc_appl.shape = .node .leaf (.node .leaf (.node .leaf .leaf)) := rfl

theorem pvc_sc_shape :
    pvc_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

theorem pvc_complexPred_shape :
    pvc_complexPred.shape = .node .leaf .leaf := rfl

theorem pd_shape :
    pd.shape = .node (.node .leaf .leaf) (.node .leaf .leaf) := rfl

theorem transitive_control_shape :
    transitive_control.shape = .node .leaf .leaf := rfl

theorem resultative_sc_shape :
    resultative_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

theorem causative_sc_shape :
    causative_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

/-! ## Structural isomorphism -/

/-- SC-DOC and SC-PVC share tree shape. -/
theorem sc_doc_pvc_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc = true := by native_decide

/-- ApplP-DOC and ComplexPred-PVC have different shapes. -/
theorem appl_complexPred_not_isomorphic :
    structurallyIsomorphic doc_appl pvc_complexPred = false := by native_decide

/-- SC-DOC differs from ApplP-DOC. -/
theorem sc_appl_doc_not_isomorphic :
    structurallyIsomorphic doc_sc doc_appl = false := by native_decide

/-- SC-DOC differs from PD. -/
theorem sc_doc_pd_not_isomorphic :
    structurallyIsomorphic doc_sc pd = false := by native_decide

/-- SC-PVC differs from PD. -/
theorem sc_pvc_pd_not_isomorphic :
    structurallyIsomorphic pvc_sc pd = false := by native_decide

/-- The non-PVC transitive control has a different shape from SC-DOC. -/
theorem control_doc_not_isomorphic :
    structurallyIsomorphic transitive_control doc_sc = false := by native_decide

/-- The non-PVC control has the SAME shape as the complex predicate PVC. -/
theorem control_matches_complexPred :
    structurallyIsomorphic transitive_control pvc_complexPred = true := by native_decide

/-- SC is the unique source of DOC/PVC tree-shape isomorphism. -/
theorem sc_unique_among_haddican_analyses :
    structurallyIsomorphic doc_sc pvc_sc = true ∧
    structurallyIsomorphic doc_sc doc_appl = false ∧
    structurallyIsomorphic doc_sc pvc_complexPred = false ∧
    structurallyIsomorphic doc_sc pd = false ∧
    structurallyIsomorphic doc_appl pvc_sc = false ∧
    structurallyIsomorphic doc_appl pvc_complexPred = false ∧
    structurallyIsomorphic doc_appl pd = false ∧
    structurallyIsomorphic pvc_sc pvc_complexPred = false ∧
    structurallyIsomorphic pvc_sc pd = false ∧
    structurallyIsomorphic pvc_complexPred pd = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Den Dikken SC family isomorphism -/

/-- The SC family shares a single tree shape. -/
theorem sc_family_same_shape :
    doc_sc.shape = pvc_sc.shape ∧
    doc_sc.shape = resultative_sc.shape ∧
    doc_sc.shape = causative_sc.shape := by
  exact ⟨rfl, rfl, rfl⟩

/-- All four SC constructions are pairwise isomorphic. -/
theorem sc_family_all_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc = true ∧
    structurallyIsomorphic doc_sc resultative_sc = true ∧
    structurallyIsomorphic doc_sc causative_sc = true ∧
    structurallyIsomorphic pvc_sc resultative_sc = true ∧
    structurallyIsomorphic pvc_sc causative_sc = true ∧
    structurallyIsomorphic resultative_sc causative_sc = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- None of the SC family members are isomorphic with PD. -/
theorem sc_family_all_differ_from_pd :
    structurallyIsomorphic pvc_sc pd = false ∧
    structurallyIsomorphic resultative_sc pd = false ∧
    structurallyIsomorphic causative_sc pd = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## SC family categorization -/

def pvc_category : SCPredCategory := .P
def doc_category : SCPredCategory := .P
def resultative_category : SCPredCategory := .A
def causative_category : SCPredCategory := .V
def copular_category : SCPredCategory := .N

/-- DOC and PVC share SC predicate category P. -/
theorem doc_pvc_share_P : doc_category = pvc_category := rfl

/-- The SC family spans all four lexical categories {A, N, P, V}. -/
theorem sc_family_covers_all_categories :
    pvc_category = .P ∧
    resultative_category = .A ∧
    causative_category = .V ∧
    copular_category = .N := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Nested SC for DOC -/

/-- Nested SC DOC: `give [SC book [PP to Hsu]]`. -/
def doc_nested : SyntacticObject :=
  merge V_give (merge DP_book (merge P_to DP_hsu))

theorem doc_nested_shape :
    doc_nested.shape = .node .leaf (.node .leaf (.node .leaf .leaf)) := rfl

theorem doc_nested_not_flat :
    structurallyIsomorphic doc_nested doc_sc = false := by native_decide

theorem doc_nested_matches_appl :
    structurallyIsomorphic doc_nested doc_appl = true := by native_decide

/-! ## @cite{bruening-2021}: process-level isomorphism -/

def doc_bruening : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D, .D] "give").combine
                (LexicalItem.simple .P [] "∅_R"), 14⟩)
       (merge DP_hsu DP_book)

def pvc_bruening := pvc_complexPred

theorem doc_bruening_shape :
    doc_bruening.shape = .node .leaf (.node .leaf .leaf) := rfl

theorem bruening_shapes_differ :
    structurallyIsomorphic doc_bruening pvc_bruening = false := by native_decide

theorem bruening_both_use_incorporation :
    (match doc_bruening with
     | .node (.leaf tok) _ => tok.item.isComplex
     | _ => false) = true ∧
    (match pvc_bruening with
     | .node (.leaf tok) _ => tok.item.isComplex
     | _ => false) = true := by
  constructor <;> native_decide

theorem bruening_doc_matches_sc_doc :
    structurallyIsomorphic doc_bruening doc_sc = true := by native_decide

/-! ## Bridge to experimental data -/

/-- The SC analysis predicts DOC/PVC isomorphism and DOC/PD non-isomorphism. -/
theorem sc_predictions :
    structurallyIsomorphic doc_sc pvc_sc = true ∧
    structurallyIsomorphic doc_sc pd = false := by
  exact ⟨sc_doc_pvc_isomorphic, sc_doc_pd_not_isomorphic⟩

/-- The ApplP + ComplexPred combination predicts DOC/PVC non-isomorphism. -/
theorem appl_complexPred_no_isomorphism :
    structurallyIsomorphic doc_appl pvc_complexPred = false :=
  appl_complexPred_not_isomorphic

/-- PVC priming magnitude equals DOC priming magnitude, as SC predicts. -/
theorem sc_predicts_equal_magnitude :
    pvc_doc_equivalent.significant = false ∧
    doc_sc.shape = pvc_sc.shape := by
  exact ⟨rfl, rfl⟩

/-- The complex predicate PVC analysis cannot explain the priming asymmetry. -/
theorem complexPred_fails_at_control :
    pvc_primes_doc.significant = true ∧
    structurallyIsomorphic pvc_complexPred transitive_control = true := by
  exact ⟨rfl, by native_decide⟩

end Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026
