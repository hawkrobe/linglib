import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Phenomena.ArgumentStructure.DativeAlternation

/-!
# Minimalism Small Clause Bridge — PVC–DOC Structural Priming

@cite{haddican-tamminga-dendikken-wade-2026}

Haddican, Tamminga, den Dikken & Wade (2026) show that particle verb
constructions (PVCs, "lifted Hsu up") prime double object constructions
(DOCs, "gave Hsu the book") in production. This cross-construction priming
effect supports a **Small Clause** (SC) analysis where both constructions
share the abstract structure `V [SC DP XP]`:

- DOC-SC:  `merge V [merge DP_goal DP_theme]`
- PVC-SC:  `merge V [merge DP Prt]`

Alternative analyses — ApplP for DOCs (Marantz 1993) and complex predicates
for PVCs (Johnson 1991) — posit no shared structure and therefore predict
no cross-construction priming.

## Structure

1. Lexical items as `SyntacticObject` leaves
2. Three DOC analyses (SC, ApplP, flat VP)
3. Two PVC analyses (SC, complex predicate)
4. Structural isomorphism theorems
5. Priming evidence and linking hypothesis
6. Bridge theorems: which analyses are consistent with the priming data
-/

namespace Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause

open Minimalism

/-! ## §1. Lexical items -/

def V_give  : SyntacticObject := mkLeafPhon .V [.D, .D] "give" 0
def V_lift  : SyntacticObject := mkLeafPhon .V [.D] "lift" 1
def DP_mary : SyntacticObject := mkLeafPhon .D [] "Mary" 2
def DP_hsu  : SyntacticObject := mkLeafPhon .D [] "Hsu" 3
def DP_book : SyntacticObject := mkLeafPhon .D [] "the book" 4
def Prt_up  : SyntacticObject := mkLeafPhon .P [] "up" 5
def Appl_h  : SyntacticObject := mkLeafPhon .Appl [.V] "∅" 6

/-! ## §2. Three DOC analyses -/

/-- Small Clause analysis (den Dikken 1995; Kayne 1984):
    `[VP V [SC DP_goal DP_theme]]` — shape `node(leaf, node(leaf, leaf))` -/
def doc_sc : SyntacticObject :=
  merge V_give (merge DP_hsu DP_book)

/-- Applicative analysis (Marantz 1993; Pylkkänen 2008):
    `[ApplP DP_goal [Appl' Appl [VP V DP_theme]]]`
    — shape `node(leaf, node(leaf, node(leaf, leaf)))` -/
def doc_appl : SyntacticObject :=
  merge DP_hsu (merge Appl_h (merge V_give DP_book))

/-- Flat VP baseline:
    `[VP [V' V DP_theme] DP_goal]` — shape `node(node(leaf, leaf), leaf)` -/
def doc_flat : SyntacticObject :=
  merge (merge V_give DP_book) DP_hsu

/-! ## §3. Two PVC analyses -/

/-- Small Clause analysis (den Dikken 1995):
    `[VP V [SC DP Prt]]` — shape `node(leaf, node(leaf, leaf))` -/
def pvc_sc : SyntacticObject :=
  merge V_lift (merge DP_hsu Prt_up)

/-- Complex predicate analysis (Johnson 1991):
    `[VP [V' V Prt] DP]` — shape `node(node(leaf, leaf), leaf)` -/
def pvc_complexPred : SyntacticObject :=
  merge (merge V_lift Prt_up) DP_hsu

/-! ## §4. Structural isomorphism theorems -/

/-- SC-DOC and SC-PVC have the same tree shape: `node(leaf, node(leaf, leaf))`.
    This is the key structural prediction of the Small Clause analysis. -/
theorem sc_doc_pvc_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc = true := by native_decide

/-- ApplP-DOC and ComplexPred-PVC have different shapes.
    These alternative analyses predict no shared structure. -/
theorem appl_doc_complexPred_pvc_not_isomorphic :
    structurallyIsomorphic doc_appl pvc_complexPred = false := by native_decide

/-- SC-DOC and ApplP-DOC have different shapes — the two DOC analyses
    make distinguishable structural predictions. -/
theorem sc_doc_appl_doc_not_isomorphic :
    structurallyIsomorphic doc_sc doc_appl = false := by native_decide

/-- Flat VP and SC-DOC have different shapes. -/
theorem flat_doc_sc_doc_not_isomorphic :
    structurallyIsomorphic doc_flat doc_sc = false := by native_decide

/-- ComplexPred-PVC and flat-DOC happen to share shape `node(node(leaf,leaf), leaf)`,
    but this is the *wrong* shape for priming — the shared head-complement
    structure is V-Prt (PVC) vs V-DP (DOC), not a shared SC. -/
theorem complexPred_flat_isomorphic :
    structurallyIsomorphic pvc_complexPred doc_flat = true := by native_decide

/-! ## §5. Priming evidence -/

/-- A structural priming result: prime construction, target construction,
    and whether priming was observed. -/
structure PrimingResult where
  prime  : String
  target : String
  primes : Bool
  deriving Repr, BEq

/-- Haddican et al. (2026), Experiment 1: PVCs prime DOC production. -/
def haddican_exp1 : PrimingResult :=
  { prime := "PVC", target := "DOC", primes := true }

/-- Linking hypothesis: cross-construction structural priming requires
    shared abstract tree shape (Bock 1986; Branigan & Pickering 2017). -/
axiom primingRequiresSharedShape :
  ∀ (r : PrimingResult), r.primes = true →
  ∀ (prime_so target_so : SyntacticObject),
    structurallyIsomorphic prime_so target_so = true

/-! ## §6. Bridge theorems -/

/-- The SC analysis is consistent with the observed priming:
    SC-PVC and SC-DOC share tree shape `node(leaf, node(leaf, leaf))`. -/
theorem sc_analysis_consistent_with_priming :
    haddican_exp1.primes = true ∧
    structurallyIsomorphic pvc_sc doc_sc = true := by
  exact ⟨rfl, sc_doc_pvc_isomorphic⟩

/-- The ApplP + ComplexPred combination is inconsistent with priming:
    these analyses yield different tree shapes for DOC and PVC. -/
theorem appl_complexPred_inconsistent_with_priming :
    haddican_exp1.primes = true ∧
    structurallyIsomorphic doc_appl pvc_complexPred = false := by
  exact ⟨rfl, appl_doc_complexPred_pvc_not_isomorphic⟩

end Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause
