import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# PVC–DOC Structural Priming — Small Clause Bridge

@cite{haddican-tamminga-dendikken-wade-2026}

Haddican, Tamminga, den Dikken & Wade (2026) report a production priming
experiment (N=238) showing PVCs ("put down the vase") prime DOCs
("gave Hsu the book") relative to non-PVC controls (β=0.296, p=.005).
PVC and DOC primes do not differ in priming magnitude (β=−0.069, p=.503),
consistent with identical structural representations.

The results "do not uniquely support SC approaches to PVCs and DOCs,
but rather any framework that yields structural isomorphism between them
that is not shared with PDs" (p.10). We formalize the four analyses the
paper compares and prove which pairs yield tree-shape isomorphism.

## Analyses formalized (paper's examples)

| # | Construction | Analysis | Source | Example |
|---|-------------|----------|--------|---------|
| 1 | DOC | Small Clause: `V [SC DP_goal DP_theme]` | Kayne 1984; Harley 2002 | (3) |
| 2 | DOC | ApplP: `[ApplP DP [Appl' Appl [VP V DP]]]` | Marantz 1993 | (6)/(9) |
| 3 | PVC | Small Clause: `V [SC DP Prt]` | den Dikken 1995 | (4a) |
| 4 | PVC | Complex predicate: `[VP [V+Prt] DP]` | Johnson 1991 | (5) |
| 5 | PD  | `[VP [V' V DP] [PP P DP]]` | (control) | — |

## Caveats

The paper notes Bruening's (2021) complex predicate approach to *both*
DOC and PVC would also furnish isomorphism, but at the process level
(both involve V+Head complex predicate formation) rather than tree-shape
identity — "We know of no priming literature testing specifically whether
movement or other syntactic operations can feed priming" (p.11). Pylkkänen's
(2008) low ApplP and Wood & Marantz's (2017) i* head are also noted as
potential sources of isomorphism (nn. 13, 15).
-/

namespace Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause

open Minimalism

/-! ## §1. Lexical items -/

def V_give  : SyntacticObject := mkLeafPhon .V [.D, .D] "give" 0
def V_lift  : SyntacticObject := mkLeafPhon .V [.D] "lift" 1
def DP_hsu  : SyntacticObject := mkLeafPhon .D [] "Hsu" 2
def DP_book : SyntacticObject := mkLeafPhon .D [] "the book" 3
def Prt_up  : SyntacticObject := mkLeafPhon .P [] "up" 4
def Appl_h  : SyntacticObject := mkLeafPhon .Appl [.V] "∅" 5
def P_to    : SyntacticObject := mkLeafPhon .P [.D] "to" 6

/-! ## §2. Structural analyses -/

/-- **DOC, Small Clause** (Kayne 1984, 1985; Harley 1997, 2002;
    Beck & Johnson 2004): `[VP V [SC DP_goal DP_theme]]` — paper's (3). -/
def doc_sc : SyntacticObject :=
  merge V_give (merge DP_hsu DP_book)

/-- **DOC, Applicative** (Marantz 1993; Bruening 2010a,b):
    `[ApplP DP_goal [Appl' Appl [VP V DP_theme]]]` — paper's (6)/(9). -/
def doc_appl : SyntacticObject :=
  merge DP_hsu (merge Appl_h (merge V_give DP_book))

/-- **PVC, Small Clause** (Aarts 1989; den Dikken 1995; Svenonius 1996a,b):
    `[VP V [SC DP Prt]]` — paper's (4a), underlying obj-particle order.
    Experimental primes used particle-object surface order ("put down the
    vase") to control for V-NP-X string similarity with DOC targets (p.5). -/
def pvc_sc : SyntacticObject :=
  merge V_lift (merge DP_hsu Prt_up)

/-- **PVC, Complex predicate** (Johnson 1991; Radford 1997; McIntyre 2015):
    `[VP [V lift+up] DP]` — paper's (5). V and particle form a composite
    terminal (complex head via head incorporation), not a phrase. Uses the
    existing `LexicalItem.combine` infrastructure for head-to-head movement. -/
def pvc_complexPred : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D] "lift").combine
                (LexicalItem.simple .P [] "up"), 7⟩) DP_hsu

/-- **PD, Prepositional dative** (control construction):
    `[VP [V' V DP_theme] [PP P DP_goal]]` — the baseline against which
    DOC priming is measured. -/
def pd : SyntacticObject :=
  merge (merge V_give DP_book) (merge P_to DP_hsu)

/-! ## §3. Explicit shapes

Making the tree geometries visible for inspection. -/

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

/-! ## §4. Structural isomorphism

The linking hypothesis (Bock 1986; Branigan & Pickering 2017): structural
priming is sensitive to abstract constituent structure. Shared tree shape
predicts cross-construction priming; distinct shape predicts none. -/

/-- SC-DOC and SC-PVC share tree shape `node(leaf, node(leaf, leaf))`.
    Both are `V [SC DP XP]` — the core prediction of the SC analysis. -/
theorem sc_doc_pvc_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc = true := by native_decide

/-- ApplP-DOC and ComplexPred-PVC have different shapes.
    These are the principal competitors to SC (Marantz 1993 for DOC,
    Johnson 1991 for PVC). -/
theorem appl_complexPred_not_isomorphic :
    structurallyIsomorphic doc_appl pvc_complexPred = false := by native_decide

/-- SC-DOC differs from ApplP-DOC: the two DOC analyses make
    distinguishable structural predictions. -/
theorem sc_appl_doc_not_isomorphic :
    structurallyIsomorphic doc_sc doc_appl = false := by native_decide

/-- SC-DOC differs from PD. This is why PD works as a baseline:
    if priming tracks tree shape, PD primes should not boost DOC
    production — and they don't (baseline subdesign). -/
theorem sc_doc_pd_not_isomorphic :
    structurallyIsomorphic doc_sc pd = false := by native_decide

/-- SC-PVC differs from PD. PVC-specific priming of DOCs cannot
    be attributed to shared PVC/PD structure. -/
theorem sc_pvc_pd_not_isomorphic :
    structurallyIsomorphic pvc_sc pd = false := by native_decide

/-- Among the four analyses formalized, SC is the unique source of
    DOC/PVC tree-shape isomorphism. All 10 pairwise comparisons across
    the five structures: only SC-DOC = SC-PVC. -/
theorem sc_unique_isomorphism :
    -- SC-DOC = SC-PVC (the key match)
    structurallyIsomorphic doc_sc pvc_sc = true ∧
    -- all other pairs differ
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

/-! ## §5. Experimental data

Production priming experiment (N=238 participants, sentence completion).
Two subdesigns (Table 1, p.7):

- **Baseline**: DOC vs PD primes → DOC/PD target completions
- **PV**: PVC vs non-PVC primes → DOC/PD target completions

PVC primes used particle-object order ("put down the vase") to control
for surface string similarity with DOC targets (p.5). -/

/-- A priming contrast between two prime conditions. -/
structure PrimingContrast where
  primeA       : String   -- test condition
  primeB       : String   -- control condition
  target       : String   -- response measure
  aFavorsTarget : Bool    -- primeA increases target production vs primeB
  significant  : Bool     -- p < .05
  deriving Repr, BEq

/-- Baseline replication: DOC primes boost DOC production relative to
    PD primes (β=0.569, SE=0.114, p<.001). Table 1: DOC→59%, PD→49%. -/
def baseline : PrimingContrast :=
  { primeA := "DOC", primeB := "PD", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- Key finding: PVC primes boost DOC production relative to non-PVC
    control primes (β=0.296, SE=0.105, p=.005). Table 1: PVC→58%,
    non-PVC→52%. -/
def pvc_primes_doc : PrimingContrast :=
  { primeA := "PVC", primeB := "non-PVC", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- PVC and DOC primes do not differ in their priming of DOCs
    (β=−0.069, SE=0.104, p=.503; combined 2×4 model, n.9). Consistent
    with identical structural representations under SC. -/
def pvc_doc_equivalent : PrimingContrast :=
  { primeA := "PVC", primeB := "DOC", target := "DOC"
  , aFavorsTarget := false, significant := false }

/-! ## §6. Bridge theorems

The structural predictions and experimental results are stated
independently. The linking hypothesis (shared shape ↔ priming)
connects them: theorems below show which analysis pairs are
consistent with which experimental contrasts. -/

/-- The SC analysis predicts DOC/PVC isomorphism (priming expected)
    and DOC/PD non-isomorphism (no priming expected). Both predictions
    match the data: PVC primes DOC (`pvc_primes_doc`), and PD does not
    prime DOC relative to DOC primes (`baseline`). -/
theorem sc_predictions :
    structurallyIsomorphic doc_sc pvc_sc = true ∧
    structurallyIsomorphic doc_sc pd = false := by
  exact ⟨sc_doc_pvc_isomorphic, sc_doc_pd_not_isomorphic⟩

/-- The ApplP + ComplexPred combination predicts DOC/PVC
    non-isomorphism, inconsistent with observed PVC→DOC priming. -/
theorem appl_complexPred_no_isomorphism :
    structurallyIsomorphic doc_appl pvc_complexPred = false :=
  appl_complexPred_not_isomorphic

/-- PVC priming magnitude equals DOC priming magnitude, and SC
    predicts exactly this: the structures are literally identical
    in shape (`node(leaf, node(leaf, leaf))`), so priming strength
    should not differ. -/
theorem sc_predicts_equal_magnitude :
    pvc_doc_equivalent.significant = false ∧
    doc_sc.shape = pvc_sc.shape := by
  exact ⟨rfl, rfl⟩

end Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause
