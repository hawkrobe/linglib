import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.SmallClause
import Linglib.Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026
import Linglib.Phenomena.Constructions.ParticleVerbs.Data

/-!
# PVC–DOC Structural Priming — Small Clause Bridge

@cite{haddican-tamminga-dendikken-wade-2026} @cite{dendikken-1995} @cite{halle-marantz-1993} @cite{johnson-1991} @cite{aarts-1989} @cite{svenonius-1996a} @cite{bruening-2010a}

Haddican, @cite{haddican-tamminga-dendikken-wade-2026} report a production priming
experiment (N=238) showing PVCs ("put down the vase") prime DOCs
("gave Hsu the book") relative to non-PVC controls (β=0.296, p=.005).
PVC and DOC primes do not differ in priming magnitude (β=−0.069, p=.503),
consistent with identical structural representations.

The results "do not uniquely support SC approaches to PVCs and DOCs,
but rather any framework that yields structural isomorphism between them
that is not shared with PDs" (p.10). We formalize the four analyses the
paper compares, plus @cite{dendikken-1995}'s broader SC family and @cite{bruening-2021}'s complex predicate alternative, and prove which pairs yield
tree-shape isomorphism.

## Analyses formalized (paper's examples)

| # | Construction | Analysis | Source | Example |
|---|-------------|----------|--------|---------|
| 1 | DOC | Small Clause: `V [SC DP_goal DP_theme]` | Kayne 1984; Harley 2002 | (3) |
| 2 | DOC | ApplP: `[ApplP DP [Appl' Appl [VP V DP]]]` | Marantz 1993 | (6)/(9) |
| 3 | PVC | Small Clause: `V [SC DP Prt]` | den Dikken 1995 | (4a) |
| 4 | PVC | Complex predicate: `[VP [V+Prt] DP]` | Johnson 1991 | (5) |
| 5 | PD  | `[VP [V' V DP] [PP P DP]]` | (control) | — |

## @cite{dendikken-1995} SC family

Den Dikken's thesis (1995:25, ex. 41–42) is that all subject-predicate
relationships are incarnated as small clauses `[SC Subj Pred]`:

| Construction | Example | SC structure |
|---|---|---|
| PVC | "lift Hsu up" | `V [SC DP Prt]` |
| DOC | "give Hsu the book" | `V [SC DP DP]` |
| Resultative | "hammer the metal flat" | `V [SC DP AP]` |
| Causative | "make the child laugh" | `V [SC DP VP]` |

All share tree shape `node(leaf, node(leaf, leaf))`. This predicts mutual
cross-construction priming — resultatives and causatives should also prime
DOCs. See `Phenomena.Constructions.Resultatives.Data` for resultative data.

## Caveats

@cite{bruening-2021}'s complex predicate approach to *both* DOC and PVC would
furnish isomorphism at the process level (both involve V+Head complex
predicate formation) rather than tree-shape identity — "We know of no
priming literature testing specifically whether movement or other syntactic
operations can feed priming" (p.11). @cite{brennan-pylkkanen-2008}'s low ApplP and
@cite{wood-marantz-2017} i* head are also noted as potential sources of
isomorphism (nn. 13, 15).

## Cross-references

- `Phenomena.ArgumentStructure.DativeAlternation`: The DOC/PD distinction
  is the dative alternation — both frames grammatical.
- `Phenomena.Constructions.ParticleVerbs.Data`: PVC inventory and shift
  constraints; experimental items derive from this inventory.
- `Phenomena.WordOrder.Studies.ArnoldEtAl2000`: Heaviness and newness in
  dative alternation and particle placement — a processing complement
  to the structural priming perspective here.
- `Phenomena.Constructions.Resultatives.Data`: Resultative data; the SC
  analysis predicts resultatives should also prime DOCs.
- `Minimalism.VoiceFlavor.causer`, `Minimalism.buildDecomposition`:
  Causative structure via Voice; the SC causative analysis here parallels
  Voice's treatment of the causative alternation.
-/

namespace Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause

open Minimalism
open Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026

/-! ## §1. Lexical items -/

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

/-- Experimental PVC primes derive from the ParticleVerbs inventory.
    The paper's stimuli included "put down the vase" (p.5). -/
theorem experimental_pvcs_in_inventory :
    (Phenomena.Constructions.ParticleVerbs.inventory.any
      (· == Phenomena.Constructions.ParticleVerbs.lift_up)) = true ∧
    (Phenomena.Constructions.ParticleVerbs.inventory.any
      (· == Phenomena.Constructions.ParticleVerbs.put_down)) = true := by
  constructor <;> native_decide

/-- The ApplP analysis uses a LOW applicative.
    Low applicatives relate the applied argument (goal) to the theme,
    consistent with transfer/possession semantics ("give X to Y"). -/
def doc_appl_type : ApplType := .low

/-! ## §2. Structural analyses (Haddican et al.) -/

/-- **DOC, Small Clause**: `[VP V [SC DP_goal DP_theme]]` — paper's (3).
    Den Dikken (1995:25, ex. 41e): the dative is an instance of SC
    predication, with the goal as SC subject and theme as predicate. -/
def doc_sc : SyntacticObject :=
  merge V_give (merge DP_hsu DP_book)

/-- **DOC, Applicative** (Marantz 1993; Bruening 2010a,b):
    `[ApplP DP_goal [Appl' Appl [VP V DP_theme]]]` — paper's (6)/(9).
    Uses a low applicative (`doc_appl_type =.low`), relating goal to theme. -/
def doc_appl : SyntacticObject :=
  merge DP_hsu (merge Appl_h (merge V_give DP_book))

/-- **PVC, Small Clause** (Aarts 1989; den Dikken 1995; Svenonius 1996a,b):
    `[VP V [SC DP Prt]]` — paper's (4a), underlying obj-particle order.
    Den Dikken (1995:25, ex. 41d): the particle is an SC predicate
    ascribing a resultant state/location to the DP subject.
    Experimental primes used particle-object surface order ("put down the
    vase") to control for V-NP-X string similarity with DOC targets (p.5). -/
def pvc_sc : SyntacticObject :=
  merge V_lift (merge DP_hsu Prt_up)

/-- **PVC, Complex predicate**:
    `[VP [V lift+up] DP]` — paper's (5). V and particle form a composite
    terminal (complex head via head incorporation), not a phrase. Uses the
    existing `LexicalItem.combine` infrastructure for head-to-head movement. -/
def pvc_complexPred : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D] "lift").combine
                (LexicalItem.simple .P [] "up"), 7⟩) DP_hsu

/-- **PD, Prepositional dative** (control construction):
    `[VP [V' V DP_theme] [PP P DP_goal]]` — the baseline against which
    DOC priming is measured. One half of the dative alternation
    (see `Phenomena.ArgumentStructure.DativeAlternation`). -/
def pd : SyntacticObject :=
  merge (merge V_give DP_book) (merge P_to DP_hsu)

/-- **Non-PVC transitive control**: `[VP V DP]` — the baseline in the PV
    subdesign ("Ana lifted Hsu without a struggle"). A simple transitive
    with no particle, no small clause complement. -/
def transitive_control : SyntacticObject :=
  merge V_lift DP_hsu

/-! ## §3. @cite{dendikken-1995} SC family

@cite{dendikken-1995}'s monograph title is "Particles: On the Syntax of
Verb-Particle, *Triadic*, and *Causative* Constructions." His central
thesis (Ch.1, ex. 42) is that all subject-predicate relationships are
incarnated as small clauses:

    [SC subject [XP predicate]] (den Dikken 1995:27, ex. 44)

He identifies a family of constructions sharing this template (p.25, ex. 41):

    a. John is a fool/foolish. (copular)
    b. They consider John a fool/foolish. (ECM)
    c. They hammered the metal flat. (resultative)
    d. They put the books on the shelf. (PVC / locative)
    e. They gave the books to Mary. (triadic / dative)

All share the abstract tree shape `V [SC X Y]` = `node(leaf, node(leaf, leaf))`.
See also `Phenomena.Constructions.Resultatives.Data` for resultative data. -/

/-- **Resultative, Small Clause** (den Dikken 1995:25, ex. 41c):
    `[VP V [SC DP AP]]` — "They hammered the metal flat."
    The result-state AP is the SC predicate; the direct object DP
    is the SC subject to which the property is ascribed. -/
def resultative_sc : SyntacticObject :=
  merge V_hammer (merge DP_metal AP_flat)

/-- **Causative, Small Clause**:
    `[VP V [SC DP VP]]` — "She made the child laugh."
    The embedded VP is the SC predicate; the causee DP is the
    SC subject. See also `Minimalism.buildDecomposition` for the
    causative alternation via Voice. -/
def causative_sc : SyntacticObject :=
  merge V_make (merge DP_child VP_laugh)

/-! ## §4. Explicit shapes

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

theorem transitive_control_shape :
    transitive_control.shape = .node .leaf .leaf := rfl

theorem resultative_sc_shape :
    resultative_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

theorem causative_sc_shape :
    causative_sc.shape = .node .leaf (.node .leaf .leaf) := rfl

/-! ## §5. Structural isomorphism (Haddican et al. analyses)

The linking hypothesis: structural
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

/-- The non-PVC transitive control has a different shape from SC-DOC.
    This validates the experimental design: if priming tracks tree shape,
    non-PVC controls (simple transitives) should not prime DOCs. -/
theorem control_doc_not_isomorphic :
    structurallyIsomorphic transitive_control doc_sc = false := by native_decide

/-- The non-PVC control has the SAME shape as the complex predicate
    PVC analysis: both are `node(leaf, leaf)`. Under the complex predicate
    analysis, PVCs and simple transitives are structurally indistinguishable,
    predicting NO priming difference — but the experiment found one
    (β=0.296, p=.005). This is evidence against the complex predicate
    analysis at the tree-shape level. -/
theorem control_matches_complexPred :
    structurallyIsomorphic transitive_control pvc_complexPred = true := by native_decide

/-- Among the five Haddican et al. structures, SC is the unique source of
    DOC/PVC tree-shape isomorphism. All 10 pairwise comparisons: only
    SC-DOC = SC-PVC.

    N.B.: This is uniqueness among the analyses *formalized here*. The paper
    acknowledges other analyses (Bruening 2021, Pylkkänen low ApplP, Wood &
    Marantz i*) that could also yield isomorphism (see §7 below). -/
theorem sc_unique_among_haddican_analyses :
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

/-! ## §6. Den Dikken SC family isomorphism

All four members of the SC predication family share the same tree shape:
`node(leaf, node(leaf, leaf))`. This predicts mutual cross-construction
priming — resultatives and causatives should also prime DOCs. -/

/-- The SC family shares a single tree shape. PVCs, DOCs, resultatives,
    and causatives are all `V [SC Subj Pred]` (den Dikken 1995:25). -/
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

/-- None of the SC family members are isomorphic with PD (the control).
    All four should prime DOC relative to PD — Haddican et al. confirm
    this for PVC; the resultative and causative predictions are untested. -/
theorem sc_family_all_differ_from_pd :
    structurallyIsomorphic pvc_sc pd = false ∧
    structurallyIsomorphic resultative_sc pd = false ∧
    structurallyIsomorphic causative_sc pd = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §6a. SC family categorization

Each SC construction is tagged with its predicate category from
`SmallClause.lean`. This connects the geometric analysis (§§5–6) to
the category-level analysis: constructions share tree shape because
they share the `V [SC Subj Pred]` template, differing only in the
category of the predicate head. -/

/-- PVC is a P-predicate SC. -/
def pvc_category : SCPredCategory := .P

/-- DOC is a P-predicate SC — the dative P "to" is the SC predicate,
    incorporated into V in the DOC surface form.
    This is den Dikken's deep claim: DOC and PVC share category P because
    dative P is structurally a particle. -/
def doc_category : SCPredCategory := .P

/-- Resultative is an A-predicate SC (property resultatives). -/
def resultative_category : SCPredCategory := .A

/-- Causative is a V-predicate SC. -/
def causative_category : SCPredCategory := .V

/-- Copular/ECM is an N-predicate SC: "consider John a fool."
    Den Dikken (1995:25, ex. 41a-b). -/
def copular_category : SCPredCategory := .N

/-- DOC and PVC share SC predicate category P. This is one of
    den Dikken's central claims: dative P = particle, both are
    intransitive/ergative P heads mediating SC predication. -/
theorem doc_pvc_share_P : doc_category = pvc_category := rfl

/-- The SC family spans all four lexical categories {A, N, P, V}
    (den Dikken 1995:25, ex. 43). -/
theorem sc_family_covers_all_categories :
    pvc_category = .P ∧
    resultative_category = .A ∧
    causative_category = .V ∧
    copular_category = .N := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §6b. Nested SC for DOC

Den Dikken's DOC analysis: the theme is the SC subject (paralleling
the object's role in PVCs), and the PP `[PP to Goal]` is the SC
predicate — a P head with a goal complement:

    `V [SC Theme [PP P Goal]]` = `give [SC book [PP to Hsu]]`

P-incorporation into V yields the DOC surface ("give Hsu the book");
P in situ yields the PP-dative ("give the books to Mary"). This
derives the dative alternation from a single underlying SC structure,
exactly as PVC particle shift derives from `V [SC DP Prt]` — see
`DativeAlternation` for the empirical data.

The nested analysis has more internal structure than the flat
`V [SC DP DP]` from @cite{kayne-1984}, but both share the outermost
SC template `V [SC Subj XP]`. -/

/-- Nested SC DOC: `give [SC book [PP to Hsu]]`.
    @cite{dendikken-1995}: the theme (book) is the SC subject —
    paralleling PVCs where the object is SC subject — and the PP
    "to Hsu" is the SC predicate (P head with goal complement).
    P-incorporation yields DOC; P in situ yields PP-dative. -/
def doc_nested : SyntacticObject :=
  merge V_give (merge DP_book (merge P_to DP_hsu))

theorem doc_nested_shape :
    doc_nested.shape = .node .leaf (.node .leaf (.node .leaf .leaf)) := rfl

/-- The nested SC DOC is NOT isomorphic to the flat SC DOC.
    More internal structure → different tree geometry. -/
theorem doc_nested_not_flat :
    structurallyIsomorphic doc_nested doc_sc = false := by native_decide

/-- The nested SC DOC IS isomorphic to the ApplP analysis — both
    have a right-branching depth-3 tree `node(leaf, node(leaf, node(leaf, leaf)))`.
    They differ only in terminal labels: the intermediate head is
    P ("to") in den Dikken's analysis vs Appl in Marantz's. -/
theorem doc_nested_matches_appl :
    structurallyIsomorphic doc_nested doc_appl = true := by native_decide

/-! ## §7. @cite{bruening-2021}: process-level vs tree-shape isomorphism

@cite{bruening-2021} proposes complex predicate formation (V+Head) for BOTH
DOC and PVC. The paper notes this would "also furnish isomorphism, but
at the process level (both involve V+Head complex predicate formation)
rather than tree-shape identity" (p.11).

Under Bruening's analysis:
- DOC: `[VP [V+R] DP_goal DP_theme]` — V incorporates a relational head
- PVC: `[VP [V+Prt] DP]` — V incorporates the particle

The tree shapes DIFFER (the DOC has a binary complement, the PVC has a
single complement), but both derivations involve the same operation
(complex predicate formation = head incorporation). If priming can be
driven by shared derivational operations (not just shared tree shapes),
Bruening's analysis also predicts PVC→DOC priming. -/

/-- @cite{bruening-2021} DOC: `[VP [V+R] DP_goal DP_theme]`. V incorporates
    a relational head R, yielding a complex predicate with two DP
    complements. -/
def doc_bruening : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D, .D] "give").combine
                (LexicalItem.simple .P [] "∅_R"), 14⟩)
       (merge DP_hsu DP_book)

/-- Bruening's PVC is the same as Johnson's complex predicate analysis. -/
def pvc_bruening := pvc_complexPred

theorem doc_bruening_shape :
    doc_bruening.shape = .node .leaf (.node .leaf .leaf) := rfl

/-- Bruening's DOC and PVC have DIFFERENT tree shapes. The DOC has a
    binary complement `node(leaf, leaf)`, yielding `node(leaf, node(leaf, leaf))`;
    the PVC has a single complement, yielding `node(leaf, leaf)`. -/
theorem bruening_shapes_differ :
    structurallyIsomorphic doc_bruening pvc_bruening = false := by native_decide

/-- Both Bruening analyses involve complex predicate formation: the verb's
    head LI is complex (result of `LexicalItem.combine`). This is the
    process-level isomorphism that the paper distinguishes from tree-shape
    identity. -/
theorem bruening_both_use_incorporation :
    (match doc_bruening with
     | .node (.leaf tok) _ => tok.item.isComplex
     | _ => false) = true ∧
    (match pvc_bruening with
     | .node (.leaf tok) _ => tok.item.isComplex
     | _ => false) = true := by
  constructor <;> native_decide

/-- Bruening's DOC has the same tree shape as SC-DOC (both are
    `node(leaf, node(leaf, leaf))`), since both have a head with a binary
    complement — they differ only in terminal labels (complex vs simple
    head) and in the interpretation of the inner node (complement pair
    vs small clause). Tree-shape comparison alone cannot distinguish
    these two DOC analyses. -/
theorem bruening_doc_matches_sc_doc :
    structurallyIsomorphic doc_bruening doc_sc = true := by native_decide

/-! ## §8. Bridge theorems

Connecting structural predictions to experimental data from
`Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026`. -/

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

/-- The complex predicate PVC analysis cannot explain the priming
    asymmetry: complex-predicate PVC has the same tree shape as a
    simple transitive control, predicting no priming difference.
    But PVCs DO prime DOCs while controls do not (β=0.296, p=.005). -/
theorem complexPred_fails_at_control :
    pvc_primes_doc.significant = true ∧
    structurallyIsomorphic pvc_complexPred transitive_control = true := by
  exact ⟨rfl, by native_decide⟩

end Phenomena.ArgumentStructure.Bridge.MinimalismSmallClause
