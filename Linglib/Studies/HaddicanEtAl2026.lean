import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.SmallClause
import Linglib.Phenomena.Constructions.ParticleVerbs.Data
import Linglib.Studies.Bruening2021

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

- `ArnoldEtAl2000`: The same two constructions
  (dative alternation + particle placement) studied from a processing
  perspective — heaviness drives linearization while abstract structure
  drives priming.
- `Phenomena.ArgumentStructure.DativeAlternation`: Records both DOC and PD
  frames as grammatical — the precondition for the priming study.
-/

namespace HaddicanEtAl2026

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

open Minimalist

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
  constructor <;> decide

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

/-- A leaf shape, abbreviated. -/
-- Local alias for substrate `Minimalist.leafShape` (hoisted in 0.230.877).
private abbrev leafShape : FreeCommMagma Unit := Minimalist.leafShape

/-- DOC small clause: `[VP V [SC DP DP]]` — three leaves in a
    right-branching shape. -/
theorem doc_sc_shape :
    doc_sc.shape = leafShape * (leafShape * leafShape) := by
  decide

/-- DOC-Applicative: `[ApplP DP_goal [Appl' Appl [VP V DP_theme]]]` — 4 leaves. -/
theorem doc_appl_shape :
    doc_appl.shape = leafShape * (leafShape * (leafShape * leafShape)) := by
  decide

theorem pvc_sc_shape :
    pvc_sc.shape = leafShape * (leafShape * leafShape) := by decide

theorem pvc_complexPred_shape :
    pvc_complexPred.shape = leafShape * leafShape := by decide

theorem pd_shape :
    pd.shape = (leafShape * leafShape) * (leafShape * leafShape) := by decide

theorem transitive_control_shape :
    transitive_control.shape = leafShape * leafShape := by decide

theorem resultative_sc_shape :
    resultative_sc.shape = leafShape * (leafShape * leafShape) := by decide

theorem causative_sc_shape :
    causative_sc.shape = leafShape * (leafShape * leafShape) := by decide

/-! ## Structural isomorphism

`structurallyIsomorphic x y` is `Prop`-valued (substrate change at
0.230.865; revived as `x.shape = y.shape`); previously `Bool`-valued
on planar `TraceTree`. Decidable, so `decide` works. -/

/-- SC-DOC and SC-PVC share tree shape. -/
theorem sc_doc_pvc_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc := by decide

/-- ApplP-DOC and ComplexPred-PVC have different shapes. -/
theorem appl_complexPred_not_isomorphic :
    ¬ structurallyIsomorphic doc_appl pvc_complexPred := by decide

/-- SC-DOC differs from ApplP-DOC. -/
theorem sc_appl_doc_not_isomorphic :
    ¬ structurallyIsomorphic doc_sc doc_appl := by decide

/-- SC-DOC differs from PD. -/
theorem sc_doc_pd_not_isomorphic :
    ¬ structurallyIsomorphic doc_sc pd := by decide

/-- SC-PVC differs from PD. -/
theorem sc_pvc_pd_not_isomorphic :
    ¬ structurallyIsomorphic pvc_sc pd := by decide

/-- The non-PVC transitive control has a different shape from SC-DOC. -/
theorem control_doc_not_isomorphic :
    ¬ structurallyIsomorphic transitive_control doc_sc := by decide

/-- The non-PVC control has the SAME shape as the complex predicate PVC. -/
theorem control_matches_complexPred :
    structurallyIsomorphic transitive_control pvc_complexPred := by decide

/-- SC is the unique source of DOC/PVC tree-shape isomorphism. -/
theorem sc_unique_among_haddican_analyses :
    structurallyIsomorphic doc_sc pvc_sc ∧
    ¬ structurallyIsomorphic doc_sc doc_appl ∧
    ¬ structurallyIsomorphic doc_sc pvc_complexPred ∧
    ¬ structurallyIsomorphic doc_sc pd ∧
    ¬ structurallyIsomorphic doc_appl pvc_sc ∧
    ¬ structurallyIsomorphic doc_appl pvc_complexPred ∧
    ¬ structurallyIsomorphic doc_appl pd ∧
    ¬ structurallyIsomorphic pvc_sc pvc_complexPred ∧
    ¬ structurallyIsomorphic pvc_sc pd ∧
    ¬ structurallyIsomorphic pvc_complexPred pd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Den Dikken SC family isomorphism -/

/-- The SC family shares a single tree shape. -/
theorem sc_family_same_shape :
    doc_sc.shape = pvc_sc.shape ∧
    doc_sc.shape = resultative_sc.shape ∧
    doc_sc.shape = causative_sc.shape := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- All four SC constructions are pairwise isomorphic. -/
theorem sc_family_all_isomorphic :
    structurallyIsomorphic doc_sc pvc_sc ∧
    structurallyIsomorphic doc_sc resultative_sc ∧
    structurallyIsomorphic doc_sc causative_sc ∧
    structurallyIsomorphic pvc_sc resultative_sc ∧
    structurallyIsomorphic pvc_sc causative_sc ∧
    structurallyIsomorphic resultative_sc causative_sc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- None of the SC family members are isomorphic with PD. -/
theorem sc_family_all_differ_from_pd :
    ¬ structurallyIsomorphic pvc_sc pd ∧
    ¬ structurallyIsomorphic resultative_sc pd ∧
    ¬ structurallyIsomorphic causative_sc pd := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

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
    doc_nested.shape = leafShape * (leafShape * (leafShape * leafShape)) := by
  decide

theorem doc_nested_not_flat :
    ¬ structurallyIsomorphic doc_nested doc_sc := by decide

theorem doc_nested_matches_appl :
    structurallyIsomorphic doc_nested doc_appl := by decide

/-! ## @cite{bruening-2021}: process-level isomorphism

`doc_bruening` below is a `SyntacticObject` witness of Bruening's V+P
amalgam analysis. The lexical-fragment side of the same paper —
Bruening's classification of implicit-argument behavior across
~43 ditransitive verbs (Table 56) — is formalized in
`Studies/Bruening2021.lean`. The
`bruening_give_field_consistent` theorem below ties this structural
witness to that lexical-fragment side. -/

def doc_bruening : SyntacticObject :=
  merge (.leaf ⟨(LexicalItem.simple .V [.D, .D] "give").combine
                (LexicalItem.simple .P [] "∅_R"), 14⟩)
       (merge DP_hsu DP_book)

def pvc_bruening := pvc_complexPred

theorem doc_bruening_shape :
    doc_bruening.shape = leafShape * (leafShape * leafShape) := by decide

theorem bruening_shapes_differ :
    ¬ structurallyIsomorphic doc_bruening pvc_bruening := by decide

/-- Both Bruening structures use a complex (incorporated) head leaf.
    The original theorem (planar substrate) projected the head via
    `match doc_bruening with | .node (.leaf tok) _ => tok.item.isComplex`,
    which doesn't reduce under MCB nonplanar SOs (children of `.mul` are
    unordered).

    The claim itself remains true and verifiable: both DOC and PVC
    structures contain a complex (head-incorporated) LIToken among their
    subtrees. Reformulate as a Multiset-membership claim:

    ```
    (∃ tok ∈ doc_bruening.subtrees.filterMap getLIToken, tok.item.isComplex) ∧
    (∃ tok ∈ pvc_bruening.subtrees.filterMap getLIToken, tok.item.isComplex)
    ```

    TODO Phase 2 / polish: prove the Multiset-version directly, or
    re-derive from a head-function-aware `headLIToken : SO → Option LIToken`
    once Phase 2 substrate lands. -/
theorem bruening_both_use_incorporation :
    (∃ tok ∈ (doc_bruening.subtrees.filterMap SyntacticObject.getLIToken), tok.item.isComplex) ∧
    (∃ tok ∈ (pvc_bruening.subtrees.filterMap SyntacticObject.getLIToken), tok.item.isComplex) := by
  refine ⟨?_, ?_⟩
  · -- DOC witness: the explicit complex `give.combine ∅_R` LIToken
    refine ⟨⟨(LexicalItem.simple .V [.D, .D] "give").combine
              (LexicalItem.simple .P [] "∅_R"), 14⟩, ?_, by decide⟩
    rw [Multiset.mem_filterMap]
    refine ⟨SyntacticObject.leaf
            ⟨(LexicalItem.simple .V [.D, .D] "give").combine
              (LexicalItem.simple .P [] "∅_R"), 14⟩, ?_, rfl⟩
    -- The complex-give leaf is in `doc_bruening.subtrees` as the LHS of the outer merge
    show _ ∈ doc_bruening.subtrees
    simp only [doc_bruening, merge, SyntacticObject.subtrees_mul,
               SyntacticObject.subtrees_leaf,
               Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto
  · -- PVC witness: the explicit complex `lift.combine up` LIToken
    refine ⟨⟨(LexicalItem.simple .V [.D] "lift").combine
              (LexicalItem.simple .P [] "up"), 7⟩, ?_, by decide⟩
    rw [Multiset.mem_filterMap]
    refine ⟨SyntacticObject.leaf
            ⟨(LexicalItem.simple .V [.D] "lift").combine
              (LexicalItem.simple .P [] "up"), 7⟩, ?_, rfl⟩
    show _ ∈ pvc_bruening.subtrees
    simp only [pvc_bruening, pvc_complexPred, merge,
               SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
               Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto

theorem bruening_doc_matches_sc_doc :
    structurallyIsomorphic doc_bruening doc_sc := by decide

/-! ### Bridge to Bruening 2021 lexical fragment

`doc_bruening` above is a `SyntacticObject` witness; this theorem ties
it to the corresponding lexical-fragment entry in `Bruening2021.lean`,
ensuring the verb we structurally treat as "give-in-DOC" is also the
verb whose implicit-argument profile licenses Bruening's Table (56)
classification. If `Verbal.lean` ever moves `give` to a different
complement type or implicit-arg profile, this bridge fails — alerting
both files. -/
open Fragments.English.Predicates.Verbal Semantics.Lexical in
theorem bruening_give_field_consistent :
    give.complementType = ComplementType.np_np
    ∧ give.altComplementType = some ComplementType.np_pp
    ∧ give.implicitObj = some ImplicitInterp.indef
    ∧ give.implicitGoal = some ImplicitInterp.def := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Bridge to experimental data -/

/-- The SC analysis predicts DOC/PVC isomorphism and DOC/PD non-isomorphism. -/
theorem sc_predictions :
    structurallyIsomorphic doc_sc pvc_sc ∧
    ¬ structurallyIsomorphic doc_sc pd :=
  ⟨sc_doc_pvc_isomorphic, sc_doc_pd_not_isomorphic⟩

/-- The ApplP + ComplexPred combination predicts DOC/PVC non-isomorphism. -/
theorem appl_complexPred_no_isomorphism :
    ¬ structurallyIsomorphic doc_appl pvc_complexPred :=
  appl_complexPred_not_isomorphic

/-- PVC priming magnitude equals DOC priming magnitude, as SC predicts. -/
theorem sc_predicts_equal_magnitude :
    pvc_doc_equivalent.significant = false ∧
    doc_sc.shape = pvc_sc.shape := by
  refine ⟨rfl, ?_⟩
  decide

/-- The complex predicate PVC analysis cannot explain the priming asymmetry. -/
theorem complexPred_fails_at_control :
    pvc_primes_doc.significant = true ∧
    structurallyIsomorphic pvc_complexPred transitive_control := by
  refine ⟨rfl, ?_⟩
  decide

/-! ## IsSmallClause companion-predicate witnesses

The flat encodings (`pvc_sc`, `doc_sc`, `resultative_sc`,
`causative_sc`) name the *whole* `[VP V SC]` constituent — the SC
itself is the right child. We characterise the inner SCs against
the `IsSmallClause` companion predicate (`SmallClause.lean`).

Three of the four families satisfy the predicate; **DOC's flat
DP–DP encoding does not**. This surfaces a real subtlety: Haddican
et al. (2026) explicitly say (p.2) "we set aside details of the
internal structure of the small clause", and the flat DP–DP shape
is the deliberate simplification. The richer DOC encoding (with
BE+P decomposition / Predicate Inversion) in
`Studies/Dendikken1995` does satisfy
`IsSmallClause` at every nested SC layer. -/

/-- Phase 1.0 caveat: `IsSmallClause` is `noncomputable` because it
    routes through `outerCat`/`headCat`, which are Phase 1.0 placeholders
    via `Quot.out` on the FreeCommMagma carrier. Concrete-instance checks
    via `decide` fail at the kernel-reduction step. TODO Phase 2: once
    LCA-based head selection lands, restore `by decide`. -/
theorem pvc_sc_inner_isSmallClause :
    IsSmallClause (merge DP_hsu Prt_up) := by
  rw [isSmallClause_merge]
  right
  -- Prt_up has outerCat = .P
  show IsSmallClausePredicate Prt_up
  unfold IsSmallClausePredicate
  left
  show HeadFunction.leftSpine.outerCat (mkLeafPhon _ _ _ _) = _
  simp only [Prt_up, mkLeafPhon, HeadFunction.outerCat_leaf]
  rfl

theorem resultative_sc_inner_isSmallClause :
    IsSmallClause (merge DP_metal AP_flat) := by
  rw [isSmallClause_merge]
  right
  show IsSmallClausePredicate AP_flat
  unfold IsSmallClausePredicate
  right; left
  show HeadFunction.leftSpine.outerCat (mkLeafPhon _ _ _ _) = _
  simp only [AP_flat, mkLeafPhon, HeadFunction.outerCat_leaf]
  rfl

theorem causative_sc_inner_isSmallClause :
    IsSmallClause (merge DP_child VP_laugh) := by
  rw [isSmallClause_merge]
  right
  show IsSmallClausePredicate VP_laugh
  unfold IsSmallClausePredicate
  right; right; left
  show HeadFunction.leftSpine.outerCat (mkLeafPhon _ _ _ _) = _
  simp only [VP_laugh, mkLeafPhon, HeadFunction.outerCat_leaf]
  rfl

/-- Diagnostic: the flat DP–DP DOC encoding does NOT satisfy
    `IsSmallClause` — neither child is in the SC predicate set
    {P,A,V,N}. Both children are DPs (head category D). The companion
    predicate surfaces the simplification — the encoding is correct
    *for the priming argument* but incomplete as a structural SC
    analysis; den Dikken's BE+P decomposition supplies the missing
    predicate. -/
theorem doc_sc_flat_inner_not_smallClause :
    ¬ IsSmallClause (merge DP_hsu DP_book) := by
  rw [isSmallClause_merge]
  rintro (hl | hr)
  · -- DP_hsu has outerCat = .D, not in {P,A,V,N}
    unfold IsSmallClausePredicate at hl
    have hhsu : DP_hsu.headCat = .D := by
      show HeadFunction.leftSpine.outerCat (mkLeafPhon _ _ _ _) = _
      simp only [DP_hsu, mkLeafPhon, HeadFunction.outerCat_leaf]; rfl
    rcases hl with h | h | h | h <;> rw [hhsu] at h <;> contradiction
  · unfold IsSmallClausePredicate at hr
    have hbook : DP_book.headCat = .D := by
      show HeadFunction.leftSpine.outerCat (mkLeafPhon _ _ _ _) = _
      simp only [DP_book, mkLeafPhon, HeadFunction.outerCat_leaf]; rfl
    rcases hr with h | h | h | h <;> rw [hbook] at h <;> contradiction

end HaddicanEtAl2026
