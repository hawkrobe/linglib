/-
# Extended Projection: Derived Properties

Properties derived from @cite{grimshaw-2005} Extended Projection theory.

## Key Ideas

1. **Semantic types track EP levels**: F0 = ⟨e,t⟩ properties, higher levels
   progressively close off arguments (event quantification, tense, force).
2. **Generalized Theta Criterion**: Only L-heads (F0) assign theta roles.
3. **Complement/Specifier in EP terms**: Complements are EP-internal (same family,
   lower F-value); specifiers are EP-external.
4. **Truncation**: Small clauses are truncated EPs lacking functional layers.

-/

import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

namespace Minimalism

-- ═══════════════════════════════════════════════════════════════
-- Part 1: Semantic Types of EP Levels
-- ═══════════════════════════════════════════════════════════════

/-- The semantic type associated with a projection level (Grimshaw §1.5).
    EP levels map systematically to semantic types:
    - F0 heads denote properties ⟨e,t⟩ (V = event predicates, N = entity predicates)
    - Higher functional heads progressively bind variables
    - The top of a verbal EP denotes a proposition ⟨s,t⟩
    - The top of a nominal EP denotes an entity (e) -/
inductive EPSemanticType where
  | property       -- ⟨e,t⟩: predicates (V, N, A, P at F0)
  | proposition    -- ⟨s,t⟩: propositions (C at F3 in verbal EP)
  | entity         -- e: entities (D at F1 in nominal EP)
  | intermediate   -- between property and closed type (v, T)
  deriving Repr, DecidableEq, BEq

/-- Map categories to their EP semantic type.
    This reflects how functional structure progressively
    changes the denotation from ⟨e,t⟩ to a closed type. -/
def epSemanticType : Cat → EPSemanticType
  | .V | .N | .A | .P => .property       -- F0: property-denoting
  | .v                 => .intermediate   -- F1: event quantification domain
  | .n                 => .intermediate   -- F1: categorizer (gender/class, @cite{marantz-2001})
  | .a                 => .intermediate   -- F1: adjectival categorizer (@cite{panagiotidis-2015})
  | .Voice             => .intermediate   -- F1: introduces external argument (@cite{kratzer-1996})
  | .Appl              => .intermediate   -- F1: introduces applied argument (@cite{pylkknen-2008})
  | .Num               => .intermediate   -- F2: number inflection (@cite{ritter-1991})
  | .Q                 => .intermediate   -- F3: quantity/classifier (@cite{borer-2005})
  | .D                 => .entity         -- F4: entity-denoting (in nominal EP)
  | .T                 => .intermediate   -- F2: tense/aspect binding
  | .Neg               => .intermediate   -- F2: negation (@cite{pollock-1989})
  | .Mod               => .intermediate   -- F2: modality (@cite{cinque-1999})
  | .Pol               => .intermediate   -- F2: polarity (@cite{laka-1990})
  | .Asp               => .intermediate   -- F2: aspect (@cite{cinque-1999})
  | .Evid              => .intermediate   -- F2: evidential (@cite{cinque-1999})
  | .Foc               => .intermediate   -- F4: focus (@cite{rizzi-1997} split-CP)
  | .Top               => .intermediate   -- F5: topic (@cite{rizzi-1997} split-CP)
  | .Rel               => .intermediate   -- F5: relative (@cite{rizzi-1997})
  | .Fin               => .intermediate   -- F3: finiteness (@cite{rizzi-1997})
  | .C                 => .proposition    -- F6: proposition (force)
  | .Force             => .proposition    -- F6: force (@cite{rizzi-1997} split-CP)
  | .SA                => .proposition    -- F7: speech act (@cite{speas-tenny-2003})

-- ═══════════════════════════════════════════════════════════════
-- Part 2: Generalized Theta Criterion
-- ═══════════════════════════════════════════════════════════════

/-- Only L-heads (F0 = lexical categories) assign theta roles.
    Functional heads (v, D, T, C) do not introduce new theta roles —
    they provide functional structure (agreement, tense, force, determination).

    @cite{grimshaw-2005} Definition 10: theta-role assignment is restricted
    to the lexical level of projection. -/
def canAssignTheta (c : Cat) : Bool := isLHead c

/-- Theta assignment is exactly the lexical heads. -/
theorem theta_iff_lexical (c : Cat) :
    canAssignTheta c = true ↔ isLHead c = true := by
  simp [canAssignTheta]

-- ═══════════════════════════════════════════════════════════════
-- Part 3: EP-Internal vs EP-External
-- ═══════════════════════════════════════════════════════════════

/-- A daughter is EP-internal (complement) if it shares [±V, ±N] features
    with its parent AND has a strictly lower F-value.

    EP-internal elements are inside the extended projection:
    - VP is EP-internal to vP (both verbal, F0 < F1)
    - NP is EP-internal to DP (both nominal, F0 < F1)

    EP-external elements (specifiers) are outside:
    - DP in Spec-vP is EP-external (nominal ≠ verbal) -/
def isEPInternal (daughter parent : Cat) : Bool :=
  categoryConsistent daughter parent && (fValue daughter < fValue parent)

/-- EP-external: either different family or not lower F-value.
    Specifiers are typically EP-external to the projection they sit. -/
def isEPExternal (daughter parent : Cat) : Bool :=
  !isEPInternal daughter parent

-- ═══════════════════════════════════════════════════════════════
-- Part 4: Standard EP Spines
-- ═══════════════════════════════════════════════════════════════

/-- Full verbal EP: V → v → T → C.
    This is the standard clausal spine for finite clauses. -/
def fullVerbalEP : List Cat := [.V, .v, .T, .C]

/-- Full nominal EP: N → n → Q → Num → D.
    Q (classifier / individuation) is below Num (number / counting)
    per @cite{borer-2005}: individuation must precede counting. -/
def fullNominalEP : List Cat := [.N, .n, .Q, .Num, .D]

/-- Small clause EP: just the lexical head, no functional layers.
    E.g., "consider [SC him intelligent]" — the SC has no T or C. -/
def smallClauseVerbalEP : List Cat := [.V]

/-- Adjectival EP: A → a.
    The minimal adjectival extended projection, parallel to the
    verbal (V → v) and nominal (N → n) categorizer layers.
    Further adjectival functional structure (DegP, etc.) is
    language-dependent and not included here. -/
def adjectivalEP : List Cat := [.A, .a]

/-- Adjectival small clause EP: just A.
    E.g., "consider [SC him happy]" -/
def smallClauseAdjectivalEP : List Cat := [.A]

/-- Infinitival EP: V → v → T (no C).
    E.g., "want [to leave]" — truncated at T, no complementizer. -/
def infinitivalEP : List Cat := [.V, .v, .T]

/-- Is this EP truncated (missing functional layers compared to the full EP)? -/
def isTruncated (spine : List Cat) : Bool :=
  match spine.head?.map catFamily with
  | some .verbal     => spine.length < fullVerbalEP.length
  | some .nominal    => spine.length < fullNominalEP.length
  | _                => false  -- A and P have no standard extended EP

-- ═══════════════════════════════════════════════════════════════
-- Part 5: Argument Domain (Grimshaw / Anand et al.)
-- ═══════════════════════════════════════════════════════════════

/-- The highest F-value that still denotes a property ⟨e,t⟩ or is
    in the intermediate zone. This defines the argument domain boundary.

    For verbal EPs: the argument domain extends to vP (F1)
    - vP still denotes ⟨e,t⟩ (property of events)
    - TP (F2) starts binding tense → no longer ⟨e,t⟩

    For nominal EPs: the argument domain extends to nP (F1)
    - nP still denotes ⟨e,t⟩ (property of entities)
    - NumP (F2) starts binding number → no longer ⟨e,t⟩
    This parallels the verbal domain: v ↔ n at the same F-level. -/
def argumentDomainCat (topCat : Cat) : Cat :=
  match topCat with
  | .C | .Force | .Fin | .Foc | .Top | .Rel | .SA
  | .T | .Neg | .Mod | .Pol | .Asp | .Evid => .v  -- clausal functional heads → vP is argument domain
  | .D | .Q | .Num                          => .n  -- nominal functional heads → nP is argument domain
  | _       => topCat  -- small clause / lexical head → the SC itself is argument domain

/-- Is a category within the argument domain of a given top category?
    The argument domain includes all F-levels ≤ the boundary. -/
def isInArgumentDomain (c topCat : Cat) : Bool :=
  fValue c ≤ fValue (argumentDomainCat topCat)

-- ═══════════════════════════════════════════════════════════════
-- Part 6: Bridge Theorems
-- ═══════════════════════════════════════════════════════════════

/-- v denotes an intermediate type (event quantification domain). -/
theorem v_is_intermediate :
    epSemanticType .v = .intermediate := by decide

/-- C denotes a proposition (clausal force). -/
theorem c_is_proposition :
    epSemanticType .C = .proposition := by decide

/-- D denotes an entity (determination/referentiality). -/
theorem d_is_entity :
    epSemanticType .D = .entity := by decide

/-- Nominal categorizer n is intermediate (still ⟨e,t⟩-ish). -/
theorem n_is_intermediate :
    epSemanticType .n = .intermediate := by decide

/-- Q is intermediate (classifier/individuation: CUM → QUA). -/
theorem q_is_intermediate :
    epSemanticType .Q = .intermediate := by decide

/-- Num is intermediate (number/counting: QUA → measured). -/
theorem num_is_intermediate :
    epSemanticType .Num = .intermediate := by decide

/-- All lexical heads denote properties. -/
theorem lexical_heads_are_properties :
    epSemanticType .V = .property ∧ epSemanticType .N = .property ∧
    epSemanticType .A = .property ∧ epSemanticType .P = .property := by decide

/-- VP is EP-internal to vP (complement position). -/
theorem vp_internal_to_vp :
    isEPInternal .V .v = true := by decide

/-- NP is EP-internal to nP (complement of categorizer). -/
theorem np_internal_to_np :
    isEPInternal .N .n = true := by decide

/-- nP is EP-internal to QP (complement of classifier/individuation). -/
theorem np_internal_to_qp :
    isEPInternal .n .Q = true := by decide

/-- QP is EP-internal to NumP (complement of number/counting). -/
theorem qp_internal_to_nump :
    isEPInternal .Q .Num = true := by decide

/-- NumP is EP-internal to DP (complement of determiner). -/
theorem nump_internal_to_dp :
    isEPInternal .Num .D = true := by decide

/-- NP is EP-internal to DP (transitively). -/
theorem np_internal_to_dp :
    isEPInternal .N .D = true := by decide

/-- DP is EP-external to vP (specifier position):
    different [±V, ±N] features (nominal ≠ verbal). -/
theorem dp_external_to_vp :
    isEPExternal .D .v = true := by decide

/-- The argument domain of a full clause (C) is vP. -/
theorem full_clause_argdomain :
    argumentDomainCat .C = .v := by decide

/-- The argument domain of a TP is also vP. -/
theorem tp_argdomain :
    argumentDomainCat .T = .v := by decide

/-- The argument domain of a full DP is nP (parallel to vP for clauses). -/
theorem full_dp_argdomain :
    argumentDomainCat .D = .n := by decide

/-- The argument domain of QP is nP. -/
theorem qp_argdomain :
    argumentDomainCat .Q = .n := by decide

/-- The argument domain of NumP is nP. -/
theorem nump_argdomain :
    argumentDomainCat .Num = .n := by decide

/-- V is within the argument domain of a full clause. -/
theorem v_in_argdomain :
    isInArgumentDomain .V .C = true := by decide

/-- v is within the argument domain of a full clause. -/
theorem v_head_in_argdomain :
    isInArgumentDomain .v .C = true := by decide

/-- T is NOT within the argument domain of a full clause. -/
theorem t_not_in_argdomain :
    isInArgumentDomain .T .C = false := by decide

/-- C is NOT within the argument domain (it's the top). -/
theorem c_not_in_argdomain :
    isInArgumentDomain .C .C = false := by decide

/-- Full verbal EP is well-formed: consistent and monotone. -/
theorem full_verbal_ep_wellformed :
    allCategoryConsistent fullVerbalEP = true ∧
    allFMonotone fullVerbalEP = true := by decide

/-- Full nominal EP is well-formed: consistent and monotone. -/
theorem full_nominal_ep_wellformed :
    allCategoryConsistent fullNominalEP = true ∧
    allFMonotone fullNominalEP = true := by decide

/-- Adjectival EP is well-formed: consistent and monotone. -/
theorem adjectival_ep_wellformed :
    allCategoryConsistent adjectivalEP = true ∧
    allFMonotone adjectivalEP = true := by decide

/-- Infinitival EP is well-formed. -/
theorem infinitival_ep_wellformed :
    allCategoryConsistent infinitivalEP = true ∧
    allFMonotone infinitivalEP = true := by decide

/-- A small clause is truncated relative to a full verbal EP. -/
theorem small_clause_is_truncated :
    isTruncated smallClauseVerbalEP = true := by decide

/-- A full verbal EP is not truncated. -/
theorem full_verbal_not_truncated :
    isTruncated fullVerbalEP = false := by decide

/-- F1+ heads cannot assign theta roles (@cite{grimshaw-2005} Definition 10).
    Note: Panagiotidis (2015 §4.5) argues categorizers (v, n, a) are lexical,
    not functional — but in Grimshaw's F-value system they are F1 (non-lexical).
    The theta restriction here follows Grimshaw, not Panagiotidis. -/
theorem functional_heads_no_theta :
    canAssignTheta .v = false ∧ canAssignTheta .n = false ∧
    canAssignTheta .a = false ∧
    canAssignTheta .Num = false ∧ canAssignTheta .Q = false ∧
    canAssignTheta .D = false ∧
    canAssignTheta .T = false ∧ canAssignTheta .C = false := by decide

/-- Lexical heads can assign theta roles. -/
theorem lexical_heads_assign_theta :
    canAssignTheta .V = true ∧ canAssignTheta .N = true ∧
    canAssignTheta .A = true ∧ canAssignTheta .P = true := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Well-Formedness of Split-CP Spines
-- ═══════════════════════════════════════════════════════════════

/-- The split-CP spine is well-formed (consistent and monotone). -/
theorem splitCP_ep_wellformed :
    allCategoryConsistent splitCPVerbalEP = true ∧
    allFMonotone splitCPVerbalEP = true := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 8: Split-CP EP-Internal Relations
-- ═══════════════════════════════════════════════════════════════

/-- Fin is EP-internal to Foc: same [+V,-N], F3 < F4.
    The IP/CP boundary (Fin) is properly dominated by focus. -/
theorem fin_internal_to_foc : isEPInternal .Fin .Foc = true := by decide

/-- Foc is EP-internal to Top: same [+V,-N], F4 < F5.
    Focus is below topic in the C-domain hierarchy. -/
theorem foc_internal_to_top : isEPInternal .Foc .Top = true := by decide

/-- Top is EP-internal to C: same [+V,-N], F5 < F6.
    Topic is below the complementizer (= Force in unsplit contexts). -/
theorem top_internal_to_c : isEPInternal .Top .C = true := by decide

/-- T is EP-internal to Fin: same [+V,-N], F2 < F3.
    Tense is properly dominated by finiteness. -/
theorem t_internal_to_fin : isEPInternal .T .Fin = true := by decide

/-- Fin and Foc are NOT perfect projections of each other: F3 ≠ F4.
    Before the fValue fix, both had fValue 3 and this was incorrectly true. -/
theorem fin_foc_not_perfect : perfectProjection .Fin .Foc = false := by decide

end Minimalism
