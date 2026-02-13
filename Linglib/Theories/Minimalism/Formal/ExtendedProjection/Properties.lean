/-
# Extended Projection: Derived Properties

Properties derived from Grimshaw (2005) Extended Projection theory.

## Key Ideas

1. **Semantic types track EP levels**: F0 = ⟨e,t⟩ properties, higher levels
   progressively close off arguments (event quantification, tense, force).
2. **Generalized Theta Criterion**: Only L-heads (F0) assign theta roles.
3. **Complement/Specifier in EP terms**: Complements are EP-internal (same family,
   lower F-value); specifiers are EP-external.
4. **Truncation**: Small clauses are truncated EPs lacking functional layers.

## References

- Grimshaw, J. (2005). Words and Structure, Chapters 1, 2.
- Anand, P., Hardt, D., & McCloskey, J. (2025). Sluicing and Syntactic Identity.
-/

import Linglib.Theories.Minimalism.Formal.ExtendedProjection.Basic

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
  | .Voice             => .intermediate   -- F1: introduces external argument (Kratzer 1996)
  | .Appl              => .intermediate   -- F1: introduces applied argument (Pylkkänen 2008)
  | .D                 => .entity         -- F1: entity-denoting (in nominal EP)
  | .T                 => .intermediate   -- F2: tense/aspect binding
  | .Fin               => .intermediate   -- F3: finiteness (Rizzi 1997)
  | .C                 => .proposition    -- F3: proposition (force)
  | .SA                => .proposition    -- F4: speech act (Speas & Tenny 2003)

-- ═══════════════════════════════════════════════════════════════
-- Part 2: Generalized Theta Criterion
-- ═══════════════════════════════════════════════════════════════

/-- Only L-heads (F0 = lexical categories) assign theta roles.
    Functional heads (v, D, T, C) do not introduce new theta roles —
    they provide functional structure (agreement, tense, force, determination).

    Grimshaw (2005) Definition 10: theta-role assignment is restricted
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
    Specifiers are typically EP-external to the projection they sit in. -/
def isEPExternal (daughter parent : Cat) : Bool :=
  !isEPInternal daughter parent

-- ═══════════════════════════════════════════════════════════════
-- Part 4: Standard EP Spines
-- ═══════════════════════════════════════════════════════════════

/-- Full verbal EP: V → v → T → C.
    This is the standard clausal spine for finite clauses. -/
def fullVerbalEP : List Cat := [.V, .v, .T, .C]

/-- Full nominal EP: N → D.
    This is the standard nominal spine. -/
def fullNominalEP : List Cat := [.N, .D]

/-- Small clause EP: just the lexical head, no functional layers.
    E.g., "consider [SC him intelligent]" — the SC has no T or C. -/
def smallClauseVerbalEP : List Cat := [.V]

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

    For nominal EPs: the argument domain is NP (F0)
    - DP (F1) denotes e (entity), not ⟨e,t⟩ -/
def argumentDomainCat (topCat : Cat) : Cat :=
  match topCat with
  | .C | .T => .v     -- full/infinitival clause → vP is argument domain
  | _       => topCat  -- small clause → the SC itself is argument domain

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

/-- All lexical heads denote properties. -/
theorem lexical_heads_are_properties :
    epSemanticType .V = .property ∧ epSemanticType .N = .property ∧
    epSemanticType .A = .property ∧ epSemanticType .P = .property := by decide

/-- VP is EP-internal to vP (complement position). -/
theorem vp_internal_to_vp :
    isEPInternal .V .v = true := by decide

/-- NP is EP-internal to DP (complement position). -/
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

/-- Functional heads cannot assign theta roles. -/
theorem functional_heads_no_theta :
    canAssignTheta .v = false ∧ canAssignTheta .D = false ∧
    canAssignTheta .T = false ∧ canAssignTheta .C = false := by decide

/-- Lexical heads can assign theta roles. -/
theorem lexical_heads_assign_theta :
    canAssignTheta .V = true ∧ canAssignTheta .N = true ∧
    canAssignTheta .A = true ∧ canAssignTheta .P = true := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Eval Tests
-- ═══════════════════════════════════════════════════════════════

-- Semantic types
#eval epSemanticType .V  -- property
#eval epSemanticType .v  -- intermediate
#eval epSemanticType .T  -- intermediate
#eval epSemanticType .C  -- proposition
#eval epSemanticType .D  -- entity

-- EP-internal/external
#eval isEPInternal .V .v  -- true (VP is complement of vP)
#eval isEPInternal .N .D  -- true (NP is complement of DP)
#eval isEPExternal .D .v  -- true (DP is specifier of vP)

-- Argument domain
#eval argumentDomainCat .C  -- v (argument domain of CP = vP)
#eval argumentDomainCat .T  -- v (argument domain of TP = vP)
#eval argumentDomainCat .V  -- V (small clause: arg domain = itself)

-- Truncation
#eval isTruncated smallClauseVerbalEP  -- true
#eval isTruncated fullVerbalEP         -- false
#eval isTruncated infinitivalEP        -- true

-- Theta
#eval canAssignTheta .V  -- true
#eval canAssignTheta .T  -- false

end Minimalism
