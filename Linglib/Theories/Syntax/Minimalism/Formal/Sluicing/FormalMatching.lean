/-
# Sluicing: Syntactic Isomorphism Condition

Formalization of Anand, Hardt & McCloskey (2025) Syntactic Isomorphism Condition
for sluicing, building on Grimshaw (2005) Extended Projection.

## Key Ideas

Sluicing is licensed when the **argument domain** of the ellipsis site is
**structurally identical** to the argument domain of the antecedent.

1. **Argument Domain** (Def 4): The most inclusive projection in an EP that
   denotes type ⟨e,t⟩ (property). For full clauses, this is vP.
2. **Head Pair** (Def 5): A pair ⟨head, complement⟩ within the argument domain,
   encoding local syntactic structure.
3. **Structural Identity** (Def 6): Two argument domains are structurally identical
   iff their head pairs can be put in 1-1 correspondence with lexical identity.
4. **SIC**: Sluicing is licensed iff structural identity holds between
   antecedent and ellipsis argument domains.

## Predictions

- **Voice mismatch**: v[agentive] ≠ v[nonThematic] within argument domain → SIC violation (AHM 2025)
- **Case matching**: Case is assigned within the argument domain → must match
- **Small clause antecedents**: Smaller argument domain → more permissive matching

## References

- Anand, P., Hardt, D., & McCloskey, J. (2025). Sluicing and Syntactic Identity.
- Grimshaw, J. (2005). Words and Structure.
- Merchant, J. (2001). The Syntax of Silence.
-/

import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Properties
import Linglib.Theories.Syntax.Minimalism.Core.Voice

namespace Minimalism.Sluicing

open Minimalism

-- ═══════════════════════════════════════════════════════════════
-- Part 1: Argument Domain
-- ═══════════════════════════════════════════════════════════════

/-- The argument domain of an extended projection (Anand et al. 2025, Def 4).

    The argument domain is the most inclusive projection in the EP that
    denotes type ⟨e,t⟩ (a property). This is the domain relevant for
    syntactic identity in sluicing.

    For full clauses (CP/TP): the argument domain = vP
    - vP still denotes ⟨e,t⟩ (property of events)
    - Everything above vP (T, C) is outside the argument domain

    For small clauses: the argument domain = the SC itself
    - No functional layers above the lexical head -/
structure ArgumentDomain where
  /-- The EP this argument domain belongs to -/
  ep : ExtendedProjection
  /-- The syntactic object at the argument domain boundary -/
  boundary : SyntacticObject
  /-- The category at the boundary -/
  boundaryCat : Cat
  /-- The boundary denotes a property or is intermediate -/
  denotesProperty : epSemanticType boundaryCat = .property ∨
                    epSemanticType boundaryCat = .intermediate

/-- The categories within the argument domain for a given top category.
    Filters the full EP spine to just those at or below the AD boundary. -/
def argumentDomainSpine (topCat : Cat) : List Cat → List Cat :=
  List.filter (λ c => isInArgumentDomain c topCat)

-- ═══════════════════════════════════════════════════════════════
-- Part 2: Head Pairs
-- ═══════════════════════════════════════════════════════════════

/-- A head pair: a head and its complement category within the argument domain.
    Head pairs encode the local syntactic structure that must match
    between antecedent and ellipsis site.

    Anand et al. (2025) Definition 5: Two heads are lexically identical
    iff they have the same category AND complement category. Case is
    included because it is assigned within the argument domain: a V that
    assigns dative is structurally distinct from one that assigns
    accusative (Merchant 2001, Anand et al. 2021 §5.5). -/
structure HeadPair where
  /-- The category of the head -/
  head : Cat
  /-- The category of its complement -/
  complement : Cat
  /-- Lexical identity token (from LIToken.id) for identity tracking -/
  headId : Nat := 0
  /-- Case assigned by the head to its complement, when relevant.
      `none` for head pairs where case is not assigned (e.g., v–V). -/
  assignedCase : Option UD.Case := none
  /-- Voice flavor of the head (agentive, nonThematic, etc.), when relevant.
      Distinguishes active v[agentive] from passive v[nonThematic] within
      the argument domain (AHM 2025). -/
  voiceFlavor : Option VoiceFlavor := none
  deriving Repr, DecidableEq, BEq

/-- Extract head pairs from a syntactic object, restricted to heads
    whose F-value falls within the argument domain of the given top category.

    Each node ⟨head, complement⟩ where the head selects the complement
    produces a head pair recording their categories. -/
partial def extractHeadPairs (so : SyntacticObject) (topCat : Cat) : List HeadPair :=
  match so with
  | .leaf _ => []
  | .node a b =>
    let pairsBelow := extractHeadPairs a topCat ++ extractHeadPairs b topCat
    -- Check if this node contributes a head pair within the argument domain
    match getCategory a, getCategory b with
    | some catA, some catB =>
      if selectsB a b && isInArgumentDomain catA topCat then
        -- a selects b: a is head, b is complement
        let hid := match a.getLIToken with
                   | some tok => tok.id
                   | none => 0
        ⟨catA, catB, hid, none, none⟩ :: pairsBelow
      else if selectsB b a && isInArgumentDomain catB topCat then
        -- b selects a: b is head, a is complement
        let hid := match b.getLIToken with
                   | some tok => tok.id
                   | none => 0
        ⟨catB, catA, hid, none, none⟩ :: pairsBelow
      else
        pairsBelow
    | _, _ => pairsBelow

-- ═══════════════════════════════════════════════════════════════
-- Part 3: Syntactic Identity
-- ═══════════════════════════════════════════════════════════════

/-- Lexical identity of head pairs (Anand et al. 2025, Def 5):
    Two head pairs are lexically identical iff they have the same
    head category, complement category, and assigned case (when both
    specify case).

    Case matching follows from the SIC because case is assigned within
    the argument domain: if the head assigns different case, the
    head-complement relationship is structurally distinct.

    Note: `headId` is ignored — lexical identity is about structural
    properties, not token identity. When either side has `assignedCase
    = none`, case is not checked (the head pair does not involve case
    assignment, e.g., v selecting VP). -/
def lexicallyIdentical (hp1 hp2 : HeadPair) : Bool :=
  hp1.head == hp2.head && hp1.complement == hp2.complement &&
  (match hp1.assignedCase, hp2.assignedCase with
  | some c1, some c2 => c1 == c2
  | _, _ => true) &&
  (match hp1.voiceFlavor, hp2.voiceFlavor with
  | some v1, some v2 => v1 == v2
  | _, _ => true)

/-- Remove the first element matching a predicate from a list.
    Returns `none` if no match found, `some remaining` otherwise. -/
def removeFirst {α : Type} (p : α → Bool) : List α → Option (List α)
  | [] => none
  | x :: xs =>
    if p x then some xs
    else (removeFirst p xs).map (x :: ·)

/-- Check if every head pair in `pairs1` has a lexically identical
    match in `pairs2`, consuming matches (1-1 correspondence). -/
def matchHeadPairs : List HeadPair → List HeadPair → Bool
  | [], _ => true
  | hp :: rest, candidates =>
    match removeFirst (lexicallyIdentical hp) candidates with
    | some remaining => matchHeadPairs rest remaining
    | none => false

/-- Structural identity (Anand et al. 2025, Def 6):
    Two sets of head pairs are structurally identical iff they can be
    put in 1-1 correspondence where each pair is lexically identical.

    This requires same cardinality AND a bijective matching. -/
def structurallyIdentical (pairs1 pairs2 : List HeadPair) : Bool :=
  pairs1.length == pairs2.length && matchHeadPairs pairs1 pairs2

-- ═══════════════════════════════════════════════════════════════
-- Part 4: Sluicing License (SIC)
-- ═══════════════════════════════════════════════════════════════

/-- Sluicing license: the Syntactic Isomorphism Condition (SIC).

    Sluicing of a CP is licensed iff the argument domain of the
    ellipsis site has structurally identical head pairs to the
    argument domain of the antecedent. -/
structure SluicingLicense where
  /-- Head pairs from the antecedent's argument domain -/
  antecedentPairs : List HeadPair
  /-- Head pairs from the ellipsis site's argument domain -/
  ellipsisPairs : List HeadPair
  /-- Top category of the antecedent clause -/
  antecedentTop : Cat
  /-- Top category of the ellipsis clause -/
  ellipsisTop : Cat

/-- Is sluicing licensed? Checks structural identity of head pairs. -/
def SluicingLicense.isLicensed (sl : SluicingLicense) : Bool :=
  structurallyIdentical sl.antecedentPairs sl.ellipsisPairs

/-- Build a sluicing license from two syntactic objects. -/
def mkSluicingLicense (antecedent ellipsis : SyntacticObject)
    (antTop ellTop : Cat) : SluicingLicense :=
  { antecedentPairs := extractHeadPairs antecedent antTop
    ellipsisPairs := extractHeadPairs ellipsis ellTop
    antecedentTop := antTop
    ellipsisTop := ellTop }

-- ═══════════════════════════════════════════════════════════════
-- Part 5: Bridge Theorems — SIC Predictions
-- ═══════════════════════════════════════════════════════════════

-- Voice Mismatch Resolution (AHM 2025)

/-- Voice is within the argument domain (F1, same level as v).
    AHM 2025: voice mismatches ARE blocked by the SIC because
    v[agentive] ≠ v[nonThematic] within the argument domain. -/
theorem voice_flavor_in_argdomain :
    isInArgumentDomain .Voice .C = true := by decide

/-- T is not within the argument domain of a CP. -/
theorem t_outside_argdomain :
    isInArgumentDomain .T .C = false := by decide

/-- C is not within the argument domain. -/
theorem c_outside_argdomain :
    isInArgumentDomain .C .C = false := by decide

/-- Head pairs for an active (agentive) transitive vP.
    v[agentive] selects VP, V selects DP. -/
def activeVP : List HeadPair :=
  [⟨.v, .V, 0, none, some .agentive⟩, ⟨.V, .D, 0, none, none⟩]

/-- Head pairs for a passive (non-thematic) transitive vP.
    v[nonThematic] selects VP, V selects DP. -/
def passiveVP : List HeadPair :=
  [⟨.v, .V, 0, none, some .nonThematic⟩, ⟨.V, .D, 0, none, none⟩]

/-- Voice mismatch blocks sluicing: active v[agentive] ≠ passive v[nonThematic]
    within the argument domain (AHM 2025). -/
theorem voice_mismatch_blocks_sluicing :
    structurallyIdentical activeVP passiveVP = false := by
  native_decide

/-- Same voice licenses sluicing: active→active is structurally identical. -/
theorem voice_match_licenses_sluicing :
    structurallyIdentical activeVP activeVP = true := by
  native_decide

-- Argument domain boundaries

/-- V is within the argument domain of a CP (F0 ≤ F1). -/
theorem v_lexical_in_argdomain :
    isInArgumentDomain .V .C = true := by decide

/-- v is within the argument domain of a CP (F1 ≤ F1). -/
theorem v_functional_in_argdomain :
    isInArgumentDomain .v .C = true := by decide

-- Small clause predictions

/-- For a small clause (top = V), the argument domain is V itself.
    Only F0 heads are in the argument domain. -/
theorem small_clause_argdomain_is_self :
    argumentDomainCat .V = .V := by decide

/-- In a small clause, v is NOT in the argument domain
    (since the top is V at F0, and v is F1). -/
theorem small_clause_excludes_v :
    isInArgumentDomain .v .V = false := by decide

/-- Small clause argument domains are smaller (fewer head pairs to match).
    This predicts more permissive matching for SC sluicing,
    because fewer structural correspondences are required. -/
theorem small_clause_smaller_argdomain :
    (argumentDomainSpine .V fullVerbalEP).length <
    (argumentDomainSpine .C fullVerbalEP).length := by decide

-- Matching properties

/-- BEq on Cat is reflexive. -/
theorem cat_beq_refl (c : Cat) : (c == c) = true := by
  cases c <;> decide

/-- BEq on UD.Case is reflexive. -/
private theorem ud_case_beq_refl (c : UD.Case) : (c == c) = true := by
  cases c <;> decide

/-- BEq on VoiceFlavor is reflexive. -/
private theorem voiceFlavor_beq_refl (v : VoiceFlavor) : (v == v) = true := by
  cases v <;> decide

/-- Lexical identity is reflexive for any head pair. -/
theorem lexicallyIdentical_refl (hp : HeadPair) :
    lexicallyIdentical hp hp = true := by
  simp only [lexicallyIdentical, beq_self_eq_true, Bool.true_and, Bool.and_self,
             Bool.and_eq_true]
  exact ⟨by cases hp.assignedCase with
           | none => rfl
           | some c => exact ud_case_beq_refl c,
         by cases hp.voiceFlavor with
           | none => rfl
           | some v => exact voiceFlavor_beq_refl v⟩

/-- Empty argument domains are trivially structurally identical. -/
theorem empty_domains_identical :
    structurallyIdentical [] [] = true := by
  unfold structurallyIdentical matchHeadPairs
  decide

/-- A single head pair matches itself. -/
theorem single_pair_matches (hp : HeadPair) :
    structurallyIdentical [hp] [hp] = true := by
  unfold structurallyIdentical
  simp only [List.length]
  unfold matchHeadPairs removeFirst
  simp only [lexicallyIdentical_refl, ite_true]
  unfold matchHeadPairs
  decide

-- Case matching

/-- Case mismatch blocks lexical identity: a V–D pair assigning dative
    is not lexically identical to one assigning accusative. -/
theorem case_mismatch_not_identical :
    lexicallyIdentical ⟨.V, .D, 0, some .Dat, none⟩ ⟨.V, .D, 0, some .Acc, none⟩ = false := by
  native_decide

/-- Case match preserves lexical identity. -/
theorem case_match_identical :
    lexicallyIdentical ⟨.V, .D, 0, some .Dat, none⟩ ⟨.V, .D, 0, some .Dat, none⟩ = true := by
  native_decide

/-- When no case is specified (e.g., v–V), identity depends only on
    categories. -/
theorem no_case_identity :
    lexicallyIdentical ⟨.v, .V, 0, none, none⟩ ⟨.v, .V, 0, none, none⟩ = true := by
  native_decide

/-- Case mismatch blocks structural identity even when all other head
    pairs match. This is the formal basis of the German case-matching
    data (Merchant 2001): "wem" (dat) matches "jemandem" (dat), but
    "wen" (acc) does not. -/
theorem case_mismatch_blocks_sluicing :
    structurallyIdentical
      [⟨.v, .V, 0, none, none⟩, ⟨.V, .D, 0, some .Dat, none⟩]
      [⟨.v, .V, 0, none, none⟩, ⟨.V, .D, 0, some .Acc, none⟩] = false := by
  native_decide

/-- Same case → structural identity holds → sluicing licensed. -/
theorem case_match_licenses_sluicing :
    structurallyIdentical
      [⟨.v, .V, 0, none, none⟩, ⟨.V, .D, 0, some .Dat, none⟩]
      [⟨.v, .V, 0, none, none⟩, ⟨.V, .D, 0, some .Dat, none⟩] = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- Part 6: e-GIVENness (Merchant 2001)
-- ═══════════════════════════════════════════════════════════════

/-- e-GIVENness: the semantic identity condition for ellipsis (Merchant 2001).
    The antecedent entails the F-closure of the ellipsis site and vice versa.
    F-closure existentially binds all F-marked (focused) material. -/
structure EGivenness (Prop' : Type) where
  /-- The antecedent proposition -/
  antecedent : Prop'
  /-- The ellipsis site proposition -/
  ellipsisSite : Prop'
  /-- F-closure: existentially bind all F-marked material -/
  fClosure : Prop' → Prop'
  /-- Entailment relation -/
  entails : Prop' → Prop' → Prop
  /-- Forward: antecedent entails F-closure of ellipsis site -/
  forward : entails antecedent (fClosure ellipsisSite)
  /-- Backward: ellipsis site entails F-closure of antecedent -/
  backward : entails ellipsisSite (fClosure antecedent)

/-- Full ellipsis license: semantic identity (e-GIVENness) + optional SIC.
    Sluicing requires both; VP ellipsis requires only e-GIVENness (AHM 2025). -/
structure EllipsisLicense (Prop' : Type) where
  /-- Semantic identity: e-GIVENness (required for all ellipsis) -/
  semantic : EGivenness Prop'
  /-- Syntactic identity: SIC (required for sluicing, not for VPE) -/
  syntactic : Option SluicingLicense := none

end Minimalism.Sluicing
