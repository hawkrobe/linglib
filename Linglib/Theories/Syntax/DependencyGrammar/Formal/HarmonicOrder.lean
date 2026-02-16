import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength
import Linglib.Phenomena.WordOrder.Typology

/-!
# Harmonic Word Order via Dependency Length Minimization

Gibson (2025, Ch. 5.3) argues that **dependency length minimization** (DLM)
explains the **head-direction generalization** (Greenberg 1963, Dryer 1992):
languages overwhelmingly prefer consistent head direction across construction
types. The argument:

1. In recursive structures, consistent direction (HH or FF) keeps spine
   dependencies local — each dependent is adjacent to its head.
2. Mixed direction (HF or FH) forces intervening subtree material between
   a head and its spine dependent, inflating dependency lengths.
3. For **single-word** dependents (leaves), direction is irrelevant to DLM
   because there is no subtree to intervene.

## Structure

- §1: **Chain TDL** — abstract theory over `List Nat` position sequences
- §2: **Intervening material** — connecting DLM to tree topology
- §3: **Single-word exception** — leaf dependents have no intervening material
- §4: **Direction change cost** — concrete DepTree examples (Gibson's pattern)
- §5: **Bridge to WALS** — connecting DLM prediction to typological observation

## References

- Gibson, E. (2025). Syntax: A cognitive approach. Ch. 5.3. MIT Press.
- Greenberg, J. (1963). Some universals of grammar.
- Dryer, M. (1992). The Greenbergian word order correlations. Language 68.
- Futrell, R., Levy, R. & Gibson, E. (2020). Dependency locality. Language 96(2).
-/

namespace DepGrammar.HarmonicOrder

open DepGrammar DependencyLength
open Phenomena.WordOrder.Typology

-- ============================================================================
-- §1: Chain TDL — Abstract Theory
-- ============================================================================

/-! ### Chain Total Dependency Length

For a sequence of positions p[0], p[1], ..., p[k] representing a chain of
dependencies (head → dep₁ → dep₂ → ...), the total dependency length is
the sum of |p[i+1] - p[i]| for all consecutive pairs.

Key insight: monotone sequences (all ascending or all descending) achieve
the minimum TDL = span = max - min. Non-monotone sequences must exceed
the span because each direction reversal adds distance. -/

/-- Total dependency length of a chain of positions: sum of consecutive
    absolute differences |p[i+1] - p[i]|. -/
def chainTDL : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (max a b - min a b) + chainTDL (b :: rest)

/-- A list is monotone ascending. -/
def isAscending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && isAscending (b :: rest)

/-- A list is monotone descending. -/
def isDescending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≥ b && isDescending (b :: rest)

/-- A list is monotone if it is all ascending or all descending. -/
def isMonotone (l : List Nat) : Bool :=
  isAscending l || isDescending l

/-- The span of a list: max - min. For a chain of k+1 positions spanning
    k dependencies, this is the minimum possible TDL. -/
def listSpan (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ =>
    let mx := l.foldl max 0
    let mn := l.foldl min mx
    mx - mn

-- ============================================================================
-- §1a: Core Chain TDL Theorems
-- ============================================================================

/-- Triangle inequality for chains: total dep length ≥ span.

    Proof sketch: by induction on the list. For a :: b :: rest,
    chainTDL = |a-b| + chainTDL(b :: rest) ≥ |a-b| + span(b::rest)
    ≥ span(a :: b :: rest) by the triangle inequality on Nat.

    TODO: Full induction proof requires auxiliary lemmas about how
    foldl min/max interact with consing. -/
theorem chain_tdl_ge_span (l : List Nat) :
    chainTDL l ≥ listSpan l := by
  sorry

/-- Monotone (ascending) chain achieves TDL = span.

    For [a, a+1, ..., a+k], each consecutive difference is exactly the
    step size, and they sum to max - min = span. -/
theorem monotone_ascending_achieves_span (l : List Nat) (h : isAscending l = true) :
    chainTDL l = listSpan l := by
  sorry

/-- The consecutive sequence [0, 1, ..., k] has chainTDL = k. -/
theorem consecutive_tdl (k : Nat) :
    chainTDL (List.range (k + 1)) = k := by
  sorry

-- Concrete verifications for small k
example : chainTDL [0, 1, 2] = 2 := by native_decide
example : chainTDL [0, 1, 2, 3] = 3 := by native_decide
example : chainTDL [0, 1, 2, 3, 4] = 4 := by native_decide
example : chainTDL [4, 3, 2, 1, 0] = 4 := by native_decide

/-- Non-monotone sequence has strictly higher TDL than monotone with same span. -/
example : chainTDL [0, 2, 1, 3] > chainTDL [0, 1, 2, 3] := by native_decide
example : chainTDL [0, 3, 1, 4, 2] > chainTDL [0, 1, 2, 3, 4] := by native_decide

/-- Monotone ascending and descending have equal TDL (direction doesn't matter). -/
example : chainTDL [0, 1, 2, 3] = chainTDL [3, 2, 1, 0] := by native_decide
example : chainTDL [0, 1, 2, 3, 4] = chainTDL [4, 3, 2, 1, 0] := by native_decide

-- ============================================================================
-- §2: Intervening Material in Projective Trees
-- ============================================================================

/-! ### Intervening Material

The structural heart of Gibson's argument: dependency length between a head h
and dependent d equals 1 + the number of subtree members of d that fall
between h and d in linear order. In a projective tree, all subtree members
of d are on the same side of h as d, so they may intervene.

When direction is consistent (harmonic), recursive spine dependents are
adjacent to their heads. When direction is mixed (disharmonic), subtree
material from one dependent intervenes between the next spine dependent
and its head. -/

/-- Collect all transitive descendants of a node (excluding the node itself).
    Uses `projection` from Core/Basic.lean. -/
def subtreeMembers (t : DepTree) (idx : Nat) : List Nat :=
  (projection t.deps idx).filter (· != idx)

/-- Count nodes from subtree(d) that fall between positions h and d
    in linear order. These are the "intervening" nodes that inflate
    dependency length beyond 1. -/
def interveningSubtreeNodes (t : DepTree) (headPos depPos : Nat) : Nat :=
  let lo := min headPos depPos
  let hi := max headPos depPos
  let members := subtreeMembers t depPos
  members.filter (λ m => lo < m && m < hi) |>.length

/-- Dependency length = 1 + intervening nodes from dep's subtree.

    This is the structural theorem connecting DLM to tree topology.
    In a well-formed projective tree, the only nodes between h and d
    are subtree members of d (projectivity ensures no crossing arcs).

    TODO: Proof requires formalizing projectivity constraints and
    showing that in a projective tree, only subtree-of-d nodes can
    appear in the (h,d) interval. -/
theorem dep_length_eq_one_plus_intervening (t : DepTree) (d : Dependency)
    (hd : d ∈ t.deps)
    (hne : d.headIdx ≠ d.depIdx) :
    depLength d = 1 + interveningSubtreeNodes t d.headIdx d.depIdx := by
  sorry

-- ============================================================================
-- §3: Single-Word Exception
-- ============================================================================

/-! ### Single-Word (Leaf) Exception

When a dependent is a leaf (no children), its subtree is empty, so there
are no intervening nodes regardless of direction. This is why single-word
dependents (adjectives, demonstratives, intensifiers, negation markers)
can freely violate the head-direction generalization without DLM cost. -/

/-- A node is a leaf if it has no dependents. -/
def isLeaf (t : DepTree) (idx : Nat) : Bool :=
  t.deps.all (·.headIdx != idx)

/-- A leaf has no subtree members. -/
theorem leaf_no_subtree_members (t : DepTree) (idx : Nat)
    (h : isLeaf t idx = true) :
    subtreeMembers t idx = [] := by
  simp [subtreeMembers, isLeaf] at *
  -- The direct deps filter returns [], so go [] [] fuel = []
  sorry

/-- A leaf has 0 intervening nodes for any head position.

    Since leaves have no subtree, no subtree members can intervene.
    Direction of a leaf dependent is irrelevant to DLM. -/
theorem leaf_no_intervening (t : DepTree) (headPos depPos : Nat)
    (h : isLeaf t depPos = true) :
    interveningSubtreeNodes t headPos depPos = 0 := by
  sorry

/-- Bridge to `single_dep_direction_irrelevant` from DependencyLength.lean:
    a single (leaf) dependency has the same length regardless of direction.
    This is the formal basis for Gibson's Table 4 exceptions. -/
theorem leaf_direction_irrelevant_bridge (h d : Nat) :
    depLength ⟨h, d, .amod⟩ = depLength ⟨d, h, .amod⟩ :=
  single_dep_direction_irrelevant h d

-- ============================================================================
-- §4: Direction Change Cost — Concrete Examples
-- ============================================================================

/-! ### Harmonic vs Disharmonic Trees

Gibson (2025, examples 122–123) pattern: a recursive embedding where
the verb takes a clausal complement. With 3 levels of embedding:

    V₁ — S₁ — V₂ — S₂ — V₃ — O₃

In head-initial (HH): V₁ S₁ V₂ S₂ V₃ O₃ — each V is adjacent to its S
In head-final (FF): O₃ V₃ S₂ V₂ S₁ V₁ — same TDL, mirror image
In mixed (HF): V₁ S₁ S₂ V₃ O₃ V₂ — V₂ separated from V₁ by intervening material
In mixed (FH): S₁ V₁ V₂ O₃ V₃ S₂ — similar inflation

We build concrete DepTrees for each and verify TDL. -/

/-- Consistent head-initial (HH) tree: V₁(0) S₁(1) V₂(2) S₂(3) V₃(4) O₃(5)
    Dependencies: V₁→S₁ (nsubj, 1), V₁→V₂ (ccomp, 2), V₂→S₂ (nsubj, 1),
                  V₂→V₃ (ccomp, 2), V₃→O₃ (obj, 1) -/
def harmonicHI : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "knows" .VERB, Word.mk' "Mary" .PROPN
             , Word.mk' "likes" .VERB, Word.mk' "cats" .NOUN ]
    deps := [ ⟨0, 1, .nsubj⟩    -- thinks ← John, len 1
            , ⟨0, 2, .ccomp⟩    -- thinks → knows, len 2
            , ⟨2, 3, .nsubj⟩    -- knows ← Mary, len 1
            , ⟨2, 4, .ccomp⟩    -- knows → likes, len 2
            , ⟨4, 5, .obj⟩      -- likes → cats, len 1
            ]
    rootIdx := 0 }

/-- Consistent head-final (FF) tree: O₃(0) V₃(1) S₂(2) V₂(3) S₁(4) V₁(5)
    Mirror image of HH. Same TDL. -/
def harmonicHF : DepTree :=
  { words := [ Word.mk' "cats" .NOUN, Word.mk' "likes" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨1, 0, .obj⟩      -- likes ← cats, len 1
            , ⟨3, 1, .ccomp⟩    -- knows ← likes, len 2
            , ⟨3, 2, .nsubj⟩    -- knows ← Mary, len 1
            , ⟨5, 3, .ccomp⟩    -- thinks ← knows, len 2
            , ⟨5, 4, .nsubj⟩    -- thinks ← John, len 1
            ]
    rootIdx := 5 }

/-- Disharmonic HF tree: verb-initial main clause but verb-final embedding.
    V₁(0) S₁(1) S₂(2) O₃(3) V₃(4) V₂(5)
    The ccomp V₁→V₂ now spans the entire sentence (length 5). -/
def disharmonicHF : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "Mary" .PROPN, Word.mk' "cats" .NOUN
             , Word.mk' "likes" .VERB, Word.mk' "knows" .VERB ]
    deps := [ ⟨0, 1, .nsubj⟩    -- thinks ← John, len 1
            , ⟨0, 5, .ccomp⟩    -- thinks → knows, len 5
            , ⟨5, 2, .nsubj⟩    -- knows ← Mary, len 3
            , ⟨5, 4, .ccomp⟩    -- knows ← likes, len 1
            , ⟨4, 3, .obj⟩      -- likes ← cats, len 1
            ]
    rootIdx := 0 }

/-- Disharmonic FH tree: verb-final main clause but verb-initial embedding.
    S₁(0) V₂(1) S₂(2) V₃(3) O₃(4) V₁(5)
    The ccomp V₁→V₂ again spans far. -/
def disharmonicFH : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "likes" .VERB
             , Word.mk' "cats" .NOUN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨5, 0, .nsubj⟩    -- thinks ← John, len 5
            , ⟨5, 1, .ccomp⟩    -- thinks ← knows, len 4
            , ⟨1, 2, .nsubj⟩    -- knows → Mary, len 1
            , ⟨1, 3, .ccomp⟩    -- knows → likes, len 2
            , ⟨3, 4, .obj⟩      -- likes → cats, len 1
            ]
    rootIdx := 5 }

-- TDL computations
/-- HH total dep length = 1+2+1+2+1 = 7 -/
example : totalDepLength harmonicHI = 7 := by native_decide

/-- FF total dep length = 1+2+1+2+1 = 7 -/
example : totalDepLength harmonicHF = 7 := by native_decide

/-- HF (disharmonic) total dep length = 1+5+3+1+1 = 11 -/
example : totalDepLength disharmonicHF = 11 := by native_decide

/-- FH (disharmonic) total dep length = 5+4+1+2+1 = 13 -/
example : totalDepLength disharmonicFH = 13 := by native_decide

/-- Core DLM prediction: HH < HF (harmonic beats disharmonic). -/
theorem harmonic_hi_beats_disharmonic_hf :
    totalDepLength harmonicHI < totalDepLength disharmonicHF := by native_decide

/-- Core DLM prediction: FF < FH (harmonic beats disharmonic). -/
theorem harmonic_hf_beats_disharmonic_fh :
    totalDepLength harmonicHF < totalDepLength disharmonicFH := by native_decide

/-- Direction itself doesn't matter, only consistency: HH = FF. -/
theorem direction_irrelevant_consistency_matters :
    totalDepLength harmonicHI = totalDepLength harmonicHF := by native_decide

/-- Both harmonic orders beat both disharmonic orders. -/
theorem harmonic_always_shorter :
    totalDepLength harmonicHI < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHI < totalDepLength disharmonicFH ∧
    totalDepLength harmonicHF < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHF < totalDepLength disharmonicFH :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §5: Bridge to WALS Typology
-- ============================================================================

/-! ### DLM Prediction ↔ Typological Observation

For each of the 3 construction pairs in WALS (Gibson Tables 1–3):
- **DLM predicts**: disharmonic order is costly (higher TDL in recursive structures)
- **WALS observes**: disharmonic order is rare (fewer languages)

We connect the theoretical prediction (§4) to the empirical observation
(Typology.lean). -/

/-- DLM predicts harmonic order is cheaper. -/
def dlmPredictsHarmonicCheaper : Bool :=
  totalDepLength harmonicHI < totalDepLength disharmonicHF &&
  totalDepLength harmonicHF < totalDepLength disharmonicFH

/-- WALS confirms harmonic order is more common, for a given table. -/
def walsConfirmsHarmonic (t : CrossTab) : Bool :=
  t.harmonicDominant

/-- Combined consistency check: DLM prediction and WALS observation agree. -/
def dlmWalsConsistent (t : CrossTab) : Bool :=
  dlmPredictsHarmonicCheaper && walsConfirmsHarmonic t

/-- For all 3 construction pairs, DLM predicts harmonic is cheaper AND
    WALS confirms harmonic is more common.

    This is Gibson (2025) Ch. 5.3's central claim: DLM explains the
    head-direction generalization. -/
theorem dlm_explains_head_direction_generalization :
    allTables.all dlmWalsConsistent = true := by native_decide

/-- Per-table consistency theorems. -/
theorem vo_adposition_consistent :
    dlmWalsConsistent voAdposition = true := by native_decide

theorem vo_subordinator_consistent :
    dlmWalsConsistent voSubordinator = true := by native_decide

theorem vo_relative_clause_consistent :
    dlmWalsConsistent voRelativeClause = true := by native_decide

-- ============================================================================
-- Bridge to Existing DependencyLength.lean
-- ============================================================================

/-- The harmonic tree examples are well-formed (unique heads, acyclic). -/
example : hasUniqueHeads harmonicHI = true := by native_decide
example : hasUniqueHeads harmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicFH = true := by native_decide

/-- All four trees are projective (no crossing arcs). The disharmonic
    ones are longer NOT because of non-projectivity, but because
    consistent direction is a separate (stronger) constraint. -/
example : isProjective harmonicHI = true := by native_decide
example : isProjective harmonicHF = true := by native_decide
example : isProjective disharmonicHF = true := by native_decide
example : isProjective disharmonicFH = true := by native_decide

/-- Bridge to Behaghel: harmonic trees satisfy Oberstes Gesetz with
    threshold 2 (no dep longer than 2). Disharmonic trees do not. -/
example : oberstesGesetz harmonicHI 2 = true := by native_decide
example : oberstesGesetz harmonicHF 2 = true := by native_decide
example : oberstesGesetz disharmonicHF 2 = false := by native_decide
example : oberstesGesetz disharmonicFH 2 = false := by native_decide

end DepGrammar.HarmonicOrder
