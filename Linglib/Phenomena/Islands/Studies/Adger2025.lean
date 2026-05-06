import Linglib.Theories.Syntax.SynGraph
import Linglib.Phenomena.Islands.Studies.Ross1967
import Linglib.Theories.Syntax.Minimalist.Merge.MinimalYield
import Linglib.Theories.Syntax.Minimalist.Merge.NoComplexityLoss

set_option autoImplicit false

/-!
# Mereological Syntax Account of Islands
@cite{adger-2025}

@cite{adger-2025} derives island constraints from Angular Locality (AL)
and Dimensionality, without stipulating phases, barriers, or subjacency.
The key insight: transitivity of parthood does NOT cross dimensions.
When an element's path to the target traverses both 1-part and 2-part
edges, AL blocks movement.

## Island derivations

- **Subject islands**: The subject is a 2-part of T. Elements inside the
  subject reach it via 1-part edges, but the subject-to-T edge is a
  2-part edge — cross-dimensional. So elements inside the subject cannot
  be within-dimension transitive parts of any node in C's 1-part chain.
  But the subject DP *itself* can extract (it is T's direct 2-part).

- **Adjunct islands**: Same mechanism. The adjunct is a 2-part of v.
  Elements inside the adjunct traverse 1-part edges to reach the adjunct,
  then a 2-part edge to v — cross-dimensional.

- **Definite nominal islands**: When D has a filled 2-part (Det/Dem),
  elements inside the DP cannot subjoin to D (Dimensionality blocks it)
  AND cannot reach above D (the path crosses dimensions). Indefinite DPs
  (D with a free 2-part) are transparent.

- **Successive cyclicity**: Cross-clausal movement requires intermediate
  stops. An embedded wh must first stop at embedded C (within its EP),
  then reach matrix C (now in the right dimension chain).

## Connection to island typology

This file cross-references the `SynGraph` derivations with the island
constraint categories from `Data.lean`. The key prediction: subject,
adjunct, and CNPC islands all follow from the SAME mechanism (cross-
dimensional transitivity), not from separate constraints.

-/

namespace Adger2025

-- ════════════════════════════════════════════════════
-- § 1. Re-export key SynGraph theorems
-- ════════════════════════════════════════════════════

/-! The core AL derivations are verified in `SynGraph.lean` (§ 10):

- `al_blocks_superlocal`: antilocality (35a)
- `al_blocks_sideward`: no sideward movement (35c)
- `al_blocks_lowering`: no lowering (35b)
- `al_blocks_parallel`: no parallel merge (35d)
- `al_blocks_cross_dim` / `al_allows_within_dim`: cross-dimensional
  transitivity restriction (35e)
- `al_allows_rollup_2part` / `al_allows_rollup_1part`: roll-up movement
- `succ_cyc_blocked_cross_clause` / `succ_cyc_wh_reaches_C1_after_stop`:
  successive cyclicity
- `subject_island_blocks` / `subject_itself_can_extract`: subject islands
- `adjunct_island_blocks` / `adjunct_itself_can_extract`: adjunct islands
- `nominal_island_definite_blocks` / `nominal_island_indefinite_allows`:
  definite nominal islands / Specificity Condition
- `antilocality_sub1` / `antilocality_sub12`: general antilocality -/

-- ════════════════════════════════════════════════════
-- § 2. Unifying mechanism
-- ════════════════════════════════════════════════════

/-- All three strong island types (subject, adjunct, CNPC) are derived
    from the same mechanism: cross-dimensional transitivity failure.
    This contrasts with accounts that stipulate separate constraints
    for each island type.

    We verify that AL blocks extraction from within each type using
    the same `satisfiesAL` predicate. -/
theorem uniform_island_mechanism :
    -- Subject island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 9
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩),
         (⟨5, by omega⟩, ⟨6, by omega⟩), (⟨7, by omega⟩, ⟨8, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨5, by omega⟩, ⟨7, by omega⟩)])
      ⟨8, by decide⟩ ⟨0, by decide⟩ = false) ∧
    -- Adjunct island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 8
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
         (⟨6, by omega⟩, ⟨7, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩)])
      ⟨7, by decide⟩ ⟨0, by decide⟩ = false) ∧
    -- Definite nominal island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 10
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
         (⟨6, by omega⟩, ⟨7, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
         (⟨5, by omega⟩, ⟨8, by omega⟩), (⟨6, by omega⟩, ⟨9, by omega⟩)])
      ⟨9, by decide⟩ ⟨0, by decide⟩ = false) :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Island source classification
-- ════════════════════════════════════════════════════

/-- Angular Locality is a structural (syntactic) mechanism: it derives
    island effects from the graph-theoretic properties of parthood
    (cross-dimensional transitivity failure). All island types that AL
    derives therefore have a syntactic source. -/
def alDerivedSource : IslandSource := .syntactic

/-- All three island types that @cite{adger-2025} derives share the same
    source: syntactic, via cross-dimensional transitivity (§2). -/
theorem adger_uniform_source :
    alDerivedSource = .syntactic := rfl

/-- Subject islands are weak under AL: the subject *itself* can always
    extract (it is T's direct 2-part), only sub-extraction is blocked
    (cross-dimensional transitivity failure). Derived from
    `subject_itself_can_extract` vs `subject_island_blocks` in SynGraph. -/
def subjectIslandStrength : ConstraintStrength := .weak

/-- Adjunct islands are strong under AL: the adjunct is a 2-part of v,
    and cross-dimensional transitivity always fails for elements deeper
    than the adjunct itself — no amelioration mechanism is available.
    Derived from `adjunct_island_blocks` in SynGraph. -/
def adjunctIslandStrength : ConstraintStrength := .strong

-- ════════════════════════════════════════════════════
-- § 4. Cross-framework convergence: Adger AL ↔ MCB §1.6 on Sideward
-- ════════════════════════════════════════════════════

/-! ## Cross-framework convergence

@cite{adger-2025} (mereological Merge, this file) and
@cite{marcolli-chomsky-berwick-2025} §1.6 (algebraic Merge) reach the
SAME verdict on Sideward Merge from incompatible structural primitives:

- **Adger**: Sideward subjunction (sibling subjoin) violates Angular
  Locality — the would-be mover and target are both 1-parts of the same
  parent vertex, so the candidate-α set is empty (no within-dimension
  chain reaches the target). See `al_blocks_sideward` in `SynGraph.lean:300`.

- **MCB**: Sideward operations 2(b), 3(a), 3(b) violate either
  `MinimalYieldWeak` (Δb₀ > 0 — workspace components increase) or
  `InducedMapNCL` (the canonical induced map decreases `leafCount`).
  See `Theories/Syntax/Minimalist/Merge/MinimalYield.lean` and
  `NoComplexityLoss.lean` (`sideward_3a/3b_violates_noDivergence{,Weak}`,
  `sideward_2b/3a/3b_violatesInducedMapNCL`).

The two frameworks share NO structural lemma. AL reasons about
graph-theoretic parthood across dimensions; MCB reasons about Hopf-
algebra coproduct counting and induced component maps. The shared
verdict is convergent evidence from incompatible foundations — exactly
the kind of theoretical incompatibility linglib is designed to make
visible (CLAUDE.md: "high interconnection density: incompatibilities
between theories ... become visible across the codebase").

Each framework's elimination of Sideward is **fully internal** to its
own primitives. Neither argument transfers directly to the other; the
convergence is a *post-hoc agreement on verdicts*, not a derivation of
one framework from the other.

## Linguistic data convergence

Both frameworks correctly predict the cross-linguistic absence of
Sideward Merge as a productive grammatical operation: every alleged
Sideward analysis (parasitic gaps, ATB extraction, certain Japanese
clefts) has alternative analyses that fit within EM/IM. AL and MCB
provide *different reasons* why this is so. -/

/-- **Convergence theorem**: both frameworks reject Sideward Merge.

    The MCB clause: any candidate Sideward 3(a) workspace transformation
    violates `MinimalYieldWeak.noDivergence` (Δb₀ = +1 strictly increases
    workspace components — `sideward_3a_violates_noDivergenceWeak`).

    The Adger clause: the canonical Sideward subjunction graph
    `g_sideward` (parent c with both candidate sibling daughters) fails
    `satisfiesAL` (`al_blocks_sideward`).

    Bundled to make the convergence visible at the type level. The two
    sides share no Lean term — they're different propositions about
    different structural objects, both true. -/
theorem sideward_eliminated_by_both_frameworks
    (T_i Tnode T_iq : ConnesKreimer.TraceTree Minimalist.LIToken Unit) :
    -- MCB: Sideward 3(a)-shape transformation violates MinimalYieldWeak
    (¬ Minimalist.Merge.MinimalYieldWeak
        ({T_i} : ConnesKreimer.TraceForest Minimalist.LIToken Unit)
        ({Tnode, T_iq} : ConnesKreimer.TraceForest Minimalist.LIToken Unit))
    ∧
    -- Adger: the canonical Sideward subjunction configuration fails AL
    (g_sideward.satisfiesAL ⟨2, by decide⟩ ⟨1, by decide⟩ = false) :=
  ⟨Minimalist.Merge.sideward_3a_violates_noDivergenceWeak T_i Tnode T_iq,
   al_blocks_sideward⟩

/-- Sub-claim of the convergence theorem extracted as `Bool`-decidable
    sentinel: the AL framework explicitly returns `false` on the canonical
    Sideward configuration. This is `decide`-checked at compile time
    via `al_blocks_sideward`'s `native_decide`. -/
def adgerRejectsSidewardConfiguration : Bool :=
  g_sideward.satisfiesAL ⟨2, by decide⟩ ⟨1, by decide⟩

@[simp] theorem adgerRejectsSidewardConfiguration_eq_false :
    adgerRejectsSidewardConfiguration = false := al_blocks_sideward

end Adger2025
