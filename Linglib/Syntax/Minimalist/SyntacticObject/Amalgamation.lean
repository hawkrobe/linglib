import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation

/-
# Amalgamation and the Head Movement Constraint
[harizanov-gribanova-2019] [embick-noyer-2001]

Per [harizanov-gribanova-2019], **amalgamation** is a postsyntactic
(PF-layer) operation that combines adjacent heads into a complex morphological
word. It is distinct from syntactic Internal Merge: amalgamation obeys the
Head Movement Constraint (HMC), produces head-adjunction structures (→
words), is driven by morphological properties of heads, and lacks
interpretive effects.

Per [marcolli-larson-huijbregts-2025] §4.1, amalgamation "probably
belongs to Externalization" — it is not part of MCB's narrow-syntactic Merge
(which has only EM and IM). Per [senturia-marcolli-2025] §1, the natural
algebraic home for postsyntactic morphological operations (fission, fusion,
obliteration, impoverishment, amalgamation) is the morphology-syntax
interface layer, where DM-style operations transform morphosyntactic trees.

## What this file provides

- `immediatelyCCommands` — the local c-command relation that defines
  amalgamation locality (HMC compliance).
- `Amalgamation` — the amalgamation record (host, target, locality proof).
- Theorems about Amalgamation locality: `amalgamation_no_intervener`,
  `intervener_rules_out_amalgamation`, `amalgamation_host_ccommands_target`.

## What used to be here

Pre-MCB-cleanup (deleted at 0.230.788): Movement-dependent predicates
`respectsHMC`, `violatesHMC`, `respectsHMC_positional`,
`violatesHMC_positional`, `head_to_spec_violates_hmc{,_positional}`, plus
the Movement-based `isSyntacticHeadMovement` / `compatibleWithAmalgamation`
predicates. These were tied to the legacy `Movement` record (also deleted)
which presupposed copy-theory bookkeeping incompatible with MCB IM-as-quotient.

The HMC-violation diagnostic for syntactic head movement is now stated
directly in terms of `Step.im` + `Derivation` (since syntactic head movement
IS Internal Merge per MCB §1.4.3); the diagnostic content "this construction
violates HMC" is a property of the Step.im step's mover/target relation in
the resulting tree. Concrete HMC-violation theorems live in per-paper Studies
files (e.g., HG2019Amalgamation.lean's diagnostic predicates).
-/

namespace Minimalist

-- ============================================================================
-- § 1: Immediate C-Command for Heads
-- ============================================================================

/-- X immediately c-commands Y within tree `root` iff X c-commands Y
    (in `root`) and there is no Z such that X c-commands Z and Z
    c-commands Y (in `root`).

    This is the "closest" c-command relation, used to define amalgamation
    locality (HMC compliance). -/
def immediatelyCCommands (x y root : SyntacticObject) : Prop :=
  SO.cCommandsIn root x y ∧
  ¬∃ z, z ≠ x ∧ z ≠ y ∧ SO.cCommandsIn root x z ∧ SO.cCommandsIn root z y

-- ============================================================================
-- § 2: Amalgamation
-- ============================================================================

/-- An **amalgamation** of two heads at PF ([harizanov-gribanova-2019]).

    Amalgamation forms a complex morphological word from two adjacent
    heads via PF affixation. Since affixation requires adjacency,
    amalgamation is strictly local and cannot skip intervening heads
    (HMC compliance).

    Example: French V-to-T in *Jean ne parlait pas français* — V
    amalgamates with T at PF.

    NB: This is NOT MCB-Merge content. Amalgamation lives in the PF
    layer (per [marcolli-larson-huijbregts-2025] §4.1). It is
    distinct from `Step.im`, which is narrow-syntactic Internal Merge
    of a head leaf (e.g., Bulgarian LHM). -/
structure Amalgamation where
  /-- The element that amalgamates (the "target"). -/
  target : SyntacticObject
  /-- The host (what it amalgamates to). -/
  host : SyntacticObject
  /-- Amalgamation is LOCAL: host immediately c-commands target.
      Defining property that distinguishes amalgamation from
      narrow-syntactic head movement (which can skip intervening heads,
      e.g., Bulgarian LHM, Germanic V2). -/
  is_local : ∀ root, immediatelyCCommands host target root

/-- Amalgamation cannot skip intervening elements
    ([harizanov-gribanova-2019] §3.3, p.15: "Amalgamation-based
    displacement obeys the Head Movement Constraint"). Immediate from
    the definition: `is_local` requires no intervener. -/
theorem amalgamation_no_intervener (a : Amalgamation) (root : SyntacticObject) :
    ¬∃ z, z ≠ a.host ∧ z ≠ a.target ∧
      SO.cCommandsIn root a.host z ∧ SO.cCommandsIn root z a.target := by
  have h := a.is_local root
  unfold immediatelyCCommands at h
  exact h.2

/-- If there's an intervening element, the displacement cannot be
    amalgamation. Diagnostic: a head displacement that skips an
    intervening head must be syntactic (= `Step.im`), not amalgamation. -/
theorem intervener_rules_out_amalgamation
    (host target intervener root : SyntacticObject)
    (h_neq_host : intervener ≠ host)
    (h_neq_target : intervener ≠ target)
    (h_host_cmd : SO.cCommandsIn root host intervener)
    (h_int_cmd : SO.cCommandsIn root intervener target) :
    ¬∃ (a : Amalgamation), a.host = host ∧ a.target = target := by
  intro ⟨a, hHost, hTarget⟩
  have hLocal := a.is_local root
  unfold immediatelyCCommands at hLocal
  apply hLocal.2
  use intervener
  subst hHost hTarget
  exact ⟨h_neq_host, h_neq_target, h_host_cmd, h_int_cmd⟩

/-- Amalgamation respects locality: the host c-commands the target. -/
theorem amalgamation_host_ccommands_target (a : Amalgamation) (root : SyntacticObject) :
    SO.cCommandsIn root a.host a.target := by
  have h := a.is_local root
  unfold immediatelyCCommands at h
  exact h.1

-- ============================================================================
-- § 3: VerbDoublingIsSyntacticIn (MCB-aligned diagnostic predicate)
-- ============================================================================

/-- "x underwent syntactic Internal Merge in derivation d" — MCB-aligned
    via `Derivation.movedItems`.

    Per [marcolli-chomsky-berwick-2025] §1.4.3.1, IM is the
    syntactic mechanism that produces surface verb doubling via PF
    copy/trace pronunciation rules: the verb appears once in the
    syntactic tree (with its deeper copy replaced by `mkTrace`), but
    PF rules pronounce both positions in certain constructions.

    A construction's verb-doubling is "syntactic" iff the analyst can
    exhibit a `Derivation` where the verb appears as the mover of a
    `Step.im` step. Russian ([harizanov-gribanova-2019]) and
    Guébie ([sande-clem-dabkowski-2026]) license positive
    instances; Hebrew ([landau-2006]) is argued to be PF-driven
    instead.

    Decidable for any concrete `Derivation`.

    Migration note: previously lived in `Studies/
    HarizanovGribanova2019Amalgamation.lean`, which was deleted at
    0.230.X. The relational-predicate substrate from that file
    (`covers`, `coversAmongHeads`, `coversProjection`,
    `isMaximalProjectionOf`, `containsAmongHeads`, `headsIn`,
    `HeadDisplacement`, etc.) was tied to the deleted legacy
    `getCategory`/`isHeadIn`/`sameLabel`/`isMaximalIn` API. A future
    rewrite will rebuild HG2019's amalgamation-as-covering analysis
    on top of the MCB-native `Minimalist.Labeling.isMaximalAt h /
    isHeadIn h` predicates. -/
def VerbDoublingIsSyntacticIn (d : SO.Derivation) (x : SyntacticObject) : Prop :=
  x ∈ d.movedItems

instance (d : SO.Derivation) (x : SyntacticObject) :
    Decidable (VerbDoublingIsSyntacticIn d x) := by
  unfold VerbDoublingIsSyntacticIn; infer_instance

end Minimalist
