import Linglib.Theories.Syntax.Minimalist.Basic

/-!
# Multidominance: Substrate for Shared-Material Syntax
@cite{citko-2014} @cite{wilder-2008}

A multidominance (MD) structure is a syntactic object built once that is
structurally accessible from two (or more) dominating nodes. At PF, it
linearizes once. MD is one of the two main mechanisms for producing
PF-reduced representations (representations where some material is
interpreted but not pronounced); the other is ellipsis.

This file is the substrate for MD primitives that any MD-using analysis
needs:

- `PFReductionMechanism` — the two PF-reduction mechanisms (ellipsis vs
  multidominance);
- `MDSharing` — bulk vs non-bulk sharing in coordination;
- `SharedNode` — a multiply-dominated node + its category + whether it
  is pronounced;
- `PFReducedCoordination` — a coordinate &P with PF reduction.

Anchored on @cite{citko-2014} (textbook treatment of parallel-Merge MD)
and @cite{wilder-2008} (constituent-sharing flavor). The canonical
non-paper-specific apparatus; consumers include
@cite{citko-gracanin-yuksek-2025}, and (when written) Bachrach-Katzir
2008, Larson 2012, and Belk-Neeleman-Philip 2023 on RNR.

## Convention notes

- This file does **not** commit to a particular MD flavor (parallel-Merge
  vs constituent-sharing vs 3-D phrase structure). `SharedNode` records
  the multiply-dominated node abstractly; specific MD theories
  instantiate the dominance/sharing relation via their own apparatus.
- `MDSharing` was renamed from `SharingType` at 0.230.575 to avoid a
  bare-name collision with
  `Theories/Syntax/DependencyGrammar/Formal/CoordinationParallelism.lean`'s
  `SharingType` (which classifies *extraction symmetry*, not constituent
  sharing).
- `UsesMD` / `UsesEllipsis` / `UsesBoth` are `Prop` with decidability
  instances (per `feedback_no_intrinsic_bool` discipline); decide-checked
  consumers continue to work.
-/

namespace Minimalist

/-- The two mechanisms of PF reduction.

    Both produce representations where material is interpreted but not
    pronounced. Economy (`Theories/Syntax/Minimalist/Economy.lean`)
    governs the choice between them. -/
inductive PFReductionMechanism where
  /-- E-feature on a functional head triggers deletion of its complement
      at PF. The deleted material is built in full during the derivation. -/
  | ellipsis
  /-- A syntactic object is built once and shared between two dominating
      nodes. Pronounced at one position only. -/
  | multidominance
  deriving Repr, DecidableEq

/-- How material is shared between conjuncts in an MD coordination.

    The empirical motivation is @cite{citko-gracanin-yuksek-2025}:
    coordinated wh-questions use non-bulk-sharing (individual heads
    shared), while coordinated sluices use bulk-sharing (entire C'
    shared). The two sharing modes derive different syntactic and
    interpretive properties.

    NB: name distinguished from
    `Theories/Syntax/DependencyGrammar/Formal/CoordinationParallelism.SharingType`
    (extraction symmetry, not constituent sharing). -/
inductive MDSharing where
  /-- Individual functional heads shared between conjuncts. Each conjunct
      remains a separate full phrase; only specific heads (e.g., C, T)
      are multiply dominated. -/
  | nonBulk
  /-- An entire constituent is shared between conjuncts. Both conjuncts
      dominate the same subtree, so they share all material inside it
      (C, TP, vP, VP, ...). -/
  | bulk
  deriving Repr, DecidableEq

/-- A node shared between two conjuncts in a coordination structure.

    The shared node is built once but is structurally accessible from
    both `parent1` and `parent2`. At PF, it is linearized once. -/
structure SharedNode where
  /-- The multiply dominated node. -/
  node : SyntacticObject
  /-- Category of the shared node, when labelled. -/
  category : Option Cat
  /-- The shared node has PF content (vs. is silent). -/
  pronounced : Bool
  deriving Repr, DecidableEq

/-- A coordination structure with PF reduction.

    Models a coordinate &P where material is either multiply dominated
    (shared between conjuncts) or elided by an E-feature. -/
structure PFReducedCoordination where
  /-- First conjunct. -/
  conjunct1 : SyntacticObject
  /-- Second conjunct. -/
  conjunct2 : SyntacticObject
  /-- PF reduction mechanism(s) used. -/
  mechanisms : List PFReductionMechanism
  /-- Mode of sharing (for MD structures). -/
  sharing : Option MDSharing
  /-- Nodes that are shared or deleted. -/
  sharedNodes : List SharedNode
  /-- PF output after reduction. -/
  pfOutput : List String
  deriving Repr, DecidableEq

namespace PFReducedCoordination

/-- Does this coordination use multidominance? -/
def UsesMD (c : PFReducedCoordination) : Prop :=
  PFReductionMechanism.multidominance ∈ c.mechanisms

instance (c : PFReducedCoordination) : Decidable c.UsesMD := by
  unfold UsesMD; infer_instance

/-- Does this coordination use ellipsis? -/
def UsesEllipsis (c : PFReducedCoordination) : Prop :=
  PFReductionMechanism.ellipsis ∈ c.mechanisms

instance (c : PFReducedCoordination) : Decidable c.UsesEllipsis := by
  unfold UsesEllipsis; infer_instance

/-- Does this coordination use both MD and ellipsis? -/
def UsesBoth (c : PFReducedCoordination) : Prop :=
  c.UsesMD ∧ c.UsesEllipsis

instance (c : PFReducedCoordination) : Decidable c.UsesBoth := by
  unfold UsesBoth; infer_instance

end PFReducedCoordination

end Minimalist
