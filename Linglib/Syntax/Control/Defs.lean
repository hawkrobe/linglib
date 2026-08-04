/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Rel
import Mathlib.Order.Basic
import Mathlib.Logic.Relator

/-!
# Control: Basic Definitions

The framework-neutral vocabulary of control theory. Control is
pre-theoretically an antecedence relation between the understood subject of a
clause-like complement and the matrix argument that supplies its
interpretation ([landau-2013] (74)); the one definition in the literature
written to be neutral between the rival mechanisms is [stiebels-2007] (22):
the control predicate requires one of its arguments to be (improperly)
included in the reference of the embedded subject, "open as to how the
control reading is obtained: either structurally or semantically/lexically".
A dependency here is a relation `SetRel Pos Pos` over argument positions,
read `antecedent ~[r] dependent`, with a valuation `val : Pos → Ref`
assigning referents. Identical inclusion is *exhaustive control*
([landau-2000]): related positions are co-valued (`IsExhaustive`); proper
inclusion is a *partial* reading (`IsPartial`), and joint antecedence is
*split* control (`IsSplit`). Control *shift* — the antecedent varying across
readings of one construction — is deliberately not a property of a single
dependency: a dependency encodes one reading, so shift lives at the
controller-choice stratum.

Grammatical dependencies share the fixed format of the configurational
matrix: [koster-1987]'s five shared properties, as explained by
[neeleman-vandekoot-2002] — c-command by the antecedent, obligatoriness,
uniqueness of the antecedent, nonuniqueness of the dependent, and locality.
Every clause of the matrix is mathlib vocabulary: c-command and locality are
refinements `r ⊆ s` in the `SetRel` lattice, uniqueness of the antecedent is
`Relator.LeftUnique`, obligatoriness is `dependent ⊆ r.cod`. Movement chains,
bound anaphora, and both control mechanisms instantiate the format, so
nothing here chooses between base-generation and movement.

`Mechanism` names what a dependency shares — the framework-neutral cut behind
the movement vs. base-generation and functional vs. anaphoric
([bresnan-1982]) oppositions. `IsSaturating` is the profile of a dependency
enforced by saturation (predication, structure sharing): bi-unique
(`Relator.BiUnique`) and exhaustive. The lemmas — composition, the
phenomenology of saturation, the occupant-mismatch refutation engine — are in
`Syntax/Control/Basic.lean`.

## Main definitions

- `Control.IsExhaustive`, `Control.IsPartial`, `Control.IsSplit`
- `Control.Mechanism`
- `Control.IsSaturating`
-/

namespace Control

open SetRel

variable {Pos Ref : Type*}

/-- Exhaustive control ([landau-2000]): the dependency shares the valuation
    exhaustively — related positions are co-valued, i.e. the dependency
    refines the kernel of the valuation. -/
def IsExhaustive (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ante ⊆ {(a, b) | val a = val b}

/-- A partial reading ([landau-2000]): some dependent's referent strictly
    extends its controller's. -/
def IsPartial [Preorder Ref] (val : Pos → Ref) (d : SetRel Pos Pos) : Prop :=
  ∃ a b, a ~[d] b ∧ val a < val b

/-- Split control: some dependent has two distinct controllers — the
    dependency is not left-unique. -/
abbrev IsSplit (d : SetRel Pos Pos) : Prop :=
  ¬ Relator.LeftUnique (· ~[d] ·)

/-- What a control dependency shares — the framework-neutral cut behind the
    movement vs. base-generation and functional vs. anaphoric
    ([bresnan-1982]) oppositions. -/
inductive Mechanism where
  /-- Token identity: the occupant assignment itself is shared (movement
      chains; LFG functional control). -/
  | occupant
  /-- Referential co-valuation only (LFG anaphoric control; predication). -/
  | referent
  /-- A binding leg composed over a predication leg ([landau-2024]). -/
  | composite
  /-- No grammatical dependency (non-obligatory control). -/
  | free
  deriving DecidableEq, Repr

/-- The profile of a dependency enforced by saturation (predication,
    structure sharing): each dependent has a unique controller, each
    controller saturates a single slot, and the referent is shared
    exhaustively. -/
structure IsSaturating (val : Pos → Ref) (d : SetRel Pos Pos) : Prop where
  biUnique : Relator.BiUnique (· ~[d] ·)
  exhaustive : IsExhaustive val d

end Control
