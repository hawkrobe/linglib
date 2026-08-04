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

The framework-neutral vocabulary of control. A dependency is a relation
`SetRel Pos Pos` over argument positions, read `antecedent ~[r] dependent`,
with a valuation `val : Pos → Ref` assigning referents — [stiebels-2007]'s
mechanism-neutral definition of control as referential inclusion, "open as to
how the control reading is obtained". Reading types follow [landau-2000]:
exhaustive (`IsExhaustive`), partial (`IsPartial`), and split (`IsSplit`);
control *shift* varies the antecedent across readings of one construction, so
it is not a property of a single dependency. `Mechanism` names what a
dependency shares ([bresnan-1982]'s functional vs. anaphoric cut), and
`IsSaturating` is the bi-unique, exhaustive profile of saturation
(predication, structure sharing). Grammatical dependencies share
[koster-1987]'s configurational-matrix format ([neeleman-vandekoot-2002]),
whose clauses are mathlib vocabulary: refinement `r ⊆ s`,
`Relator.LeftUnique`, `dependent ⊆ r.cod`. Lemmas are in
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
