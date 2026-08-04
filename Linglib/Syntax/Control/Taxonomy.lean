/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Dependency
import Mathlib.Logic.Relator

/-!
# The Descriptive Taxonomy of Control

The shared descriptive vocabulary of control — reading types and dependency
shapes every framework's account is answerable to — as properties of a
dependency `SetRel Pos Pos` with valuation `val : Pos → Ref`
(`Syntax/Control/Dependency.lean`): exhaustive vs. partial readings
([landau-2000]; [pearson-2016]) and split antecedents. Control *shift* — the
antecedent varying across readings of one construction — is deliberately not a
property of a single dependency: a dependency encodes one reading, so shift
lives at the controller-choice stratum.

`Mechanism` names what a dependency shares — the framework-neutral cut behind
the movement vs. base-generation and functional vs. anaphoric
([bresnan-1982]) oppositions. `IsSaturating` is the profile of a dependency
enforced by saturation (predication, structure sharing): bi-unique
(`Relator.BiUnique`) and exhaustive, with the phenomenology — no partial
reading, no split antecedents — as theorems.

## Main definitions

- `Control.HasPartial`, `Control.HasSplit`
- `Control.Mechanism`
- `Control.IsSaturating`
-/

namespace Control

open SetRel

variable {Pos Ref : Type*} {val : Pos → Ref} {d : SetRel Pos Pos} {a b p q : Pos}

/-! ### Reading types -/

/-- A partial reading ([landau-2000]): some dependent's referent strictly
    extends its controller's. -/
def HasPartial [Preorder Ref] (val : Pos → Ref) (d : SetRel Pos Pos) : Prop :=
  ∃ a b, a ~[d] b ∧ val a < val b

/-- Split control: some dependent has two distinct controllers — the
    dependency is not left-unique. -/
abbrev HasSplit (d : SetRel Pos Pos) : Prop :=
  ¬ Relator.LeftUnique (· ~[d] ·)

/-- An exhaustive dependency admits no partial reading. -/
theorem IsExhaustive.not_hasPartial [Preorder Ref] (h : IsExhaustive val d) :
    ¬ HasPartial val d :=
  fun ⟨_, _, hab, hlt⟩ => absurd (h.eq hab) hlt.ne

/-! ### Mechanism -/

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

/-! ### Saturation -/

/-- The profile of a dependency enforced by saturation (predication,
    structure sharing): each dependent has a unique controller, each
    controller saturates a single slot, and the referent is shared
    exhaustively. -/
structure IsSaturating (val : Pos → Ref) (d : SetRel Pos Pos) : Prop where
  biUnique : Relator.BiUnique (· ~[d] ·)
  exhaustive : IsExhaustive val d

/-- A saturating dependency admits no partial reading. -/
theorem IsSaturating.not_hasPartial [Preorder Ref] (h : IsSaturating val d) :
    ¬ HasPartial val d :=
  h.exhaustive.not_hasPartial

/-- A saturating dependency admits no split: joint controllers coincide. -/
theorem IsSaturating.eq_of_controllers (h : IsSaturating val d)
    (ha : a ~[d] p) (hb : b ~[d] p) : a = b :=
  h.biUnique.1 ha hb

/-- A saturating dependency admits no split antecedents. -/
theorem IsSaturating.not_hasSplit (h : IsSaturating val d) : ¬ HasSplit d :=
  not_not_intro h.biUnique.1

/-- A saturating controller saturates a single slot: its dependents
    coincide. -/
theorem IsSaturating.eq_of_controlled (h : IsSaturating val d)
    (hp : a ~[d] p) (hq : a ~[d] q) : p = q :=
  h.biUnique.2 hp hq

end Control
