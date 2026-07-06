/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Function.Basic

/-!
# Lenses

A lens onto an `Option V`-valued slot of `α`, exposed through its `some`-writes:
`read` may find the slot unvalued, `write` always values it, and `read_write` is
the put-get law. Lenses originate in the view-update problem
([bancilhon-spyratos-1981]) and were named and axiomatized in the bidirectional
transformation literature ([foster-greenwald-moore-pierce-schmitt-2007]).
Very-well-behaved lenses are simultaneously the coalgebras of the store comonad
and the algebras of the state monad (the two are adjoint); this structure
carries the put-get fragment.

A lens-equipped alphabet is a data-word alphabet (symbol paired with a value
slot). With an infinite value domain, a transducer whose state is one slot
readout is a one-register machine in the sense of [kaminski-francez-1994];
with finite `V` — the case here — everything stays classical finite-state,
which is what lets an alphabet-generic subregular transducer compress its
state to the slot readout rather than carry a full symbol
(`Subregular.Harmony.System` runs its harmony feature through one). The
"monadic" of `BMRS` (monadic second-order logic, one free variable) is
unrelated.

## Main definitions

* `Lens`: the read/write pair with the put-get law.
* `Lens.proj`: the canonical lens of a function type at an index — evaluation
  paired with `Function.update`.
-/

universe u v

/-- A lens onto an `Option V`-valued slot of `α`, exposed through its
    `some`-writes. -/
structure Lens (α : Type u) (V : Type v) where
  /-- Read the slot; `none` when it is unvalued. -/
  read : α → Option V
  /-- Write a value into the slot. -/
  write : V → α → α
  /-- Put-get: reading back a written value gives that value. -/
  read_write : ∀ v s, read (write v s) = some v

namespace Lens

variable {ι : Type u} {V : Type v}

/-- The canonical lens of a function type at an index: read is evaluation,
    write is `Function.update`. -/
def proj [DecidableEq ι] (i : ι) : Lens (ι → Option V) V where
  read s := s i
  write v s := Function.update s i (some v)
  read_write v s := Function.update_self ..

@[simp] theorem proj_read [DecidableEq ι] (i : ι) (s : ι → Option V) :
    (proj i).read s = s i := rfl

@[simp] theorem proj_write [DecidableEq ι] (i : ι) (v : V) (s : ι → Option V) :
    (proj i).write v s = Function.update s i (some v) := rfl

end Lens
