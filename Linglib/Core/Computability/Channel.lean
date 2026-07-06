/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Function.Basic

/-!
# Alphabet channels

A readable/writable `V`-valued slot on an alphabet `α`: a lawful lens in its
partial-getter form. Lawful lenses are the coalgebras of the store comonad;
here the channel equips a transducer alphabet with the designated slot its
machines read and write, which is what lets an alphabet-generic subregular
transducer compress its state to the channel readout rather than carry a full
symbol (`Subregular.Harmony.System` runs its harmony feature through one).

## Main definitions

* `Channel`: the read/write pair with the get-put law.
* `Channel.proj`: the canonical channel of a function type at an index —
  evaluation paired with `Function.update`.
-/

universe u v

/-- A readable/writable `V`-channel on `α`: a partial-getter lens satisfying
    the get-put law. -/
structure Channel (α : Type u) (V : Type v) where
  /-- Read the channel; `none` when the slot is unspecified. -/
  read : α → Option V
  /-- Write a value into the channel. -/
  write : V → α → α
  /-- Get-put: reading back a written value gives that value. -/
  read_write : ∀ v s, read (write v s) = some v

namespace Channel

variable {ι : Type u} {V : Type v}

/-- The canonical channel of a function type at an index: read is evaluation,
    write is `Function.update`. -/
def proj [DecidableEq ι] (i : ι) : Channel (ι → Option V) V where
  read s := s i
  write v s := Function.update s i (some v)
  read_write v s := Function.update_self ..

@[simp] theorem proj_read [DecidableEq ι] (i : ι) (s : ι → Option V) :
    (proj i).read s = s i := rfl

@[simp] theorem proj_write [DecidableEq ι] (i : ι) (v : V) (s : ι → Option V) :
    (proj i).write v s = Function.update s i (some v) := rfl

end Channel
