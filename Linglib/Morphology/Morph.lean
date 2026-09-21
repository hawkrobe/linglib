/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Morphs

A **morph** is a minimal segmental form together with its attachment kind:
root, prefix, suffix, infix, proclitic, enclitic, or free form, the form side
of [haspelmath-2020]'s form–content pairing. Morphs are never zero and never
discontinuous.

## Main declarations

* `Morph.Side`, `Morph.Attachment`, `Morph.Kind` — the side of its host a bound
  morph attaches on, how tightly it attaches, and the attachment kinds: bound on
  a side as an affix or a clitic, infixed, root, or free.
* `Morph` — an attachment kind with the bare segmental material; `Morph.bound`
  and its specializations `Morph.pref`, `Morph.suff`, `Morph.procl`,
  `Morph.encl` build the bound morphs, `Morph.infixed`, `Morph.root` and
  `Morph.free` the rest.
* `Morph.Kind.side?`, `Morph.Kind.attachment?` — the side and the attachment of
  a bound kind.
* `Morph.Side.attach` — attachment of an element on a side of a sequence, the
  linear shadow of attachment on a word tree.
* `Morph.surface` — the surface form of a contiguous sequence of morphs in
  boundary notation.

## Implementation notes

`ToString` renders a morph in Leipzig boundary notation, `un-`, `-able`, `l=`,
`=s`, `<um>`, and `Morph.surface` joins a contiguous sequence, `un-do-able`. A
discontinuous exponent is a sequence of such pieces (a circumfix is a prefix
and a suffix, [haspelmath-2020]), which its owner renders with `…` between the
pieces.

## References

* [haspelmath-2020]
-/

@[expose] public section

namespace Morphology

/-- The side of its host on which a bound morph attaches. -/
inductive Morph.Side where
  /-- Before the host: prefixes and proclitics. -/
  | before
  /-- After the host: suffixes and enclitics. -/
  | after
  deriving DecidableEq, Repr, Fintype

/-- How tightly a bound morph attaches to its host. -/
inductive Morph.Attachment where
  /-- An affix, written with `-`. -/
  | affix
  /-- A clitic, written with `=`. -/
  | clitic
  deriving DecidableEq, Repr, Fintype

/-- The ways a morph attaches. -/
inductive Morph.Kind where
  /-- A bound morph attaches on a side of its host, as an affix or a clitic. -/
  | bound (side : Morph.Side) (attachment : Morph.Attachment)
  /-- An infix, inserted into its host. -/
  | infixed
  /-- A root morph. -/
  | root
  /-- A free non-root morph, such as a particle or an auxiliary. -/
  | free
  deriving DecidableEq, Repr, Fintype

/-- A **morph** is a minimal segmental form with its attachment kind. -/
structure Morph where
  /-- How the morph attaches. -/
  kind : Morph.Kind
  /-- The bare segmental material, with no boundary notation. -/
  form : String
  deriving DecidableEq, Repr

namespace Morph

/-! ### Sides -/

namespace Side

variable {α : Type*}

/-- Attach an element on a side of a sequence. -/
def attach : Side → α → List α → List α
  | .before, a, l => a :: l
  | .after, a, l => l ++ [a]

@[simp] theorem attach_before (a : α) (l : List α) : before.attach a l = a :: l := rfl

@[simp] theorem attach_after (a : α) (l : List α) : after.attach a l = l ++ [a] := rfl

theorem attach_ne_nil (s : Side) (a : α) (l : List α) : s.attach a l ≠ [] := by
  cases s <;> simp

end Side

/-! ### Kinds -/

namespace Kind

/-- The side a bound kind attaches on; `none` for infixes, roots and free forms. -/
def side? : Kind → Option Side
  | .bound s _ => some s
  | .infixed | .root | .free => none

/-- The attachment of a bound kind; `none` for infixes, roots and free forms. -/
def attachment? : Kind → Option Attachment
  | .bound _ a => some a
  | .infixed | .root | .free => none

@[simp] theorem side?_bound (s : Side) (a : Attachment) : (bound s a).side? = some s := rfl

@[simp] theorem side?_infixed : infixed.side? = none := rfl

@[simp] theorem side?_root : root.side? = none := rfl

@[simp] theorem side?_free : free.side? = none := rfl

@[simp] theorem attachment?_bound (s : Side) (a : Attachment) :
    (bound s a).attachment? = some a := rfl

@[simp] theorem attachment?_infixed : infixed.attachment? = none := rfl

@[simp] theorem attachment?_root : root.attachment? = none := rfl

@[simp] theorem attachment?_free : free.attachment? = none := rfl

theorem side?_eq_some_iff {k : Kind} {s : Side} : k.side? = some s ↔ ∃ a, k = bound s a := by
  cases k <;> simp [eq_comm]

theorem attachment?_eq_some_iff {k : Kind} {a : Attachment} :
    k.attachment? = some a ↔ ∃ s, k = bound s a := by
  cases k <;> simp [eq_comm]

theorem side?_eq_none_iff {k : Kind} : k.side? = none ↔ k = infixed ∨ k = root ∨ k = free := by
  cases k <;> simp

end Kind

/-! ### Morphs of each kind -/

/-- A bound morph. -/
def bound (side : Side) (attachment : Attachment) (s : String) : Morph :=
  ⟨.bound side attachment, s⟩

/-- A prefix morph. -/
def pref (s : String) : Morph := bound .before .affix s

/-- A suffix morph. -/
def suff (s : String) : Morph := bound .after .affix s

/-- A proclitic morph. -/
def procl (s : String) : Morph := bound .before .clitic s

/-- An enclitic morph. -/
def encl (s : String) : Morph := bound .after .clitic s

/-- An infix morph. -/
def infixed (s : String) : Morph := ⟨.infixed, s⟩

/-- A root morph. -/
def root (s : String) : Morph := ⟨.root, s⟩

/-- A free non-root morph. -/
def free (s : String) : Morph := ⟨.free, s⟩

variable (side : Side) (attachment : Attachment) (s : String)

@[simp] theorem kind_bound : (bound side attachment s).kind = .bound side attachment := rfl

@[simp] theorem form_bound : (bound side attachment s).form = s := rfl

@[simp] theorem kind_pref : (pref s).kind = .bound .before .affix := rfl

@[simp] theorem form_pref : (pref s).form = s := rfl

@[simp] theorem kind_suff : (suff s).kind = .bound .after .affix := rfl

@[simp] theorem form_suff : (suff s).form = s := rfl

@[simp] theorem kind_procl : (procl s).kind = .bound .before .clitic := rfl

@[simp] theorem form_procl : (procl s).form = s := rfl

@[simp] theorem kind_encl : (encl s).kind = .bound .after .clitic := rfl

@[simp] theorem form_encl : (encl s).form = s := rfl

@[simp] theorem kind_infixed : (infixed s).kind = .infixed := rfl

@[simp] theorem form_infixed : (infixed s).form = s := rfl

@[simp] theorem kind_root : (root s).kind = .root := rfl

@[simp] theorem form_root : (root s).form = s := rfl

@[simp] theorem kind_free : (free s).kind = .free := rfl

@[simp] theorem form_free : (free s).form = s := rfl

/-! ### Boundary notation -/

instance : ToString Morph :=
  ⟨fun m => match m.kind with
    | .bound .before .affix => m.form ++ "-"
    | .bound .after .affix => "-" ++ m.form
    | .bound .before .clitic => m.form ++ "="
    | .bound .after .clitic => "=" ++ m.form
    | .infixed => "<" ++ m.form ++ ">"
    | .root | .free => m.form⟩

/-- The surface form of a contiguous sequence of morphs: each in boundary
notation, joined. -/
def surface (ms : List Morph) : String := String.join (ms.map toString)

end Morph

end Morphology
