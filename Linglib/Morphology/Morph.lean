/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Morphs

A **morph** is a minimal segmental form together with its attachment kind:
root, prefix, suffix, proclitic, enclitic, or free form — the form side of
[haspelmath-2020]'s form–content pairing. Morphs are never zero and never
discontinuous.
-/

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
  /-- A root is a morph denoting a thing, an action, or a property. -/
  | root
  /-- A free non-root morph, such as a particle or an auxiliary. -/
  | free
  deriving DecidableEq, Repr, Fintype

/-- A morph is **bound** when its recorded `Kind` is `bound` — attaching on a
side of its host as an affix or clitic; roots and free forms are not.

The coarse two-way cut is read across domains: acquisition ([clark-2017]: free
morphemes are acquired more readily than bound ones) and coordination typology
([mitrovic-sauerland-2016]). `IsBound` reflects the *recorded* attachment: a
root morph may itself be bound in a language, but `Kind` does not record it, so
`(Kind.root).IsBound` is `False` by definition, not by claim. -/
def Morph.Kind.IsBound : Morph.Kind → Prop
  | .bound .. => True
  | .root | .free => False

instance : DecidablePred Morph.Kind.IsBound := fun k =>
  match k with
  | .bound .. => .isTrue trivial
  | .root | .free => .isFalse (fun h => h)

/-- A **morph** is a minimal segmental form with its attachment kind. -/
structure Morph where
  /-- How the morph attaches. -/
  kind : Morph.Kind
  /-- The bare segmental material, with no boundary notation. -/
  form : String
  deriving DecidableEq, Repr

namespace Morph

/-- A prefix morph. -/
def pref (s : String) : Morph := ⟨.bound .before .affix, s⟩

/-- A suffix morph. -/
def suff (s : String) : Morph := ⟨.bound .after .affix, s⟩

/-- A proclitic morph. -/
def procl (s : String) : Morph := ⟨.bound .before .clitic, s⟩

/-- An enclitic morph. -/
def encl (s : String) : Morph := ⟨.bound .after .clitic, s⟩

/-- A free non-root morph. -/
def free (s : String) : Morph := ⟨.free, s⟩

/-- A root morph. -/
def root (s : String) : Morph := ⟨.root, s⟩

/-- The attachment of a bound morph; `none` for roots and free forms. -/
def attachment? : Morph → Option Attachment
  | ⟨.bound _ a, _⟩ => some a
  | _ => none

/-- A morph is bound when its `kind` is; roots and free forms are not. -/
def IsBound (m : Morph) : Prop := m.kind.IsBound

instance : DecidablePred IsBound := fun m => inferInstanceAs (Decidable m.kind.IsBound)

instance : ToString Morph :=
  ⟨fun m => match m.kind with
    | .bound .before .affix => m.form ++ "-"
    | .bound .after .affix => "-" ++ m.form
    | .bound .before .clitic => m.form ++ "="
    | .bound .after .clitic => "=" ++ m.form
    | .root | .free => m.form⟩

end Morph

instance : ToString (List Morph) :=
  ⟨fun
    | [] => "∅"
    | ms => String.intercalate "…" (ms.map toString)⟩

end Morphology
