import Mathlib.Tactic.DeriveFintype

/-!
# Morphs and exponents

A **morph** is a minimal segmental form together with its attachment kind:
root, prefix, suffix, proclitic, enclitic, or free form ([haspelmath-2020]).
An **exponent** is a possibly empty sequence of morphs realizing a paradigm
cell. Morphs are never zero and never discontinuous: zero exponence is the
empty exponent, and a discontinuous realization is a multi-morph exponent.

## Main declarations

* `Morph`, `Morph.Kind` — a segmental form with its attachment kind
* `Exponent` — a sequence of morphs; `[]` is zero exponence
* `Morph.toString`, `Exponent.toString` — descriptive-notation display
  (`X-`, `-X`, `X=`, `=X`; `∅` for zero exponence)
* `Following` — following-segment environment for variant selection

## Implementation notes

[haspelmath-2020] defines a morph as a minimal pairing of content with a
continuous string of segments; the carrier stores only the form side, so
empty and superfluous morphs (Cree connective *-t-*, [anderson-2015] p. 19)
remain representable. `[]` means *no segmental exponent*, not *unmarked*: a
cell whose sole marker is a process (North Saami gradation-only genitives,
[anderson-2015] p. 22) also renders as `[]`. Nonconcatenative exponence
(apophony, reduplication, tone, subtraction) is a process, not a form, and
is out of scope here: `Word.Structure` covers reduplication and conversion,
the autosegmental machinery covers tone.

Boundary notation (`X-`, `-X`, `X=`, `=X`) is display, not data: `Morph.form`
is bare segmental material, and `Morph.toString` reproduces the descriptive
convention from `Morph.Kind`.
-/

namespace Morphology

/-- The ways a morph attaches. -/
inductive Morph.Kind where
  /-- A root is a morph denoting a thing, an action, or a property. -/
  | root
  /-- A prefix (`X-`). -/
  | pref
  /-- A suffix (`-X`). -/
  | suff
  /-- A proclitic (`X=`). -/
  | procl
  /-- An enclitic (`=X`). -/
  | encl
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

/-- An **exponent**: the possibly empty sequence of morphs realizing a
paradigm cell. `[]` is zero exponence; a discontinuous realization
(Q'anjob'al *s-…heb'*) is a two-morph exponent. -/
abbrev Exponent := List Morph

namespace Morph

/-- A prefix morph. -/
def pref (s : String) : Morph := ⟨.pref, s⟩

/-- A suffix morph. -/
def suff (s : String) : Morph := ⟨.suff, s⟩

/-- A proclitic morph. -/
def procl (s : String) : Morph := ⟨.procl, s⟩

/-- An enclitic morph. -/
def encl (s : String) : Morph := ⟨.encl, s⟩

/-- A free non-root morph. -/
def free (s : String) : Morph := ⟨.free, s⟩

/-- A root morph. -/
def root (s : String) : Morph := ⟨.root, s⟩

/-- A morph is an **affix** if it is a prefix or a suffix. -/
def IsAffix (m : Morph) : Prop := m.kind = .pref ∨ m.kind = .suff

instance (m : Morph) : Decidable m.IsAffix :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A morph is a **clitic** if it is a proclitic or an enclitic. -/
def IsClitic (m : Morph) : Prop := m.kind = .procl ∨ m.kind = .encl

instance (m : Morph) : Decidable m.IsClitic :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Display in descriptive notation: `X-`, `-X`, `X=`, `=X`, bare. -/
def toString : Morph → String
  | ⟨.pref, s⟩ => s ++ "-"
  | ⟨.suff, s⟩ => "-" ++ s
  | ⟨.procl, s⟩ => s ++ "="
  | ⟨.encl, s⟩ => "=" ++ s
  | ⟨.root, s⟩ | ⟨.free, s⟩ => s

end Morph

/-- Display an exponent in descriptive notation: `∅` for zero exponence,
`…` linking the parts of a discontinuous realization. -/
def Exponent.toString : Exponent → String
  | [] => "∅"
  | ms => String.intercalate "…" (ms.map Morph.toString)

/-- The class of the following segment: the commonest phonological
environment conditioning the choice among a morph's variant shapes
(pre-consonantal vs pre-vocalic). -/
inductive Following where
  /-- The next segment is a consonant. -/
  | consonant
  /-- The next segment is a vowel. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

end Morphology
