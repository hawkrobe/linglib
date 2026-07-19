import Mathlib.Tactic.DeriveFintype

/-!
# The morph: minimal segmental form
[haspelmath-2020]

The form-side carrier of the morphology layer, following
[haspelmath-2020]'s proposal: a **morph** is a minimal linguistic form —
[haspelmath-2020] defines it as a minimal pairing of syntacticosemantic
content with a continuous string of phonological segments, but the
carrier stores only the form side, which is what keeps empty and
superfluous morphs (Cree connective *-t-*, [anderson-2015] p. 19)
representable. Morphs are never zero and never discontinuous
(a "circumfix" is a construction containing a prefix and a suffix, not a
single morph); zero and discontinuity live one level up, in the
**exponent** — a possibly empty sequence of morphs. `[]` means *no
segmental exponent*, not *unmarked*: a cell whose sole marker is a
process (North Saami gradation-only genitives, [anderson-2015] p. 22)
also renders as `[]` here. Nonconcatenative exponence (apophony,
reduplication, tone, subtraction) is a process, not a form, and is out
of this carrier's scope — `Word.Structure`'s tree constructors cover
reduplication and conversion, the autosegmental machinery covers tone;
the rest of the process catalogue ([anderson-2015] pp. 21-24), like
overlapping morphs (Breton mutation, p. 20), currently has no carrier.

`Morph.Kind` records the attachment classification that descriptive
notation itself encodes — `X-` prefix, `-X` suffix, `X=` proclitic,
`=X` enclitic, bare free form — plus `root`.
`Morph.toString`/`Exponent.toString` reproduce that notation, so the
display convention is derived, not data.

## Main declarations

* `Morph` with `Morph.Kind` — a segmental form with its attachment kind
* `Exponent` — a sequence of morphs; `[]` is zero exponence
* `Morph.toString`, `Exponent.toString` — descriptive-notation display
* `Following` — following-segment environment for pre-consonantal vs
  pre-vocalic variant selection
-/

namespace Morphology

/-- The attachment kind of a morph, as descriptive notation encodes it:
`X-` prefix, `-X` suffix, `X=` proclitic, `=X` enclitic, bare form.
`root` follows [haspelmath-2020]'s definitional criterion (a morph
denoting a thing, an action, or a property); `free` covers free
non-root morphs (particles, plural words, auxiliaries) — the class
[haspelmath-2020] notes has no established general name. -/
inductive Morph.Kind where
  | root | pref | suff | procl | encl | free
  deriving DecidableEq, Repr, Fintype

/-- A **morph**: a minimal segmental form with its attachment kind,
following [haspelmath-2020]'s proposal. `form` is the bare segmental
material as sources print it, with no boundary notation — hyphens and
clitic signs are display, produced by `Morph.toString`. -/
structure Morph where
  /-- Attachment kind, per the source's notation. -/
  kind : Morph.Kind
  /-- Bare segmental material, boundary-notation-free. -/
  form : String
  deriving DecidableEq, Repr

/-- An **exponent**: the possibly empty sequence of morphs realizing a
paradigm cell. `[]` is zero exponence — a form cannot be zero, so there
is no zero morph; a discontinuous realization (Q'anjob'al *s-…heb'*) is
a two-morph exponent, [haspelmath-2020]'s "construction containing both
a prefix and a suffix". Segmental exponence only. -/
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

/-- Prefixes and suffixes are affixes. -/
def IsAffix (m : Morph) : Prop := m.kind = .pref ∨ m.kind = .suff

instance (m : Morph) : Decidable m.IsAffix :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Proclitics and enclitics are clitics. -/
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

/-- Display an exponent in descriptive notation: `∅` for zero
exponence, `…` linking the parts of a discontinuous realization. -/
def Exponent.toString : Exponent → String
  | [] => "∅"
  | ms => String.intercalate "…" (ms.map Morph.toString)

/-- The class of the following segment — the commonest conditioning
environment for selecting among a morph's variant shapes
(pre-consonantal vs pre-vocalic pairs; phonological conditioning in
[haspelmath-2020]'s sense, which cross-cuts the variant-vs-suppletive
split of their §§6-8). -/
inductive Following where
  | consonant | vowel
  deriving DecidableEq, Repr, Fintype

end Morphology
