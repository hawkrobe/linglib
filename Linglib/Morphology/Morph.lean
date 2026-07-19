import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Morphs and exponents

A **morph** is a minimal segmental form together with its attachment kind:
root, prefix, suffix, proclitic, enclitic, or free form ([haspelmath-2020]).
An **exponent** is a possibly empty sequence of morphs realizing a paradigm
cell. Morphs are never zero and never discontinuous: zero exponence is the
empty exponent, and a discontinuous realization is a multi-morph exponent.

## Main declarations

* `Morph` — a segmental form with its attachment kind, factored as
  side × attachment for bound morphs
* `Exponent` — a sequence of morphs; `[]` is zero exponence
* the `ToString Morph` instance, `Exponent.toString` — descriptive-notation display
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

/-- Descriptive boundary notation: `X-`, `-X`, `X=`, `=X`; bare for roots
and free forms. -/
instance : ToString Morph :=
  ⟨fun m => match m.kind with
    | .bound .before .affix => m.form ++ "-"
    | .bound .after .affix => "-" ++ m.form
    | .bound .before .clitic => m.form ++ "="
    | .bound .after .clitic => "=" ++ m.form
    | .root | .free => m.form⟩

end Morph

/-- An **exponent** is the sequence of morphs realizing a paradigm cell. -/
abbrev Exponent := List Morph

/-- Descriptive notation for an exponent: `∅` if empty, parts linked by `…`. -/
def Exponent.toString : Exponent → String
  | [] => "∅"
  | ms => String.intercalate "…" (ms.map ToString.toString)

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
