import Linglib.Syntax.Clause.Basic
import Linglib.Morphology.Word.Basic
import Mathlib.Data.Fintype.Basic

open Morphology (Word)

/-!
# Particle

This file defines `Particle`, the lexical core for uninflectable
function words ([zwicky-1985-clitics]): form, position, and a recorded
distribution over licensing cells — pairs of a [sadock-zwicky-1985]
sentence type (interrogatives subtyped by the `Semantics/Questions`
constructions) and a `Clause.EmbeddingContext`. The distribution records
distributional felicity, not licensing mechanism (analytical,
study-side); a `none` cell means the source records nothing, not
exclusion. Sentence-type and embedding-context profiles are marginals of
the table, derived by existential projection (`LicensedIn`,
`LicensedInEmbed`), never stored separately.

## Main declarations

* `Particle`, `Particle.ClauseType`, `Particle.Position`, `ParticleStatus`
* `Particle.Licensed`, `Particle.LicensedIn`, `Particle.LicensedInEmbed`
  — derived, decidable
* `Particle.toWord` — projection to `Word` (UD `PART`)
-/

set_option autoImplicit false

open Clause (EmbeddingContext)

/-- Where a particle sits relative to its host domain — the
[zwicky-1985-clitics] positional diagnostic. -/
inductive Particle.Position where
  | clauseInitial
  /-- Second position (Wackernagel; Slavic *li*). -/
  | secondPosition
  /-- Clause-medial / middle field (German *denn*, Swedish *väl*). -/
  | clauseMedial
  | clauseFinal
  /-- Immediately before a host constituent (adnominal focus particles). -/
  | preHost
  /-- Immediately after a host constituent. -/
  | postHost
  /-- No fixed position (Hindi-Urdu *kya:*, [bhatt-dayal-2020] §2). -/
  | free
  deriving DecidableEq, Repr

/-- Three-valued distribution status of a particle in a licensing
context (cf. WALS ch. 116). -/
inductive ParticleStatus where
  | obligatory
  | optional
  | excluded
  deriving DecidableEq, Repr

/-- Sentence-type cells of the particle licensing space: the
[sadock-zwicky-1985] types, interrogatives subtyped. -/
inductive Particle.ClauseType where
  | declarative
  /-- Polar (yes/no) interrogative. -/
  | polar
  /-- Alternative interrogative (*p or q?*). -/
  | alternative
  /-- Constituent (wh) interrogative. -/
  | constituent
  | imperative
  | exclamative
  deriving DecidableEq, Repr, Fintype

/-- An uninflectable function word associated with a host constituent
([zwicky-1985-clitics]). -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization (Mandarin 吗). -/
  script : Option String := none
  /-- Host/position class; `none` when the source records no placement. -/
  position : Option Particle.Position := none
  /-- Recorded status per licensing cell (sentence type × embedding
      context); `none` when the source records nothing for that cell. -/
  distribution : Particle.ClauseType → EmbeddingContext → Option ParticleStatus :=
    fun _ _ => none
  deriving DecidableEq

namespace Particle

variable (p : Particle) (c : ClauseType) (e : EmbeddingContext)

/-- The particle is positively recorded as available (obligatorily or
optionally) in the sentence-type × embedding cell `(c, e)`. -/
def Licensed : Prop :=
  match p.distribution c e with
  | some .obligatory | some .optional => True
  | _ => False

instance : Decidable (p.Licensed c e) := by
  unfold Licensed; exact match p.distribution c e with
    | some .obligatory => .isTrue trivial
    | some .optional => .isTrue trivial
    | some .excluded => .isFalse nofun
    | none => .isFalse nofun

/-- Positively recorded in sentence type `c`, in some embedding context. -/
def LicensedIn : Prop := ∃ e, p.Licensed c e

instance : Decidable (p.LicensedIn c) :=
  inferInstanceAs (Decidable (∃ e, p.Licensed c e))

/-- Positively recorded in embedding context `e`, for some sentence type. -/
def LicensedInEmbed : Prop := ∃ c, p.Licensed c e

instance : Decidable (p.LicensedInEmbed e) :=
  inferInstanceAs (Decidable (∃ c, p.Licensed c e))

/-- Some cell is recorded (the sentential/illocutionary particle family:
question, modal, sentence-final particles). -/
def IsSentential : Prop := ∃ c e, (p.distribution c e).isSome

instance : Decidable p.IsSentential :=
  inferInstanceAs (Decidable (∃ c e, (p.distribution c e).isSome = true))

/-- Projection to `Word` (UD `PART`). -/
def toWord : Word :=
  { form := p.form, cat := .PART, features := {} }

end Particle
