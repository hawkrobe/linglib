import Linglib.Syntax.Clause.Basic
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Particle

This file defines `Particle`, the lexical core for uninflectable
function words ([zwicky-1985-clitics]): form, position, and optional
three-valued distribution facets over the [sadock-zwicky-1985]
sentence-type cells and `Clause.EmbeddingContext`. Facets record
distributional felicity, not licensing mechanism (analytical,
study-side); a `none` cell means the source records nothing, not
exclusion. The cells are record fields, not a taxonomy: force is
`Mood.Illocutionary`, and the interrogative subtypes are the question
constructions of `Semantics/Questions` — a lookup is keyed by field
projection (`p.LicensedIn (·.declarative)`).

## Main declarations

* `Particle`, `Particle.Position`
* `ParticleStatus`, `ClauseDistribution`, `EmbedDistribution`
* `Particle.LicensedIn`, `Particle.LicensedInEmbed` — derived,
  decidable
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

/-- Per-clause-context distribution record over the
[sadock-zwicky-1985] sentence-type cells (interrogatives subtyped:
polar, alternative, constituent — the `Semantics/Questions`
constructions). Each cell is `Option`-valued: `none` means the
anchoring source records nothing for that context — distinct from
`some .excluded`, which is a positive claim. Cells are addressed by
field projection; there is no index enum (force is
`Mood.Illocutionary`, not a parallel type here). -/
structure ClauseDistribution where
  declarative : Option ParticleStatus := none
  polarInterrogative : Option ParticleStatus := none
  alternativeInterrogative : Option ParticleStatus := none
  constituentInterrogative : Option ParticleStatus := none
  imperative : Option ParticleStatus := none
  exclamative : Option ParticleStatus := none
  deriving DecidableEq, Repr

/-- Per-embedding-context distribution record ([bhatt-dayal-2020]
axis). Same `Option`-valued honesty convention as `ClauseDistribution`. -/
structure EmbedDistribution where
  matrix : Option ParticleStatus := none
  subordinated : Option ParticleStatus := none
  quasiSubordinated : Option ParticleStatus := none
  quotation : Option ParticleStatus := none
  deriving DecidableEq, Repr

/-- Recorded status in embedding context `c`, if any. -/
def EmbedDistribution.status? (d : EmbedDistribution) : Clause.EmbeddingContext → Option ParticleStatus
  | .matrix => d.matrix
  | .subordinated => d.subordinated
  | .quasiSubordinated => d.quasiSubordinated
  | .quotation => d.quotation

/-- An uninflectable function word associated with a host constituent
([zwicky-1985-clitics]). -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization (Mandarin 吗). -/
  script : Option String := none
  /-- Host/position class; `none` when the source records no placement. -/
  position : Option Particle.Position := none
  /-- Clause-type distribution facet; `none` for particles with no
      clause-type restriction (focus particles, case particles). -/
  distribution : Option ClauseDistribution := none
  /-- Interrogative-embedding distribution facet ([bhatt-dayal-2020]
      axis); `none` when the source records no embedding data. -/
  embedding : Option EmbedDistribution := none
  deriving DecidableEq, Repr

namespace Particle


/-- Recorded clause-type distribution status in the cell picked out by
projection `c` (e.g. `(·.declarative)`), if any. -/
def status? (p : Particle) (c : ClauseDistribution → Option ParticleStatus) :
    Option ParticleStatus :=
  p.distribution.bind c

/-- The particle is positively recorded as available (obligatorily or
optionally) in the cell picked out by projection `c`. -/
def LicensedIn (p : Particle) (c : ClauseDistribution → Option ParticleStatus) : Prop :=
  match p.status? c with
  | some .obligatory | some .optional => True
  | _ => False

instance (p : Particle) (c : ClauseDistribution → Option ParticleStatus) :
    Decidable (p.LicensedIn c) := by
  unfold LicensedIn; exact match p.status? c with
    | some .obligatory => .isTrue trivial
    | some .optional => .isTrue trivial
    | some .excluded => .isFalse nofun
    | none => .isFalse nofun

/-- Recorded embedding-distribution status in context `c`, if any. -/
def embedStatus? (p : Particle) (c : Clause.EmbeddingContext) : Option ParticleStatus :=
  p.embedding.bind (·.status? c)

/-- The particle is positively recorded as available in embedding
context `c`. -/
def LicensedInEmbed (p : Particle) (c : Clause.EmbeddingContext) : Prop :=
  match p.embedStatus? c with
  | some .obligatory | some .optional => True
  | _ => False

instance (p : Particle) (c : Clause.EmbeddingContext) : Decidable (p.LicensedInEmbed c) := by
  unfold LicensedInEmbed; exact match p.embedStatus? c with
    | some .obligatory => .isTrue trivial
    | some .optional => .isTrue trivial
    | some .excluded => .isFalse nofun
    | none => .isFalse nofun

/-- Carries a clause-type distribution (the sentential/illocutionary
particle family: question, modal, sentence-final particles). -/
def IsSentential (p : Particle) : Prop := p.distribution.isSome

instance (p : Particle) : Decidable p.IsSentential :=
  inferInstanceAs (Decidable (_ = true))

/-- Projection to `Word` (UD `PART`). -/
def toWord (p : Particle) : Word :=
  { form := p.form, cat := .PART, features := {} }

end Particle
