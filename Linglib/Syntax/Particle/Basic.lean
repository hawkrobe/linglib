import Linglib.Features.ClauseCtx
import Linglib.Morphology.Word

/-!
# Particle
[zwicky-1985-clitics]

Lexical core for the particle as a grammatical object: an uninflectable
function word associated with a host constituent. Per [zwicky-1985-clitics],
"particle" is a residual class — membership is non-inflectability plus
function-word status, not a rich natural kind — so the core carries only
what every particle has (form, position), and everything else lives in
domain-layer facets and study files.

The clause-type distribution facet records *distributional felicity*
across [sadock-zwicky-1985] clause contexts, three-valued per cell
(obligatory / optional / excluded, cf. WALS ch. 116 on polar-question
marking: Polish *czy* is obligatory in polar interrogatives, Japanese
*ka* optional in matrix but obligatory in subordinated clauses). It does
NOT record the licensing *mechanism* (use-conditional conflict,
clause-typing, selection) — that is analytical and stays in study files.
A cell is `none` when the anchoring source records nothing for it —
absence of a record is not a claim of exclusion.

## Main declarations

* `Particle` — the core: surface `form`, optional native `script`,
  `position`, and an optional clause-type `distribution` facet
  (particles with no clause-type restriction — focus, case — carry
  `none`).
* `Particle.Position` — host/position class (the [zwicky-1985-clitics]
  positional diagnostic; second-position = Wackernagel).
* `ParticleStatus` / `ClauseDistribution` — three-valued per-cell
  distribution over `Features.ClauseCtx`.
* `Particle.status?` / `Particle.LicensedIn` — derived distribution
  views; `status?` is the class-ready signature a future
  `Distributed α Ctx` capability abstracts.
* `Particle.toWord` — projection to `Word` (UD `PART`).
-/

set_option autoImplicit false

open Features (ClauseCtx)

/-- Where a particle sits relative to its host domain
([zwicky-1985-clitics]'s positional diagnostic; the cline from free
word to clitic surfaces here — Polish *czy* clause-initial free word,
Slavic *li* second-position Wackernagel clitic, Japanese *ka*
clause-final clitic/suffix). -/
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
  deriving DecidableEq, Repr

/-- Three-valued distribution status of a particle in a clause context
(cf. WALS ch. 116): obligatorily present, optionally present, or
excluded. -/
inductive ParticleStatus where
  | obligatory
  | optional
  | excluded
  deriving DecidableEq, Repr

/-- Per-clause-context distribution record. Each cell is `Option`-valued:
`none` means the anchoring source records nothing for that context —
distinct from `some .excluded`, which is a positive claim. -/
structure ClauseDistribution where
  declarative : Option ParticleStatus := none
  polarInterrogative : Option ParticleStatus := none
  alternativeInterrogative : Option ParticleStatus := none
  constituentInterrogative : Option ParticleStatus := none
  imperative : Option ParticleStatus := none
  exclamative : Option ParticleStatus := none
  deriving DecidableEq, Repr

/-- Recorded status in context `c`, if any. -/
def ClauseDistribution.status? (d : ClauseDistribution) : ClauseCtx → Option ParticleStatus
  | .declarative => d.declarative
  | .polarInterrogative => d.polarInterrogative
  | .alternativeInterrogative => d.alternativeInterrogative
  | .constituentInterrogative => d.constituentInterrogative
  | .imperative => d.imperative
  | .exclamative => d.exclamative

/-- A particle: an uninflectable function word associated with a host
constituent. -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization (Mandarin 吗). -/
  script : Option String := none
  /-- Host/position class. -/
  position : Particle.Position
  /-- Clause-type distribution facet; `none` for particles with no
      clause-type restriction (focus particles, case particles). -/
  distribution : Option ClauseDistribution := none
  deriving DecidableEq, Repr

namespace Particle

/-- Recorded distribution status in context `c`, if any. Class-ready
signature: a future `Distributed α Ctx` capability exposes exactly this. -/
def status? (p : Particle) (c : ClauseCtx) : Option ParticleStatus :=
  p.distribution.bind (·.status? c)

/-- The particle is positively recorded as available (obligatorily or
optionally) in context `c`. -/
def LicensedIn (p : Particle) (c : ClauseCtx) : Prop :=
  match p.status? c with
  | some .obligatory | some .optional => True
  | _ => False

instance (p : Particle) (c : ClauseCtx) : Decidable (p.LicensedIn c) := by
  unfold LicensedIn; exact match p.status? c with
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
