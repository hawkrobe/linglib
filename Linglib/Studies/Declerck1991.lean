import Linglib.Data.Examples.Schema
import Linglib.Semantics.Aspect.Boundedness
import Linglib.Semantics.Reference.Context.Basic
import Linglib.Semantics.Reference.Context.Tower
import Linglib.Semantics.Tense.Basic
import Linglib.Semantics.Tense.Domain
import Linglib.Semantics.Tense.Orientation
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.System
import Linglib.Data.Examples.Declerck1991

/-!
# Declerck (1991): Time-Spheres, TO-Chains, and Temporal Domains

[declerck-1991] organizes English tense around two **time-spheres** — past
and present, the latter divided into pre-present, present, and post-present
sectors — and chains of **times of orientation** (TOs): an absolute tense
establishes a temporal domain, relative tenses bind further TOs within it,
and the time of the situation always coincides with a TO (TS = TO_sit).
Example sentences in the generated block are drawn from Declerck's
companion volume, [declerck-1991-grammar].

## Main declarations

- `TOChain.DeclercianSchema`: a tense as a chain of TOs plus a time-sphere
- `TOChain.preterit` … `TOChain.conditionalPerfect`: the eight English tenses
- `TOChain.DeclercianSchema.toFrame`, `toDomain`, `declercianToTower`:
  projections to the shared Reichenbach, `Domain`, and `ContextTower` substrates
- `TOChain.DeclercianSchema.zoneOf`: project-side zone classifier
- `putiDefault`: Declerck's principle of unmarked temporal interpretation
-/

open Time

namespace Declerck1991

open Tense (shiftedFrame)
open Data.Examples (LinguisticExample)

namespace TOChain

open Tense (Domain NamedTO Orientation)

/-! ### Time-spheres -/

/-- The two time-spheres of English ([declerck-1991]): the tense system
divides time into a **past** time-sphere lying wholly before t₀ (preterit,
past perfect, conditional, conditional perfect) and a **present** time-sphere
including t₀ (present, present perfect, future, future perfect).

This is a conceptual partition, not a temporal relation: both "I visited
Paris" and "I have visited Paris" can refer to the same objective event,
but differ in time-sphere membership. -/
inductive TimeSphere where
  /-- wholly before t₀ -/
  | past
  /-- includes t₀ -/
  | present
  deriving DecidableEq, Repr

/-! ### TO-chain architecture -/

/-- A single link in a TO chain: a `Tense.Orientation`-labelled
time of orientation related to the next TO inward by a temporal relation.

Example: in the past perfect schema `TS simul TO_sit before TO₂ before TO₁`,
the link for TO₂ is `⟨.sub 0, .lt, t₂⟩` — meaning TO₂ (= `.sub 0`,
one step out from the binding TO₁ = `.perspective`) stands in the
`before` relation to the next TO outward. The `.situation` role
labels TO_sit. -/
structure TOLink (Time : Type*) where
  /-- The orientation-time role of this link (`.situation` for TO_sit;
      `.sub n` for an intermediate TO). -/
  name : Orientation
  /-- How this TO relates to the next TO inward toward TO₁, as a point comparison
      (`Ordering`): `.lt` = this TO precedes the next (before); `.gt` = this TO follows
      it (after); `.eq` = simultaneous (overlapping). -/
  relation : Ordering
  /-- The resolved time value. -/
  time : Time

/-- Declerck's tense schema: a chain of TOs from TO₁ outward to TO_sit,
with a time-sphere classification.

The `chain` runs from TO₁ (innermost, adjacent to t₀) outward through
intermediate TOs to TO_sit. The situation time TS is always simultaneous
with TO_sit (Declerck's universal principle: every tense represents TS
as coinciding with some TO), so there is no separate `ts` field — both
E and R in the Reichenbach projection are derived from TO_sit.

The chain captures only adjacent relations. Non-adjacent TOs (e.g.,
TO_sit and TO₁ in the conditional tense) have no asserted relation —
this is Declerck's account of temporal vagueness. -/
structure DeclercianSchema (Time : Type*) where
  /-- Temporal zero-point (usually = speech time) -/
  t0 : Time
  /-- Basic TO (TO₁): the starting point for temporal relations.
      Usually = t₀, but can be a future or past time in embedded contexts. -/
  to1 : Time
  /-- Chain of TOs from TO₁ outward. Each link's `relation` connects it
      to the previous link (or to TO₁ for the first link). The last element
      is TO_sit, which TS is simultaneous with. -/
  chain : List (TOLink Time)
  /-- Which time-sphere the tense belongs to -/
  timeSphere : TimeSphere

/-- The situation-TO (= TS): the TO with which the situation time coincides.
This is the last element of the chain, or TO₁ if the chain is empty. -/
def DeclercianSchema.toSit {Time : Type*} (s : DeclercianSchema Time) : Time :=
  match s.chain.getLast? with
  | some link => link.time
  | none => s.to1

/-- Number of TOs in the schema (including TO₁). -/
def DeclercianSchema.depth {Time : Type*} (s : DeclercianSchema Time) : ℕ :=
  s.chain.length + 1

/-! ### Projection to ReichenbachFrame -/

/-- Project a Declercian schema to a Reichenbach frame: S = t₀, P = TO₁,
R = E = TO_sit (by Declerck's universal principle TS = TO_sit).

Since R = E always, no Declercian frame satisfies `isPerfect` (E < R) —
see `toFrame_not_isPerfect`. The "perfect" in Declerck's system is a chain
property (TO_sit before TO₂), not an E/R relation. The projection is lossy:
intermediate TOs and temporal vagueness are collapsed. -/
def DeclercianSchema.toFrame {Time : Type*}
    (s : DeclercianSchema Time) : ReichenbachFrame Time where
  speechTime := s.t0
  perspectiveTime := s.to1
  referenceTime := s.toSit
  eventTime := s.toSit

/-- Every Declercian frame has E = R (Declerck's TS = TO_sit principle). -/
theorem DeclercianSchema.eventTime_eq_referenceTime {Time : Type*}
    (s : DeclercianSchema Time) :
    s.toFrame.eventTime = s.toFrame.referenceTime := rfl

/-! ### The eight English tense schemata

Each schema is parameterized by concrete times so that bridge
theorems can verify the structural relations. -/

section Schemata

variable {Time : Type*}

/-- **Preterit**: TS simul TO_sit, TO_sit before TO₁. Past time-sphere.

Example: "John was ill yesterday." — TO₁ = t₀ (absolute use),
TO_sit before TO₁, TS = TO_sit. -/
def preterit (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .lt, toSit⟩]
  timeSphere := .past

/-- **Present tense**: TS simul TO_sit, TO_sit includes t₀. Present time-sphere.

Declerck's key claim: the present tense does NOT assert `TO_sit = t₀`
but rather `TO_sit includes t₀`. For point times this degenerates to
equality (captured by `.eq`); interval-level inclusion is
handled by `NonemptyInterval.le_def`.

Example: "John is in London." -/
def present (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .eq, toSit⟩]
  timeSphere := .present

/-- **Present perfect**: TS simul TO_sit, TO_sit before TO₁.
Present time-sphere (the crucial difference from the preterit).

Declerck's distinctive claim: the present perfect and preterit differ
in time-sphere membership, not in definiteness or current relevance
(current relevance is "no more than an implicature"). Both can refer to
the same event; the perfect places it in the pre-present sector.

Example: "I have visited Paris."

Scope note: the schema represents the **predicated** situation's TO_sit;
the continuative reading ("I have lived here for ten years"), where the
full situation extends through t₀, is not representable here. -/
def presentPerfect (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .lt, toSit⟩]
  timeSphere := .present

/-- **Past perfect**: TS simul TO_sit, TO_sit before TO₂, TO₂ before TO₁.
Past time-sphere. "The past of the preterit" or "the past of the present
perfect": TO₂ lies in the past time-sphere relative to TO₁, and TO_sit
is anterior to TO₂.

Example: "John had left before we arrived." -/
def pastPerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .lt, to2⟩, ⟨.situation, .lt, toSit⟩]
  timeSphere := .past

/-- **Future tense**: TS simul TO_sit, TO_sit after TO₁. Present time-sphere.
TO_sit lies in the post-present sector.

Example: "I will do it next week." -/
def future (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .gt, toSit⟩]
  timeSphere := .present

/-- **Future perfect**: TS simul TO_sit, TO_sit before TO₂, TO₂ after TO₁.
Present time-sphere.

The future perfect is vague about the relation between TO_sit and TO₁:
John may have already left, may be leaving now, or may leave later.
The chain captures this by NOT asserting a TO_sit–TO₁ relation.

Example: "John will have left when we arrive." -/
def futurePerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .gt, to2⟩, ⟨.situation, .lt, toSit⟩]
  timeSphere := .present

/-- **Conditional tense**: TS simul TO_sit, TO_sit after TO₂, TO₂ before TO₁.
Past time-sphere (for TO₂). The mirror image of the future perfect:
"future in the past". Like the future perfect, it is vague about TO_sit's
relation to TO₁ — the situation may or may not have occurred by speech time.

Example (from [declerck-1991]): "The faded red brick of the house had
weathered many London storms and would weather many more." -/
def conditional (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .lt, to2⟩, ⟨.situation, .gt, toSit⟩]
  timeSphere := .past

/-- **Conditional perfect**: TS simul TO_sit, TO_sit before TO₃,
TO₃ after TO₂, TO₂ before TO₁. Past time-sphere. The most intricate
English tense: "past in the future in the past".

Example: "He would have left by then." -/
def conditionalPerfect (t0 to2 to3 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .lt, to2⟩, ⟨.sub 1, .gt, to3⟩, ⟨.situation, .lt, toSit⟩]
  timeSphere := .past

end Schemata

/-! ### Bridge theorems: Declercian schema → Reichenbach frame

Each bridge theorem shows that a Declercian schema, when resolved to
concrete times satisfying the chain constraints, projects to a
`ReichenbachFrame` satisfying the expected Reichenbach tense predicate.
This connects Declerck's chain architecture to the Reichenbach
infrastructure used by the other tense theories in linglib. -/

section Bridge

variable {Time : Type*} [LinearOrder Time]

/-- No Declercian frame is `isPerfect` (E < R): the TS = TO_sit principle
forces E = R. The perfect lives in the chain, not in the E/R relation. -/
theorem DeclercianSchema.toFrame_not_isPerfect (s : DeclercianSchema Time) :
    ¬ s.toFrame.isPerfect :=
  λ h => lt_irrefl _ h

/-- Preterit projects to a frame satisfying PAST (R < P). -/
theorem preterit_isPast (t0 toSit : Time) (h : toSit < t0) :
    (preterit t0 toSit).toFrame.isPast := (ReichenbachFrame.isPast_def _).mpr h

omit [LinearOrder Time] in
/-- Present projects to a frame satisfying PRESENT (R = P) for point times. -/
theorem present_isPresent (t0 : Time) :
    (present t0 t0).toFrame.isPresent := rfl

/-- Present perfect projects to PAST (R < P) — because TO_sit (= R) < TO₁
(= P). The present-sphere membership is tracked by `timeSphere`, not by
the Reichenbach R/P relation. -/
theorem presentPerfect_frame_isPast (t0 toSit : Time) (h : toSit < t0) :
    (presentPerfect t0 toSit).toFrame.isPast := (ReichenbachFrame.isPast_def _).mpr h

omit [LinearOrder Time] in
/-- Preterit and present perfect produce identical Reichenbach frames for
the same times — they differ ONLY in time-sphere. This is Declerck's
central thesis about the perfect/preterit distinction: the contrast
is sphere membership, not R/P configuration. -/
theorem preterit_presentPerfect_same_frame (t0 toSit : Time) :
    (preterit t0 toSit).toFrame = (presentPerfect t0 toSit).toFrame := rfl

omit [LinearOrder Time] in
/-- … but they differ in time-sphere. -/
theorem preterit_presentPerfect_differ_sphere (t0 toSit : Time) :
    (preterit t0 toSit).timeSphere ≠ (presentPerfect t0 toSit).timeSphere :=
  nofun

/-- Past perfect projects to PAST (R < P): the chain gives
TO_sit < TO₂ < TO₁, so R (= TO_sit) < P (= TO₁). -/
theorem pastPerfect_isPast (t0 to2 toSit : Time)
    (h₁ : toSit < to2) (h₂ : to2 < t0) :
    (pastPerfect t0 to2 toSit).toFrame.isPast :=
  (ReichenbachFrame.isPast_def _).mpr (lt_trans h₁ h₂)

/-- Future projects to FUTURE (P < R). -/
theorem future_isFuture (t0 toSit : Time) (h : t0 < toSit) :
    (future t0 toSit).toFrame.isFuture := (ReichenbachFrame.isFuture_def _).mpr h

end Bridge

/-! ### Temporal vagueness

When a schema's chain has no direct link between two TOs, their relation
is genuinely unspecified. The future perfect and conditional tense are
both vague about TO_sit's relation to TO₁. [declerck-1991] argues this
against the [reichenbach-1947] format, which generates three orderings
for the posterior past (R–E–S; R–S,E; R–S–E): if one tense form realizes
three configurations, the form would have to be three-ways ambiguous, and
there is no evidence that the English conditional (or future perfect) is
ambiguous rather than vague. -/

/-- The future perfect is vague about TO_sit's relation to t₀:
the chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT TO_sit to TO₁.
All three scenarios are consistent. -/
theorem futurePerfect_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ after TO₁ (= t₀ = 0) in all cases
      to2 > 0 ∧
      -- TO_sit before TO₂ in all cases
      toSit₁ < to2 ∧ toSit₂ < to2 ∧ toSit₃ < to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  refine ⟨-1, 0, 1, 5, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;> decide

/-- The conditional tense is vague about TO_sit's relation to t₀: the
chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT TO_sit to TO₁.
The three Reichenbach orderings for the posterior past are instances
of a single vague schema, not distinct tenses. -/
theorem conditional_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ before TO₁ (= t₀ = 0) in all cases
      to2 < 0 ∧
      -- TO_sit after TO₂ in all cases
      toSit₁ > to2 ∧ toSit₂ > to2 ∧ toSit₃ > to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  refine ⟨-1, 0, 1, -3, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;> decide

/-! ### Tower bridge: TO-chain as context tower

Each link in a TO-chain corresponds to a temporal shift in a context
tower: TO₁ is the tower origin, and each subsequent TO maps to a push
with a `temporalShift`. `DeclercianSchema.depth` counts TOs including
TO₁, while the tower counts shifts, so `schema.depth = tower.depth + 1`. -/

section TowerBridge

variable {Time : Type*}

open Semantics.Context (ContextTower ContextShift KContext)

/-- Convert a Declercian TO-chain to a list of temporal shifts.
Each `TOLink` becomes a temporal shift with `.temporal` label.
The relation in the link is not encoded in the shift itself —
it is a constraint on the times, not a transformation. -/
def declercianToShifts {E P : Type*} (chain : List (TOLink Time)) :
    List (ContextShift (KContext Time E P Time)) :=
  chain.map λ link => {
    apply := λ c => { c with time := link.time }
    label := .temporal
  }

/-- Convert a Declercian schema to a context tower: the origin context has
`time := to1` (the basic TO), and each chain link becomes a temporal shift. -/
def declercianToTower {E P : Type*}
    (s : DeclercianSchema Time) (agent addressee : E) (world : Time) (pos : P) :
    ContextTower (KContext Time E P Time) where
  origin := {
    agent := agent
    addressee := addressee
    world := world
    time := s.to1
    position := pos
  }
  shifts := declercianToShifts (E := E) (P := P) s.chain

/-- The tower depth equals the chain length. -/
theorem declercianToTower_depth {E P : Type*}
    (s : DeclercianSchema Time) (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) s agent addr world pos).depth = s.chain.length := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts, List.length_map]

/-- Declerck's depth = tower depth + 1: Declerck counts TO₁ as part of the
depth (number of TOs), while the tower counts only shifts (pushes). -/
theorem declerck_depth_is_tower_depth_plus_one {E P : Type*}
    (s : DeclercianSchema Time) (agent addr : E) (world : Time) (pos : P) :
    s.depth = (declercianToTower (E := E) (P := P) s agent addr world pos).depth + 1 := by
  simp only [DeclercianSchema.depth, declercianToTower_depth]

/-- For simple tenses (chain length 1), the tower has depth 1. -/
theorem preterit_tower_depth (t0 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (preterit t0 toSit) agent addr world pos).depth = 1 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             preterit, List.length_map, List.length_cons, List.length_nil]

/-- For compound tenses (chain length 2), the tower has depth 2. -/
theorem pastPerfect_tower_depth (t0 to2 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (pastPerfect t0 to2 toSit)
      agent addr world pos).depth = 2 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             pastPerfect, List.length_map, List.length_cons, List.length_nil]

/-- For the conditional perfect (chain length 3), the tower has depth 3. -/
theorem conditionalPerfect_tower_depth (t0 to2 to3 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (conditionalPerfect t0 to2 to3 toSit)
      agent addr world pos).depth = 3 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             conditionalPerfect, List.length_map, List.length_cons, List.length_nil]

end TowerBridge

/-! ### Domain bridge: TO-chain as `Tense.Domain`

Re-express `DeclercianSchema` via the framework-agnostic
`Tense.Domain` substrate (central TO + list of sub-TOs, with
Allen relations computed on demand from the underlying linear order).
Additive: the schema structure and named-tense constructors stay
unchanged; domain-level tooling can work uniformly with
`s.toDomain.relatedByName`, while Reichenbach-projecting code continues
to use `s.toFrame`. -/

section DomainBridge

variable {Time : Type*} [LinearOrder Time]

/-- The schema as a `Tense.Domain` over the universal
`Orientation` role vocabulary: central = `.utterance` (t₀), sub-TOs =
`.perspective` (TO₁) followed by every chain link as a point interval.

The Allen relations between any pair of TOs are **computed** from the
underlying `LinearOrder Time` via `NonemptyInterval.allenRel`; nothing
is stored. The chain's `relation` field encodes the *intended* Declercian
temporal relation but is not consulted here — its job is to constrain
admissible time assignments at the call site. -/
def DeclercianSchema.toDomain (s : DeclercianSchema Time) :
    Domain Time Orientation where
  central := NamedTO.ofPoint .utterance s.t0
  subTOs := NamedTO.ofPoint .perspective s.to1 ::
            s.chain.map (λ link => NamedTO.ofPoint link.name link.time)

@[simp] theorem DeclercianSchema.toDomain_central (s : DeclercianSchema Time) :
    s.toDomain.central = NamedTO.ofPoint .utterance s.t0 := rfl

@[simp] theorem DeclercianSchema.toDomain_subTOs (s : DeclercianSchema Time) :
    s.toDomain.subTOs = NamedTO.ofPoint .perspective s.to1 ::
      s.chain.map (λ link => NamedTO.ofPoint link.name link.time) := rfl

/-- The schema's domain labels: utterance first, then perspective, then
every chain link's role. Useful for stating role-set invariants. -/
theorem DeclercianSchema.toDomain_labels (s : DeclercianSchema Time) :
    s.toDomain.labels =
      Orientation.utterance :: .perspective :: s.chain.map TOLink.name := by
  simp only [Domain.labels, Domain.all, DeclercianSchema.toDomain_central,
             DeclercianSchema.toDomain_subTOs, List.map_cons, List.map_map]
  rfl

end DomainBridge

/-! ### Zone classifier

`Zone` crosses the two time-spheres with three positions (anterior,
central, posterior). **Project-side caveat**: Declerck's own inventory of
*absolute sectors* is four — pre-present, present, and post-present
sectors of the present time-sphere, plus a single undivided past sector.
`prePast` and `postPast` are not Declercian sectors but domain-internal
positions (anteriority/posteriority to a TO inside a past temporal
domain); the symmetric 2×3 cross is this file's classifier, not the
book's taxonomy.

`DeclercianSchema.zoneOf` classifies by `(timeSphere, chain length, last
link's relation)`. The classifier is **not** the inverse of the chain —
vague tenses (future perfect, conditional) under-determine TO_sit's zone,
and the classifier returns the zone of the immediate anchor. -/

/-- The two time-spheres crossed with three positions: Declerck's four
absolute sectors (`past`, `prePresent`, `present`, `postPresent`) plus
the domain-internal positions `prePast` and `postPast` (see the section
docstring caveat). -/
inductive Zone where
  | prePast
  | past
  | postPast
  | prePresent
  | present
  | postPresent
  deriving DecidableEq, Repr

namespace DeclercianSchema

variable {Time : Type*}

/-- Classify a schema's TO_sit by zone, based on `(timeSphere, chain
length, last chain link's relation)`. Simple past-sphere tenses
(chain length 1) classify as `past`; deeper past-sphere chains land in
the domain-internal `prePast`/`postPast` positions. Defaults to the
sphere's center for empty chains and non-strict relations. -/
def zoneOf (s : DeclercianSchema Time) : Zone :=
  match s.timeSphere, s.chain.length, (s.chain.getLast?).map TOLink.relation with
  | .past,    1, some .lt => .past         -- preterit
  | .past,    _, some .lt => .prePast      -- past perfect, conditional perfect
  | .past,    _, some .gt  => .postPast     -- conditional
  | .present, _, some .lt => .prePresent   -- present perfect, future perfect
  | .present, _, some .gt  => .postPresent  -- future
  | .past,    _, _            => .past
  | .present, _, _            => .present

end DeclercianSchema

section ZoneClassification

variable {Time : Type*}

/-! Each named English tense classifies to its expected zone; these
exercise the `zoneOf` match against all eight constructors. -/

theorem preterit_zone (t0 toSit : Time) :
    (preterit t0 toSit).zoneOf = .past := rfl

theorem present_zone (t0 toSit : Time) :
    (present t0 toSit).zoneOf = .present := rfl

theorem presentPerfect_zone (t0 toSit : Time) :
    (presentPerfect t0 toSit).zoneOf = .prePresent := rfl

theorem future_zone (t0 toSit : Time) :
    (future t0 toSit).zoneOf = .postPresent := rfl

theorem pastPerfect_zone (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).zoneOf = .prePast := rfl

theorem conditional_zone (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).zoneOf = .postPast := rfl

theorem futurePerfect_zone (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).zoneOf = .prePresent := rfl

theorem conditionalPerfect_zone (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).zoneOf = .prePast := rfl

/-- Preterit and present perfect classify to **different zones** (`past`
vs `prePresent`) despite projecting to identical Reichenbach frames
(`preterit_presentPerfect_same_frame`). The Zone classifier surfaces
what `toFrame` flattens. -/
theorem preterit_presentPerfect_differ_zone (t0 toSit : Time) :
    (preterit t0 toSit).zoneOf ≠ (presentPerfect t0 toSit).zoneOf :=
  nofun

end ZoneClassification

/-! ### `TenseSystem` and `AspectSystem` instances

The aspect instance collapses event and reference roles both to
`.situation` — Declerck's universal TS = TO_sit principle means E = R
always holds, so "event precedes reference" can never hold and the
perfect lives in the chain structure instead. Exactly Declerck's claim. -/

instance declercianSchema_tenseSystem {Time : Type*} [LinearOrder Time] :
    TenseSystem (DeclercianSchema Time) Time Orientation where
  toDomain := DeclercianSchema.toDomain
  anchor := .perspective
  located := .situation
  anchor_mem := fun s => by
    rw [DeclercianSchema.toDomain_labels]
    exact List.mem_cons_of_mem _ List.mem_cons_self

instance declercianSchema_aspectSystem {Time : Type*} [LinearOrder Time] :
    AspectSystem (DeclercianSchema Time) Time Orientation where
  toDomain := DeclercianSchema.toDomain
  event := .situation
  reference := .situation

end TOChain

/-! ### Temporal domain: subordination vs shift

A stretch of discourse may either incorporate each new clause into an
existing temporal domain (relative tenses expressing anteriority,
simultaneity, posteriority — Declerck's "temporal subordination") or
shift to a new absolute domain. Subordination keeps the perspective on
the existing domain anchor; shift resets the perspective to S.

See `Examples.domainShift1a` (subordination) and `Examples.domainShift1b`
(shift) for the book's examples. -/

/-- "He left…" — past domain anchor. Serves both discourse continuations
below: temporal subordination ("…and would never come back") and domain
shift ("…and never came back"). -/
def domainLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "…and would never come back" — relative tense within the past domain
established by `left`. Constructed via `shiftedFrame` so the perspective
is taken from `domainLeft.eventTime`. -/
def domainSubordWouldReturn : ReichenbachFrame ℤ :=
  shiftedFrame domainLeft (-3) (-3)

/-- "…and never came back" — independent past domain (shift): an absolute
preterit, perspective reset to S. -/
def domainShiftCameBack : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- The domain anchor is past (R < P). -/
theorem domainLeft_isPast : domainLeft.isPast := by
  rw [ReichenbachFrame.isPast_def]; decide

/-- Subordination: `wouldReturn` is posterior within the domain. -/
theorem domainSubordWouldReturn_posterior :
    domainSubordWouldReturn.referenceTime > domainLeft.eventTime := by decide

/-- Shift: the shifted continuation has absolute perspective (P = S). -/
theorem domainShiftCameBack_absolute : domainShiftCameBack.isSimpleCase := rfl

/-- Subordination: `wouldReturn` has a shifted (non-absolute) perspective. -/
theorem domainSubordWouldReturn_shifted : ¬ domainSubordWouldReturn.isSimpleCase := by
  show ¬ (-5 : ℤ) = 0; decide

/-! ### Modal (false) past

Some uses of the past tense have non-past reference: the past morphology
marks modal remoteness (tentativeness, politeness, hypotheticality)
rather than past temporal location — Declerck's "modal past".

A bare `ReichenbachFrame` cannot encode this phenomenon: a single (R, E)
pair represents either the morphology or the interpretation, not their
divergence. The data therefore live as `Examples.modalPastWish` and
`Examples.modalPastIfWas`; no frames are stipulated here. -/

/-! ### Future-time subclauses: Present vs Future Perspective System

[declerck-1991] distinguishes two systems for tense in clauses about
post-present time. The **FPS** (Future Perspective System) uses tenses
that establish post-present domains directly from t₀: the future tense
(as absolute tense) and the future perfect. The **PPS** (Present
Perspective System) consists of relative tenses binding into an
established post-present domain whose binding TO behaves as a
**pseudo-t₀**: present tense for simultaneity, preterit or present
perfect for anteriority, future for posteriority. In "If the weather is
good, John will go to the seaside", the matrix is FPS (absolute future)
and the protasis is PPS (relative present against the pseudo-t₀);
*will* in a pure-future protasis is the marked FPS option.

Encoded via `shiftedFrame`: PPS = relative present against a shifted
perspective, FPS = absolute frame (P = S). `Examples.whenPresent` is the
same phenomenon in a when-clause. -/

/-- "John will go to the seaside" — FPS: absolute future establishing a
post-present domain. -/
def fpsSeaside : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- "…if the weather is good" — PPS: present tense binding into the
post-present domain, simultaneous with the pseudo-t₀. -/
def ppsWeatherGood : ReichenbachFrame ℤ :=
  shiftedFrame fpsSeaside 3 3

/-- The FPS matrix is an absolute future: P = S and P < R. -/
theorem fpsSeaside_absolute_future :
    fpsSeaside.isSimpleCase ∧ fpsSeaside.isFuture :=
  ⟨rfl, by rw [ReichenbachFrame.isFuture_def]; decide⟩

/-- The PPS protasis is a *relative present*: R = P at the shifted
perspective, even though the situation is post-present. -/
theorem ppsWeatherGood_relative_present : ppsWeatherGood.isPresent := rfl

/-- The PPS perspective is the pseudo-t₀ — the post-present domain
anchor, not speech time. -/
theorem ppsWeatherGood_pseudo_t0 :
    ppsWeatherGood.perspectiveTime = fpsSeaside.eventTime ∧
    ¬ ppsWeatherGood.isSimpleCase :=
  ⟨rfl, by show ¬ (3 : ℤ) = 0; decide⟩

/-! ### Past perfect in before-clauses

The past perfect encodes an event anterior to a past reference point.
The frames below use the orthodox Reichenbach convention (E < R for the
perfect) — the convention `DeclercianSchema.toFrame` deliberately cannot
express; see the perfect-vs-preterit section for the explicit divergence.

The future-perfect counterpart (`Examples.futurePerfect`) and the
future-referring present in when-clauses (`Examples.whenPresent`, the
PPS phenomenon above) are kept as examples only: frame-encoding the
latter would conflate morphology with interpretation. -/

/-- "I had left before he arrived" — past perfect, event anterior to a
past reference point (orthodox convention: E < R). -/
def hadLeftBefore : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -5

/-- "…before he arrived" — past time-sphere reference point. -/
def beforeArrived : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Before-clause: leaving precedes arrival. -/
theorem hadLeftBefore_event_lt_arrival :
    hadLeftBefore.eventTime < beforeArrived.eventTime := by decide

/-- The past-perfect frame has E < R (perfect, orthodox convention). -/
theorem hadLeftBefore_isPerfect : hadLeftBefore.isPerfect := by
  show (-5 : ℤ) < -3; decide

/-! ### Boundedness and unmarked temporal interpretation

Declerck's **principle of unmarked temporal interpretation** (his label,
building on earlier work on temporal anaphora in discourse): in a
sequence of clauses each establishing its own domain,
(a) bounded + bounded → interpreted as sequential, in report order;
(b) unbounded + unbounded → interpreted as simultaneous;
(c) mixed → the bounded situation is included in the unbounded one.

Boundedness is sentence-level and distinct from telicity: *Bill ran five
miles* is bounded but *Bill was running five miles* is unbounded, with
the same telic VP. These are pragmatic defaults, not entailments. -/

open Semantics.Aspect (SituationBoundedness)

/-- The three default temporal arrangements of Declerck's principle of
unmarked temporal interpretation. -/
inductive TemporalArrangement where
  | sequential
  | simultaneous
  | inclusion
  deriving DecidableEq, Repr

/-- Declerck's unmarked-interpretation default for a pair of juxtaposed
situations, by boundedness. -/
def putiDefault : SituationBoundedness → SituationBoundedness → TemporalArrangement
  | .bounded, .bounded => .sequential
  | .unbounded, .unbounded => .simultaneous
  | _, _ => .inclusion

/-- An arrangement holding of two point-time frames. For point times,
inclusion degenerates to coincidence of event times (genuine interval
inclusion would need interval-valued frames). -/
def TemporalArrangement.holdsAt :
    TemporalArrangement → ReichenbachFrame ℤ → ReichenbachFrame ℤ → Prop
  | .sequential, f, g => f.eventTime < g.eventTime
  | .simultaneous, f, g => f.eventTime = g.eventTime
  | .inclusion, f, g => f.eventTime = g.eventTime

/-- "He arrived." — bounded (achievement). -/
def arrivedFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "He sat down." — bounded (achievement), after arriving by default. -/
def satDownFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -4
  eventTime := -4

/-- "It was raining." — unbounded (state/activity). -/
def rainingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The wind was blowing." — unbounded (activity), simultaneous with
raining by default. -/
def windBlowingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "He was reading." — unbounded (activity). -/
def readingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The phone rang." — bounded (achievement), included in the reading
interval by default. -/
def phoneRangFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Bounded + bounded → sequential: the constructed frames instantiate
the unmarked-interpretation default. -/
theorem arrived_satDown_puti :
    (putiDefault .bounded .bounded).holdsAt arrivedFrame satDownFrame := by
  show (-5 : ℤ) < -4; decide

/-- Unbounded + unbounded → simultaneous. -/
theorem raining_windBlowing_puti :
    (putiDefault .unbounded .unbounded).holdsAt rainingFrame windBlowingFrame := rfl

/-- Mixed → inclusion (point-degenerate: coincidence). -/
theorem phoneRang_reading_puti :
    (putiDefault .bounded .unbounded).holdsAt phoneRangFrame readingFrame := rfl

/-! ### Present perfect vs preterit: time-sphere, and two frame conventions

Declerck's distinctive claim: the present perfect and preterit differ in
time-sphere membership, not in definiteness or current relevance (an
implicature, for Declerck). Both can refer to the same objective event.
The companion grammar's minimal pair (`Examples.perfectOverslept`):
"I have overslept this morning" requires that the morning not be over;
"I overslept this morning" does not.

Two Reichenbach encodings of the perfect coexist in this file:

- `DeclercianSchema.toFrame` (TS = TO_sit, so E = R always): perfect and
  preterit project to the *same* frame (`preterit_presentPerfect_same_frame`);
  the contrast lives in `timeSphere`/`zoneOf`.
- The orthodox convention below (R at the sphere anchor): the perfect has
  E < R = P, making the contrast frame-visible.

`perfect_frame_conventions_diverge` states the discrepancy explicitly:
the orthodox perfect frame is unreachable from any Declercian schema. -/

/-- "I have overslept this morning." — present perfect in the orthodox
convention: E < R and R = P (pre-present, present orientation). -/
def perfectOversleptFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := -3

/-- "I overslept this morning." — simple preterit: E = R < P. -/
def preteritOversleptFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Same event time — the difference is structural, not temporal. -/
theorem oversleptFrames_eventTime_eq :
    perfectOversleptFrame.eventTime = preteritOversleptFrame.eventTime := rfl

/-- The perfect frame is perfect (E < R) with present orientation (R = P). -/
theorem perfectOversleptFrame_isPerfect_isPresent :
    perfectOversleptFrame.isPerfect ∧ perfectOversleptFrame.isPresent :=
  ⟨by show (-3 : ℤ) < 0; decide, rfl⟩

/-- The preterit frame is past (R < P) and perfective (E = R). -/
theorem preteritOversleptFrame_isPast_isPerfective :
    preteritOversleptFrame.isPast ∧ preteritOversleptFrame.isPerfective :=
  ⟨by rw [ReichenbachFrame.isPast_def]; decide, rfl⟩

/-- The two perfect conventions diverge: Declerck's `toFrame` projection
of the present perfect is not the orthodox perfect frame, and no
Declercian projection can be `isPerfect` — while the orthodox frame is.
This is the visible fault line between R-as-TO_sit (Declerck) and
R-as-extended-now (the orthodox reading of the perfect). -/
theorem perfect_frame_conventions_diverge :
    (TOChain.presentPerfect (0 : ℤ) (-3)).toFrame ≠ perfectOversleptFrame ∧
    ¬ (TOChain.presentPerfect (0 : ℤ) (-3)).toFrame.isPerfect ∧
    perfectOversleptFrame.isPerfect :=
  ⟨λ h => absurd (congrArg ReichenbachFrame.referenceTime h) (by decide),
   TOChain.DeclercianSchema.toFrame_not_isPerfect _,
   by show (-3 : ℤ) < 0; decide⟩

end Declerck1991
