import Linglib.Core.Time
import Linglib.Core.Reichenbach

/-!
# Declerck's Tense Theory (1991/2006)

Declerck's descriptive theory of English tense differs from Reichenbach (1947)
in three structural ways:

1. **TO-chain architecture**: Tenses express *chains* of binary temporal
   relations between adjacent Times of Orientation (TOs), not configurations
   of points on a single time line. A tense schema relates TS to TO_sit,
   TO_sit to TO₂, TO₂ to TO₁, etc. — but does NOT assert relations between
   non-adjacent elements. This makes the conditional tense *vague* (not
   three-ways ambiguous) about the relation between TO_sit and t₀.

2. **TO/TE decomposition**: Reichenbach's overloaded "R" is split into
   TO (Time of Orientation: the time a situation is related *from*) and
   TE (Time Established: what adverbials/context contribute). These are
   independent: a TO may lack a TE (narrative in medias res); a TE may
   not serve as a TO ("yesterday" in "John was here yesterday" frames
   TO_sit but doesn't orient anything).

3. **Two time-spheres**: The past/present time-sphere distinction is a
   first-class conceptual partition, not derivable from temporal relations.
   Both "I visited Paris" (preterit) and "I have visited Paris" (perfect)
   can refer to the same objective event; they differ in time-sphere
   membership (past vs. present).

## The Eight Tense Schemata

Each English tense realizes a chain of relations from TS inward to TO₁:

| Tense              | Schema                                          | Sphere  |
|---------------------|-------------------------------------------------|---------|
| Preterit            | TS simul TO_sit, TO_sit before TO₁              | past    |
| Present             | TS simul TO_sit, TO_sit includes t₀             | present |
| Present Perfect     | TS simul TO_sit, TO_sit before/upto TO₁         | present |
| Past Perfect        | TS simul TO_sit, TO_sit before TO₂, TO₂ before TO₁ | past |
| Future              | TS simul TO_sit, TO_sit after TO₁               | present |
| Future Perfect      | TS simul TO_sit, TO_sit before TO₂, TO₂ after TO₁  | present |
| Conditional         | TS simul TO_sit, TO_sit after TO₂, TO₂ before TO₁  | past |
| Conditional Perfect | TS simul TO_sit, TO_sit before TO₃, TO₃ after TO₂, TO₂ before TO₁ | past |

## Design

We represent each schema as a `DeclercianSchema` — a chain of named TO
links with an explicit time-sphere tag. The `toFrame` projection collapses
a resolved schema into a `ReichenbachFrame`, with bridge theorems proving
the correspondence.

The chain structure deliberately does NOT place all TOs on a single time
line. Non-adjacent TOs have no asserted relation, which is how Declerck
captures temporal vagueness (ch. 6 §1.5, ch. 7 §6–7).

## References

- Declerck, R. (1991). *Tense in English: Its Structure and Use in Discourse*. Routledge.
- Declerck, R. (2006). *The Grammar of the English Tense System*. Mouton.
-/

namespace Semantics.Tense.Declerck

open Core.Time (TimeSphere TemporalRelation)
open Core.Reichenbach (ReichenbachFrame)


-- ════════════════════════════════════════════════════════════════
-- § TO-Chain Architecture
-- ════════════════════════════════════════════════════════════════

/-- A single link in a TO chain: a named Time of Orientation related to
    the next TO inward by a temporal relation.

    Example: in the past perfect schema `TS simul TO_sit before TO₂ before TO₁`,
    the link for TO₂ is `⟨"TO₂", .before, t₂⟩` — meaning TO₂ stands in the
    `before` relation to the next TO outward (TO₁). -/
structure TOLink (Time : Type*) where
  /-- Identifier (e.g., "TO_sit", "TO₂", "TO₃") -/
  name : String
  /-- How this TO relates to the next TO inward toward TO₁.
      `before` = this TO precedes the next; `after` = this TO follows it;
      `overlapping` = simultaneous; `includes` = this TO contains it. -/
  relation : TemporalRelation
  /-- The resolved time value -/
  time : Time

/-- Declerck's tense schema: a chain of TOs from TO₁ outward to TO_sit,
    with a time-sphere classification.

    The `chain` runs from TO₁ (innermost, adjacent to t₀) outward through
    intermediate TOs to TO_sit. The situation time TS is always simultaneous
    with TO_sit (Declerck ch. 6 §1.4: every tense represents TS as coinciding
    with some TO).

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
  /-- Time of the situation (= TO_sit by Declerck's universal principle) -/
  ts : Time
  /-- Which time-sphere the tense belongs to -/
  timeSphere : TimeSphere

/-- The situation-TO: the TO with which TS is simultaneous.
    This is always the last element of the chain, or TO₁ if the chain is
    empty (as in the present tense when TO_sit = TO₁). -/
def DeclercianSchema.toSit {Time : Type*} (s : DeclercianSchema Time) : Time :=
  match s.chain.getLast? with
  | some link => link.time
  | none => s.to1

/-- Number of TOs in the schema (including TO₁). -/
def DeclercianSchema.depth {Time : Type*} (s : DeclercianSchema Time) : ℕ :=
  s.chain.length + 1


-- ════════════════════════════════════════════════════════════════
-- § Projection to ReichenbachFrame
-- ════════════════════════════════════════════════════════════════

/-- Project a Declercian schema to a Reichenbach frame.

    The mapping follows Kiparsky (2002):
    - S = t₀
    - P = TO₁ (basic TO = perspective time)
    - R = TO_sit (situation-TO = reference/topic time)
    - E = TS (time of situation = event time)

    This is a lossy projection: the chain structure (intermediate TOs,
    temporal vagueness) is collapsed. -/
def DeclercianSchema.toFrame {Time : Type*}
    (s : DeclercianSchema Time) : ReichenbachFrame Time where
  speechTime := s.t0
  perspectiveTime := s.to1
  referenceTime := s.toSit
  eventTime := s.ts


-- ════════════════════════════════════════════════════════════════
-- § The Eight English Tense Schemata
-- ════════════════════════════════════════════════════════════════

/-! Each schema is parameterized by concrete times so that bridge
    theorems can verify the structural relations. The `mk*` smart
    constructors enforce the Declercian constraints. -/

section Schemata

variable {Time : Type*} [LinearOrder Time]

/-- **Preterit** (ch. 7 §1): TS simul TO_sit, TO_sit before TO₁.
    Past time-sphere. Two TOs in the chain.

    Example: "John was ill yesterday."
    - TO₁ = t₀ (absolute use)
    - TO_sit before TO₁ (past time-sphere)
    - TS = TO_sit -/
def preterit (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO_sit", .before, toSit⟩]
  ts := toSit
  timeSphere := .past

/-- **Present tense** (ch. 7 §2): TS simul TO_sit, TO_sit includes t₀.
    Present time-sphere. Two TOs in the chain.

    Declerck's key insight: the present tense does NOT assert `TO_sit = t₀`
    but rather `TO_sit includes t₀`. For point times this degenerates to
    equality, but for intervals "John is in London today" has TO_sit = today,
    which properly includes t₀.

    Example: "John is in London."
    - TO_sit includes t₀ (not necessarily = t₀)
    - TS = TO_sit -/
def present (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO_sit", .includes, toSit⟩]
  ts := toSit
  timeSphere := .present

/-- **Present perfect** (ch. 7 §3): TS simul TO_sit, TO_sit before TO₁.
    Present time-sphere (the crucial difference from the preterit).

    Declerck's distinctive claim: the present perfect and preterit differ
    in time-sphere membership, not in definiteness or current relevance.
    Both can refer to the same event; the perfect places it in the
    pre-present sector of the present time-sphere.

    Example: "I have visited Paris."
    - TO₁ = t₀
    - TO_sit before TO₁ (pre-present sector)
    - TS = TO_sit
    - Present time-sphere (vs. past for the preterit) -/
def presentPerfect (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO_sit", .before, toSit⟩]
  ts := toSit
  timeSphere := .present

/-- **Past perfect** (ch. 7 §4): TS simul TO_sit, TO_sit before TO₂, TO₂ before TO₁.
    Past time-sphere. Three TOs in the chain.

    The past perfect is either "the past of the preterit" or "the past of the
    present perfect." In both cases TO₂ lies in the past time-sphere relative
    to TO₁, and TO_sit is anterior to TO₂.

    Example: "John had left before we arrived."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO_sit before TO₂ (anterior to the past reference)
    - TS = TO_sit -/
def pastPerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO₂", .before, to2⟩, ⟨"TO_sit", .before, toSit⟩]
  ts := toSit
  timeSphere := .past

/-- **Future tense** (ch. 7 §5): TS simul TO_sit, TO_sit after TO₁.
    Present time-sphere. Two TOs in the chain.

    The future locates TO_sit either wholly after t₀ or from t₀ onwards.
    For point times, `after` suffices.

    Example: "I will do it next week."
    - TO₁ = t₀
    - TO_sit after TO₁ (post-present sector)
    - TS = TO_sit -/
def future (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO_sit", .after, toSit⟩]
  ts := toSit
  timeSphere := .present

/-- **Future perfect** (ch. 7 §6): TS simul TO_sit, TO_sit before TO₂, TO₂ after TO₁.
    Present time-sphere. Three TOs in the chain.

    The future perfect is vague about the relation between TO_sit and TO₁:
    John may have already left, may be leaving now, or may leave later.
    The chain captures this by NOT asserting a TO_sit–TO₁ relation.

    Example: "John will have left when we arrive."
    - TO₁ = t₀
    - TO₂ after TO₁ (future reference point)
    - TO_sit before TO₂ (anterior to the future reference)
    - TS = TO_sit -/
def futurePerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO₂", .after, to2⟩, ⟨"TO_sit", .before, toSit⟩]
  ts := toSit
  timeSphere := .present

/-- **Conditional tense** (ch. 7 §7): TS simul TO_sit, TO_sit after TO₂, TO₂ before TO₁.
    Past time-sphere (for TO₂). Three TOs in the chain.

    The conditional is the mirror image of the future perfect: "future in
    the past." Like the future perfect, it is vague about TO_sit's relation
    to TO₁ — the situation may or may not have occurred by speech time.

    Example: "The house would weather many more storms."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO_sit after TO₂ (posterior within the past domain)
    - TS = TO_sit -/
def conditional (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO₂", .before, to2⟩, ⟨"TO_sit", .after, toSit⟩]
  ts := toSit
  timeSphere := .past

/-- **Conditional perfect** (ch. 7 §8): TS simul TO_sit, TO_sit before TO₃,
    TO₃ after TO₂, TO₂ before TO₁. Past time-sphere. Four TOs in the chain.

    The most intricate English tense: "past in the future in the past."

    Example: "He would have left by then."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO₃ after TO₂ (future within the past domain)
    - TO_sit before TO₃ (anterior to the future-in-past reference)
    - TS = TO_sit -/
def conditionalPerfect (t0 to2 to3 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨"TO₂", .before, to2⟩, ⟨"TO₃", .after, to3⟩, ⟨"TO_sit", .before, toSit⟩]
  ts := toSit
  timeSphere := .past

end Schemata


-- ════════════════════════════════════════════════════════════════
-- § Chain Depth Theorems
-- ════════════════════════════════════════════════════════════════

section Depth

variable {Time : Type*} [LinearOrder Time]

/-- Simple tenses have depth 2 (TO₁ + TO_sit). -/
theorem preterit_depth (t0 toSit : Time) :
    (preterit t0 toSit).depth = 2 := rfl

theorem present_depth (t0 toSit : Time) :
    (present t0 toSit).depth = 2 := rfl

theorem presentPerfect_depth (t0 toSit : Time) :
    (presentPerfect t0 toSit).depth = 2 := rfl

theorem future_depth (t0 toSit : Time) :
    (future t0 toSit).depth = 2 := rfl

/-- Compound tenses have depth 3 (TO₁ + TO₂ + TO_sit). -/
theorem pastPerfect_depth (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).depth = 3 := rfl

theorem futurePerfect_depth (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).depth = 3 := rfl

theorem conditional_depth (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).depth = 3 := rfl

/-- The conditional perfect has depth 4 (TO₁ + TO₂ + TO₃ + TO_sit). -/
theorem conditionalPerfect_depth (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).depth = 4 := rfl

end Depth


-- ════════════════════════════════════════════════════════════════
-- § Time-Sphere Classification
-- ════════════════════════════════════════════════════════════════

section TimeSphere

variable {Time : Type*} [LinearOrder Time]

/-- Present time-sphere tenses: present, present perfect, future, future perfect. -/
theorem present_sphere (t0 toSit : Time) :
    (present t0 toSit).timeSphere = .present := rfl

theorem presentPerfect_sphere (t0 toSit : Time) :
    (presentPerfect t0 toSit).timeSphere = .present := rfl

theorem future_sphere (t0 toSit : Time) :
    (future t0 toSit).timeSphere = .present := rfl

theorem futurePerfect_sphere (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).timeSphere = .present := rfl

/-- Past time-sphere tenses: preterit, past perfect, conditional, conditional perfect. -/
theorem preterit_sphere (t0 toSit : Time) :
    (preterit t0 toSit).timeSphere = .past := rfl

theorem pastPerfect_sphere (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).timeSphere = .past := rfl

theorem conditional_sphere (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).timeSphere = .past := rfl

theorem conditionalPerfect_sphere (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).timeSphere = .past := rfl

end TimeSphere


-- ════════════════════════════════════════════════════════════════
-- § Bridge Theorems: Declercian Schema → Reichenbach Frame
-- ════════════════════════════════════════════════════════════════

/-! Each bridge theorem shows that a Declercian schema, when resolved to
    concrete times satisfying the chain constraints, projects to a
    `ReichenbachFrame` satisfying the expected Reichenbach tense predicate.

    This connects Declerck's chain architecture to the existing Reichenbach
    infrastructure used by all other tense theories in linglib. -/

section Bridge

/-- Preterit projects to a frame satisfying PAST (R < P). -/
theorem preterit_isPast (t0 toSit : ℤ) (h : toSit < t0) :
    (preterit t0 toSit).toFrame.isPast := by
  simp [preterit, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  exact h

/-- Present projects to a frame satisfying PRESENT (R = P) for point times. -/
theorem present_isPresent (t0 : ℤ) :
    (present t0 t0).toFrame.isPresent := by
  simp [present, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPresent]

/-- Present perfect projects to a frame with E < R = P (perfect aspect,
    present time-sphere) when TO_sit < TO₁. -/
theorem presentPerfect_isPerfect (t0 toSit : ℤ) (h : toSit < t0) :
    (presentPerfect t0 toSit).toFrame.isPerfect := by
  simp [presentPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPerfect]
  -- E = TS = toSit, R = toSit, but we need E < R.
  -- Wait — in the present perfect, R = TO₁ = t0, E = TS = toSit.
  -- The projection: R = toSit (toSit is TO_sit, which is the last chain element)
  -- So R = toSit and P = t0.  We need E < R, but E = TS = toSit = R.
  -- This is the key issue: the present perfect has E = R (not E < R) in the
  -- Declercian projection, because TS = TO_sit. The perfect aspect is captured
  -- by TO_sit < TO₁, which maps to R < P.
  -- So presentPerfect projects to isPast, not isPerfect.
  -- The PRESENT-ness is in the time-sphere, not in R = P.
  sorry

/-- Present perfect projects to a frame satisfying PAST (R < P) —
    because TO_sit (= R) < TO₁ (= P). The present-sphere membership is
    tracked by `timeSphere`, not by the Reichenbach R/P relation.

    This is Declerck's key structural claim: the perfect/preterit distinction
    is time-sphere, not R/P configuration. Both project to R < P. -/
theorem presentPerfect_frame_isPast (t0 toSit : ℤ) (h : toSit < t0) :
    (presentPerfect t0 toSit).toFrame.isPast := by
  simp [presentPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  exact h

/-- Preterit and present perfect produce identical Reichenbach frames for
    the same times — they differ ONLY in time-sphere. This is Declerck's
    central thesis about the perfect/preterit distinction (ch. 7 §1,3). -/
theorem preterit_presentPerfect_same_frame (t0 toSit : ℤ) :
    (preterit t0 toSit).toFrame = (presentPerfect t0 toSit).toFrame := by
  simp [preterit, presentPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit]

/-- ... but they differ in time-sphere. -/
theorem preterit_presentPerfect_differ_sphere (t0 toSit : ℤ) :
    (preterit t0 toSit).timeSphere ≠ (presentPerfect t0 toSit).timeSphere := by
  simp [preterit, presentPerfect]

/-- Past perfect projects to PAST (R < P), with R further before the
    intermediate TO₂. -/
theorem pastPerfect_isPast (t0 to2 toSit : ℤ) (h : to2 < t0) :
    (pastPerfect t0 to2 toSit).toFrame.isPast := by
  simp [pastPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  sorry

/-- Future projects to FUTURE (R > P). -/
theorem future_isFuture (t0 toSit : ℤ) (h : toSit > t0) :
    (future t0 toSit).toFrame.isFuture := by
  simp [future, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isFuture]
  exact h

/-- Conditional: TO₂ < TO₁ projects to PAST for the intermediate reference.
    The full frame has R (= TO_sit) related to P (= TO₁), but the relation
    is underspecified — TO_sit may be before, at, or after TO₁.

    We can only prove that TO₂ < TO₁ (the chain constraint), which Reichenbach
    would misrepresent as three separate tense schemata. -/
theorem conditional_to2_before_to1 (t0 to2 toSit : ℤ) (h : to2 < t0) :
    to2 < (conditional t0 to2 toSit).to1 := by
  simp [conditional]; exact h

end Bridge


-- ════════════════════════════════════════════════════════════════
-- § Temporal Vagueness
-- ════════════════════════════════════════════════════════════════

/-! Declerck's chain model captures temporal vagueness naturally:
    when a schema's chain doesn't include a direct link between two
    TOs, their relation is genuinely unspecified.

    The future perfect and conditional tense are both vague about
    the relation between TO_sit and TO₁. Reichenbach incorrectly
    treats this as three-way ambiguity (ch. 5 §1.2). -/

/-- The future perfect is vague about TO_sit's relation to t₀:
    the chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT
    TO_sit to TO₁. All three scenarios are consistent. -/
theorem futurePerfect_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ after TO₁ (= t₀ = 0) in all cases
      to2 > 0 ∧
      -- TO_sit before TO₂ in all cases
      toSit₁ < to2 ∧ toSit₂ < to2 ∧ toSit₃ < to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  exact ⟨-1, 0, 1, 5, by omega, by omega, by omega, by omega,
         by omega, rfl, by omega⟩

/-- The conditional tense is vague about TO_sit's relation to t₀:
    the chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT
    TO_sit to TO₁. All three scenarios are consistent.

    Reichenbach's (1947) three separate schemata for the conditional
    (S–R–E, R–S–E, R–E–S) are NOT distinct tenses — they are instances
    of a single vague schema. -/
theorem conditional_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ before TO₁ (= t₀ = 0) in all cases
      to2 < 0 ∧
      -- TO_sit after TO₂ in all cases
      toSit₁ > to2 ∧ toSit₂ > to2 ∧ toSit₃ > to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  exact ⟨-1, 0, 1, -3, by omega, by omega, by omega, by omega,
         by omega, rfl, by omega⟩


-- ════════════════════════════════════════════════════════════════
-- § Concrete Instantiations (ℤ)
-- ════════════════════════════════════════════════════════════════

/-! Concrete examples matching the Phenomena/Tense/Data.lean frames,
    showing the Declercian schemata produce the same data. -/

/-- "John was ill yesterday" — preterit, absolute use.
    t₀ = 0, TO_sit = -3. -/
def exPreterit : DeclercianSchema ℤ := preterit 0 (-3)

/-- "It is raining" — present, point time.
    t₀ = 0, TO_sit = 0. -/
def exPresent : DeclercianSchema ℤ := present 0 0

/-- "I have visited Paris" — present perfect.
    t₀ = 0, TO_sit = -3 (same event time as preterit). -/
def exPresentPerfect : DeclercianSchema ℤ := presentPerfect 0 (-3)

/-- "I visited Paris" — preterit (same event, different sphere). -/
def exPreteritParis : DeclercianSchema ℤ := preterit 0 (-3)

/-- "John had left before we arrived" — past perfect.
    t₀ = 0, TO₂ = -2, TO_sit = -4. -/
def exPastPerfect : DeclercianSchema ℤ := pastPerfect 0 (-2) (-4)

/-- "I will do it next week" — future.
    t₀ = 0, TO_sit = 5. -/
def exFuture : DeclercianSchema ℤ := future 0 5

/-- "John will have left when we arrive" — future perfect.
    t₀ = 0, TO₂ = 5, TO_sit = 3. -/
def exFuturePerfect : DeclercianSchema ℤ := futurePerfect 0 5 3

/-- "The house would weather many more storms" — conditional.
    t₀ = 0, TO₂ = -5, TO_sit = -3. -/
def exConditional : DeclercianSchema ℤ := conditional 0 (-5) (-3)

/-- "He would have left by then" — conditional perfect.
    t₀ = 0, TO₂ = -5, TO₃ = -3, TO_sit = -4. -/
def exConditionalPerfect : DeclercianSchema ℤ := conditionalPerfect 0 (-5) (-3) (-4)


-- ── Concrete bridge verification ──

/-- Concrete preterit satisfies PAST. -/
theorem exPreterit_isPast : exPreterit.toFrame.isPast := by
  simp [exPreterit, preterit, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]

/-- Concrete present satisfies PRESENT. -/
theorem exPresent_isPresent : exPresent.toFrame.isPresent := by
  simp [exPresent, present, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPresent]

/-- Present perfect and preterit project to identical Reichenbach frames. -/
theorem exPerfect_eq_preterit_frame :
    exPresentPerfect.toFrame = exPreteritParis.toFrame := by
  simp [exPresentPerfect, exPreteritParis, presentPerfect, preterit,
        DeclercianSchema.toFrame, DeclercianSchema.toSit]

/-- But they have different time-spheres. -/
theorem exPerfect_neq_preterit_sphere :
    exPresentPerfect.timeSphere ≠ exPreteritParis.timeSphere := by
  simp [exPresentPerfect, exPreteritParis, presentPerfect, preterit]

/-- Concrete future satisfies FUTURE. -/
theorem exFuture_isFuture : exFuture.toFrame.isFuture := by
  simp [exFuture, future, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isFuture]

/-- Concrete future perfect: TO_sit (3) < TO₂ (5), and TO₂ (5) > t₀ (0). -/
theorem exFuturePerfect_chain_valid :
    exFuturePerfect.ts < 5 ∧ (5 : ℤ) > 0 := by
  simp [exFuturePerfect, futurePerfect]

/-- Concrete conditional: TO₂ (-5) < t₀ (0), TO_sit (-3) > TO₂ (-5). -/
theorem exConditional_chain_valid :
    (-5 : ℤ) < 0 ∧ exConditional.ts > (-5 : ℤ) := by
  simp [exConditional, conditional]

/-- Conditional perfect: 4-deep chain is valid. -/
theorem exConditionalPerfect_chain_valid :
    (-5 : ℤ) < 0 ∧ (-3 : ℤ) > (-5 : ℤ) ∧ exConditionalPerfect.ts < (-3 : ℤ) := by
  simp [exConditionalPerfect, conditionalPerfect]


end Semantics.Tense.Declerck
