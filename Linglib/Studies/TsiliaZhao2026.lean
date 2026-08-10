import Linglib.Semantics.Tense.Perspective
import Linglib.Semantics.Reference.Context.Basic
import Linglib.Studies.Zhao2025

/-!
# Tsilia & Zhao 2026: Tense and perspective

[tsilia-zhao-2026] solve the ⌈then⌉-present puzzle: temporal ⌈then⌉ is
incompatible with the present tense across languages, even where the present
*shifts* (denoting the attitude 'now' rather than utterance time) — yet
compatible in the very same language (Modern Greek) with *deleted* (SOT)
tense, distinguishing the shifted present from deleted tense for the first
time. Tenses and ⌈then⌉ are interpreted relative to a temporal perspective π;
the operator OP_π rebinds π clause-wide, so a shifted PRES and a clausemate
⌈then⌉ read the SAME π and their overlap/disjointness presuppositions clash —
a shift-together effect in the temporal domain, after the indexical-shift
monsters of [anand-nevins-2004] and [deal-2020]
(`shifted_present_blocks_then`). Deleted tense has no perspectival
presupposition, so ⌈then⌉ stays satisfiable
(`Tense.Perspective.thenPresup_satisfiable`). The [sharvit-2003] simultaneous
reading is the case where the shifted PRES presupposition holds trivially
(`Tense.simultaneousFrame_isPresent`).

## Cross-linguistic data

The ⌈then⌉ inventory is `Zhao2025.thenAdverbs` (Greek *tóte*, Hebrew *az*,
Russian *togda*, Japanese *tōji*, English *then*). The tense-shift
typology (`TenseShiftProfile`): present-under-past shifts in attitude
reports in Greek, Hebrew and Russian, also in relative clauses in Japanese,
and never in English; present-under-future shifts everywhere, because
will = WOLL + PRES and WOLL is intensional, providing the OP_π site even in
relative clauses. The English present under future is *deleted* by SOT
(c-commanded by WOLL's PRES), not shifted — which is why English ⌈then⌉
tolerates present-under-future.
-/

namespace TsiliaZhao2026

open Time Tense Tense.Perspective
open Semantics.Context (KContext)

/-! ### Shift together -/

/-- A shifted present blocks ⌈then⌉: OP_π rebinds π for the whole frame, so
    the shifted PRES (R = π') and a clausemate ⌈then⌉ (reference disjoint
    from π') read the same π' — no reference satisfies both the "during
    then" containment and disjointness. *Nate said Erica is angry (*then)*. -/
theorem shifted_present_blocks_then {Time : Type*}
    (f : ReichenbachFrame Time) (attitudeTime : Time)
    (hPres : (opPi f attitudeTime).isPresent) :
    ¬∃ thenRef, (opPi f attitudeTime).referenceTime = thenRef ∧
      thenPresup thenRef (opPi f attitudeTime).perspectiveTime :=
  λ ⟨_, hDuring, hThen⟩ => then_present_clash _ hPres hDuring hThen

/-! ### Tense-shift typology -/

/-- A language's tense-shift profile: whether a simultaneous reading of an
    embedded present is available in each of the four
    past/future × attitude/relative configurations, and whether the
    language's SOT rule can delete a present. -/
structure TenseShiftProfile where
  /-- Language name -/
  language : String
  /-- Present-under-past, attitude report complement -/
  pastAttitude : Bool
  /-- Present-under-past, relative clause -/
  pastRelative : Bool
  /-- Present-under-future, attitude report complement -/
  futAttitude : Bool
  /-- Present-under-future, relative clause -/
  futRelative : Bool
  /-- Does the language have SOT deletion that can apply to the present?
      English: yes (present under future is deleted, not shifted).
      Modern Greek: no (the "Interpret the Present" constraint blocks
      deletion). -/
  sotDeletesPresent : Bool
  /-- Is ⌈then⌉ restricted to past-oriented contexts?
      Japanese *tōji* cannot co-occur with future matrix tense. -/
  thenPastOnly : Bool := false
  deriving Repr, DecidableEq

/-- Modern Greek: shifts in attitude reports (past & future) and relative
    clauses under future, but NOT in relative clauses under past. -/
def greekProfile : TenseShiftProfile where
  language := "Modern Greek"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Modern Hebrew: same pattern as Greek for shift; no SOT deletion of
    present. -/
def hebrewProfile : TenseShiftProfile where
  language := "Modern Hebrew"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Russian: same pattern as Greek/Hebrew for shift. -/
def russianProfile : TenseShiftProfile where
  language := "Russian"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Japanese: uniquely shifts in relative clauses under past too (tenses are
    intensional). *tōji* is restricted to past-oriented contexts. -/
def japaneseProfile : TenseShiftProfile where
  language := "Japanese"
  pastAttitude := true
  pastRelative := true
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false
  thenPastOnly := true

/-- English: no shift under past; simultaneous reading under future comes
    from SOT deletion (will = WOLL + PRES, embedded PRES deleted by SOT). -/
def englishProfile : TenseShiftProfile where
  language := "English"
  pastAttitude := false
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := true

/-- The surveyed languages' tense-shift profiles. -/
def allProfiles : List TenseShiftProfile :=
  [greekProfile, hebrewProfile, russianProfile, japaneseProfile, englishProfile]

/-- No language allows shift in relative clauses under past unless it also
    allows shift in attitude reports under past. -/
theorem relative_shift_implies_attitude_shift :
    ∀ p ∈ allProfiles, p.pastRelative = true → p.pastAttitude = true := by
  intro p hp hRel
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile,
      englishProfile]

/-- Under future, all surveyed languages shift, in attitude reports and
    relative clauses alike — WOLL is universally intensional. -/
theorem universal_shift_under_future :
    ∀ p ∈ allProfiles, p.futAttitude = true ∧ p.futRelative = true := by
  intro p hp
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- English is the only surveyed language whose SOT deletes the present. -/
theorem sot_deletes_present_unique :
    ∀ p ∈ allProfiles, p.sotDeletesPresent = true → p = englishProfile := by
  intro p hp hSOT
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile,
      englishProfile]

/-- Japanese is the only surveyed language that shifts the present in a
    relative clause under past. -/
theorem past_relative_shift_unique :
    ∀ p ∈ allProfiles, p.pastRelative = true → p = japaneseProfile := by
  intro p hp hRel
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile,
      englishProfile]

/-! ### Perspective is not context -/

/-- The interpretation parameter tuple ⟨c, π⟩ from ⟦·⟧^{c,π,g}. Context c
    (for indexicals, [anand-nevins-2004]) and perspective π (for tense) are
    independent parameters: `shiftPerspective` preserves `context`, and
    `shiftContext` preserves `perspective`. This is the paper's argument that
    the perspective can be identified with neither the context nor the
    evaluation index: tense shift is possible without indexical shift
    (Modern Greek shifts the present but never τώρα 'now'), and neither
    shift is obligatory. -/
structure InterpParams (W E P T : Type*) where
  /-- Context parameter c = ⟨c_s, c_a, c_t, c_w⟩ — for indexicals
      (I, now, here) -/
  context : KContext W E P T
  /-- Temporal perspective π — for tense (PRES, PAST, ⌈then⌉).
      Defaults to c_t in root clauses; shifted by OP_π under attitude
      verbs. -/
  perspective : T

variable {W E P T : Type*}

/-- OP_π on the interpretation parameter tuple: shift π, preserve c. -/
def InterpParams.shiftPerspective (ip : InterpParams W E P T) (newPi : T) :
    InterpParams W E P T :=
  { ip with perspective := newPi }

/-- OP_c on the interpretation parameter tuple: shift c, preserve π. -/
def InterpParams.shiftContext (ip : InterpParams W E P T)
    (newC : KContext W E P T) : InterpParams W E P T :=
  { ip with context := newC }

/-- OP_π preserves the context parameter (including c_t): tense shift does
    not entail indexical shift. -/
theorem InterpParams.shiftPerspective_preserves_context
    (ip : InterpParams W E P T) (newPi : T) :
    (ip.shiftPerspective newPi).context = ip.context := rfl

/-- OP_c preserves the temporal perspective: indexical shift does not entail
    tense shift. -/
theorem InterpParams.shiftContext_preserves_perspective
    (ip : InterpParams W E P T) (newC : KContext W E P T) :
    (ip.shiftContext newC).perspective = ip.perspective := rfl

/-- In root clauses, π defaults to c_t: the Truth Convention evaluates
    ⟦φ⟧ relative to c and π = c_t. -/
def InterpParams.rootDefault (c : KContext W E P T) : InterpParams W E P T where
  context := c
  perspective := c.time

/-- After OP_π, c_t is unchanged — π and c_t can diverge. -/
theorem InterpParams.perspective_context_diverge
    (ip : InterpParams W E P T) (newPi : T)
    (hDistinct : newPi ≠ ip.context.time) :
    (ip.shiftPerspective newPi).perspective ≠
      (ip.shiftPerspective newPi).context.time :=
  hDistinct

end TsiliaZhao2026
