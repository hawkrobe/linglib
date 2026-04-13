import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Clause Spine: Fine-Grained Clause Size
@cite{elkins-torrence-brown-2026} @cite{grimshaw-2005} @cite{wurmbrand-2014}

`ComplementSize` (ExtendedProjection/Basic.lean) classifies clausal complements
by their highest functional head, which works well for tense-Agree transparency
and CTP classification. But it can't distinguish VoiceP from ApplP, since both
have fValue = 1. Languages like Mam need this
distinction: =(y)a' appears when Voice⁰ is projected but not when only Appl⁰ is.

`ClauseSpine` records the full list of projected heads, enabling per-head
projection queries.

-/

namespace Minimalism

-- ============================================================================
-- § 1: ClauseSpine Structure
-- ============================================================================

/-- A clause spine: the ordered sequence of functional heads projected in a
    clause, from lowest (V) to highest (e.g., C). Unlike `ComplementSize`,
    which records only the highest head, `ClauseSpine` records every projected
    head, enabling per-head queries.

    Example: a transitive clause with Voice projects [V, Appl, v, Voice],
    while an infinitival without Voice projects [V, Appl]. -/
structure ClauseSpine where
  /-- Projected heads, ordered bottom-up (V first, highest last).
      Non-empty: every clause projects at least a lexical head. -/
  projectedHeads : List Cat
  /-- The spine is non-empty -/
  nonempty : projectedHeads ≠ []
  deriving Repr

-- ============================================================================
-- § 2: Queries
-- ============================================================================

/-- Does this spine project a given functional head? -/
def ClauseSpine.projects (spine : ClauseSpine) (c : Cat) : Bool :=
  spine.projectedHeads.any (· == c)

/-- The highest head in the spine (always exists by nonempty invariant). -/
def ClauseSpine.highestHead (spine : ClauseSpine) : Cat :=
  match spine.projectedHeads.getLast? with
  | some c => c
  | none => .V  -- unreachable by invariant

/-- The lowest (lexical) head in the spine. -/
def ClauseSpine.lowestHead (spine : ClauseSpine) : Cat :=
  match spine.projectedHeads.head? with
  | some c => c
  | none => .V  -- unreachable by invariant

/-- Number of projected heads. -/
def ClauseSpine.size (spine : ClauseSpine) : Nat :=
  spine.projectedHeads.length

-- ============================================================================
-- § 3: Named Spines
-- ============================================================================

/-- ApplP-sized clause: [V, Appl]. Infinitival complement without Voice.
    In Mam, this is the size of infinitival complements where =(y)a' is
    impossible — Voice is not projected, so there is no host for [oblique]. -/
def ClauseSpine.applP : ClauseSpine :=
  ⟨[.V, .Appl], by decide⟩

/-- Bare VP: [V]. Minimal clause — just the lexical verb.
    In Mam, this is the size of infinitival complements:
    the embedded clause is just VP, lacking Voice, Appl, v. -/
def ClauseSpine.bareVP : ClauseSpine :=
  ⟨[.V], by decide⟩

/-- vP-sized clause: [V, v]. Light verb shell without Voice or Appl. -/
def ClauseSpine.vP : ClauseSpine :=
  ⟨[.V, .v], by decide⟩

/-- VoiceP-sized clause: [V, Appl, v, Voice]. Projects Voice head.
    In Mam, this is the size of "aspectless" complements — Voice is projected,
    so [oblique] can be hosted, and =(y)a' is obligatory on oblique extraction. -/
def ClauseSpine.voiceP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice], by decide⟩

/-- TP-sized clause: [V, Appl, v, Voice, T]. Full inflectional domain. -/
def ClauseSpine.tP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T], by decide⟩

/-- CP-sized clause: [V, Appl, v, Voice, T, C]. Full finite clause. -/
def ClauseSpine.cP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T, .C], by decide⟩

/-- NmlzP-sized clause: [V, Appl, v, Voice, T, Nmlz]. Hindi nominalized clause.
    @cite{keine-2020} ch. 2: NmlzP is a distinct clause type from CP — their
    transparency profiles are incomparable (NmlzP blocks Ā but not wh;
    CP blocks wh but not Ā in Hindi). -/
def ClauseSpine.nmlzP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T, .Nmlz], by decide⟩

/-- ForceP-sized clause: [V, Appl, v, Voice, T, C, Force]. German V2 clause.
    @cite{keine-2020} ch. 4: V2 clauses in German are structurally larger
    than V-final (CP) clauses — they project ForceP above CP. -/
def ClauseSpine.forceP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T, .C, .Force], by decide⟩

-- ============================================================================
-- § 4: Projection Theorems
-- ============================================================================

/-- VoiceP projects Voice. -/
theorem voiceP_has_voice : ClauseSpine.voiceP.projects .Voice = true := by decide

/-- ApplP does not project Voice. This is the key distinction that
    `ComplementSize` cannot capture (both have fValue = 1 as highest head). -/
theorem applP_lacks_voice : ClauseSpine.applP.projects .Voice = false := by decide

/-- CP projects Voice (inherited from the full spine). -/
theorem cP_has_voice : ClauseSpine.cP.projects .Voice = true := by decide

/-- TP projects Voice. -/
theorem tP_has_voice : ClauseSpine.tP.projects .Voice = true := by decide

/-- Bare VP does not project Voice. -/
theorem bareVP_lacks_voice : ClauseSpine.bareVP.projects .Voice = false := by decide

/-- Bare VP does not project Appl. -/
theorem bareVP_lacks_appl : ClauseSpine.bareVP.projects .Appl = false := by decide

/-- vP does not project Voice. -/
theorem vP_lacks_voice : ClauseSpine.vP.projects .Voice = false := by decide

/-- ApplP projects Appl. -/
theorem applP_has_appl : ClauseSpine.applP.projects .Appl = true := by decide

/-- NmlzP projects Nmlz but not C. -/
theorem nmlzP_has_nmlz : ClauseSpine.nmlzP.projects .Nmlz = true := by decide
theorem nmlzP_lacks_c : ClauseSpine.nmlzP.projects .C = false := by decide

/-- CP projects C but not Nmlz. -/
theorem cP_lacks_nmlz : ClauseSpine.cP.projects .Nmlz = false := by decide

/-- ForceP projects Force and C. -/
theorem forceP_has_force : ClauseSpine.forceP.projects .Force = true := by decide
theorem forceP_has_c : ClauseSpine.forceP.projects .C = true := by decide

/-- VoiceP and ApplP have the same fValue for their highest head, showing
    why ComplementSize can't distinguish them. -/
theorem voiceP_applP_same_fLevel :
    fValue ClauseSpine.voiceP.highestHead = fValue ClauseSpine.applP.highestHead := by
  decide

-- ============================================================================
-- § 5: F-Level Bridge
-- ============================================================================

/-- The F-level of a clause spine: the `fValue` of its highest projected
    head. This bridges `ClauseSpine` (concrete head list) to
    `ExtendedProjection`'s F-value hierarchy, enabling
    @cite{keine-2019}'s transparency calculations.

    Example: `ClauseSpine.cP.fLevel = 6` (C is F6),
    `ClauseSpine.tP.fLevel = 2` (T is F2). -/
def ClauseSpine.fLevel (spine : ClauseSpine) : Nat :=
  fValue spine.highestHead

/-- CP-sized clauses are F6. -/
theorem cP_fLevel : ClauseSpine.cP.fLevel = 6 := by decide

/-- TP-sized clauses are F2. -/
theorem tP_fLevel : ClauseSpine.tP.fLevel = 2 := by decide

/-- vP-sized clauses are F1. -/
theorem vP_fLevel : ClauseSpine.vP.fLevel = 1 := by decide

/-- VoiceP-sized clauses are F1. -/
theorem voiceP_fLevel : ClauseSpine.voiceP.fLevel = 1 := by decide

/-- NmlzP-sized clauses are F3 (same as FinP). -/
theorem nmlzP_fLevel : ClauseSpine.nmlzP.fLevel = 3 := by decide

/-- ForceP-sized clauses are F6 (same as CP in fValue, but structurally larger). -/
theorem forceP_fLevel : ClauseSpine.forceP.fLevel = 6 := by decide

-- ============================================================================
-- § 6: Size Ordering
-- ============================================================================

/-- Spine sizes are ordered: ApplP < vP < VoiceP < TP < CP < ForceP.
    NmlzP has the same size as CP (both have 6 projected heads). -/
theorem spine_size_ordering :
    ClauseSpine.applP.size < ClauseSpine.voiceP.size ∧
    ClauseSpine.voiceP.size < ClauseSpine.tP.size ∧
    ClauseSpine.tP.size < ClauseSpine.cP.size ∧
    ClauseSpine.cP.size < ClauseSpine.forceP.size := by
  decide

/-- NmlzP and CP have the same number of projected heads — their
    difference is in WHICH heads are projected, not how many. -/
theorem nmlzP_cP_same_size :
    ClauseSpine.nmlzP.size = ClauseSpine.cP.size := by decide

end Minimalism
