import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Clause Spine: Fine-Grained Clause Size

`ComplementSize` (ExtendedProjection/Basic.lean) classifies clausal complements
by their highest functional head, which works well for tense-Agree transparency
and CTP classification. But it can't distinguish VoiceP from ApplP, since both
have fValue = 1. Languages like Mam (Elkins, Imanishi & Coon 2026) need this
distinction: =(y)a' appears when Voice⁰ is projected but not when only Appl⁰ is.

`ClauseSpine` records the full list of projected heads, enabling per-head
projection queries while remaining backward-compatible with `ComplementSize`.

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique extraction
  in SJO Mam.
- Wurmbrand, S. (2014). Restructuring across the world.
- Grimshaw, J. (2005). Words and Structure.
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
-- § 3: Bridge to ComplementSize
-- ============================================================================

/-- Convert a ClauseSpine to a ComplementSize by extracting the highest head.
    This preserves backward compatibility: existing consumers of ComplementSize
    can interoperate with the new ClauseSpine. -/
def ClauseSpine.toComplementSize (spine : ClauseSpine) : ComplementSize :=
  ⟨spine.highestHead⟩

-- ============================================================================
-- § 4: Named Spines
-- ============================================================================

/-- ApplP-sized clause: [V, Appl]. Infinitival complement without Voice.
    In Mam, this is the size of infinitival complements where =(y)a' is
    impossible — Voice is not projected, so there is no host for [oblique]. -/
def ClauseSpine.applP : ClauseSpine :=
  ⟨[.V, .Appl], by decide⟩

/-- Bare VP: [V]. Minimal clause — just the lexical verb.
    In Mam, this is the size of infinitival complements (Elkins et al. 2026, §6.1):
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

-- ============================================================================
-- § 5: Projection Theorems
-- ============================================================================

/-- VoiceP projects Voice. -/
theorem voiceP_has_voice : ClauseSpine.voiceP.projects .Voice = true := by native_decide

/-- ApplP does not project Voice. This is the key distinction that
    `ComplementSize` cannot capture (both have fValue = 1 as highest head). -/
theorem applP_lacks_voice : ClauseSpine.applP.projects .Voice = false := by native_decide

/-- CP projects Voice (inherited from the full spine). -/
theorem cP_has_voice : ClauseSpine.cP.projects .Voice = true := by native_decide

/-- TP projects Voice. -/
theorem tP_has_voice : ClauseSpine.tP.projects .Voice = true := by native_decide

/-- Bare VP does not project Voice. -/
theorem bareVP_lacks_voice : ClauseSpine.bareVP.projects .Voice = false := by native_decide

/-- Bare VP does not project Appl. -/
theorem bareVP_lacks_appl : ClauseSpine.bareVP.projects .Appl = false := by native_decide

/-- vP does not project Voice. -/
theorem vP_lacks_voice : ClauseSpine.vP.projects .Voice = false := by native_decide

/-- ApplP projects Appl. -/
theorem applP_has_appl : ClauseSpine.applP.projects .Appl = true := by native_decide

/-- VoiceP and ApplP have the same fValue for their highest head, showing
    why ComplementSize can't distinguish them. -/
theorem voiceP_applP_same_fLevel :
    fValue ClauseSpine.voiceP.highestHead = fValue ClauseSpine.applP.highestHead := by
  native_decide

/-- CP spine roundtrips through ComplementSize. -/
theorem cP_roundtrips : ClauseSpine.cP.toComplementSize = ComplementSize.cP := by
  native_decide

/-- TP spine roundtrips through ComplementSize. -/
theorem tP_roundtrips : ClauseSpine.tP.toComplementSize = ComplementSize.tP := by
  native_decide

-- ============================================================================
-- § 6: Size Ordering
-- ============================================================================

/-- Spine sizes are ordered: ApplP < vP < VoiceP < TP < CP. -/
theorem spine_size_ordering :
    ClauseSpine.applP.size < ClauseSpine.voiceP.size ∧
    ClauseSpine.voiceP.size < ClauseSpine.tP.size ∧
    ClauseSpine.tP.size < ClauseSpine.cP.size := by
  native_decide

end Minimalism
