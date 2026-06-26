import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Clause Spine: Fine-Grained Clause Size
[elkins-torrence-brown-2026] [grimshaw-2005] [wurmbrand-2014]

`ComplementSize` (ExtendedProjection/Basic.lean) classifies clausal complements
by their highest functional head, which works well for tense-Agree transparency
and CTP classification. But it can't distinguish VoiceP from ApplP, since both
have fValue = 1. Languages like Mam need this
distinction: =(y)a' appears when Voice⁰ is projected but not when only Appl⁰ is.

`ClauseSpine` records the full list of projected heads, enabling per-head
projection queries.

-/

namespace Minimalist

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
    [keine-2020] ch. 2: NmlzP is a distinct clause type from CP — their
    transparency profiles are incomparable (NmlzP blocks Ā but not wh;
    CP blocks wh but not Ā in Hindi). -/
def ClauseSpine.nmlzP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T, .Nmlz], by decide⟩

/-- ForceP-sized clause: [V, Appl, v, Voice, T, C, Force]. German V2 clause.
    [keine-2020] ch. 4: V2 clauses in German are structurally larger
    than V-final (CP) clauses — they project ForceP above CP. -/
def ClauseSpine.forceP : ClauseSpine :=
  ⟨[.V, .Appl, .v, .Voice, .T, .C, .Force], by decide⟩

-- ============================================================================
-- § 4: F-Level Bridge
-- ============================================================================

/-- The F-level of a clause spine: the `fValue` of its highest projected
    head. This bridges `ClauseSpine` (concrete head list) to
    `ExtendedProjection`'s F-value hierarchy, enabling
    [keine-2019]'s transparency calculations.

    Example: `ClauseSpine.cP.fLevel = 6` (C is F6),
    `ClauseSpine.tP.fLevel = 2` (T is F2). -/
def ClauseSpine.fLevel (spine : ClauseSpine) : Nat :=
  fValue spine.highestHead

end Minimalist
