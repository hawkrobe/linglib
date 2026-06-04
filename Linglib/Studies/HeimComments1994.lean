import Linglib.Semantics.Tense.DeRe
import Linglib.Semantics.Reference.Acquaintance

/-!
# [heim-1994-comments]: Comments on Abusch's Theory of Tense
[heim-1994-comments] [abusch-1997] [lewis-1979-attitudes]

Single-paper formalisation of [heim-1994-comments] ("Comments on
Abusch's theory of tense", in Kamp ed. *Ellipsis, Tense and Questions*,
Dyana-2 R2.2.B; pp. 143–162). Heim's contribution: "more concrete
formulations of some of the sketchier portions" of [abusch-1997]'s
sequence-of-tense + temporal de re analysis. Three substrate-relevant
contributions:

1. **§1 (pp. 143–148)** — tense-as-pronoun + presupposition formulation
   of constraints; doxastic-alternatives quantification for `believe`
   (eq 9). The substrate's `IsRigidAcrossAlternatives` quantifies
   over the same alternative-set.

2. **§2 (pp. 148–157)** — Heim's central contribution. Two pieces:
   - **ULC as presupposition** (eq 16, p. 149): "If α_i is a tense,
     then [[α_i]]^g,c is only defined if `g(i)` does-not-follow `g(0)`."
     The substrate's `Tense.upperLimitConstraint` (in `Tense/Basic.lean`)
     IS this presupposition, already typed at `[LE Time]` and credited
     to [heim-1994-comments] in its docstring; this study file
     proves the felicity-to-ULC bridge through the substrate primitive.
   - **Time-concept** (p. 155): "By a 'time-concept' I mean a function
     from world-time pairs to times. Think of these as the meanings
     of descriptions which a thinker might represent a time to herself."
     **This is precisely `Intension (WorldTimeIndex W T) T`** — one
     coordinate fewer than the substrate's
     `TimeConcept := Intension (KContext W E P T) T` (which adds the
     Speas-Tenny agent slot).
   - **"Suitable" qualification** (p. 155): "meant to exclude
     descriptions by which one might pick out a time without being
     sufficiently acquainted with it; see Abusch and Lewis." Maps to
     the substrate's `Acquaintance.Cover` filter at
     `Idx := WorldTimeIndex W T`, `Res := T`.

3. **§3 (pp. 158–162)** — "Tense Licensing Condition" (TLC, eq 49,
   p. 161): an alternative framework using covert `<` and `≺` zero
   affixes plus an LF-distribution constraint. Out of substrate scope
   (would require Tree-rewrite operators on `Tree C W`, deferred
   per `Tense/DeRe.lean` docstring). Cited but not formalised here.

## Substrate identification

Heim's `time-concept` framework is a **proper coordinate-projection**
of the substrate's: Heim works at `Intension (WorldTimeIndex W T) T`
(world + time → time), the substrate at
`Intension (KContext W E P T) T` (agent + addressee + world + time +
position → time). The pullback `toSubstrate := Intension.precomp
KContext.toSituation` carries Heim's framework into the substrate by
pre-composing with the forgetful projection. The image is exactly the
**agent-blind** substrate concepts (universal property below). Rigidity
preservation, set-relativized rigidity preservation, and
exhaustiveness preservation all factor through the substrate's
intensional precomp infrastructure
(`Core/Logic/Intensional/Rigidity.lean`).

## What's not formalised

- **§3 TLC**: covert affix + LF-distribution constraint. Requires
  modelling tense morphemes as elements of a `Tree C W` LF and
  defining "in the domain of" on tree contexts. The substrate
  exposes only the `output` of res-movement (no Tree-rewrite
  operators). Heim's TLC IS a substrate-orthogonal proposal —
  it makes claims about LF distribution (syntactic side), not about
  the centered-world content (semantic side) the substrate captures.
- **Heim's de se PRO analysis** (eq 11–12, p. 147): de se reading
  via Comp-binding of an i-typed variable. The substrate's
  `holderContext.agent` is structurally Heim's de se anchor, but
  the LF-binding mechanism is deferred along with §3 TLC.
- **Heim's "back-shifted" reading via res-movement** (eq 32–33,
  pp. 154–155): res-moved tense + Lewis acquaintance-relation lexical
  entry for `believe`. Substrate's `TemporalDeReReading` IS the
  output-level encoding of this; the Tree-rewrite syntactic
  operation that produces it is deferred.

-/

namespace HeimComments1994

open Core (Intension WorldTimeIndex)
open Semantics.Context (KContext)
open Semantics.Tense.DeRe (TemporalDeReReading)


-- ════════════════════════════════════════════════════════════════
-- § Heim's "time-concept" (p. 155)
-- ════════════════════════════════════════════════════════════════

/-- [heim-1994-comments] (p. 155): "By a 'time-concept' I mean
    a function from world-time pairs to times." This is the Lewis-style
    centered-world intension at one coordinate less than the substrate's
    `Semantics.Tense.DeRe.TimeConcept` (which adds a Speas-Tenny agent
    slot). Definitionally `Intension (WorldTimeIndex W T) T`. -/
abbrev TimeConcept (W T : Type*) := Intension (WorldTimeIndex W T) T


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Heim TimeConcept ↔ Substrate TimeConcept
-- ════════════════════════════════════════════════════════════════

/-- **Substrate-level pullback** of a Heim time-concept along the
    forgetful projection `Semantics.Context.KContext.toSituation`. This IS
    the substrate's intensional pre-composition operator
    `Intension.precomp` instantiated at `g := KContext.toSituation` —
    no new content; the pullback's structural properties transport
    from the substrate's `precomp`/`IsRigid.precomp`/`IsRigidOn.precomp`
    closure lemmas (`Core/Logic/Intensional/Rigidity.lean`). -/
def toSubstrate {W E P T : Type*} (c : TimeConcept W T) :
    Semantics.Tense.DeRe.TimeConcept W E P T :=
  Intension.precomp KContext.toSituation c

/-- **Pullback preserves rigidity**: a rigid Heim time-concept lifts to
    a rigid substrate `TimeConcept`. Direct application of substrate's
    `Intension.IsRigid.precomp` at `g := KContext.toSituation`. -/
theorem toSubstrate_isRigid {W E P T : Type*}
    {c : TimeConcept W T} (h : Intension.IsRigid c) :
    Intension.IsRigid (toSubstrate (E := E) (P := P) c) :=
  h.precomp KContext.toSituation

/-- **Pullback preserves set-relativized rigidity**: rigidity on a set
    `S : Set (WorldTimeIndex W T)` of Heim alternatives lifts to
    rigidity on the preimage `Set.preimage KContext.toSituation S` of
    substrate alternatives. Direct application of substrate's
    `Intension.IsRigidOn.precomp` at `g := KContext.toSituation`.

    This is the last-mile companion to `toSubstrate_isRigid` that
    closes the substrate's `IsRigidAcrossAlternatives` family
    (in `Tense/DeRe.lean`) under the Heim quotient — Heim time-concepts
    that are rigid across a doxastic alternative set lift to substrate
    concepts rigid across the corresponding pulled-back alternative
    set. -/
theorem toSubstrate_isRigidOn {W E P T : Type*}
    {c : TimeConcept W T} {S : Set (WorldTimeIndex W T)}
    (h : Intension.IsRigidOn c S) :
    Intension.IsRigidOn (toSubstrate (E := E) (P := P) c)
      (Set.preimage KContext.toSituation S) :=
  h.precomp KContext.toSituation

/-- **Universal property of the pullback** (the deep structural
    claim): a substrate `TimeConcept` `k` arises as the pullback of
    some Heim time-concept iff `k` is **agent-blind** (factors
    through `KContext.toSituation`).

    This characterises Heim's framework as the *quotient* of the
    substrate's framework by agent variation — Heim works at the
    ⟨world, time⟩ resolution; the substrate adds a ⟨agent,
    addressee, position⟩ refinement. The pullback-image is precisely
    the substrate concepts that "don't see" the refinement.

    The witness construction in the backward direction uses
    `Classical.arbitrary` on the agent / position coordinates, so
    the theorem requires `Nonempty E` and `Nonempty P` (otherwise
    `KContext W E P T` is empty and the universal property is
    degenerate). -/
theorem toSubstrate_factors_iff_agent_blind {W E P T : Type*}
    [Nonempty E] [Nonempty P]
    (k : Semantics.Tense.DeRe.TimeConcept W E P T) :
    (∃ c : TimeConcept W T, k = toSubstrate c) ↔
    (∀ c₁ c₂ : KContext W E P T,
      c₁.toSituation = c₂.toSituation → k c₁ = k c₂) := by
  constructor
  · rintro ⟨c, rfl⟩ k₁ k₂ heq
    show c k₁.toSituation = c k₂.toSituation
    rw [heq]
  · intro h
    refine ⟨fun s => k ⟨Classical.arbitrary E, Classical.arbitrary E,
                          s.world, s.time, Classical.arbitrary P⟩, ?_⟩
    funext k₀
    apply h
    rfl


-- ════════════════════════════════════════════════════════════════
-- § ULC as presupposition (eq 16, p. 149)
-- ════════════════════════════════════════════════════════════════

/-- [heim-1994-comments] eq (16) p. 149: "If α_i is a tense, then
    [[α_i]]^g,c is only defined if `g(i)` does-not-follow `g(0)`."
    Heim's presuppositional construal of [abusch-1997]'s Upper
    Limit Constraint is already encoded in the substrate as
    `Semantics.Tense.upperLimitConstraint` (typed `[LE Time]`,
    anchored to [heim-1994-comments] in its docstring). This
    bridge theorem projects the substrate's `TemporalDeReReading`
    `isFelicitousWith .past` (strict `<`) onto the substrate's ULC
    primitive (weak `≤`), via `le_of_lt`.

    The implication is one-way: substrate `.past` is strict precedence,
    Heim's ULC is non-strict, the converse fails on the simultaneous
    boundary case. The substrate's `.present` constraint (which Heim
    handles separately as a tense-pronoun resolution) covers the
    boundary case. -/
theorem isFelicitousWith_past_imp_upperLimitConstraint
    {W E P T : Type*} [LinearOrder T]
    (dr : TemporalDeReReading W E P T)
    (h : dr.isFelicitousWith .past) :
    Semantics.Tense.upperLimitConstraint
      dr.actualRes dr.holderContext.time :=
  le_of_lt h


-- ════════════════════════════════════════════════════════════════
-- § Acquaintance: Heim's "suitable" qualification (p. 155)
-- ════════════════════════════════════════════════════════════════

/-- [heim-1994-comments] (p. 155): "the qualification 'suitable'
    is meant to exclude descriptions by which one might pick out a time
    without being sufficiently acquainted with it; see Abusch and
    Lewis."

    Heim's "suitable" set of time-concepts IS the substrate's
    `Semantics.Reference.Acquaintance.Cover` at the appropriate
    instantiation `Idx := WorldTimeIndex W T`, `Res := T`. Membership
    `c ∈ cov` is the suitability predicate directly — no separate
    `IsSuitable` wrapper is needed. -/
abbrev SuitableTimeCover (W T : Type*) :=
  Semantics.Reference.Acquaintance.Cover (WorldTimeIndex W T) T

/-- **Pullback preserves cover exhaustiveness**: if `cov` is a
    suitability cover for Heim time-concepts that exhaustively
    identifies values in `dom : Set T` at every Heim
    `WorldTimeIndex`, then the lifted cover `toSubstrate '' cov`
    exhaustively identifies the same `dom` at every substrate
    `KContext`. This is the substantive content of "Heim's
    acquaintance qualification carries through to the substrate
    framework": the agent-blind quotient does not weaken
    exhaustiveness, because every substrate context projects to a
    Heim index where the cover is exhaustive. -/
theorem toSubstrate_image_isExhaustiveOn {W E P T : Type*}
    {cov : SuitableTimeCover W T} {dom : Set T}
    (h : cov.isExhaustiveOn dom) :
    Semantics.Reference.Acquaintance.Cover.isExhaustiveOn
      ((fun c : TimeConcept W T =>
        toSubstrate (E := E) (P := P) c) '' cov) dom := by
  intro k r hr
  obtain ⟨c, hcov, hcr⟩ := h k.toSituation hr
  refine ⟨toSubstrate (E := E) (P := P) c, ⟨c, hcov, rfl⟩, ?_⟩
  exact hcr


end HeimComments1994
