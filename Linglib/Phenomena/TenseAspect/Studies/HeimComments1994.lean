import Linglib.Theories.Semantics.Tense.DeRe
import Linglib.Theories.Semantics.Reference.Acquaintance

/-!
# @cite{heim-1994-comments}: Comments on Abusch's Theory of Tense
@cite{heim-1994-comments} @cite{abusch-1997} @cite{lewis-1979-attitudes}

Single-paper formalisation of @cite{heim-1994-comments} ("Comments on
Abusch's theory of tense", in Kamp ed. *Ellipsis, Tense and Questions*,
Dyana-2 R2.2.B; pp. 143–162). Heim's contribution: "more concrete
formulations of some of the sketchier portions" of @cite{abusch-1997}'s
sequence-of-tense + temporal de re analysis. Three substrate-relevant
contributions:

1. **§1 (pp. 143–148)** — tense-as-pronoun + presupposition formulation
   of constraints; doxastic-alternatives quantification for `believe`
   (eq 9). The substrate's `IsRigidAcrossAlternatives` quantifies
   over the same alternative-set.

2. **§2 (pp. 148–157)** — Heim's central contribution. Two pieces:
   - **ULC as presupposition** (eq 16, p. 149): "If α_i is a tense,
     then [[α_i]]^g,c is only defined if `g(i)` does-not-follow `g(0)`." Implemented
     as a definedness condition on semantic values (eq 18, p. 150).
     The substrate's `isFelicitousWith` is the value-level Prop
     analog (no partiality).
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
of the substrate's:

```
   Heim:       Intension (WorldTimeIndex W T)        T
                  (W × T → T, no agent)
                                ↑
                          precompose
                          (KContext.toSituation)
                                |
   Substrate:  Intension (KContext W E P T)          T
                  (agent + world + time + ... → T)
```

By @cite{abusch-1997}-substrate's `Intension.IsRigid.precomp`
(`Core/IntensionalLogic/Rigidity.lean`), the pullback preserves
rigidity. The image of `toSubstrate` is exactly the **agent-blind**
substrate concepts — concepts that factor through `KContext.toSituation`,
i.e., depend only on the ⟨world, time⟩ projection. Universal-property
characterisation below.

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

namespace Phenomena.TenseAspect.Studies.HeimComments1994

open Core (Intension WorldTimeIndex)
open Core.Context (KContext)
open Semantics.Tense.DeRe (TemporalDeReReading)


-- ════════════════════════════════════════════════════════════════
-- § Heim's "time-concept" (p. 155)
-- ════════════════════════════════════════════════════════════════

/-- @cite{heim-1994-comments} (p. 155): "By a 'time-concept' I mean
    a function from world-time pairs to times." This is the Lewis-style
    centered-world intension at one coordinate less than the substrate's
    `Semantics.Tense.DeRe.TimeConcept` (which adds a Speas-Tenny agent
    slot). Definitionally `Intension (WorldTimeIndex W T) T`. -/
abbrev TimeConcept (W T : Type*) := Intension (WorldTimeIndex W T) T


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Heim TimeConcept ↔ Substrate TimeConcept
-- ════════════════════════════════════════════════════════════════

/-- **Substrate-level pullback** of a Heim time-concept along the
    forgetful projection `Core.Context.KContext.toSituation`. This is
    the canonical embedding of Heim's framework into the substrate's
    centered-world setup: any Heim time-concept lifts to an agent-blind
    substrate `TimeConcept` via pre-composition with the projection. -/
def toSubstrate {W E P T : Type*} (c : TimeConcept W T) :
    Semantics.Tense.DeRe.TimeConcept W E P T :=
  fun k => c k.toSituation

/-- **Pullback preserves rigidity**: by `Intension.IsRigid.precomp`
    (PR-C functoriality), a rigid Heim time-concept lifts to a rigid
    substrate `TimeConcept`. The forgetful projection is the
    substrate's instantiation of the precomposition closure lemma
    at `g := KContext.toSituation`. -/
theorem toSubstrate_isRigid {W E P T : Type*}
    {c : TimeConcept W T} (h : Intension.IsRigid c) :
    Intension.IsRigid (toSubstrate (E := E) (P := P) c) :=
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

/-- **`toSubstrate` is precomposition with `KContext.toSituation`** —
    the bridge IS the substrate's intensional precomposition operator
    at the forgetful projection. This rfl-equivalence wires the
    `Intension.IsRigid.precomp` (and `IsRigidOn.precomp`)
    functoriality lemmas on `Core/IntensionalLogic/Rigidity.lean`
    directly through to Heim time-concepts: any closure property of
    rigidity under precomposition transports to the pullback. -/
theorem toSubstrate_eq_precomp {W E P T : Type*}
    (c : TimeConcept W T) :
    toSubstrate (E := E) (P := P) c = c ∘ KContext.toSituation := rfl


-- ════════════════════════════════════════════════════════════════
-- § ULC as presupposition (eq 16, p. 149; eq 18, p. 150)
-- ════════════════════════════════════════════════════════════════

/-- @cite{heim-1994-comments} eq (16) p. 149: "If α_i is a tense, then
    [[α_i]]^g,c is only defined if `g(i)` does-not-follow `g(0)`." Heim's
    presuppositional construal of @cite{abusch-1997}'s Upper Limit
    Constraint, encoded as a definedness condition.

    ``g(i)` does-not-follow `g(0)`` reads "g(i) does not follow g(0)" — i.e., the
    resolved tense value does not strictly succeed the local evaluation
    time. The substrate's `isFelicitousWith` `.past` is the Prop-valued
    analog: `actualRes < holderContext.time`.

    This def captures Heim's "does not follow" as `¬ (resolved >
    evalTime)` (using the `LinearOrder` ambient on `T`). For
    `LinearOrder`, this is equivalent to `resolved ≤ evalTime`. -/
def ulcDefined {T : Type*} [LinearOrder T] (resolved evalTime : T) : Prop :=
  ¬ (resolved > evalTime)

/-- @cite{heim-1994-comments}'s ULC-as-presupposition (eq 16, p. 149)
    matches the substrate's `isFelicitousWith` for a `TemporalDeReReading`
    under the past constraint, modulo `≤` vs `<`. Heim's "does not
    follow" (`¬ >`, equivalently `≤`) is the strict-past presupposition;
    `isFelicitousWith .past` is `<` (strict precedence). The two
    coincide only on the strict-precedence reading of past tense; the
    weak version (`≤`) admits same-time as the eval-time, which is the
    canonical present-under-past coincidence the substrate's
    `.present` constraint handles. -/
theorem ulcDefined_iff_le {T : Type*} [LinearOrder T] (resolved evalTime : T) :
    ulcDefined resolved evalTime ↔ resolved ≤ evalTime := by
  unfold ulcDefined
  exact not_lt

/-- @cite{heim-1994-comments}'s ULC presupposition projected onto the
    substrate: a `TemporalDeReReading`'s `isFelicitousWith .past`
    implies Heim's ULC definedness. The converse fails for the
    strict-equality case (Heim allows simultaneous; substrate's `.past`
    requires strict precedence). -/
theorem isFelicitousWith_past_imp_ulcDefined
    {W E P T : Type*} [LinearOrder T]
    (dr : TemporalDeReReading W E P T)
    (h : dr.isFelicitousWith .past) :
    ulcDefined dr.actualRes dr.holderContext.time := by
  exact (ulcDefined_iff_le _ _).mpr (le_of_lt h)


-- ════════════════════════════════════════════════════════════════
-- § Acquaintance: Heim's "suitable" qualification (p. 155)
-- ════════════════════════════════════════════════════════════════

/-- @cite{heim-1994-comments} (p. 155): "the qualification 'suitable'
    is meant to exclude descriptions by which one might pick out a time
    without being sufficiently acquainted with it; see Abusch and
    Lewis."

    Heim's "suitable" set of time-concepts IS the substrate's
    `Semantics.Reference.Acquaintance.Cover` at the appropriate
    instantiation `Idx := WorldTimeIndex W T`, `Res := T`. The
    polymorphic substrate's Cover infrastructure handles Heim's
    informal "suitability" filter as a typeclass-shaped concept-set. -/
abbrev SuitableTimeCover (W T : Type*) :=
  Semantics.Reference.Acquaintance.Cover (WorldTimeIndex W T) T

/-- Heim's "suitable" predicate on a Heim time-concept: a `TimeConcept
    W T` is suitable iff it belongs to the available cover. The
    substrate's `Acquaintance.Cover` membership predicate handles
    this directly. -/
def IsSuitable {W T : Type*}
    (c : TimeConcept W T) (cov : SuitableTimeCover W T) : Prop :=
  c ∈ cov

/-- Suitability is preserved under the pullback to the substrate: a
    suitable Heim time-concept lifts to a substrate `TimeConcept` whose
    image lies in the corresponding pulled-back substrate cover. The
    image cover construction documents how Heim's acquaintance
    qualification carries through to the substrate framework. -/
theorem toSubstrate_isSuitable_image {W E P T : Type*}
    (c : TimeConcept W T) (cov : SuitableTimeCover W T)
    (h : IsSuitable c cov) :
    toSubstrate (E := E) (P := P) c ∈
      (fun c' : TimeConcept W T =>
        toSubstrate (E := E) (P := P) c') '' cov := by
  exact ⟨c, h, rfl⟩


end Phenomena.TenseAspect.Studies.HeimComments1994
