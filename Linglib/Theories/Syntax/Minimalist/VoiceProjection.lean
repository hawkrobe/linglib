import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Theories.Syntax.Minimalist.Movement.Smuggling

/-!
# What is Voice? Two competing views
@cite{kratzer-1996} @cite{pylkkanen-2008} @cite{collins-2005} @cite{storment-2026}

A formalizer-side meta-bridge surfacing a substantive theoretical
disagreement neither paper sets up directly: what is the *job* of the
syntactic head called Voice?

## The two views

**Pylkkänen / Kratzer view** (@cite{kratzer-1996}, @cite{pylkkanen-2008}):
Voice is the head that *introduces the external argument*. Its job is
thematic — it bears a θ-relation between the external argument and the
event described by the verb (Event Identification, @cite{kratzer-1996}
eq. 10). All argument-structure theory follows from where Voice projects
and what it bundles with (Cause-Voice bundling, @cite{pylkkanen-2008}
Ch. 3 §3.3). Without Voice, no external argument is introduced at all.

**Collins / Storment view** (@cite{collins-2005}, @cite{storment-2026}):
Voice is the *smuggling projection*. Its job is structural — it provides
the landing site (Spec,VoiceP) into which a constituent can move,
licensing A-movement past an in-situ external argument. The external
argument itself is introduced by *v*, not Voice
(@cite{storment-2026} §4.3). Voice's status as a non-phase head is what
permits smuggling. The voice-as-smuggling-projection conception is "a
notable departure from the view of Voice⁰ as an applicative head that
introduces the external argument" (@cite{storment-2026}, §4.3).

## The disagreement is partly substantive, partly terminological

The two camps do not disagree about *the empirical phenomena*. They
disagree about *which functional head does which job*. Pylkkänen
attributes external-argument introduction to Voice and structural
licensing to higher functional projections (`T⁰`, `Infl`). Collins
attributes external-argument introduction to *v* and structural
licensing (Case + smuggling) to Voice. The label "Voice" denotes
different positions in the two systems.

The orthogonality of the two predicates `IsExternalArgIntroducer` and
`IsSmugglingProjection` (defined below) reflects this: a `VoiceHead`
instance can satisfy one, both, or neither. Linglib's `VoiceHead`
structure encodes both axes (`assignsTheta` and `permitsSmuggling`)
independently, accommodating both views simultaneously.

## Where this meta-bridge sits

Per the CLAUDE.md cross-theory-meta-bridges convention, this is a
formalizer-side synthesis (neither Pylkkänen nor Collins/Storment
formulates the contrast in these exact terms). It lives under
`Theories/Syntax/Minimalism/` because both views are pure-theory
positions about a syntactic head, with no specific empirical phenomenon
at stake. Topic-named (`VoiceProjection`), not stance-named.
-/

namespace Minimalist

/-! ## §1. Two predicates over Voice heads

The Pylkkänen view and the Collins/Storment view make different claims
about what makes a Voice head "well-formed Voice." -/

/-- **Pylkkänen / Kratzer view**: a Voice head is "doing its job" iff
    it introduces an external argument (assigns external θ).
    @cite{kratzer-1996}: Voice = the head bearing the θ-relation. -/
def IsExternalArgIntroducer (v : VoiceHead) : Prop :=
  v.AssignsTheta

instance (v : VoiceHead) : Decidable (IsExternalArgIntroducer v) := by
  unfold IsExternalArgIntroducer; infer_instance

/-- **Collins / Storment view**: a Voice head is "doing its job" iff
    it permits smuggling (it is the structural landing site for a
    constituent moving past an in-situ external argument).
    @cite{collins-2005}, @cite{storment-2026}. -/
def IsSmugglingProjection (v : VoiceHead) : Prop :=
  v.permitsSmuggling = true

instance (v : VoiceHead) : Decidable (IsSmugglingProjection v) := by
  unfold IsSmugglingProjection; infer_instance

/-! ## §2. The two views are orthogonal

Linglib's `VoiceHead` already encodes both axes. The question is
whether they coincide for the canonical Voice instances.
**Answer: they don't.** A Voice head can satisfy either one, both, or
neither — the four corners of the orthogonality square. -/

/-- `voiceAgent` satisfies the Pylkkänen view (it introduces the agent
    external argument) but **fails** the Collins/Storment view
    (agentive Voice is a strong phase head; smuggling is blocked). -/
theorem voiceAgent_pylkkanen_yes_collins_no :
    IsExternalArgIntroducer voiceAgent ∧ ¬ IsSmugglingProjection voiceAgent := by
  decide

/-- `voicePassive` satisfies the Collins view (it is the smuggling
    landing site) but **fails** the Pylkkänen view (it does not
    introduce an external argument — the external arg is in Spec,vP
    per @cite{collins-2005} §2 UTAH). The passive Voice head is
    *puzzling* on Pylkkänen's view: a Voice head with no θ-role to
    assign. -/
theorem voicePassive_collins_yes_pylkkanen_no :
    IsSmugglingProjection voicePassive ∧ ¬ IsExternalArgIntroducer voicePassive := by
  decide

/-- `voiceAnticausative` similarly fits the Collins view (smuggling
    target for the unaccusative-like derivation Storment uses for QI
    and LI) and fails the Pylkkänen view (no external argument). -/
theorem voiceAnticausative_collins_yes_pylkkanen_no :
    IsSmugglingProjection voiceAnticausative ∧
    ¬ IsExternalArgIntroducer voiceAnticausative := by
  decide

/-- The two views are not equivalent: there exist Voice heads
    distinguishing them (in fact, the canonical instances above all do). -/
theorem views_not_equivalent :
    ¬ (∀ v : VoiceHead, IsExternalArgIntroducer v ↔ IsSmugglingProjection v) := by
  intro h
  -- voiceAgent introduces external arg but blocks smuggling
  have hExt : IsExternalArgIntroducer voiceAgent := by decide
  have hSmug : IsSmugglingProjection voiceAgent := (h voiceAgent).mp hExt
  exact absurd hSmug (by decide)

/-! ## §3. What the disagreement amounts to

In Pylkkänen's framework, every Voice head should be an
`IsExternalArgIntroducer`. The fact that linglib's `voicePassive` and
`voiceAnticausative` are not means *Pylkkänen would not call these
"Voice"* — she would attribute the structural-licensing function to a
different (perhaps unnamed) head.

In Collins/Storment's framework, every Voice head should be an
`IsSmugglingProjection`. The fact that linglib's `voiceAgent` is not
means *Collins/Storment would not call this "Voice"* — they would call
it *v* (which `voiceAgent`'s thematic role and phase status more
closely match in their system).

The disagreement is therefore partly *labeling*: which functional head
gets the name "Voice." But it is also partly *substantive*: whether the
same syntactic position can simultaneously introduce an external
argument *and* serve as a smuggling target. Pylkkänen's framework
requires Voice to do (a); Collins/Storment's framework requires Voice
to do (b); and the two functions are made structurally incompatible by
the phase/θ-role correlations Storment defends in §4 of his paper. -/

/-- The substantive incompatibility: a Voice head cannot simultaneously
    satisfy both views. (Equivalently: introducing an external argument
    requires being a phase head, which blocks smuggling.) -/
theorem views_jointly_unsatisfiable_for_canonical_voices :
    ¬ (IsExternalArgIntroducer voiceAgent ∧ IsSmugglingProjection voiceAgent) ∧
    ¬ (IsExternalArgIntroducer voicePassive ∧ IsSmugglingProjection voicePassive) ∧
    ¬ (IsExternalArgIntroducer voiceAnticausative ∧ IsSmugglingProjection voiceAnticausative) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Minimalist
