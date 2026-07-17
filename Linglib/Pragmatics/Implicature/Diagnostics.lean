import Mathlib.Tactic.TypeStar

/-!
# Gricean diagnostics for pragmatic inference
[grice-1975] [sadock-1978] [hirschberg-1985] [horn-1991] [geurts-2010]

The classical cancellability and reinforceability tests, stated over a
bare pair of an **assertion** `φ : W → Prop` and an inferred **content**
`W → Prop`. Any strengthening mechanism — a Neo-Gricean recipe
(`Pragmatics/NeoGricean/`), grammatical exhaustification
(`Semantics/Exhaustification/`), a thresholded RSA posterior
(`Pragmatics/RSA/`) — can submit its output to these predicates; no
shared record type is required, so the diagnostics stay neutral between
frameworks that disagree about what an implicature *is*.

[grice-1975] introduced calculability and non-detachability as defining
features; [sadock-1978] added cancellability and schematized the test
battery; [horn-1991] extends the reinforceability discussion via the
redundancy diagnostic. Calculability and detachability are properties of
a *derivation*, not of an (assertion, content) pair, so they are stated
where the derivations live, not here.

The headline consumer is `Studies/DelPinalBassiSauerland2024.lean`: pex
outputs fail cancellability via
`IsCancellable.false_of_assertion_implies_content` because the pex
assertion entails its presupposed content.

Magri-style obligatory SI ([magri-2009]) is **not** an `IsCancellable`
failure, even common-ground-relativized: for "#Some Italians come from a
warm country" with CK restricting to all-warm worlds, "in fact all" is a
consistent continuation contradicting the EXH'd implicature, so
`IsCancellable` holds. The contentful Magri claim — no CK-realizer of
the strengthened meaning — is `magri_blindOdd_no_ck_realizer` in
`Studies/Magri2009.lean`.
-/

namespace Implicature

variable {W : Type*} {φ content : W → Prop}

/-- An inferred `content` derived from an assertion `φ` is
**cancellable** iff some continuation is consistent with `φ` and
contradicts the content: "Some students passed — in fact, all of them
did" is felicitous iff "all passed" is consistent with the assertion and
contradicts *not all*. [sadock-1978]'s diagnostic. -/
def IsCancellable (φ content : W → Prop) : Prop :=
  ∃ cancel : W → Prop,
    (∃ w, φ w ∧ cancel w) ∧
    (∀ w, cancel w → ¬ content w)

/-- Cancellation by the negation of the content itself: if some
assertion-world falsifies the content, `¬content` witnesses
cancellability. The most common cancellation form. -/
theorem IsCancellable.of_assertion_compatible_with_negation
    (h : ∃ w, φ w ∧ ¬ content w) : IsCancellable φ content :=
  ⟨fun w => ¬ content w, h, fun _ hw => hw⟩

/-- The load-bearing non-cancellability principle: if every
assertion-world satisfies the content, no continuation cancels it. Fires
for pex outputs from `holds → presup`. -/
theorem IsCancellable.false_of_assertion_implies_content
    (h : ∀ w, φ w → content w) : ¬ IsCancellable φ content :=
  fun ⟨_, ⟨w, hφ, hc⟩, hcontra⟩ => hcontra w hc (h w hφ)

/-- An inferred `content` is **reinforceable** over assertion `φ` iff it
is not already entailed by the assertion: "Some students passed, but not
all" is non-redundant iff *some passed* does not entail *not all*.
([sadock-1978]; [horn-1991]'s redundancy diagnostic.) -/
def IsReinforceable (φ content : W → Prop) : Prop :=
  ∃ w, φ w ∧ ¬ content w

/-- Reinforceable ⇒ cancellable: the same witness works, so
reinforceability is the stricter diagnostic. The converse may fail
([hirschberg-1985]). -/
theorem IsReinforceable.toCancellable
    (h : IsReinforceable φ content) : IsCancellable φ content :=
  IsCancellable.of_assertion_compatible_with_negation h

end Implicature
