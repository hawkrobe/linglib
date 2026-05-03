import Linglib.Theories.Pragmatics.Implicature.Defs

/-!
# Gricean Diagnostics over `Implicature`
@cite{grice-1975} @cite{sadock-1978} @cite{hirschberg-1985} @cite{horn-1991}
@cite{geurts-2010} @cite{potts-2005} @cite{delpinal-bassi-sauerland-2024}

Formalizes the standard Gricean diagnostic tests for distinguishing
implicatures from entailments and presuppositions, stated uniformly
over the `Implicature W Prop` type from `Defs.lean`. The headline application
is the BPS bridge: when a Presuppositional-EXH output is wrapped as an
`Implicature` via the `bpsPresuppositional` mechanism, the
non-cancellability of the inferred (presupposed) content becomes a
genuine theorem (`bps_not_cancellable`, in
`Theories/Semantics/Exhaustification/Presuppositional.lean`),
not a stipulation. This is the formal contact with the
@cite{bassi-delpinal-sauerland-2021} critique of flat-EXH grammaticalism.

## The four classical tests

| Test                | Sketch                                                         |
|---------------------|----------------------------------------------------------------|
| Cancellability      | A felicitous continuation contradicting the inference exists.  |
| Reinforceability    | The inference can be added explicitly without redundancy.      |
| Calculability       | The inference is derived (not lexically encoded).              |
| Non-detachability   | Paraphrases preserve the inference (form-independence).        |

@cite{grice-1975} introduced calculability and non-detachability as
defining features. @cite{sadock-1978} added cancellability and
schematized the four-test apparatus. @cite{hirschberg-1985} surveys the
diagnostics and their interaction; @cite{horn-1991} extends the
reinforceability discussion via the redundancy diagnostic.

## Joint vs. mechanism-internal tests

`Cancellable` and `Reinforceable` are *joint* properties of an implicature
together with the assertion that gave rise to it — they ask about the
relationship between asserted content and inferred content. These take
two arguments.

`Calculable` and `NonDetachable` are properties of how the inference was
derived, and lift cleanly from the `mechanism` (and, for non-detachability,
the `kind`) field of `Implicature`. These take one argument.

## Strength specialization

The Gricean diagnostics defined here are specialized to the **discrete /
categorical** ontology — they operate on `Implicature W Prop`. The
`S = Prop` `content` lets us write `¬ i.content w` and similar. For
graded mechanisms (RSA-style `Implicature W ℝ`), the diagnostics do not
apply directly: cancellability
and reinforceability would require a thresholding interpretation, which
is itself an empirical commitment. Future work could add a separate
`GradedDiagnostics.lean` if and when graded-content study files demand
it.

The kind- and mechanism-level helpers (`isCalculable`,
`isNonDetachable`) and the failure-mode theorems are polymorphic in `S`
because they only inspect the `kind` and `mechanism` fields.

## Failure modes are diagnostic

A *conventional* implicature (Potts 2005) is by definition lexically
encoded, so it fails calculability — and that failure is itself a
theorem (`lexical_not_calculable`). A *manner* implicature is by
definition form-relative, so it fails non-detachability
(`manner_is_detachable`). These are not bugs; they're how the
diagnostics divide the implicature space.

## What this file delivers vs. what it does NOT

**Delivered:** BPS pex outputs (mechanism `.bpsPresuppositional`) wrap as
`Implicature W Prop` with `content := p.presup` and `assertion := p.holds`;
non-cancellability is a one-line theorem from
`IsCancellable.false_of_assertion_implies_content`. The formal anchor
the @cite{bassi-delpinal-sauerland-2021} critique needed.

**Not delivered as cancellability failure:** Magri-style obligatory SI
(@cite{magri-2009}) is not non-cancellable in the Sadock sense, even
CK-relativized. For "#Some Italians come from a warm country" with CK
restricting to all-warm worlds, "in fact all" is a consistent
continuation at the CK world that contradicts the EXH'd implicature —
so `IsCancellable` (and `IsCancellableInContext`) both hold. The
contentful Magri claim is a different diagnostic — *no CK-realizer of
the strengthened meaning* — formalized as
`magri_blindOdd_no_ck_realizer` in `Magri2009.lean`. Magri obligatoriness
≠ IsCancellable failure; the docstring previously conflated these.
-/

-- ============================================================
-- Mechanism- and kind-level helpers (declared at root so dot
-- notation `m.isCalculable` / `k.isNonDetachable` works on values
-- of those types, mirroring `ImplicatureKind.isConversational` in
-- Defs.lean).
-- ============================================================

/--
A *mechanism* is **calculable** iff inferences derived by it could in
principle be reconstructed from cooperative reasoning over alternatives.
This is the case for every mechanism in the library *except* the lexical
one, which by definition encodes the inference in the lexical entry.

Grice's calculability test is the philosophical anchor of the
conversational/conventional distinction.
-/
def ImplicatureMechanism.isCalculable : ImplicatureMechanism → Prop
  | .lexical => False
  | _ => True

instance : DecidablePred ImplicatureMechanism.isCalculable
  | .lexical => isFalse not_false
  | .neoGricean | .exhIE | .exhII | .exhIEII | .rsa | .ibr
  | .bpsPresuppositional => isTrue trivial

/--
A *kind* is **non-detachable** iff inferences of that kind depend on
asserted content rather than asserted form. The exception is `manner`,
whose entire raison d'être is form-relativity.

@cite{horn-1984}, @cite{levinson-2000}.
-/
def ImplicatureKind.isNonDetachable : ImplicatureKind → Prop
  | .manner => False
  | _ => True

instance : DecidablePred ImplicatureKind.isNonDetachable
  | .manner => isFalse not_false
  | .scalar | .freeChoice | .ignorance | .clausal | .conventional =>
      isTrue trivial


namespace Implicature

variable {W : Type*}

-- ============================================================
-- Cancellability (@cite{sadock-1978})
-- ============================================================

/--
An implicature `i` derived from `assertion φ` is **cancellable** iff
there exists a continuation `cancel` that:

1. is consistent with `φ` (`∃ w, φ w ∧ cancel w`), and
2. contradicts the implicature (`∀ w, cancel w → ¬ i.content w`).

This formalizes the standard Sadock test: "Some students passed —
in fact, all of them did" is felicitous (the *not all* implicature
cancels) iff the continuation "all of them did" is consistent with
the assertion and contradicts "not all."

Negation of `IsCancellable` is the load-bearing diagnostic for the
@cite{bassi-delpinal-sauerland-2021} *Presuppositional EXH* account:
when pex outputs are wrapped as `Implicature W Prop` with
`assertion := PrProp.holds · p` and `content := p.presup`, the
non-cancellability follows from `holds → presup` via
`IsCancellable.false_of_assertion_implies_content`. The substantive
content of "presuppositions fail cancellability" comes from the
structural assertion-vs-presupposition split in `PrProp`, not from
stipulation. The bridge theorem `bps_not_cancellable` is in
`Theories/Semantics/Exhaustification/Presuppositional.lean`.
-/
def IsCancellable (φ : W → Prop) (i : Implicature W Prop) : Prop :=
  ∃ cancel : W → Prop,
    (∃ w, φ w ∧ cancel w) ∧
    (∀ w, cancel w → ¬ i.content w)

/-- Cancellation by the negation of the implicature itself: if there
exists an assertion-world where the implicature fails, then `¬i.content`
witnesses cancellability. The most common cancellation form. -/
theorem IsCancellable.of_assertion_compatible_with_negation
    {φ : W → Prop} {i : Implicature W Prop}
    (h : ∃ w, φ w ∧ ¬ i.content w) : IsCancellable φ i :=
  ⟨fun w => ¬ i.content w, h, fun _ hw => hw⟩

/-- The load-bearing non-cancellability principle: if every
assertion-world satisfies the implicature content, no continuation
can cancel it. Used by the BPS bridge — when `assertion` is `pex.holds`
and `content` is `pex.presup`, this fires from `holds → presup`. -/
theorem IsCancellable.false_of_assertion_implies_content
    {φ : W → Prop} {i : Implicature W Prop}
    (h : ∀ w, φ w → i.content w) : ¬ IsCancellable φ i := by
  rintro ⟨cancel, ⟨w, hφ, hc⟩, hcontra⟩
  exact hcontra w hc (h w hφ)

/--
**Context-relativized cancellability**, generalizing `IsCancellable` by
restricting both the witness and the closing condition to a context
predicate `ctx`. Recovers `IsCancellable` when `ctx = fun _ => True`
(see `IsCancellable.iff_inContext_true`).

Useful for studies that need to relativize cancellability to common
knowledge, QuD, or any other context predicate. NB: this generalization
does NOT close the @cite{magri-2009} obligatoriness claim — Magri's
deviance is "no CK-realizer of the strengthened meaning," not
contextual non-cancellability. See file docstring.
-/
def IsCancellableInContext (φ : W → Prop) (ctx : W → Prop)
    (i : Implicature W Prop) : Prop :=
  ∃ cancel : W → Prop,
    (∃ w, ctx w ∧ φ w ∧ cancel w) ∧
    (∀ w, ctx w → cancel w → ¬ i.content w)

/-- `IsCancellable` is `IsCancellableInContext` with a vacuous context. -/
theorem IsCancellable.iff_inContext_true {φ : W → Prop} {i : Implicature W Prop} :
    IsCancellable φ i ↔ IsCancellableInContext φ (fun _ => True) i := by
  unfold IsCancellable IsCancellableInContext
  constructor
  · rintro ⟨cancel, ⟨w, hφ, hc⟩, hcontra⟩
    exact ⟨cancel, ⟨w, trivial, hφ, hc⟩, fun w _ => hcontra w⟩
  · rintro ⟨cancel, ⟨w, _, hφ, hc⟩, hcontra⟩
    exact ⟨cancel, ⟨w, hφ, hc⟩, fun w => hcontra w trivial⟩


-- ============================================================
-- Reinforceability (@cite{sadock-1978}; @cite{horn-1991})
-- ============================================================

/--
An implicature `i` derived from `assertion φ` is **reinforceable** iff
the implicature content is not already entailed by the assertion alone:
`∃ w, φ w ∧ ¬ i.content w`.

This formalizes the standard "can be reinforced without redundancy"
test: "Some students passed, but not all" is felicitous (the *not all*
implicature reinforces non-redundantly) iff the assertion *some students
passed* does not already entail *not all*.

Note the equivalence: a reinforceable implicature is exactly one whose
content is genuinely additional information beyond the assertion. By
`IsCancellable.of_assertion_compatible_with_negation`, **reinforceable
inferences are cancellable** (the same witness works), so reinforceability
implies cancellability. The converse may fail (@cite{hirschberg-1985}).
-/
def IsReinforceable (φ : W → Prop) (i : Implicature W Prop) : Prop :=
  ∃ w, φ w ∧ ¬ i.content w

/-- Reinforceable ⇒ cancellable. The two diagnostics are not independent:
reinforceability is the stricter condition. -/
theorem IsReinforceable.toCancellable
    {φ : W → Prop} {i : Implicature W Prop}
    (h : IsReinforceable φ i) : IsCancellable φ i :=
  IsCancellable.of_assertion_compatible_with_negation h


-- ============================================================
-- Calculability (Grice 1975) — lifted from `ImplicatureMechanism`
-- ============================================================

/-- An implicature is calculable iff its mechanism is. Polymorphic in
the strength type: only the `mechanism` field is inspected. -/
def IsCalculable {S : Type*} (i : Implicature W S) : Prop :=
  i.mechanism.isCalculable

instance {S : Type*} (i : Implicature W S) : Decidable (IsCalculable i) :=
  inferInstanceAs (Decidable i.mechanism.isCalculable)

/-- The lexical mechanism is the unique non-calculable mechanism. -/
theorem isCalculable_iff_not_lexical {S : Type*} (i : Implicature W S) :
    IsCalculable i ↔ i.mechanism ≠ .lexical := by
  unfold IsCalculable ImplicatureMechanism.isCalculable
  cases i.mechanism <;> decide


-- ============================================================
-- Non-detachability (Grice 1975) — lifted from `ImplicatureKind`
-- ============================================================

/-- An implicature is non-detachable iff its kind is. Polymorphic in
the strength type: only the `kind` field is inspected. -/
def IsNonDetachable {S : Type*} (i : Implicature W S) : Prop :=
  i.kind.isNonDetachable

instance {S : Type*} (i : Implicature W S) : Decidable (IsNonDetachable i) :=
  inferInstanceAs (Decidable i.kind.isNonDetachable)


-- ============================================================
-- Diagnostic profiles
-- ============================================================

/--
A bundle of the four standard diagnostics holding for an implicature
relative to its assertion. Useful as a single hypothesis for downstream
theorems.
-/
structure GriceanProfile (φ : W → Prop) (i : Implicature W Prop) : Prop where
  cancellable    : IsCancellable φ i
  reinforceable  : IsReinforceable φ i
  calculable     : IsCalculable i
  nonDetachable  : IsNonDetachable i


-- ============================================================
-- Failure-mode theorems
-- ============================================================

/-- The lexical mechanism is by definition not derived from cooperative
reasoning — the inference is encoded in the lexical entry — so it fails
calculability. The agreement with @cite{grice-1975}'s original
conventional/conversational distinction is the contentful theorem here.
(Conventional implicatures in @cite{potts-2005}'s sense are the
canonical instantiation: kind `.conventional` paired with mechanism
`.lexical`. The kind hypothesis is unnecessary for the proof; the
mechanism alone suffices.) -/
theorem lexical_not_calculable {S : Type*}
    (i : Implicature W S) (hLex : i.mechanism = .lexical) :
    ¬ IsCalculable i := by
  simp [IsCalculable, ImplicatureMechanism.isCalculable, hLex]

/-- Manner implicatures are by definition form-relative, so they fail
non-detachability. The agreement with @cite{horn-1984}'s Division of
Pragmatic Labor is the contentful theorem. -/
theorem manner_is_detachable {S : Type*}
    (i : Implicature W S) (h : i.kind = .manner) : ¬ IsNonDetachable i := by
  simp [IsNonDetachable, ImplicatureKind.isNonDetachable, h]

end Implicature
