import Linglib.Theories.Pragmatics.Implicature.Defs

/-!
# Gricean Diagnostics over `Implicature`
@cite{grice-1975} @cite{sadock-1978} @cite{hirschberg-1985}
@cite{geurts-2010} @cite{potts-2005}

Formalizes the standard Gricean diagnostic tests for distinguishing
implicatures from entailments and presuppositions, stated uniformly
over the `Implicature W` type from `Defs.lean`. Because the diagnostics
range over all mechanisms, BPS-style presuppositional EXH and Magri-style
obligatory implicatures can be proved to *fail* cancellability — the
contemporary critique of grammaticalist views becomes formal work the
library can host.

## The four classical tests

| Test                | Sketch                                                         |
|---------------------|----------------------------------------------------------------|
| Cancellability      | A felicitous continuation contradicting the inference exists.  |
| Reinforceability    | The inference can be added explicitly without redundancy.      |
| Calculability       | The inference is derived (not lexically encoded).              |
| Non-detachability   | Paraphrases preserve the inference (form-independence).        |

@cite{grice-1975} introduced calculability and non-detachability as
defining features. @cite{sadock-1978} added cancellability. @cite{hirschberg-1985}
ch. 1 surveys the diagnostics and their interaction.

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
categorical** ontology — they operate on `Implicature W` (which is
`Implicature W Prop` after the default). The `S = Prop` `content` lets
us write `¬ i.content w` and similar. For graded mechanisms (RSA-style
`Implicature W ℝ`), the diagnostics do not apply directly: cancellability
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
theorem (`conventional_not_calculable`). A *manner* implicature is by
definition form-relative, so it fails non-detachability
(`manner_is_detachable`). These are not bugs; they're how the
diagnostics divide the implicature space.
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
  | .neoGricean | .exhIE | .exhII | .exhIEII | .rsa | .ibr =>
      isTrue trivial

/--
A *kind* is **non-detachable** iff inferences of that kind depend on
asserted content rather than asserted form. The exception is `manner`,
whose entire raison d'être is form-relativity.

@cite{horn-1984}, @cite{levinson-2000} ch. 2.
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
-- Cancellability (Sadock 1978)
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

Negation of `IsCancellable` is the load-bearing diagnostic for
presuppositional and grammaticalist accounts:
@cite{bassi-delpinal-sauerland-2021} present a *Presuppositional EXH*
where the implicature becomes a presupposition, and presuppositions
characteristically fail this test (Cancellability) — the implicature
content is required by the well-formedness of the utterance, so no
consistent cancel exists. That non-cancellability is provable, not
merely cited.
-/
def IsCancellable (φ : W → Prop) (i : Implicature W) : Prop :=
  ∃ cancel : W → Prop,
    (∃ w, φ w ∧ cancel w) ∧
    (∀ w, cancel w → ¬ i.content w)

/-- Cancellation by the negation of the implicature itself: if there
exists an assertion-world where the implicature fails, then `¬i.content`
witnesses cancellability. The most common cancellation form. -/
theorem IsCancellable.of_assertion_compatible_with_negation
    {φ : W → Prop} {i : Implicature W}
    (h : ∃ w, φ w ∧ ¬ i.content w) : IsCancellable φ i :=
  ⟨fun w => ¬ i.content w, h, fun _ hw => hw⟩


-- ============================================================
-- Reinforceability (Sadock 1978; Horn 1991)
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
implies cancellability. The converse may fail (Hirschberg 1985 ch. 1).
-/
def IsReinforceable (φ : W → Prop) (i : Implicature W) : Prop :=
  ∃ w, φ w ∧ ¬ i.content w

/-- Reinforceable ⇒ cancellable. The two diagnostics are not independent:
reinforceability is the stricter condition. -/
theorem IsReinforceable.toCancellable
    {φ : W → Prop} {i : Implicature W}
    (h : IsReinforceable φ i) : IsCancellable φ i :=
  IsCancellable.of_assertion_compatible_with_negation h


-- ============================================================
-- Calculability (Grice 1975) — lifted from `ImplicatureMechanism`
-- ============================================================

/-- An implicature is calculable iff its mechanism is. Polymorphic in
the strength type: only the `mechanism` field is inspected. -/
def IsCalculable {S : Type} (i : Implicature W S) : Prop :=
  i.mechanism.isCalculable

instance {S : Type} (i : Implicature W S) : Decidable (IsCalculable i) :=
  inferInstanceAs (Decidable i.mechanism.isCalculable)

/-- The lexical mechanism is the unique non-calculable mechanism. -/
theorem isCalculable_iff_not_lexical (i : Implicature W) :
    IsCalculable i ↔ i.mechanism ≠ .lexical := by
  unfold IsCalculable ImplicatureMechanism.isCalculable
  cases i.mechanism <;> simp


-- ============================================================
-- Non-detachability (Grice 1975) — lifted from `ImplicatureKind`
-- ============================================================

/-- An implicature is non-detachable iff its kind is. Polymorphic in
the strength type: only the `kind` field is inspected. -/
def IsNonDetachable {S : Type} (i : Implicature W S) : Prop :=
  i.kind.isNonDetachable

instance {S : Type} (i : Implicature W S) : Decidable (IsNonDetachable i) :=
  inferInstanceAs (Decidable i.kind.isNonDetachable)


-- ============================================================
-- Diagnostic profiles
-- ============================================================

/--
A bundle of the four standard diagnostics holding for an implicature
relative to its assertion. Useful as a single hypothesis for downstream
theorems.
-/
structure GriceanProfile (φ : W → Prop) (i : Implicature W) : Prop where
  cancellable    : IsCancellable φ i
  reinforceable  : IsReinforceable φ i
  calculable     : IsCalculable i
  nonDetachable  : IsNonDetachable i


-- ============================================================
-- Failure-mode theorems
-- ============================================================

/-- Conventional implicatures are by definition not derived from
cooperative reasoning — they're lexically encoded — so they fail
calculability. The agreement with @cite{grice-1975}'s original
distinction is the contentful theorem here. -/
theorem conventional_not_calculable {S : Type}
    (i : Implicature W S) (_hKind : i.kind = .conventional)
    (hLex : i.mechanism = .lexical) : ¬ IsCalculable i := by
  unfold IsCalculable ImplicatureMechanism.isCalculable
  rw [hLex]
  exact id

/-- Manner implicatures are by definition form-relative, so they fail
non-detachability. The agreement with @cite{horn-1984}'s Division of
Pragmatic Labor is the contentful theorem. -/
theorem manner_is_detachable {S : Type}
    (i : Implicature W S) (h : i.kind = .manner) : ¬ IsNonDetachable i := by
  unfold IsNonDetachable ImplicatureKind.isNonDetachable
  rw [h]
  exact id

end Implicature
