import Linglib.Core.Question.Basic
import Linglib.Theories.Semantics.Questions.Resolution
import Linglib.Theories.Semantics.Questions.Exhaustivity

/-!
# @cite{george-2011}: Question Embedding and the Semantics of Answers
@cite{karttunen-1977} @cite{groenendijk-stokhof-1984} @cite{heim-1994} @cite{dayal-1996}

Single-paper formalisation of @cite{george-2011}, *Question Embedding
and the Semantics of Answers* (UCLA Ph.D. dissertation). George's
central methodological claim: the **weak/intermediate exhaustivity**
that is widely posited to explain *Maggie-knows-was-admitted* /
*Maggie-knows-wasn't-admitted* contrasts is *dispensable* — what
appears to be a weak-exhaustivity reading is actually a strong
reading under (a) **domain uncertainty** (the wh-restrictor's
extension is not fixed) plus (b) **complementation failure** (the
positive and negative *wh*-questions don't have the symmetric
relationship Groenendijk-Stokhof assumed).

## Substrate identifications

| @cite{george-2011}                              | substrate                              |
|-------------------------------------------------|----------------------------------------|
| **Strong** (eq 125): `λw λα λw'(α(w) = α(w'))`  | `Exhaustivity.strongAnswer`            |
| **Weak** (eq 130): `λw λα λw' ∀β(α(w)(β) → α(w')(β))` | `Exhaustivity.weakAnswer`        |
| Strongly-exhaustive answer set (eq 129)         | `Set.range (strongAnswer Q)` (Fox 2018 LogicalPartition) |
| Weakly-exhaustive answer set (eq 131)           | not directly named; corresponds to the maximal-true-member view of weakAnswer |
| Mention-some answer (§2.6.1)                    | `Resolves σ Q`                         |

George's `Strong` operator (eq 125) takes a world `w` and an abstract
`α` (an `⟨s, τ⟩` function) and returns the proposition that holds
exactly at worlds where the abstract has the same extension as in
`w`. On the substrate's `Question W` view (which fixes `τ = ⟨e, t⟩`-ish
content), `Strong(w)(Q) = strongAnswer Q w`.

George's `Weak` operator (eq 130) takes an abstract `α` and returns
the proposition that holds at worlds where `α`'s extension in the
evaluation world is a *subset* of `α`'s extension here. On the
substrate, this is `weakAnswer Q w` — the conjunction (intersection)
of all alternatives true at `w`.

## Section coverage

* **§2.6.2** Strong operator (eq 125) — substrate identification.
* **§2.6.3** Weak operator (eq 130) — substrate identification, plus
  observation (paragraph after eq 132) that "the weakly exhaustive
  answer is the maximal true member of the weakly-exhaustive answer
  set" — captured by `weakAnswer` semantics.
* **§3.1.1** Negation Generalization (eq 5–10) — formal argument that
  `who walks` and `who doesn't walk` produce the same strongly
  exhaustive answer SET (under classical bivalence + domain
  constancy). Substrate-level: the formal equivalence holds *under
  closed-world assumption*; in the substrate, `strongAnswer Q w` and
  `strongAnswer (negation Q) w` are equivalent only if every world's
  question denotation has the right complementarity. This file states
  the assumption-relative equivalence.
* **§3.1.2** Domain Uncertainty (eq 11–15) — George's first
  dispensability argument: when the wh-restrictor's extension varies
  across worlds (de dicto reading), the equivalence fails. The
  Maggie-knows-(13)-but-not-(15) judgment is consistent with a
  uniform STRONG reading, not evidence for weak.
* **§3.1.3** Complementation Failure — second dispensability
  argument; deferred (substrate captures the underlying machinery
  via `info Q` and `compl`).
* **Chapter 4** (Non-)Reducibility — George's argument that
  responsive predicates' question-embedding semantics is *not*
  always reducible to their that-clause-embedding semantics.
  Requires a doxastic / attitudinal layer; deferred.

## What this file does NOT cover

* George's compositional system (Chapter 2): topical-property /
  abstract machinery is richer than `Question W = LowerSet (Set W)`.
* Chapters 5–6 alternative-question and mention-some scope account.
* Chapter 7 strong-ish exhaustivity speculation.
-/

namespace Phenomena.Questions.Studies.George2011

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### §2.6.2 Strong operator (eq 125) -/

/-- @cite{george-2011} (125): the **Strong** answer operator,
    `λw λα λw'(α(w) = α(w'))`. Substrate identification: the set of
    worlds whose extension on every alternative matches `w`. Same as
    the substrate's `strongAnswer Q w` (see `Heim1994` for the
    bridge to ans₂). -/
def Strong (Q : Question W) (w : W) : Set W :=
  strongAnswer Q w

@[simp] theorem Strong_eq_strongAnswer (Q : Question W) (w : W) :
    Strong Q w = strongAnswer Q w := rfl

/-! ### §2.6.3 Weak operator (eq 130) -/

/-- @cite{george-2011} (130): the **Weak** answer operator,
    `λw λα λw' ∀β(α(w)(β) → α(w')(β))`. Substrate identification:
    the set of worlds where the alternative's extension at `w` is a
    subset of its extension here. Same as the substrate's
    `weakAnswer Q w`. -/
def Weak (Q : Question W) (w : W) : Set W :=
  weakAnswer Q w

@[simp] theorem Weak_eq_weakAnswer (Q : Question W) (w : W) :
    Weak Q w = weakAnswer Q w := rfl

/-- @cite{george-2011} §2.6.3: any state σ supporting the Strong
    answer at `w` also supports the Weak answer at `w` — i.e., strong
    exhaustivity entails weak exhaustivity. This is the formal trace
    of George's claim that "weak exhaustivity is dispensable":
    everywhere we'd want to use Weak, the stronger Strong already
    serves. -/
theorem Strong_subset_Weak (Q : Question W) (w : W) :
    Strong Q w ⊆ Weak Q w :=
  strongAnswer_subset_weakAnswer Q w

/-! ### §3.1.1 Negation Generalization (eq 5)

@cite{george-2011} §3.1.1: under bivalence + domain constancy,
the strongly exhaustive answer SET to *who walks* and to *who
doesn't walk* coincide. Substrate-level: this requires a specific
relationship between the question denotation and its complement —
specifically, that for every alt `p` of `Q`, `pᶜ` (interpreted as
the corresponding negative-question alt) is also in `alt Q'` for
the negative `Q'`.

We state George's claim assumption-relatively: *under* the
bivalence-plus-constancy assumption (every world's alt-true-set
determines the alt-false-set), the strong answers are equivalent.
The substrate doesn't bake in bivalence (worlds can have arbitrary
membership in alts) so the equivalence requires explicit
hypotheses. -/

/-- The §3.1.1 formal observation as a substrate-level conditional:
    if two questions `Q` and `Q'` have alts that mutually decide
    each other (i.e., `Q`-alts and `Q'`-alts agree as a partition),
    then their `strongAnswer` cells coincide at every `w`.

    Captures the @cite{groenendijk-stokhof-1984} argument structure
    that George dissects in (5)-(10). -/
theorem strongAnswer_eq_when_alts_agree
    (Q Q' : Question W) (w : W)
    (hAgree : ∀ v, (∀ p ∈ alt Q, w ∈ p ↔ v ∈ p) ↔
                   (∀ p ∈ alt Q', w ∈ p ↔ v ∈ p)) :
    strongAnswer Q w = strongAnswer Q' w := by
  ext v
  exact hAgree v

/-! ### §3.1.2 Domain Uncertainty

@cite{george-2011} §3.1.2: the apparent inequivalence of
*Maggie-knows-(12)* and *Maggie-knows-(13)* is consistent with a
uniform STRONG-exhaustive reading, *provided* the wh-restrictor's
extension varies across worlds (de dicto interpretation).

Substrate-level: when alternatives don't fully partition the
worlds (e.g., domain restrictions like *which applicants* vary),
strong-exhaustive-Q and strong-exhaustive-(negation Q) can have
*different* extensions even though both encode "Maggie knows the
strong-exhaustive answer". The two predications are consistent
because they're about different sets of possibilities.

This is a paper-level observation about the *space* of cases
admitting weak ↔ strong inequivalence; we capture the substrate
fact that `weakAnswer ⊆ strongAnswer ↔` does NOT hold in general,
and the @cite{george-2011} argument turns on which side of this
asymmetry is empirically active. -/

/-! @cite{george-2011} §3.1.2 substrate fact: the converse
    inclusion `weakAnswer Q w ⊆ strongAnswer Q w` does **not** hold
    in general — strong exhaustivity is strictly stronger than weak.
    Concrete intuition: with `W = {0, 1, 2}` and `Q`'s alts being
    `{0,1}` and `{1,2}` (overlapping non-comparable propositions),
    at `w = 0` the weak answer is `{0,1}` (only `{0,1}` is true at
    `0`) but the strong answer is `{0}` alone (since `1` decides
    `{1,2}` differently from `0`). Constructing this concrete
    instance in Lean requires more substrate API for `alt` of
    `Question.ofList`-style constructions; the substrate fact itself
    is documented in `Exhaustivity.strongAnswer_subset_weakAnswer`'s
    one-direction status. -/

end Phenomena.Questions.Studies.George2011
