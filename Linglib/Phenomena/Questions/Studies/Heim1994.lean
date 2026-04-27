import Linglib.Core.Question.Basic
import Linglib.Theories.Semantics.Questions.Resolution
import Linglib.Theories.Semantics.Questions.Exhaustivity

/-!
# @cite{heim-1994}: Interrogative Semantics and Karttunen's Semantics for know
@cite{karttunen-1977} @cite{groenendijk-stokhof-1984}

Single-paper formalisation of @cite{heim-1994} (IATL 1, pp. 128–144),
"Interrogative Semantics and Karttunen's Semantics for know". The paper
asks how Karttunen-style and G&S-style answer notions compare under
question-embedding by `know`, and what minimal modification to
Karttunen's semantics yields G&S-equivalent predictions.

## Substrate identification

@cite{heim-1994} introduces two answer notions:

* **ans₁(α, w)** (eq 15) — "answer-in-the-first-sense":
  the *intersection* `∩⟦α⟧K(w)` of all true Karttunen alternatives at `w`.
  This is exactly `Exhaustivity.weakAnswer Q w` in the substrate.

* **ans₂(α, w)** (eq 16) — "answer-in-the-second-sense":
  `λw'. ans₁(α, w') = ans₁(α, w)` — the set of worlds whose Karttunen
  intersection equals `w`'s. This is the strongly-exhaustive answer
  in the G&S sense.

The substrate's `strongAnswer Q w := {v | ∀ p ∈ alt Q, w ∈ p ↔ v ∈ p}`
is one canonical formulation of the G&S strong answer; Heim's `ans₂`
is the *reflective* formulation that quotients worlds by their
ans₁-class. We prove `strongAnswer ⊆ heimAns2` here; the converse
holds when alternatives are pairwise distinguishable (a typical
empirical assumption — the `Heim 1994` §7 (21)/(24) examples are
counterexamples to the bare equivalence on intensional / contingent
contexts).

## Section coverage

* **§1** Karttunen — `simplifiedKarttunenKnow`-style "x believes ∩q(w)"
  is captured by `weakAnswer`. The actual lexical `know` predicate
  (which involves doxastic accessibility) lives in
  `Theories/Semantics/Attitudes/Doxastic.lean`; we identify the
  *content* `weakAnswer Q w` here.
* **§2** Exhaustiveness — Karttunen's eq (5) "if q(w) = ∅ then x
  believes that q is empty" becomes the substrate's
  `IsExhaustivelyResolvable` (Dayal 1996 EP), already in
  `Exhaustivity.lean`.
* **§3** De dicto readings — requires intensional CN-meanings beyond
  the bare `Set W` substrate; deferred.
* **§4** Generalized Karttunen analysis — Heim's eq (8)/(9): clause
  (i) "x believes ∩q(w)" is *redundant* given clause (ii) "x believes
  λw'[q(w') = q(w)]". The substrate analogue is `strongAnswer ⊆
  weakAnswer`: the strong answer entails the weak one (proved below).
* **§5** Groenendijk & Stokhof — their `whether` denotation
  `λw'. R(w') ↔ R(w)` is precisely `strongAnswer (polar R) w` in
  the substrate.
* **§6** ans₁/ans₂ bridge — formalised here via
  `heimAns1`/`heimAns2` and `strongAnswer_subset_heimAns2`.
* **§7** Non-equivalence: Heim's (21) "John knows which students are
  identical with themselves" and (24) "John knows which students live
  with their actual spouses" — divergence cases requiring intensional
  CN binding; deferred.
* **§8** Structured propositions — requires extending the `Question`
  type with CN-meaning ↔ atomic individual structure; deferred.
-/

namespace Phenomena.Questions.Studies.Heim1994

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### Heim's two answer notions (§6 eq 15-16) -/

/-- @cite{heim-1994} (15): the **answer-in-the-first-sense** is the
    Karttunen intersection `∩⟦α⟧K(w)`. Identified with the substrate's
    `weakAnswer`. -/
def heimAns1 (Q : Question W) (w : W) : Set W :=
  weakAnswer Q w

@[simp] theorem heimAns1_eq_weakAnswer (Q : Question W) (w : W) :
    heimAns1 Q w = weakAnswer Q w := rfl

/-- @cite{heim-1994} (16): the **answer-in-the-second-sense** is the
    set of worlds whose ans₁-image equals `w`'s. The reflective
    formulation of strong exhaustivity. -/
def heimAns2 (Q : Question W) (w : W) : Set W :=
  {w' | heimAns1 Q w' = heimAns1 Q w}

@[simp] theorem mem_heimAns2 (Q : Question W) (w v : W) :
    v ∈ heimAns2 Q w ↔ weakAnswer Q v = weakAnswer Q w := Iff.rfl

theorem heimAns2_self_mem (Q : Question W) (w : W) :
    w ∈ heimAns2 Q w := rfl

/-! ### §6 bridge: `strongAnswer ⊆ heimAns2`

The substrate's `strongAnswer Q w := {v | ∀ p ∈ alt Q, w ∈ p ↔ v ∈ p}`
says `v` decides every alternative the same way as `w`. Heim's
`heimAns2 Q w := {v | weakAnswer Q v = weakAnswer Q w}` says `v` and
`w` have the same Karttunen intersection.

Same-decision-on-every-alt implies same true-alt set, hence same
intersection — direct. -/

/-- Heim's §6 inclusion: if `v` decides every alternative the same
    way as `w`, then `v` and `w` have the same Karttunen intersection. -/
theorem strongAnswer_subset_heimAns2 (Q : Question W) (w : W) :
    strongAnswer Q w ⊆ heimAns2 Q w := by
  intro v hv
  show weakAnswer Q v = weakAnswer Q w
  ext u
  unfold weakAnswer
  refine ⟨fun h p hp hwp => ?_, fun h p hp hvp => ?_⟩
  · -- need v ∈ p; have w ∈ p and v decides p like w
    have hiff : w ∈ p ↔ v ∈ p := hv p hp
    exact h p hp (hiff.mp hwp)
  · have hiff : w ∈ p ↔ v ∈ p := hv p hp
    exact h p hp (hiff.mpr hvp)

/-! ### §4 redundancy

Heim's eq (8)→(9) says clause (i) "x believes ∩q(w)" is *redundant*
given clause (ii) "x believes λw'[q(w') = q(w)]". The substrate
captures this as `Exhaustivity.strongAnswer_subset_weakAnswer`:
any state contained in the strong answer is contained in the weak
answer. No paper-anchored re-export — call the substrate theorem
directly. -/

/-! ### §1: simplified Karttunen content

The simplified Karttunen meaning of `know(Q)(x)` at world `w` is
"x believes `∩q(w)`" — substrate-level: "x's doxastic state is
contained in `weakAnswer Q w`". The doxastic predicate itself lives
in `Theories/Semantics/Attitudes/Doxastic.lean`; here we expose the
content as `weakAnswer`. -/

/-- @cite{heim-1994} §1 (4): the *simplified* Karttunen content of
    `know Q w` is `weakAnswer Q w` — what the agent must believe. -/
def simplifiedKarttunenContent (Q : Question W) (w : W) : Set W :=
  weakAnswer Q w

@[simp] theorem simplifiedKarttunenContent_eq_weakAnswer
    (Q : Question W) (w : W) :
    simplifiedKarttunenContent Q w = weakAnswer Q w := rfl

/-! ### §5: G&S strong answer

@cite{groenendijk-stokhof-1984} `whether` denotes `λw'. R(w') ↔ R(w)`,
which is `strongAnswer (polar R) w`. The substrate already provides
this; we re-export under the paper's vocabulary for cross-reference. -/

/-- @cite{heim-1994} §5 / @cite{groenendijk-stokhof-1984}: the G&S
    answer is the substrate's `strongAnswer`. -/
def gsAnswer (Q : Question W) (w : W) : Set W :=
  strongAnswer Q w

@[simp] theorem gsAnswer_eq_strongAnswer (Q : Question W) (w : W) :
    gsAnswer Q w = strongAnswer Q w := rfl

/-- @cite{heim-1994} §6: G&S answer is contained in Heim's ans₂. -/
theorem gsAnswer_subset_heimAns2 (Q : Question W) (w : W) :
    gsAnswer Q w ⊆ heimAns2 Q w :=
  strongAnswer_subset_heimAns2 Q w

end Phenomena.Questions.Studies.Heim1994
