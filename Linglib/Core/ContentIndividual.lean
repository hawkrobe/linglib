import Linglib.Core.Semantics.Proposition
import Linglib.Tactics.OntSort

/-!
# Content Individuals (@cite{kratzer-2006}; @cite{liefke-2024} §4.3) @cite{kratzer-2006}
@cite{baker-jara-ettinger-saxe-tenenbaum-2017} @cite{chandra-2025} @cite{liefke-2024} @cite{moulton-2015} @cite{hintikka-1969} @cite{hintikka-1962}

A content individual is a first-class mental state carrying propositional
content — the denotation of content DPs like *John's belief that p*,
*the claim*, *every rumor*, *her wish*.

## Ontological Status

Content individuals are the shared sort underlying beliefs, desires, and
percepts (@cite{liefke-2024} §4.3). What distinguishes a belief from a desire or
a percept is not the ontological sort — it is the attitude relation (the
verb) that embeds it.

In BToM, these correspond to the type parameters over
which the observer's posterior is defined. In memo,
they are the *frames* created by `thinks[...]`.

## Identity vs. Entailment

Two ways to relate a content individual x_c to a proposition p:

| Relation    | Definition           | Gloss                  | Source              |
|-------------|----------------------|------------------------|---------------------|
| Identity    | CONT(x_c) = p       | p IS the content       | @cite{kratzer-2006}        |
| Entailment  | CONT(x_c) ⊆ p       | p FOLLOWS from content | @cite{hintikka-1969}       |

Identity is strictly stronger (§3 below).

-/

namespace Core

open Core.Proposition

-- ════════════════════════════════════════════════════
-- § 1. The Content Individual Sort
-- ════════════════════════════════════════════════════

/-- A content individual: a first-class mental state carrying propositional
    content.

    This is @cite{kratzer-2006}'s *content individual* — the denotation of content
    DPs like *John's belief that p*, *the claim*, *every rumor*, *her wish*.
    It is the shared ontological sort underlying beliefs, desires, and percepts
    (@cite{liefke-2024} §4.3), and the *frame* created by `thinks[...]` in memo.

    The `cont` field is Kratzer's CONT function: the propositional content
    this mental state carries. Two distinct content individuals can share
    the same content (my belief that p ≠ your belief that p). -/
@[ont_sort] structure ContentIndividual (W : Type*) where
  /-- Propositional content: CONT(c) -/
  cont : BProp W

-- ════════════════════════════════════════════════════
-- § 2. Basic Operations
-- ════════════════════════════════════════════════════

/-- Construct a content individual from a Hintikka-style accessibility relation.
    Given agent `a` at world `w`, the content is the set of accessible worlds.

    This shows that the classical doxastic semantics is a
    special case: a single deterministic content individual whose CONT is
    λw'. R(a, w, w'). Works for doxastic (believe), bouletic (want), and
    perceptual (see) accessibility alike — the sort is the same. -/
def ContentIndividual.fromAccessibility {W E : Type*}
    (R : E → W → W → Bool) (agent : E) (w : W) : ContentIndividual W :=
  ⟨R agent w⟩

/-- A content individual is true at a world iff its content holds there. -/
def ContentIndividual.trueAt {W : Type*} (c : ContentIndividual W) (w : W) : Bool :=
  c.cont w

/-- Two content individuals have the same content. -/
def ContentIndividual.sameContent {W : Type*} (c₁ c₂ : ContentIndividual W) : Prop :=
  c₁.cont = c₂.cont

-- ════════════════════════════════════════════════════
-- § 3. Content Entailment
-- ════════════════════════════════════════════════════

/-- Content entailment: the content of x_c entails proposition p (CONT ⊆ p).

    Every world where the content holds, p also holds:
      ∀w. CONT(x_c)(w) = true → p(w) = true

    This is the Hintikka reading of attitude reports: "x believes that p"
    means p follows from x's belief content. @cite{kratzer-2006} and @cite{moulton-2015} use the stronger notion of content *identity* (CONT = p). -/
def ContentIndividual.entails {W : Type*}
    (xc : ContentIndividual W) (p : BProp W) : Prop :=
  ∀ w, xc.cont w = true → p w = true

/-- Content identity implies content entailment: CONT(x_c) = p → CONT(x_c) ⊆ p. -/
theorem ContentIndividual.eq_implies_entails {W : Type*}
    (xc : ContentIndividual W) (p : BProp W) :
    xc.cont = p → xc.entails p := by
  intro h w
  rw [h]
  exact id

/-- Content entailment does not imply content identity.

    Counterexample: empty content (λ_ => false) entails any proposition p,
    but CONT ≠ p when p is nonempty.

    This is the key semantic distinction:
    - Hintikka: "John believes that p" ⟺ p follows from John's beliefs
    - Kratzer/Moulton: "John believes that p" ⟺ p IS John's belief content -/
theorem ContentIndividual.entails_not_implies_eq :
    ¬ ∀ (p : BProp Bool) (xc : ContentIndividual Bool),
      xc.entails p → xc.cont = p := by
  intro h
  -- The empty content (λ_ => false) entails everything
  have := h (fun _ => true) ⟨fun _ => false⟩
    (by simp [ContentIndividual.entails])
  -- But identity would require (λ_ => false) = (λ_ => true)
  exact absurd (congr_fun this true) Bool.noConfusion

end Core
