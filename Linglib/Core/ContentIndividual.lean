import Linglib.Core.Proposition
import Linglib.Tactics.OntSort

/-!
# Content Individuals (Kratzer 2006; Liefke 2024 §4.3) @cite{kratzer-2006}

A content individual is a first-class mental state carrying propositional
content — the denotation of content DPs like *John's belief that p*,
*the claim*, *every rumor*, *her wish*.

## Ontological Status

Content individuals are the shared sort underlying beliefs, desires, and
percepts (Liefke 2024 §4.3). What distinguishes a belief from a desire or
a percept is not the ontological sort — it is the attitude relation (the
verb) that embeds it.

In BToM (Baker et al. 2017), these correspond to the type parameters over
which the observer's posterior is defined. In memo (Chandra et al. 2025),
they are the *frames* created by `thinks[...]`.

## Identity vs. Entailment

Two ways to relate a content individual x_c to a proposition p:

| Relation    | Definition           | Gloss                  | Source              |
|-------------|----------------------|------------------------|---------------------|
| Identity    | CONT(x_c) = p       | p IS the content       | Kratzer 2006        |
| Entailment  | CONT(x_c) ⊆ p       | p FOLLOWS from content | Hintikka 1969       |

Identity is strictly stronger (§3 below).

## References

- Kratzer, A. (2006). Decomposing attitude reports.
- Moulton, K. (2015). CPs: Copies and compositionality. LI 46(2).
- Liefke, K. (2024). Natural Language Ontology, §4.3.
- Hintikka, J. (1969). Knowledge and Belief.
- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). BToM.
- Chandra, Goodman, Meylan, Hawkins et al. (2025). memo.
-/

namespace Core.BToM

open Core.Proposition

-- ════════════════════════════════════════════════════
-- § 1. The Content Individual Sort
-- ════════════════════════════════════════════════════

/-- A content individual: a first-class mental state carrying propositional
    content.

    This is Kratzer's (2006) *content individual* — the denotation of content
    DPs like *John's belief that p*, *the claim*, *every rumor*, *her wish*.
    It is the shared ontological sort underlying beliefs, desires, and percepts
    (Liefke 2024 §4.3), and the *frame* created by `thinks[...]` in memo
    (Chandra et al. 2025).

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

    This shows that the classical doxastic semantics (Hintikka 1969) is a
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
    means p follows from x's belief content. Kratzer (2006) and Moulton
    (2015) use the stronger notion of content *identity* (CONT = p). -/
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

end Core.BToM
