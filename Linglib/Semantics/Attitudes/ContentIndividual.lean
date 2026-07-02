import Mathlib.Logic.Basic

/-!
# Content Individuals ([kratzer-2006]; [liefke-2024] §4.3) [kratzer-2006]
[baker-jara-ettinger-saxe-tenenbaum-2017] [liefke-2024] [moulton-2015] [hintikka-1962] [hintikka-1962]

A content individual is a first-class mental state carrying propositional
content — the denotation of content DPs like *John's belief that p*,
*the claim*, *every rumor*, *her wish*.

## Ontological Status

Content individuals are the shared sort underlying beliefs, desires, and
percepts ([liefke-2024] §4.3). What distinguishes a belief from a desire or
a percept is not the ontological sort — it is the attitude relation (the
verb) that embeds it.

In BToM, these correspond to the type parameters over
which the observer's posterior is defined. In memo,
they are the *frames* created by `thinks[...]`.

## Identity vs. Entailment

Two ways to relate a content individual x_c to a proposition p:

| Relation    | Definition           | Gloss                  | Source              |
|-------------|----------------------|------------------------|---------------------|
| Identity    | CONT(x_c) = p       | p IS the content       | [kratzer-2006]        |
| Entailment  | CONT(x_c) ⊆ p       | p FOLLOWS from content | [hintikka-1962]       |

Identity is strictly stronger (§3 below).

-/

namespace Semantics.Attitudes

-- ════════════════════════════════════════════════════
-- § 1. The Content Individual Sort
-- ════════════════════════════════════════════════════

/-- A content individual: a first-class mental state carrying propositional
    content.

    This is [kratzer-2006]'s *content individual* — the denotation of content
    DPs like *John's belief that p*, *the claim*, *every rumor*, *her wish*.
    It is the shared ontological sort underlying beliefs, desires, and percepts
    ([liefke-2024] §4.3), and the *frame* created by `thinks[...]` in memo.

    The `cont` field is Kratzer's CONT function: the propositional content
    this mental state carries. Caveat: because `cont` is the only field,
    this formalization identifies individuals with their contents
    (`xc₁ = xc₂ ↔` equal `cont`) — the intuition "my belief that p ≠ your
    belief that p" is NOT captured; a Kratzerian atom-plus-model shape
    (`cont : E → W → (W → Prop)`) would capture it, deferred until a
    study states an identity-vs-content theorem. -/
structure ContentIndividual (W : Type*) where
  /-- Propositional content: CONT(c) -/
  cont : W → Prop

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
    (R : E → W → W → Prop) (agent : E) (w : W) : ContentIndividual W :=
  ⟨R agent w⟩

/-- A content individual is true at a world iff its content holds there. -/
def ContentIndividual.trueAt {W : Type*} (c : ContentIndividual W) (w : W) : Prop :=
  c.cont w

/-- Two content individuals have the same content. -/
def ContentIndividual.sameContent {W : Type*} (c₁ c₂ : ContentIndividual W) : Prop :=
  c₁.cont = c₂.cont

-- ════════════════════════════════════════════════════
-- § 3. Content Entailment
-- ════════════════════════════════════════════════════

/-- Content entailment: the content of x_c entails proposition p (CONT ⊆ p).

    Every world where the content holds, p also holds:
      ∀w. CONT(x_c)(w) → p(w)

    This is the Hintikka reading of attitude reports: "x believes that p"
    means p follows from x's belief content. [kratzer-2006] and [moulton-2015] use the stronger notion of content *identity* (CONT = p). -/
def ContentIndividual.entails {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop) : Prop :=
  ∀ w, xc.cont w → p w

/-- Content identity implies content entailment: CONT(x_c) = p → CONT(x_c) ⊆ p. -/
theorem ContentIndividual.eq_implies_entails {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop) :
    xc.cont = p → xc.entails p := by
  intro h w
  rw [h]
  exact id

/-- Content entailment does not imply content identity.

    Counterexample: empty content (λ_ => False) entails any proposition p,
    but CONT ≠ p when p is nonempty.

    This is the key semantic distinction:
    - Hintikka: "John believes that p" ⟺ p follows from John's beliefs
    - Kratzer/Moulton: "John believes that p" ⟺ p IS John's belief content -/
theorem ContentIndividual.entails_not_implies_eq :
    ¬ ∀ (p : Bool → Prop) (xc : ContentIndividual Bool),
      xc.entails p → xc.cont = p := by
  intro h
  -- The empty content (λ_ => False) entails everything
  have heq := h (fun _ => True) ⟨fun _ => False⟩
    (by simp [ContentIndividual.entails])
  -- But identity would require (λ_ => False) = (λ_ => True)
  exact (iff_of_eq (congr_fun heq true)).mpr trivial

/-! ### World-indexed content ([moulton-2015]; [bondarenko-2022])

A rigid `ContentIndividual` carries its content absolutely; an *indexed*
content individual assigns content at each evaluation index — the shape
needed for de re/de dicto contrasts and DP substitution. It is a family
of rigid individuals, so the rigid API applies pointwise (`(x w).cont`,
`compC p (x w)`): no parallel indexed API exists or should. -/

/-- World-indexed content individual: a family of rigid ones. -/
abbrev ContentIndividual.Indexed (W : Type*) := W → ContentIndividual W

/-- A rigid individual as the constant family — the specialization the
    rest of this file works with. -/
def ContentIndividual.toIndexed {W : Type*} (c : ContentIndividual W) :
    ContentIndividual.Indexed W := fun _ => c

/-- Rigidity: the family is constant across indices. -/
def ContentIndividual.Indexed.IsRigid {W : Type*}
    (x : ContentIndividual.Indexed W) : Prop := ∀ w w', x w = x w'

theorem ContentIndividual.toIndexed_isRigid {W : Type*}
    (c : ContentIndividual W) : c.toIndexed.IsRigid := fun _ _ => rfl

/-- At every index, the constant family is the rigid individual — the
    lemma that transports any rigid theorem pointwise. -/
theorem ContentIndividual.toIndexed_apply {W : Type*}
    (c : ContentIndividual W) (w : W) : c.toIndexed w = c := rfl

end Semantics.Attitudes
