import Mathlib.Tactic.Common

/-!
# Adjective Classification Hierarchy
@cite{kamp-1975} @cite{kamp-partee-1995} @cite{parsons-1970}

The standard classification of adjective meanings as functions from
properties to properties, constrained by meaning postulates.

## Hierarchy

1. **Intersective** (Kamp's "predicative", def. 4): `⟦A N⟧ = ⟦A⟧ ∩ ⟦N⟧`
2. **Subsective** (Kamp's "affirmative", def. 6): `⟦A N⟧ ⊆ ⟦N⟧`
3. **Privative** (def. 5): `⟦A N⟧ ∩ ⟦N⟧ = ∅`
4. **Extensional** (def. 7): depends only on N's extension, not intension
5. **Non-subsective** (modal): no entailment (alleged, potential)

## Implication Structure

    intersective → {extensional, subsective}

Extensional and subsective are independent: neither implies the other.
Privative is incompatible with subsective (given non-empty extension).

## Design

The hierarchy is defined over *intensional* adjective meanings
(`Property W E → Property W E`) parameterized by a world type `W` and
entity type `E`. This is the most general formulation, from which
single-world (extensional) specializations follow — see
`Montague/Modification.lean` for the Montague-typed versions and
`Kamp1975.lean` § 2 for bridge theorems.

@cite{partee-2010} argues the privative class should be eliminated
in favor of subsective + noun coercion; see `Partee2010.lean`.
-/

namespace Semantics.Lexical.Adjective.Classification

/-- An intensional property: a function from worlds to characteristic
    functions over entities. -/
abbrev Property (W E : Type*) := W → E → Bool

/-- An adjective meaning: a function from noun properties to modified
    noun-phrase properties (type `⟨⟨s,⟨e,t⟩⟩, ⟨s,⟨e,t⟩⟩⟩` in Montague
    notation). -/
abbrev AdjMeaning (W E : Type*) := Property W E → Property W E

-- ════════════════════════════════════════════════════
-- § 1. Class Definitions
-- ════════════════════════════════════════════════════

section Hierarchy

variable {W E : Type*}

/-- An adjective is **intersective** if its extension at each world is the
    intersection of the noun's extension with some fixed property Q.
    @cite{kamp-1975} definition (4) ("predicative").

    Examples: "gray", "French", "carnivorous", "four-legged". -/
def isIntersective (adj : AdjMeaning W E) : Prop :=
  ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = (Q w x && N w x)

/-- An adjective is **subsective** if its extension is always a subset
    of the noun's extension.
    @cite{kamp-1975} definition (6) ("affirmative").

    Examples: "skillful", "good", "typical". -/
def isSubsective (adj : AdjMeaning W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = true → N w x = true

/-- An adjective is **privative** if its extension is always disjoint
    from the noun's extension.
    @cite{kamp-1975} definition (5).

    Examples: "fake", "counterfeit".
    @cite{partee-2010} argues this class should be eliminated. -/
def isPrivative (adj : AdjMeaning W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = true → N w x = false

/-- An adjective is **extensional** if its extension in world w depends
    only on the noun's extension in w, not on the noun's intension.
    @cite{kamp-1975} definition (7).

    "four-legged" and "gray" are extensional; "skillful" is not (being a
    skillful surgeon depends on what counts as a surgeon across contexts,
    not just who the surgeons are in this world). -/
def isExtensional (adj : AdjMeaning W E) : Prop :=
  ∀ (N₁ N₂ : Property W E) (w : W),
    (∀ x, N₁ w x = N₂ w x) → ∀ x, adj N₁ w x = adj N₂ w x

-- ════════════════════════════════════════════════════
-- § 2. Implication Structure
-- ════════════════════════════════════════════════════

/-! Intersective → {extensional, subsective}.
    Extensional and subsective are independent.
    Privative is incompatible with subsective (given non-empty extension). -/

/-- Intersective adjectives are extensional: if `F(N)(w) = N(w) ∩ Q(w)`,
    then the result in w depends only on N(w). -/
theorem intersective_implies_extensional {adj : AdjMeaning W E}
    (h : isIntersective adj) : isExtensional adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N₁ N₂ w hext x
  simp only [hQ]
  rw [hext x]

/-- Intersective adjectives are subsective: if
    `F(N)(w)(x) = Q(w)(x) ∧ N(w)(x)`, then `F(N)(w)(x) → N(w)(x)`. -/
theorem intersective_implies_subsective {adj : AdjMeaning W E}
    (h : isIntersective adj) : isSubsective adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N w x hadj
  rw [hQ, Bool.and_eq_true] at hadj
  exact hadj.2

/-- Privative adjectives are not subsective (when the adjective has
    non-empty extension for some noun). -/
theorem privative_not_subsective {adj : AdjMeaning W E}
    (hp : isPrivative adj)
    (hne : ∃ N w x, adj N w x = true) :
    ¬isSubsective adj := by
  intro ha
  obtain ⟨N, w, x, hadj⟩ := hne
  have := ha N w x hadj
  have := hp N w x hadj
  simp_all

end Hierarchy

end Semantics.Lexical.Adjective.Classification
