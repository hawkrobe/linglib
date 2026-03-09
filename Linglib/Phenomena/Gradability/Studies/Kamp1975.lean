import Linglib.Theories.Semantics.Montague.Modification
import Linglib.Core.Logic.Truth3
import Mathlib.Data.Set.Basic

/-!
# Kamp (1975): Two Theories about Adjectives @cite{kamp-1975}

In E. Keenan (ed.), *Formal Semantics of Natural Languages*, 123–155.
Cambridge University Press.

## Overview

Kamp presents two theories of adjective semantics:

**Theory 1 (§ 1–2)**: Adjectives as functions from properties to
properties (type `⟨⟨e,t⟩,⟨e,t⟩⟩`). The classification hierarchy:

1. **Predicative** (4): `∃Q. ∀N w. F(N)(w) = N(w) ∩ Q(w)` — the
   adjective contributes an independent property
2. **Privative** (5): `∀N w. F(N)(w) ∩ N(w) = ∅` — "fake gun" is not
   a gun
3. **Affirmative** (6): `∀N w. F(N)(w) ⊆ N(w)` — subsective
4. **Extensional** (7): `∀N₁ N₂ w. N₁(w) = N₂(w) → F(N₁)(w) = F(N₂)(w)`
   — depends only on the noun's extension, not its intension

**Theory 2 (§ 3–7)**: Vague/graded models. The positive form of a
gradable adjective is vague — its extension is partial. Kamp introduces
*vague models* `⟨M, S, F, p⟩` (partial model + completions + σ-field +
probability measure) and derives the comparative from quantification
over completions. This framework is the common ancestor of both
@cite{fine-1975}'s supervaluationism and @cite{klein-1980}'s delineation
approach.

## Structure

- § 1: Intensional adjective hierarchy (Theory 1): predicativeK,
  privativeK, affirmativeK, extensionalK with implication structure
- § 2: Bridge to `Modification.lean`'s extensional hierarchy
- § 3: Many-valued logic failure (motivation for Theory 2)
- § 4: Kamp → Klein lineage: `kampAtLeastAs` ↔ `kleinMoreThan`

## Key Insight

Kamp argues (p. 233 of the Brill reprint) that truth-functional
many-valued logic *fails* for natural language connectives: if
`⟦φ⟧ = ½`, then `⟦φ ∧ ¬φ⟧` should be 0 (contradictions are false),
but any truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also
gives `F(∧)(½, ½) = 0` for non-contradictory `⟦φ ∧ φ⟧`. This
motivates the move to supervaluation / probability over completions.
-/

namespace Phenomena.Gradability.Studies.Kamp1975

-- ════════════════════════════════════════════════════
-- § 1. The Intensional Adjective Hierarchy
-- ════════════════════════════════════════════════════

/-! Kamp's classification requires possible worlds to distinguish
    **extensional** from non-extensional adjectives. We parameterize by
    a world type `W` and an entity type `E`. A *property* is an intensional
    predicate `W → E → Bool`; an adjective meaning maps properties to
    properties. -/

variable (W E : Type*) in
/-- An intensional property: a function from worlds to characteristic
    functions over entities. -/
abbrev Property (W E : Type*) := W → E → Bool

variable (W E : Type*) in
/-- An adjective meaning in Kamp's framework: a function from noun
    properties to noun-phrase properties (type `⟨⟨s,⟨e,t⟩⟩, ⟨s,⟨e,t⟩⟩⟩`
    in Montague notation). -/
abbrev AdjMeaningK (W E : Type*) := Property W E → Property W E

section Hierarchy

variable {W E : Type*}

/-- @cite{kamp-1975} definition (4): an adjective is **predicative** if
    its extension at each world is the intersection of the noun's extension
    with some fixed property Q.

    "four-legged", "French", "carnivorous". -/
def isPredicativeK (adj : AdjMeaningK W E) : Prop :=
  ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = (Q w x && N w x)

/-- @cite{kamp-1975} definition (5): an adjective is **privative** if
    its extension is always disjoint from the noun's extension.

    "fake", "counterfeit". -/
def isPrivativeK (adj : AdjMeaningK W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = true → N w x = false

/-- @cite{kamp-1975} definition (6): an adjective is **affirmative**
    (subsective) if its extension is always a subset of the noun's extension.

    "skillful", "good", "typical". -/
def isAffirmativeK (adj : AdjMeaningK W E) : Prop :=
  ∀ (N : Property W E) (w : W) (x : E),
    adj N w x = true → N w x = true

/-- @cite{kamp-1975} definition (7): an adjective is **extensional** if
    its extension in world w depends only on the noun's extension in w,
    not on the noun's intension (its extension in other worlds).

    Kamp: "if two properties have the same extension in w then the
    properties obtained by applying the adjective to them also have the
    same extension in w."

    "four-legged", "gray" are extensional; "skilful" is not (being a
    skilful surgeon depends on what counts as a surgeon across contexts,
    not just who the surgeons are in this world). -/
def isExtensionalK (adj : AdjMeaningK W E) : Prop :=
  ∀ (N₁ N₂ : Property W E) (w : W),
    (∀ x, N₁ w x = N₂ w x) → ∀ x, adj N₁ w x = adj N₂ w x

-- ════════════════════════════════════════════════════
-- Implication Structure
-- ════════════════════════════════════════════════════

/-! The implication structure is: predicative → {extensional, affirmative}.
    Extensional and affirmative are **independent** — neither implies the
    other in general. An adjective can be extensional without being
    affirmative (it could map noun extensions to unrelated sets in a
    world-independent way), and affirmative without being extensional
    (like "skilful", which is subsective but depends on the noun's
    intension).

    Privative is incompatible with affirmative (given non-empty extension). -/

/-- Predicative adjectives are extensional: if `F(N)(w) = N(w) ∩ Q(w)`,
    then the result in w depends only on N(w). -/
theorem predicativeK_implies_extensionalK {adj : AdjMeaningK W E}
    (h : isPredicativeK adj) : isExtensionalK adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N₁ N₂ w hext x
  simp only [hQ]
  rw [hext x]

/-- Predicative adjectives are affirmative (subsective): if
    `F(N)(w)(x) = Q(w)(x) ∧ N(w)(x)`, then `F(N)(w)(x) → N(w)(x)`. -/
theorem predicativeK_implies_affirmativeK {adj : AdjMeaningK W E}
    (h : isPredicativeK adj) : isAffirmativeK adj := by
  obtain ⟨Q, hQ⟩ := h
  intro N w x hadj
  rw [hQ] at hadj
  exact Bool.and_elim_right hadj

/-- Privative adjectives are not affirmative (when the adjective has
    non-empty extension for some noun). -/
theorem privativeK_not_affirmativeK {adj : AdjMeaningK W E}
    (hp : isPrivativeK adj)
    (hne : ∃ N w x, adj N w x = true) :
    ¬isAffirmativeK adj := by
  intro ha
  obtain ⟨N, w, x, hadj⟩ := hne
  have := ha N w x hadj
  have := hp N w x hadj
  simp_all

end Hierarchy

-- ════════════════════════════════════════════════════
-- § 2. Bridge to Modification.lean
-- ════════════════════════════════════════════════════

/-! `Modification.lean` defines `isIntersective` and `isSubsective` in a
    single-world extensional setting (using `Model`). These are Kamp's
    (4) and (6) specialized to a single world. -/

section Bridge

variable {W E : Type*}

/-- Single-world specialization: given a fixed world, the intensional
    hierarchy reduces to the extensional one.

    If `adj` is predicativeK, then at any fixed world `w`, the function
    `N ↦ adj N w` is intersective in the sense of `Modification.lean`
    (there exists a fixed predicate Q(w) such that the result is
    Q(w) ∩ N(w)). -/
theorem predicativeK_at_world_is_intersective {adj : AdjMeaningK W E}
    (h : isPredicativeK adj) (w : W) :
    ∃ (Q_w : E → Bool), ∀ (N : E → Bool) (x : E),
      adj (λ _ => N) w x = (Q_w x && N x) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, λ N x => hQ (λ _ => N) w x⟩

/-- Single-world specialization of affirmativeK = subsective. -/
theorem affirmativeK_at_world_is_subsective {adj : AdjMeaningK W E}
    (h : isAffirmativeK adj) (w : W) :
    ∀ (N : E → Bool) (x : E),
      adj (λ _ => N) w x = true → N x = true := by
  intro N x hadj
  exact h (λ _ => N) w x hadj

end Bridge

-- ════════════════════════════════════════════════════
-- § 3. Many-Valued Logic Failure
-- ════════════════════════════════════════════════════

/-! @cite{kamp-1975} (p. 233) argues that truth-functional many-valued
    logic cannot adequately handle vague connectives. The key observation:

    If `⟦φ⟧ = ½` (borderline), then `⟦¬φ⟧ = ½` (standard negation).
    We want `⟦φ ∧ ¬φ⟧ = 0` (contradictions are false). But any
    truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also gives
    `F(∧)(½, ½) = 0` for the non-contradictory `φ ∧ φ`, since the
    inputs are identical. This is wrong: `φ ∧ φ` should have the same
    value as `φ`.

    Strong Kleene logic (`Truth3.meet`) makes the symmetric choice:
    `meet indet indet = indet`. This preserves `φ ∧ φ ≡ φ` but fails
    to make contradictions false. Supervaluationism resolves both. -/

open Core.Duality (Truth3)

/-- Strong Kleene conjunction of `indet` with itself is `indet`, not
    `false`. This means `φ ∧ φ` is correctly handled (same as `φ`),
    but `φ ∧ ¬φ` gets `indet` rather than the desired `false`. -/
theorem kleene_indet_and_indet :
    Truth3.meet .indet .indet = .indet := rfl

/-- Kamp's dilemma: Strong Kleene `meet` cannot distinguish `φ ∧ φ`
    from `φ ∧ ¬φ` when `φ` is borderline, because both reduce to
    `meet indet indet`.

    Supervaluationism resolves this: `φ ∧ ¬φ` is **super-false** (false
    on every precisification) while `φ ∧ φ` is **indefinite** (true on
    some, false on others). See `Fine1975.non_contradiction_superfalse`. -/
theorem kleene_cant_distinguish_contradiction :
    Truth3.meet .indet .indet =
    Truth3.meet .indet (Truth3.neg .indet) := by rfl

-- ════════════════════════════════════════════════════
-- § 4. Kamp → Klein Lineage
-- ════════════════════════════════════════════════════

/-! @cite{kamp-1975}'s definition (12) for the comparative:

    u₁ is at least as A as u₂ iff for every completion M' ∈ S where
    u₂ is in the extension of A, u₁ is also in the extension.

    @cite{klein-1980} rephrases this with comparison classes: u₁ is
    more A than u₂ iff there exists a comparison class C where u₁ is
    A-in-C but u₂ is not.

    These are contrapositives: Kamp's "∀ completions, u₂ ∈ ext → u₁ ∈ ext"
    is equivalent to Klein's "¬∃ completion where u₂ ∈ ext ∧ u₁ ∉ ext",
    and Klein's strict comparative adds the asymmetric witness. -/

/-- Kamp's definition (12): u₁ is at least as A as u₂ iff every context
    that puts u₂ in the extension also puts u₁ in the extension.
    Parameterized by a set of "completions" (Kamp) or "comparison classes"
    (Klein). -/
def kampAtLeastAs {E C : Type*} (ext : C → E → Bool) (u₁ u₂ : E) (S : Set C) : Prop :=
  ∀ c ∈ S, ext c u₂ = true → ext c u₁ = true

/-- Klein's strict comparative: there exists a context that separates
    the two entities. This is `Klein.comparativeSem` from
    `Degree/Frameworks/Klein.lean`. -/
def kleinMoreThan {E C : Type*} (ext : C → E → Bool) (u₁ u₂ : E) (S : Set C) : Prop :=
  ∃ c ∈ S, ext c u₁ = true ∧ ext c u₂ = false

/-- **Kamp–Klein bridge**: Klein's strict comparative is equivalent to
    Kamp's "at least as" in one direction but not the other. Precisely:
    `kleinMoreThan u₁ u₂` implies `¬kampAtLeastAs u₂ u₁` (if u₁ is
    strictly more A than u₂, then u₂ is NOT at least as A as u₁). -/
theorem klein_implies_not_kamp_reverse {E C : Type*}
    {ext : C → E → Bool} {u₁ u₂ : E} {S : Set C}
    (h : kleinMoreThan ext u₁ u₂ S) :
    ¬kampAtLeastAs ext u₂ u₁ S := by
  intro hk
  obtain ⟨c, hc, h₁, h₂⟩ := h
  have := hk c hc h₁
  simp_all

/-- Kamp's strict comparative (asymmetric part of "at least as")
    implies Klein's: if u₁ is at least as A as u₂ but not vice versa,
    then there exists a separating context. -/
theorem kamp_strict_implies_klein {E C : Type*}
    {ext : C → E → Bool} {u₁ u₂ : E} {S : Set C}
    (h_ge : kampAtLeastAs ext u₁ u₂ S)
    (h_not : ¬kampAtLeastAs ext u₂ u₁ S) :
    kleinMoreThan ext u₁ u₂ S := by
  unfold kampAtLeastAs at h_not
  push_neg at h_not
  obtain ⟨c, hc, h₁, h₂⟩ := h_not
  refine ⟨c, hc, h₁, ?_⟩
  cases hv : ext c u₂
  · rfl
  · exact absurd hv h₂

-- ════════════════════════════════════════════════════
-- § 5. Concrete Witnesses for Each Class
-- ════════════════════════════════════════════════════

/-! Each class in Kamp's hierarchy is non-empty. We construct explicit
    adjective denotations that provably satisfy each definition, modeling
    the classic examples: "gray" (predicative), "fake" (privative),
    "skillful" (affirmative but not extensional), and "alleged"
    (non-subsective/modal).

    These are the formal counterparts of the informal entailment judgments
    from the literature (e.g., "gray cat entails cat" ↔ `isAffirmativeK`,
    "skillful surgeon + violinist ⊬ skillful violinist" ↔ `¬isExtensionalK`).

    @cite{partee-2001} argues that the privative class should be eliminated
    in favor of subsective + noun coercion. The witness `fakeK` below
    models the traditional analysis; a `Partee2001.lean` study file could
    formalize the coercion alternative. -/

section Witnesses

/-- Two worlds suffice to distinguish extensional from non-extensional. -/
inductive W2 | w₁ | w₂

/-- Three entities suffice for all witness constructions. -/
inductive E3 | a | b | c

/-- **"gray"**: a predicative (intersective) adjective. The extension of
    "gray N" is `{x | gray(x)} ∩ {x | N(w)(x)}` — a fixed property
    independent of the noun.

    Models @cite{kamp-1975} definition (4). Entailment pattern:
    "gray cat" entails both "gray" and "cat"; "gray" + "cat" entails
    "gray cat". -/
def grayK : AdjMeaningK W2 E3 := λ N w x =>
  (match x with | .a => true | _ => false) && N w x

theorem gray_predicativeK : isPredicativeK grayK :=
  ⟨λ _ x => match x with | .a => true | _ => false,
   λ N w x => by cases x <;> simp [grayK]⟩

/-- "gray" is therefore also extensional and affirmative. -/
example : isExtensionalK grayK := predicativeK_implies_extensionalK gray_predicativeK
example : isAffirmativeK grayK := predicativeK_implies_affirmativeK gray_predicativeK

/-- **"fake"**: a privative adjective (traditional analysis). "Fake N"
    entities are never N.

    Models @cite{kamp-1975} definition (5). Entailment pattern:
    "fake gun" entails "not a gun".

    @cite{partee-2001} argues this class should be reanalyzed as
    subsective with noun coercion: "fake gun" ⊆ gun* where
    gun* = real guns ∪ fake guns. -/
def fakeK : AdjMeaningK W2 E3 := λ N w x =>
  (match x with | .b => true | _ => false) && !N w x

theorem fake_privativeK : isPrivativeK fakeK := by
  intro N w x h
  unfold fakeK at h
  cases x <;> simp_all

/-- **"skillful"**: an affirmative (subsective) adjective that is NOT
    extensional. Being a "skillful N" depends on N's intension — what
    counts as an N across worlds — not just who the N's are in this world.

    Models @cite{kamp-1975} definition (6) without definition (7).
    Entailment pattern: "skillful surgeon" entails "surgeon" (subsective),
    but "skillful surgeon" + "violinist" does not entail "skillful
    violinist" (not intersective, because not extensional). -/
def skillfulK : AdjMeaningK W2 E3 := λ N w x =>
  N w x && match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _ => false

theorem skillful_affirmativeK : isAffirmativeK skillfulK := by
  intro N w x h
  unfold skillfulK at h
  cases x <;> simp_all

theorem skillful_not_extensionalK : ¬isExtensionalK skillfulK := by
  intro hext
  -- N₁ and N₂ agree at w₂ but differ at w₁
  let N₁ : Property W2 E3 := λ _ _ => true
  let N₂ : Property W2 E3 := λ w x => match w, x with
    | .w₁, .a => false | _, _ => true
  have heq : ∀ x, N₁ .w₂ x = N₂ .w₂ x := by intro x; cases x <;> rfl
  have h := hext N₁ N₂ .w₂ heq .a
  -- skillfulK N₁ w₂ a = true (N₁ w₁ a = true)
  -- skillfulK N₂ w₂ a = false (N₂ w₁ a = false)
  have h₁ : skillfulK N₁ .w₂ .a = true := rfl
  have h₂ : skillfulK N₂ .w₂ .a = false := rfl
  rw [h₁, h₂] at h; cases h

/-- **"alleged"**: a non-subsective (modal) adjective. An "alleged N"
    may or may not be an N — the adjective creates an intensional context
    without entailing or anti-entailing the noun.

    This is the complement class in Kamp's hierarchy: adjectives like
    "alleged", "potential", "putative" that carry no meaning postulate
    constraining the relationship between the modified and unmodified
    extension. -/
def allegedK : AdjMeaningK W2 E3 := λ _N _ x =>
  match x with | .a => true | _ => false

/-- "alleged N" does not entail "N" (not affirmative). -/
theorem alleged_not_affirmativeK : ¬isAffirmativeK allegedK := by
  intro h
  have := h (λ _ _ => false) .w₁ .a rfl
  cases this

/-- "alleged N" does not entail "not N" (not privative). -/
theorem alleged_not_privativeK : ¬isPrivativeK allegedK := by
  intro h
  have := h (λ _ _ => true) .w₁ .a rfl
  cases this

end Witnesses

end Phenomena.Gradability.Studies.Kamp1975
