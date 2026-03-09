import Linglib.Theories.Semantics.Lexical.Adjective.Classification
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
properties (type `⟨⟨e,t⟩,⟨e,t⟩⟩`). The classification hierarchy —
intersective, subsective, privative, extensional — is formalized in
`Theories/Semantics/Lexical/Adjective/Classification.lean`.

**Theory 2 (§ 3–7)**: Vague/graded models. The positive form of a
gradable adjective is vague — its extension is partial. Kamp introduces
*vague models* `⟨M, S, F, p⟩` (partial model + completions + σ-field +
probability measure) and derives the comparative from quantification
over completions. This framework is the common ancestor of both
@cite{fine-1975}'s supervaluationism and @cite{klein-1980}'s delineation
approach.

## Structure

- § 1: Bridge to `Modification.lean`'s extensional hierarchy
- § 2: Many-valued logic failure (motivation for Theory 2)
- § 3: Kamp → Klein lineage: `kampAtLeastAs` ↔ `kleinMoreThan`
- § 4: Concrete witnesses for each hierarchy class

## Key Insight

Kamp argues (p. 233 of the Brill reprint) that truth-functional
many-valued logic *fails* for natural language connectives: if
`⟦φ⟧ = ½`, then `⟦φ ∧ ¬φ⟧` should be 0 (contradictions are false),
but any truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also
gives `F(∧)(½, ½) = 0` for non-contradictory `⟦φ ∧ φ⟧`. This
motivates the move to supervaluation / probability over completions.
-/

namespace Phenomena.Gradability.Studies.Kamp1975

open Semantics.Lexical.Adjective.Classification

-- ════════════════════════════════════════════════════
-- § 1. Bridge to Modification.lean
-- ════════════════════════════════════════════════════

/-! `Modification.lean` defines `isIntersective` and `isSubsective` in a
    single-world extensional setting (using `Model`). These are Kamp's
    definitions (4) and (6) specialized to a single world.

    The general intensional hierarchy lives in `Classification.lean`. -/

section Bridge

variable {W E : Type*}

/-- Single-world specialization: given a fixed world, the intensional
    hierarchy reduces to the extensional one.

    If `adj` is intersective, then at any fixed world `w`, the function
    `N ↦ adj N w` is intersective in the sense of `Modification.lean`
    (there exists a fixed predicate Q(w) such that the result is
    Q(w) ∩ N(w)). -/
theorem intersective_at_world {adj : AdjMeaning W E}
    (h : isIntersective adj) (w : W) :
    ∃ (Q_w : E → Bool), ∀ (N : E → Bool) (x : E),
      adj (λ _ => N) w x = (Q_w x && N x) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, λ N x => hQ (λ _ => N) w x⟩

/-- Single-world specialization of subsective. -/
theorem subsective_at_world {adj : AdjMeaning W E}
    (h : isSubsective adj) (w : W) :
    ∀ (N : E → Bool) (x : E),
      adj (λ _ => N) w x = true → N x = true := by
  intro N x hadj
  exact h (λ _ => N) w x hadj

end Bridge

-- ════════════════════════════════════════════════════
-- § 2. Many-Valued Logic Failure
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
-- § 3. Kamp → Klein Lineage
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
    (_h_ge : kampAtLeastAs ext u₁ u₂ S)
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
-- § 4. Concrete Witnesses for Each Class
-- ════════════════════════════════════════════════════

/-! Each class in the hierarchy is non-empty. We construct explicit
    adjective denotations that provably satisfy each definition from
    `Classification.lean`, modeling the classic examples: "gray"
    (intersective), "fake" (privative), "skillful" (subsective but not
    extensional), and "alleged" (non-subsective/modal).

    These are the formal counterparts of the informal entailment judgments
    from the literature (e.g., "gray cat entails cat" ↔ `isSubsective`,
    "skillful surgeon + violinist ⊬ skillful violinist" ↔ `¬isExtensional`).

    @cite{partee-2010} argues that the privative class should be eliminated
    in favor of subsective + noun coercion. The witness `fakeAdj` below
    models the traditional analysis; see `Partee2010.lean` for the
    coercion reanalysis. -/

section Witnesses

/-- Two worlds suffice to distinguish extensional from non-extensional. -/
inductive W2 | w₁ | w₂

/-- Three entities suffice for all witness constructions. -/
inductive E3 | a | b | c

/-- **"gray"**: an intersective adjective. The extension of "gray N" is
    `{x | gray(x)} ∩ {x | N(w)(x)}` — a fixed property independent of
    the noun.

    Models @cite{kamp-1975} definition (4). Entailment pattern:
    "gray cat" entails both "gray" and "cat"; "gray" + "cat" entails
    "gray cat". -/
def grayAdj : AdjMeaning W2 E3 := λ N w x =>
  (match x with | .a => true | _ => false) && N w x

theorem gray_intersective : isIntersective grayAdj :=
  ⟨λ _ x => match x with | .a => true | _ => false,
   λ N w x => by cases x <;> simp [grayAdj]⟩

/-- "gray" is therefore also extensional and subsective. -/
example : isExtensional grayAdj := intersective_implies_extensional gray_intersective
example : isSubsective grayAdj := intersective_implies_subsective gray_intersective

/-- **"fake"**: a privative adjective (traditional analysis). "Fake N"
    entities are never N.

    Models @cite{kamp-1975} definition (5). Entailment pattern:
    "fake gun" entails "not a gun".

    @cite{partee-2010} argues this class should be reanalyzed as
    subsective with noun coercion — see `Partee2010.lean`. -/
def fakeAdj : AdjMeaning W2 E3 := λ N w x =>
  (match x with | .b => true | _ => false) && !N w x

theorem fake_privative : isPrivative fakeAdj := by
  intro N w x h
  unfold fakeAdj at h
  cases x <;> simp_all

/-- **"skillful"**: a subsective adjective that is NOT extensional.
    Being a "skillful N" depends on N's intension — what counts as an N
    across worlds — not just who the N's are in this world.

    Models @cite{kamp-1975} definition (6) without definition (7).
    Entailment pattern: "skillful surgeon" entails "surgeon" (subsective),
    but "skillful surgeon" + "violinist" does not entail "skillful
    violinist" (not intersective, because not extensional). -/
def skillfulAdj : AdjMeaning W2 E3 := λ N w x =>
  N w x && match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _ => false

theorem skillful_subsective : isSubsective skillfulAdj := by
  intro N w x h
  unfold skillfulAdj at h
  cases x <;> simp_all

theorem skillful_not_extensional : ¬isExtensional skillfulAdj := by
  intro hext
  let N₁ : Property W2 E3 := λ _ _ => true
  let N₂ : Property W2 E3 := λ w x => match w, x with
    | .w₁, .a => false | _, _ => true
  have heq : ∀ x, N₁ .w₂ x = N₂ .w₂ x := by intro x; cases x <;> rfl
  have h := hext N₁ N₂ .w₂ heq .a
  have h₁ : skillfulAdj N₁ .w₂ .a = true := rfl
  have h₂ : skillfulAdj N₂ .w₂ .a = false := rfl
  rw [h₁, h₂] at h; cases h

/-- **"alleged"**: a non-subsective (modal) adjective. An "alleged N"
    may or may not be an N — the adjective creates an intensional context
    without entailing or anti-entailing the noun.

    This is the complement class in the hierarchy: adjectives like
    "alleged", "potential", "putative" that carry no meaning postulate
    constraining the relationship between the modified and unmodified
    extension. -/
def allegedAdj : AdjMeaning W2 E3 := λ _N _ x =>
  match x with | .a => true | _ => false

/-- "alleged N" does not entail "N" (not subsective). -/
theorem alleged_not_subsective : ¬isSubsective allegedAdj := by
  intro h
  have := h (λ _ _ => false) .w₁ .a rfl
  cases this

/-- "alleged N" does not entail "not N" (not privative). -/
theorem alleged_not_privative : ¬isPrivative allegedAdj := by
  intro h
  have := h (λ _ _ => true) .w₁ .a rfl
  cases this

end Witnesses

end Phenomena.Gradability.Studies.Kamp1975
