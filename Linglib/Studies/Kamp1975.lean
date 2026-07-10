import Linglib.Semantics.Modification.Adjective
import Linglib.Core.Logic.Truth3
import Mathlib.Data.Set.Basic

/-!
# Kamp (1975): Two Theories about Adjectives [kamp-1975]

In E. Keenan (ed.), *Formal Semantics of Natural Languages*, 123–155.
Cambridge University Press.

## Overview

Kamp presents two theories of adjective semantics:

**Theory 1 (§ 1–2)**: Adjectives as functions from properties to
properties (type `⟨⟨e,t⟩,⟨e,t⟩⟩`). The classification hierarchy —
intersective, subsective, privative, extensional — is formalized in
`Semantics/Gradability/Classification.lean`.

**Theory 2 (§ 3–7)**: Vague/graded models. Kamp introduces *vague
models* `⟨M, S, F, p⟩` (partial model + completions + σ-field +
probability measure) and derives the comparative from quantification
over completions. This framework is the common ancestor of both
[fine-1975]'s supervaluationism and [klein-1980]'s delineation
approach. Theory 2 is not formalized here; § 2 captures only the
motivating argument (why truth-functional many-valued logic fails)
and § 3 formalizes the comparative definitions that descend from it.

## Structure

- § 1: Single-world specialization of `Classification.lean`'s hierarchy
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

namespace Kamp1975

open Degree.Classification

/-! ### Bridge to single-world predicates

`Classification.lean` defines the general intensional hierarchy:
`isIntersective`, `isSubsective`, `isPrivative`, `isExtensional` over
`Property W E = W → E → Prop`. The bridge theorems below show that
fixing a world reduces the intensional definitions to their single-
world counterparts. -/

section Bridge

variable {W E : Type*}

/-- Single-world specialization: given a fixed world, the intensional
    hierarchy reduces to the extensional one.

    If `adj` is intersective, then at any fixed world `w`, the function
    `N ↦ adj N w` is intersective in the extensional sense: there
    exists a fixed predicate Q(w) such that the result is Q(w) ∩ N(w). -/
theorem intersective_at_world {adj : AdjMeaning W E}
    (h : isIntersective adj) (w : W) :
    ∃ (Q_w : E → Prop), ∀ (N : E → Prop) (x : E),
      adj (fun _ => N) w x ↔ (Q_w x ∧ N x) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, fun N x => hQ (fun _ => N) w x⟩

/-- Single-world specialization of subsective. -/
theorem subsective_at_world {adj : AdjMeaning W E}
    (h : isSubsective adj) (w : W) :
    ∀ (N : E → Prop) (x : E), adj (fun _ => N) w x → N x := by
  intro N x hadj
  exact h (fun _ => N) w x hadj

/-! `intersective_at_world` and `subsective_at_world` show that fixing
    a world reduces the intensional hierarchy to single-world
    predicates. -/

end Bridge

/-! ### Many-Valued Logic Failure -/

/-! [kamp-1975] (p. 233) argues that truth-functional many-valued
    logic cannot adequately handle vague connectives. The key
    observation:

    If `⟦φ⟧ = ½` (borderline), then `⟦¬φ⟧ = ½` (standard negation).
    We want `⟦φ ∧ ¬φ⟧ = 0` (contradictions are false). But any
    truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also gives
    `F(∧)(½, ½) = 0` for the non-contradictory `φ ∧ φ`, since the
    inputs are identical. This is wrong: `φ ∧ φ` should have the same
    value as `φ`.

    Strong Kleene logic (`⊓` on `Truth3`) makes the symmetric choice:
    `meet indet indet = indet`. This preserves `φ ∧ φ ≡ φ` but fails
    to make contradictions false. Supervaluationism resolves both. -/

open Trivalent (Truth3)

/-- **Kamp's dilemma**: no truth-functional binary operator can
    simultaneously be idempotent (`F(x,x) = x`) and make borderline
    contradictions false (`F(½, ¬½) = 0`).

    Since `¬½ = ½` in any symmetric three-valued logic, the two
    requirements conflict: idempotence demands `F(½,½) = ½`, but the
    contradiction requirement demands `F(½,½) = 0`. This is what
    motivates the move to supervaluation. -/
theorem kleene_dilemma :
    ¬∃ (meet : Truth3 → Truth3 → Truth3),
      (∀ x, meet x x = x) ∧
      (meet .indet (Truth3.neg .indet) = .false) := by
  intro ⟨meet, hidem, hcontra⟩
  have : Truth3.neg .indet = .indet := rfl
  rw [this] at hcontra
  have := hidem .indet
  rw [hcontra] at this
  cases this

/-! ### Kamp → Klein Lineage -/

/-! [kamp-1975]'s definition (12) for the comparative:

    u₁ is at least as A as u₂ iff for every completion M' ∈ S where
    u₂ is in the extension of A, u₁ is also in the extension.

    [klein-1980] rephrases this with comparison classes: u₁ is
    more A than u₂ iff there exists a comparison class C where u₁ is
    A-in-C but u₂ is not.

    These are contrapositives: Kamp's "∀ completions, u₂ ∈ ext → u₁ ∈ ext"
    is equivalent to Klein's "¬∃ completion where u₂ ∈ ext ∧ u₁ ∉ ext",
    and Klein's strict comparative adds the asymmetric witness. -/

/-- Kamp's definition (12) induces a `Preorder` on entities: `u₁ ≤ u₂`
    iff every completion in S that puts u₂ in the extension also puts
    u₁ in the extension.

    This is the S-restricted analogue of `kleinPreorder` from
    `Delineation.lean`. The extension parameter remains `Bool`-valued
    here because this section interfaces with vague-model
    extension-membership (different abstraction from the intensional
    adjective `Property` migrated above). -/
@[reducible] def kampPreorder {E C : Type*} (ext : C → E → Bool) (S : Set C) :
    Preorder E where
  le u₁ u₂ := ∀ c, c ∈ S → ext c u₂ = true → ext c u₁ = true
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hab hbc := fun c hc h => hab c hc (hbc c hc h)

/-- The Kamp preorder is `Antitone` in S: enlarging S (more completions
    to quantify over) makes `≤` harder to satisfy. -/
theorem kampPreorder_antitone {E C : Type*} (ext : C → E → Bool) (u₁ u₂ : E) :
    Antitone (fun S => (kampPreorder ext S).le u₁ u₂) :=
  fun _ _ hle hall c hc => hall c (hle hc)

/-! ### Concrete Witnesses for Each Class

Each class in the hierarchy is non-empty. We construct explicit
adjective denotations that provably satisfy each definition from
`Classification.lean`, modeling the classic examples: "gray"
(intersective), "fake" (privative), "skillful" (subsective but not
extensional), and "alleged" (non-subsective/modal).

These are the formal counterparts of the informal entailment judgments
from the literature (e.g., "gray cat entails cat" ↔ `isSubsective`,
"skillful surgeon + violinist ⊬ skillful violinist" ↔ `¬isExtensional`).

[partee-2010] argues that the privative class should be eliminated
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

    Models [kamp-1975] definition (4). Entailment pattern:
    "gray cat" entails both "gray" and "cat"; "gray" + "cat" entails
    "gray cat". -/
def grayAdj : AdjMeaning W2 E3 := fun N w x =>
  (match x with | .a => True | _ => False) ∧ N w x

theorem gray_intersective : isIntersective grayAdj :=
  ⟨fun _ x => match x with | .a => True | _ => False,
   fun N w x => by cases x <;> simp [grayAdj]⟩

/-- "gray" is therefore also extensional and subsective. -/
example : isExtensional grayAdj := intersective_implies_extensional gray_intersective
example : isSubsective grayAdj := intersective_implies_subsective gray_intersective

/-- **"fake"**: a privative adjective (traditional analysis). "Fake N"
    entities are never N.

    Models [kamp-1975] definition (5). Entailment pattern:
    "fake gun" entails "not a gun".

    [partee-2010] argues this class should be reanalyzed as
    subsective with noun coercion — see `Partee2010.lean`. -/
def fakeAdj : AdjMeaning W2 E3 := fun N w x =>
  (match x with | .b => True | _ => False) ∧ ¬ N w x

theorem fake_privative : isPrivative fakeAdj := by
  intro N w x h
  exact h.2

/-- **"skillful"**: a subsective adjective that is NOT extensional.
    Being a "skillful N" depends on N's intension — what counts as an N
    across worlds — not just who the N's are in this world.

    Models [kamp-1975] definition (6) without definition (7).
    Entailment pattern: "skillful surgeon" entails "surgeon" (subsective),
    but "skillful surgeon" + "violinist" does not entail "skillful
    violinist" (not intersective, because not extensional). -/
def skillfulAdj : AdjMeaning W2 E3 := fun N w x =>
  N w x ∧ match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _  => False

theorem skillful_subsective : isSubsective skillfulAdj := by
  intro N w x h
  exact h.1

theorem skillful_not_extensional : ¬ isExtensional skillfulAdj := by
  intro hext
  let N₁ : Property W2 E3 := fun _ _ => True
  let N₂ : Property W2 E3 := fun w x => match w, x with
    | .w₁, .a => False
    | _, _    => True
  have hagree : ∀ x, N₁ .w₂ x ↔ N₂ .w₂ x := fun x => by
    cases x <;> simp [N₁, N₂]
  have h := hext N₁ N₂ .w₂ hagree .a
  have hLHS : skillfulAdj N₁ .w₂ .a := ⟨trivial, trivial⟩
  exact (h.mp hLHS).2

/-- **"alleged"**: a non-subsective (modal) adjective. An "alleged N"
    may or may not be an N — the adjective creates an intensional
    context without entailing or anti-entailing the noun.

    This is the complement class in the hierarchy: adjectives like
    "alleged", "potential", "putative" that carry no meaning postulate
    constraining the relationship between the modified and unmodified
    extension. -/
def allegedAdj : AdjMeaning W2 E3 := fun _N _ x =>
  match x with | .a => True | _ => False

/-- "alleged N" does not entail "N" (not subsective). -/
theorem alleged_not_subsective : ¬ isSubsective allegedAdj := by
  intro h
  exact h (fun _ _ => False) .w₁ .a trivial

/-- "alleged N" does not entail "not N" (not privative). -/
theorem alleged_not_privative : ¬ isPrivative allegedAdj := by
  intro h
  exact h (fun _ _ => True) .w₁ .a trivial trivial

end Witnesses

end Kamp1975
