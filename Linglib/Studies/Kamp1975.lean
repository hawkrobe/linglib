import Linglib.Semantics.Modification.Classification
import Linglib.Core.Logic.Trivalent
import Mathlib.Data.Set.Basic

/-!
# Kamp (1975): Two Theories about Adjectives [kamp-1975]

In E. Keenan (ed.), *Formal Semantics of Natural Language*, 123–155.
Cambridge University Press.

## Overview

Kamp presents two theories of adjective semantics:

**Theory 1 (§ 1–2)**: Adjectives as functions from properties to
properties (type `⟨⟨e,t⟩,⟨e,t⟩⟩`). The classification hierarchy —
intersective, subsective, privative, extensional — is formalized in
`Modification/Basic.lean` (order-theoretic core) and
`Semantics/Modification/Classification.lean` (intensional carrier).

**Theory 2 (§ 3–7)**: Vague/graded models. Kamp introduces *vague
models* `⟨M, S, F, p⟩` (partial model + completions + σ-field +
probability measure) and derives the comparative from quantification
over completions. This framework is the common ancestor of both
[fine-1975]'s supervaluationism and [klein-1980]'s delineation
approach. Theory 2 is not formalized here; § 2 captures only the
motivating argument (why truth-functional many-valued logic fails)
and § 3 formalizes the comparative definitions that descend from it.

## Structure

- § 1: Single-world specialization of the `Modifier.is*` hierarchy
- § 2: Many-valued logic failure (motivation for Theory 2)
- § 3: Kamp → Klein lineage: `kampAtLeastAs` ↔ `kleinMoreThan`
- § 4: Concrete witnesses for each hierarchy class

## Key Insight

Kamp argues that truth-functional
many-valued logic *fails* for natural language connectives: if
`⟦φ⟧ = ½`, then `⟦φ ∧ ¬φ⟧` should be 0 (contradictions are false),
but any truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also
gives `F(∧)(½, ½) = 0` for non-contradictory `⟦φ ∧ φ⟧`. This
motivates the move to supervaluation / probability over completions.
-/

namespace Kamp1975

open Modification Modifier

/-! ### Bridge to single-world predicates

The classification (`Modifier.isIntersective`, `.isSubsective`, …) is
one order-theoretic definition instantiated at two carriers: the
intensional `Property W E = W → E → Prop` and the single-world
`E → Prop`. The bridge theorems below show that fixing a world sends
the first instance to the second. -/

section Bridge

variable {W E : Type*}

/-- Single-world specialization: given a fixed world, the intensional
    instance of `Modifier.isIntersective` reduces to the `E → Prop`
    instance on the rigidified single-world view `N ↦ adj (fun _ => N) w`. -/
theorem intersective_at_world {adj : Modifier (Property W E)}
    (h : isIntersective adj) (w : W) :
    isIntersective (fun N : E → Prop => adj (fun _ => N) w) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, fun N => congrFun (hQ fun _ => N) w⟩

/-- Single-world specialization of `Modifier.isSubsective`. -/
theorem subsective_at_world {adj : Modifier (Property W E)}
    (h : isSubsective adj) (w : W) :
    isSubsective (fun N : E → Prop => adj (fun _ => N) w) :=
  fun N => h (fun _ => N) w

/-! `intersective_at_world` and `subsective_at_world` show that fixing
    a world sends the intensional instance of the hierarchy to the
    single-world instance — the same classes, one definition. -/

end Bridge

/-! ### Many-Valued Logic Failure -/

/-! [kamp-1975] argues that truth-functional many-valued
    logic cannot adequately handle vague connectives. The key
    observation:

    If `⟦φ⟧ = ½` (borderline), then `⟦¬φ⟧ = ½` (standard negation).
    We want `⟦φ ∧ ¬φ⟧ = 0` (contradictions are false). But any
    truth-functional `F(∧)` satisfying `F(∧)(½, ½) = 0` also gives
    `F(∧)(½, ½) = 0` for the non-contradictory `φ ∧ φ`, since the
    inputs are identical. This is wrong: `φ ∧ φ` should have the same
    value as `φ`.

    Strong Kleene logic (`⊓` on `Trivalent`) makes the symmetric choice:
    `meet indet indet = indet`. This preserves `φ ∧ φ ≡ φ` but fails
    to make contradictions false. Supervaluationism resolves both. -/


/-- **Kamp's dilemma**: no truth-functional binary operator can
    simultaneously be idempotent (`F(x,x) = x`) and make borderline
    contradictions false (`F(½, ¬½) = 0`).

    Since `¬½ = ½` in any symmetric three-valued logic, the two
    requirements conflict: idempotence demands `F(½,½) = ½`, but the
    contradiction requirement demands `F(½,½) = 0`. This is what
    motivates the move to supervaluation. -/
theorem kleene_dilemma :
    ¬∃ (meet : Trivalent → Trivalent → Trivalent),
      (∀ x, meet x x = x) ∧
      (meet .indet (Trivalent.neg .indet) = .false) := by
  intro ⟨meet, hidem, hcontra⟩
  have : Trivalent.neg .indet = .indet := rfl
  rw [this] at hcontra
  have := hidem .indet
  rw [hcontra] at this
  cases this

/-! ### Kamp → Klein Lineage -/

/-! [kamp-1975]'s completion-based comparative, definition (12):

    u₁ is at least as A as u₂ iff for every completion M' ∈ S where
    u₂ is in the extension of A, u₁ is also in the extension.

    [klein-1980] rephrases this with comparison classes: u₁ is
    more A than u₂ iff there exists a comparison class C where u₁ is
    A-in-C but u₂ is not.

    These are contrapositives: Kamp's "∀ completions, u₂ ∈ ext → u₁ ∈ ext"
    is equivalent to Klein's "¬∃ completion where u₂ ∈ ext ∧ u₁ ∉ ext",
    and Klein's strict comparative adds the asymmetric witness. -/

/-- Kamp's completion-based comparative (definition (12)) induces a
    `Preorder` on entities: `u₁ ≤ u₂` iff every completion in S that puts
    u₂ in the extension also puts u₁ in the extension. Kamp notes (12) is
    "precisely the proposal … in Lewis (1970), where it is attributed to
    David Kaplan".

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

    Models [kamp-1975] definition (4), his "predicative" class (the
    modern *intersective*). Entailment pattern:
    "gray cat" entails both "gray" and "cat"; "gray" + "cat" entails
    "gray cat". -/
def grayAdj : Modifier (Property W2 E3) := fun N w x =>
  (match x with | .a => True | _ => False) ∧ N w x

theorem gray_intersective : isIntersective grayAdj :=
  isIntersective_iff.mpr
    ⟨fun _ x => match x with | .a => True | _ => False,
     fun N w x => by cases x <;> simp [grayAdj]⟩

/-- "gray" is therefore also extensional and subsective. -/
example : Intensional.IsExtensional grayAdj :=
  isExtensional_of_isIntersective gray_intersective
example : isSubsective grayAdj := gray_intersective.isSubsective

/-- **"fake"**: a privative adjective (traditional analysis). "Fake N"
    entities are never N.

    Models [kamp-1975] definition (5); *fake* and *false* are Kamp's
    examples. Entailment pattern: "fake gun" entails "not a gun".

    Kamp himself doubts "that there is any English adjective which is
    privative (in the precise sense here defined) in all of its possible
    uses" — anticipating [partee-2010]'s reanalysis of the class as
    subsective with noun coercion; see `Partee2010.lean`. -/
def fakeAdj : Modifier (Property W2 E3) := fun N w x =>
  (match x with | .b => True | _ => False) ∧ ¬ N w x

theorem fake_privative : isPrivative fakeAdj :=
  isPrivative_iff.mpr fun _ _ _ h => h.2

/-- **"skillful"**: a subsective adjective that is NOT extensional.
    Being a "skillful N" depends on N's intension — what counts as an N
    across worlds — not just who the N's are in this world.

    Models [kamp-1975] definition (6), his "affirmative" class (the
    modern *subsective*), without definition (7); *skilful* is Kamp's own
    non-extensional example.
    Entailment pattern: "skillful surgeon" entails "surgeon" (subsective),
    but "skillful surgeon" + "violinist" does not entail "skillful
    violinist" (not intersective, because not extensional). -/
def skillfulAdj : Modifier (Property W2 E3) := fun N w x =>
  N w x ∧ match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _  => False

theorem skillful_subsective : isSubsective skillfulAdj :=
  fun _ _ _ h => h.1

theorem skillful_not_extensional : ¬ Intensional.IsExtensional skillfulAdj := by
  intro hext
  let N₁ : Property W2 E3 := fun _ _ => True
  let N₂ : Property W2 E3 := fun w x => match w, x with
    | .w₁, .a => False
    | _, _    => True
  have hagree : N₁ .w₂ = N₂ .w₂ := by
    funext x; cases x <;> simp [N₁, N₂]
  have h := hext .w₂ N₁ N₂ hagree
  have hLHS : skillfulAdj N₁ .w₂ .a := ⟨trivial, trivial⟩
  exact (congrFun h .a ▸ hLHS).2

/-- **"alleged"**: a non-subsective (modal) adjective — [kamp-1975]'s
    opening example (1), "Every alleged thief is a thief". An "alleged N"
    may or may not be an N — the adjective creates an intensional
    context without entailing or anti-entailing the noun.

    This is the complement class in the hierarchy: adjectives like
    "alleged", "potential", "putative" that carry no meaning postulate
    constraining the relationship between the modified and unmodified
    extension. -/
def allegedAdj : Modifier (Property W2 E3) := fun _N _ x =>
  match x with | .a => True | _ => False

/-- "alleged" ignores the noun entirely, so it is trivially extensional —
    with `skillful_not_extensional` and `skillful_subsective`, this
    witnesses that extensionality is orthogonal to subsectivity. -/
theorem alleged_extensional : Intensional.IsExtensional allegedAdj :=
  fun _ _ _ _ => rfl

/-- "alleged N" does not entail "N" (not subsective). -/
theorem alleged_not_subsective : ¬ isSubsective allegedAdj := by
  intro h
  exact h (fun _ _ => False) .w₁ .a trivial

/-- "alleged N" does not entail "not N" (not privative). -/
theorem alleged_not_privative : ¬ isPrivative allegedAdj := by
  intro h
  exact isPrivative_iff.mp h (fun _ _ => True) .w₁ .a trivial trivial

end Witnesses

end Kamp1975
