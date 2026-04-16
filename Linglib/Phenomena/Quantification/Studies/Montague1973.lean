/-
# The Proper Treatment of Quantification in Ordinary English (PTQ)

Formalization of @cite{montague-1973}, the foundational paper establishing
the homomorphism between natural language syntax and model-theoretic semantics.

## Innovations

1. Intensions: Type `s` for possible worlds, `s ⇒ a` for intensions of type `a`
2. Category-type correspondence: Syntactic categories map to semantic types
3. Quantifying-in (S14/T14): Derives scope ambiguity compositionally
4. The homomorphism: Syntax-semantics mapping is structure-preserving

## Note on Types

This module uses the canonical `Semantics.Montague.Ty` type system. Intensions are
represented as `s ⇒ τ` rather than a separate `intens` constructor.

-/

import Linglib.Core.IntensionalLogic.Frame
import Mathlib.Data.Set.Basic

namespace Montague1973

open Core.IntensionalLogic

-- Section 1: Types (IL - Intensional Logic)

/-!
Types of Intensional Logic (Definition 1)

The set of types is the smallest set Y such that:
- e ∈ Y (entities)
- t ∈ Y (truth values)
- If a, b ∈ Y then ⟨a, b⟩ ∈ Y (functions)
- If a ∈ Y then ⟨s, a⟩ ∈ Y (intensions)

We use the canonical `Semantics.Montague.Ty` which has:
- `.e` : entities
- `.t` : truth values
- `.intens a` : intensions ⟨s, a⟩
- `.fn` / `⇒` : function types
-/

-- Notation for PTQ-style types
notation "𝐞" => Ty.e
notation "𝐭" => Ty.t
notation "⦃" a ", " b "⦄" => Ty.fn a b  -- ⟨a, b⟩
notation "⦃𝐬, " a "⦄" => Ty.intens a   -- ⟨s, a⟩

/-- Common derived types -/
abbrev Ty.ptq_et := ⦃𝐞, 𝐭⦄                    -- Properties: e → t
abbrev Ty.ptq_eet := ⦃𝐞, ⦃𝐞, 𝐭⦄⦄              -- Relations: e → e → t
abbrev Ty.ptq_ett := ⦃⦃𝐞, 𝐭⦄, 𝐭⦄              -- Generalized quantifiers: (e → t) → t
abbrev Ty.setIntens := ⦃⦃𝐬, ⦃𝐞, 𝐭⦄⦄, 𝐭⦄       -- Sets of property intensions

-- Section 2: Syntactic Categories (Definition 3)

/--
Syntactic Categories

Basic categories: t (sentences), e (entity-denoting), CN (common nouns), IV (intransitive verbs)
Derived categories: A/B and A//B (slash categories)

The double slash // is for "intensional" arguments (take intensions).
-/
inductive Cat where
  | t : Cat           -- Sentences
  | e : Cat           -- Entity expressions (names, pronouns)
  | CN : Cat          -- Common nouns
  | IV : Cat          -- Intransitive verb phrases (= t/e in the paper)
  | TV : Cat          -- Transitive verbs (= IV/T in the paper)
  | T : Cat           -- Term phrases (= t/IV, generalized quantifiers)
  | rslash : Cat → Cat → Cat    -- A/B: combines with B on right to form A
  | lslash : Cat → Cat → Cat    -- A\B: combines with B on left to form A
  | rslashI : Cat → Cat → Cat   -- A//B: intensional right argument
  deriving DecidableEq, Repr

notation A " /' " B => Cat.rslash A B
notation A " \\' " B => Cat.lslash A B
notation A " //' " B => Cat.rslashI A B

-- Section 3: Category-Type Correspondence (Definition 4)

/--
The function f from categories to types.

This is the core of the syntax-semantics interface.
Each syntactic category corresponds to a semantic type.

Key mappings:
- f(e) = e
- f(t) = t
- f(CN) = f(IV) = ⟨s, ⟨e, t⟩⟩ (intensions of properties)
- f(T) = ⟨⟨s, ⟨e, t⟩⟩, t⟩ (generalized quantifiers over property intensions)
- f(A/B) = ⟨⟨s, f(B)⟩, f(A)⟩ (functions from intensions of B to A)
-/
def catToTy : Cat → Ty
  | .e => 𝐞
  | .t => 𝐭
  | .CN => ⦃𝐬, ⦃𝐞, 𝐭⦄⦄           -- Property intensions
  | .IV => ⦃𝐬, ⦃𝐞, 𝐭⦄⦄           -- Same as CN (intransitive VPs)
  | .TV => ⦃⦃𝐬, Ty.ptq_ett⦄, ⦃𝐬, ⦃𝐞, 𝐭⦄⦄⦄  -- Takes term intension, returns IV
  | .T => ⦃⦃𝐬, ⦃𝐞, 𝐭⦄⦄, 𝐭⦄       -- Generalized quantifiers
  | .rslash a b => ⦃⦃𝐬, catToTy b⦄, catToTy a⦄
  | .lslash a b => ⦃⦃𝐬, catToTy b⦄, catToTy a⦄
  | .rslashI a b => ⦃⦃𝐬, catToTy b⦄, catToTy a⦄

/--
Term phrases (T) denote generalized quantifiers.

"Every man" doesn't denote an entity; it denotes a function that takes
a property (intension) and returns true iff every man has that property.
-/
theorem term_phrase_is_gq : catToTy .T = ⦃⦃𝐬, ⦃𝐞, 𝐭⦄⦄, 𝐭⦄ := rfl

-- Section 4: Frame Structure

/--
Intensional Frame

A PTQ model uses the canonical `Semantics.Montague.Frame` which includes:
- `Entity` : domain of entities
- `Index` : possible worlds (indices)
-/
abbrev PTQModel := Frame

/-- Denotation of a type in a frame (uses canonical Denot) -/
abbrev PTQModel.Den (F : PTQModel) (τ : Ty) := F.Denot τ

/-- Intension: function from indices to extensions -/
abbrev PTQModel.Intens (F : PTQModel) (a : Ty) := F.Index → F.Denot a

-- Section 5: Lexical Entries and Translations

/--
Lexical Entry Structure

Each word has:
- Surface form
- Syntactic category
- Translation (semantic representation)
-/
structure LexEntry (F : PTQModel) where
  form : String
  cat : Cat
  -- The translation would be a term of type F.Denot (catToTy cat)

/-
Basic Expressions (BₐC for each category C)

Examples from PTQ:
- Bₐₑ = {John, Mary, Bill,...} (proper names)
- BₐCN = {man, woman, fish, pen, unicorn,...} (common nouns)
- BₐIV = {walk, talk, run,...} (intransitive verbs)
- BₐTV = {love, find, seek,...} (transitive verbs)
-/

-- Section 6: Syntactic Rules (S1-S17)

/--
Syntactic Rule

A rule specifies:
- Input categories
- Output category
- How to combine the strings (F function)
-/
inductive SynRule where
  | S1 : SynRule   -- Basic CN from BₐCN
  | S2 : SynRule   -- CN → T: "every CN", "a CN", "the CN"
  | S3 : SynRule   -- Proper name → T
  | S4 : SynRule   -- T + IV → t (subject-predicate)
  | S5 : SynRule   -- TV + T → IV (transitive verb + object)
  | S14 : Nat → SynRule  -- Quantifying-in: substitute T for heₙ in φ
  deriving DecidableEq, Repr

/-
S4: Subject-Predicate Rule

If α ∈ P_T and δ ∈ P_IV, then F₄(α, δ) ∈ P_t

"every man walks" = F₄("every man", "walks")
-/

/-
S14: Quantifying-In

If α ∈ P_T and φ ∈ P_t, then F₁₀,ₙ(α, φ) ∈ P_t

This rule substitutes α for the pronoun heₙ in φ, with proper
agreement adjustments. It's the source of scope ambiguity.

Example: "Every man loves a woman"
- Can be derived with "every man" quantified in first (∀ > ∃)
- Or with "a woman" quantified in first (∃ > ∀)
-/

-- Section 7: Translation Rules (T1-T17) - The Homomorphism

/--
Translation Rule

Maps syntactic derivations to semantic representations.
This is the homomorphism: h : Syntax → Semantics
-/
inductive TransRule where
  | T1 : TransRule   -- CN translation
  | T2 : TransRule   -- "every α" → λP.∀x[α'(x) → P(x)]
  | T3 : TransRule   -- Proper name → λP.P(j) where j is the individual
  | T4 : TransRule   -- F₄(α, δ) → α'(^δ')
  | T5 : TransRule   -- F₅(δ, α) → δ'(^α')
  | T14 : Nat → TransRule  -- F₁₀,ₙ(α, φ) → α'(^λxₙ.φ')
  deriving DecidableEq, Repr

/-
T2: Determiner Translations

- "every α" translates to: λP.∀x[α'(x) → ˇP(x)]
- "a α" / "an α" translates to: λP.∃x[α'(x) ∧ ˇP(x)]
- "the α" translates to: λP.∃y[∀x[α'(x) ↔ x = y] ∧ ˇP(y)]

Where:
- ^P is the intension of P (λi.P)
- ˇP is the extension of P at current world (P(i))
-/

/-
T4: Subject-Predicate Translation

If α translates to α' and δ translates to δ', then
F₄(α, δ) translates to α'(^δ')

"Every man walks" → every_man'(^walk')
                  → (λP.∀x[man'(x) → ˇP(x)])(^walk')
                  → ∀x[man'(x) → walk'(x)]
-/

/-
T14: Quantifying-In Translation

If α translates to α' and φ translates to φ', then
F₁₀,ₙ(α, φ) translates to α'(^λxₙ.φ')

This abstracts over the position of heₙ in φ and applies α' to
the resulting property intension.
-/

-- Section 8: Scope Ambiguity via Quantifying-In

/--
Scope Reading

Represents different scope orderings of quantifiers.
-/
inductive ScopeReading where
  | surface : ScopeReading   -- First quantifier has wide scope
  | inverse : ScopeReading   -- Second quantifier has wide scope
  deriving DecidableEq, Repr

/-
"Every man loves a woman" - Two Derivations

Derivation 1 (∀ > ∃): Surface scope
1. "he₁ loves a woman" (S5)
2. "every man loves a woman" by quantifying-in "every man" for he₁ (S14,1)
→ ∀x[man(x) → ∃y[woman(y) ∧ love(x,y)]]
  "For every man, there is some woman he loves" (possibly different women)

Derivation 2 (∃ > ∀): Inverse scope
1. "he₁ loves he₂" (S5 with pronoun object)
2. "he₁ loves a woman" by quantifying-in "a woman" for he₂ (S14,2)
3. "every man loves a woman" by quantifying-in "every man" for he₁ (S14,1)
→ ∃y[woman(y) ∧ ∀x[man(x) → love(x,y)]]
  "There is a woman that every man loves" (the same woman)
-/

/--
A toy model for demonstrating scope ambiguity.

Two men (m1, m2), two women (w1, w2).
-/
inductive ToyEntity where
  | m1 | m2 | w1 | w2
  deriving DecidableEq, Repr

def toyPTQModel : PTQModel where
  Entity := ToyEntity
  Index := Unit  -- Single index for simplicity

/-- Predicate: is a man -/
def isMan : ToyEntity → Bool
  | .m1 | .m2 => true
  | _ => false

/-- Predicate: is a woman -/
def isWoman : ToyEntity → Bool
  | .w1 | .w2 => true
  | _ => false

/-- All entities -/
def allEntities : List ToyEntity := [.m1, .m2, .w1, .w2]

/--
Love relation for surface scope scenario.

m1 loves w1, m2 loves w2 (different women)
-/
def loveSurface : ToyEntity → ToyEntity → Bool
  | .m1, .w1 => true
  | .m2, .w2 => true
  | _, _ => false

/--
Love relation for inverse scope scenario.

m1 loves w1, m2 loves w1 (same woman)
-/
def loveInverse : ToyEntity → ToyEntity → Bool
  | .m1, .w1 => true
  | .m2, .w1 => true
  | _, _ => false

/--
Surface scope reading: ∀x[man(x) → ∃y[woman(y) ∧ love(x,y)]]

"For every man, there exists a woman that he loves."
-/
def surfaceScopeTrue (love : ToyEntity → ToyEntity → Bool) : Bool :=
  allEntities.filter isMan |>.all λ x =>
    allEntities.filter isWoman |>.any λ y => love x y

/--
Inverse scope reading: ∃y[woman(y) ∧ ∀x[man(x) → love(x,y)]]

"There exists a woman such that every man loves her."
-/
def inverseScopeTrue (love : ToyEntity → ToyEntity → Bool) : Bool :=
  allEntities.filter isWoman |>.any λ y =>
    allEntities.filter isMan |>.all λ x => love x y

-- Section 9: Key Theorems

/--
Surface scope is true in surface scenario.

When each man loves a different woman, surface scope is satisfied.
-/
theorem surface_scope_surface_scenario :
    surfaceScopeTrue loveSurface = true := by native_decide

/--
Inverse scope is false in surface scenario.

No single woman is loved by all men.
-/
theorem inverse_scope_surface_scenario :
    inverseScopeTrue loveSurface = false := by native_decide

/--
Both scopes are true in inverse scenario.

When all men love the same woman, both readings are true.
-/
theorem surface_scope_inverse_scenario :
    surfaceScopeTrue loveInverse = true := by native_decide

theorem inverse_scope_inverse_scenario :
    inverseScopeTrue loveInverse = true := by native_decide

/--
Scope ambiguity theorem.

The two readings are not equivalent - they differ in the surface scenario.
This is why "Every man loves a woman" is ambiguous.
-/
theorem scope_readings_differ :
    surfaceScopeTrue loveSurface ≠ inverseScopeTrue loveSurface := by
  native_decide

/--
Inverse scope entails surface scope.

∃y∀x.R(x,y) → ∀x∃y.R(x,y)

If there's one woman everyone loves, then certainly each man loves some woman.
-/
theorem inverse_entails_surface (love : ToyEntity → ToyEntity → Bool) :
    inverseScopeTrue love = true → surfaceScopeTrue love = true := by
  intro h
  -- If there exists a woman all men love, then each man loves that woman
  simp only [inverseScopeTrue, surfaceScopeTrue] at *
  simp only [List.all_eq_true, List.any_eq_true, List.filter_filter,
             Bool.and_eq_true, decide_eq_true_eq] at *
  intro x hx
  obtain ⟨y, ⟨hy, hall⟩⟩ := h
  exact ⟨y, hy, hall x hx⟩

-- Section 10: The Homomorphism Property

/-
The fundamental insight of PTQ.

The translation h from syntax to semantics is a homomorphism:
it preserves structure.

For each syntactic rule Sₙ: A × B → C with operation Fₙ,
there is a semantic rule Tₙ: Den(A) × Den(B) → Den(C) with operation Gₙ,
such that:

    h(Fₙ(α, β)) = Gₙ(h(α), h(β))

This means:
- Parse the sentence (apply syntax rules)
- Translate each step (apply corresponding semantic rules)
- The final translation gives the sentence's meaning

This is the "proper treatment": quantifier scope is handled by
the grammar itself (via S14 quantifying-in), not by post-hoc
scope-assignment rules.
-/

/--
Derivation Tree

Represents a syntactic derivation with rule applications.
-/
inductive Derivation where
  | lex : String → Cat → Derivation
  | apply : SynRule → Derivation → Derivation → Derivation
  | quantIn : Nat → Derivation → Derivation → Derivation  -- S14,n
  deriving Repr

/--
Derived category of a derivation.
-/
def Derivation.cat : Derivation → Cat
  | .lex _ c => c
  | .apply r _ _ =>
      match r with
      | .S4 => .t
      | .S5 => .IV
      | _ => .t  -- simplified
  | .quantIn _ _ _ => .t


end Montague1973
