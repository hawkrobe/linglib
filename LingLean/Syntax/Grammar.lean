/-
# LingLean.Syntax.Grammar

Abstract grammar interface that all syntactic frameworks implement.
-/

import LingLean.Syntax.Basic

-- ============================================================================
-- Grammar Typeclass
-- ============================================================================

/--
A Grammar assigns derivations to strings.
Different frameworks implement this differently.
The key is that derivations are *proof objects*, not just yes/no.
-/
class Grammar (G : Type) where
  /-- The type of derivations/analyses this grammar produces -/
  Derivation : Type
  /-- Whether a derivation yields a given string with given clause type -/
  realizes : Derivation → List Word → ClauseType → Prop
  /-- Whether the grammar can produce *some* derivation for a string -/
  derives : G → List Word → ClauseType → Prop

-- ============================================================================
-- Framework-Neutral Theorems
-- ============================================================================

/--
If two grammars both derive the same string, they agree on that string.
(Trivial, but illustrates the kind of metatheorem we want.)
-/
theorem derives_agreement
    {G₁ G₂ : Type} [Grammar G₁] [Grammar G₂]
    (g₁ : G₁) (g₂ : G₂) (ws : List Word) (ct : ClauseType)
    (h₁ : Grammar.derives g₁ ws ct)
    (h₂ : Grammar.derives g₂ ws ct) :
    Grammar.derives g₁ ws ct ∧ Grammar.derives g₂ ws ct :=
  ⟨h₁, h₂⟩
