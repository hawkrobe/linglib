import Linglib.Core.Basic

/-!
# Grammar

Abstract grammar interface that all syntactic frameworks implement.
-/

/-- A Grammar assigns derivations to strings. Derivations are proof objects. -/
class Grammar (G : Type) where
  /-- The type of derivations/analyses this grammar produces -/
  Derivation : Type
  /-- Whether a derivation yields a given string with given clause type -/
  realizes : Derivation → List Word → ClauseType → Prop
  /-- Whether the grammar can produce *some* derivation for a string -/
  derives : G → List Word → ClauseType → Prop

/-- If two grammars both derive the same string, they agree on that string. -/
theorem derives_agreement
    {G₁ G₂ : Type} [Grammar G₁] [Grammar G₂]
    (g₁ : G₁) (g₂ : G₂) (ws : List Word) (ct : ClauseType)
    (h₁ : Grammar.derives g₁ ws ct)
    (h₂ : Grammar.derives g₂ ws ct) :
    Grammar.derives g₁ ws ct ∧ Grammar.derives g₂ ws ct :=
  ⟨h₁, h₂⟩
