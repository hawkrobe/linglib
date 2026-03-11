/-!
# Closure Properties of Formal Language Classes

Vocabulary for formal languages and string homomorphisms, plus the closure
properties of context-free languages.

## CFL Closure Properties

Context-free languages are closed under string homomorphisms and under
intersection with regular languages (Hopcroft & Ullman 1979, pp. 130–135).

@cite{shieber-1985}'s proof uses the contrapositive: if applying a
homomorphism f to a language L and intersecting with a regular language r
produces a non-context-free result, then L is not context-free.
-/

/-- A formal language over alphabet α: a decidable predicate on strings. -/
abbrev Language (α : Type) := List α → Bool

/-- A string homomorphism: maps each source symbol to a target string.
    Extends to strings by concatenation: h(ε) = ε, h(a·w) = h(a) ++ h(w). -/
abbrev StringHom (α β : Type) := α → List β

/-- Apply a string homomorphism to a string. -/
def StringHom.applyTo {α β : Type} (h : StringHom α β) : List α → List β
  | [] => []
  | a :: w => h a ++ applyTo h w

/-- A letter-to-letter homomorphism: each source symbol maps to exactly one
    target symbol. This is the case used by @cite{shieber-1985}. -/
def StringHom.letterMap {α β : Type} (f : α → β) : StringHom α β :=
  fun a => [f a]

theorem StringHom.applyTo_letterMap {α β : Type} (f : α → β) (w : List α) :
    (StringHom.letterMap f).applyTo w = w.map f := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [applyTo, letterMap, ih]

/-- Intersection of two languages. -/
def Language.inter {α : Type} (L₁ L₂ : Language α) : Language α :=
  fun w => L₁ w && L₂ w
