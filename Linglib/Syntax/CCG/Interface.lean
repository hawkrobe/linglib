module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Ty

/-!
# The CCG syntax-semantics interface

A typing of the atoms extends to every category, sending `X/Y` and `X\Y` to the function type
from the type of `Y` to that of `X` and ignoring slash modalities, which control combinatory
potential rather than meaning. Since a `Derivation` is indexed by its category, its
interpretation needs no run-time category checks: application is function application, and every
composition rule composes its daughters' meanings, Curry's combinator `B` in Steedman's
presentation. Type-raising and coordination are lexical, so their meanings (the Montague lift,
generalized conjunction) come from the lexicon. A lexicon returns meanings at the queried
category, so the interface is sound by typing rather than by a theorem.

## Main definitions

* `CCG.Cat.toTy`: the semantic type of a category under a typing of its atoms.
* `CCG.SemLexicon`: a semantic lexicon, giving a word an optional meaning at each category.
* `CCG.Derivation.interp`: the meaning of a derivation, `none` only when a word is missing from
  the lexicon.

## Main statements

* `CCG.Derivation.interp_fcomp_assoc`, `CCG.Derivation.interp_fapp_fcomp` and their backward
  mirrors: reassociating a composition-application chain does not change its interpretation,
  the source of CCG's spurious ambiguity.

## References

* [steedman-2000]
* [steedman-2019]
* [karttunen-1989]
* [pareschi-steedman-1987]
-/

@[expose] public section

namespace CCG

open Montague

variable {α : Type*}

/-! ### Type correspondence -/

/-- `c.toTy τ` is the semantic type of the category `c` when each atom `a` has type `τ a`. -/
def Cat.toTy (τ : α → Ty) : Cat α → Ty
  | .atom a => τ a
  | .rslash x _ y => y.toTy τ ⇒ x.toTy τ
  | .lslash x _ y => y.toTy τ ⇒ x.toTy τ

/-- A forward type-raised category `T/(T\X)` denotes a function over functions from the
type of `X`. -/
@[simp] theorem Cat.toTy_forwardTypeRaise (τ : α → Ty) (x t : Cat α) :
    (x.forwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

/-- A backward type-raised category `T\(T/X)` denotes the same type as its forward
counterpart. -/
@[simp] theorem Cat.toTy_backwardTypeRaise (τ : α → Ty) (x t : Cat α) :
    (x.backwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

/-! ### Derivation interpretation -/

/-- A semantic lexicon gives a word an optional meaning at each category, of that category's
type under the atom typing `τ`. Type-raised and coordinating entries carry the meanings of
type-raising and coordination. -/
def SemLexicon (τ : α → Ty) (E W : Type) :=
  String → (c : Cat α) → Option (Ty.Domain E W (c.toTy τ))

/-- `r.sem τ` is the meaning of the rule `r` as an operation on its daughters' meanings.
Application applies the function to the argument, composition composes the two meanings, and
second-order composition composes under one argument. -/
def Rule.sem (τ : α → Ty) {E W : Type} : {l r c : Cat α} → Rule α l r c →
    Ty.Domain E W (l.toTy τ) → Ty.Domain E W (r.toTy τ) → Ty.Domain E W (c.toTy τ)
  | _, _, _, .fapp, f, a => f a
  | _, _, _, .bapp, a, f => f a
  | _, _, _, .fcomp _, f, g => f ∘ g
  | _, _, _, .bcomp _, g, f => f ∘ g
  | _, _, _, .fcompx _, f, g => f ∘ g
  | _, _, _, .bcompx _, g, f => f ∘ g
  | _, _, _, .fcomp2 _, f, g => fun w ↦ f ∘ g w
  | _, _, _, .bcomp2 _, g, f => fun w ↦ f ∘ g w
  | _, _, _, .fcompx2 _, f, g => fun w ↦ f ∘ g w
  | _, _, _, .bcompx2 _, g, f => fun w ↦ f ∘ g w

/-- `d.interp lex` is the meaning of the derivation `d`. A leaf takes its meaning from `lex`
and a rule node combines its daughters' meanings by `Rule.sem`, so the result is `none` only
when a word is missing from the lexicon. -/
def Derivation.interp {τ : α → Ty} {E W : Type} (lex : SemLexicon τ E W) :
    {c : Cat α} → Derivation α c → Option (Ty.Domain E W (c.toTy τ))
  | _, .lex f c => lex f c
  | _, .node ru d₁ d₂ => do some (ru.sem τ (← d₁.interp lex) (← d₂.interp lex))

/-! ### Spurious ambiguity

Composition is associative, so left- and right-branching derivations of the same
composition-application chain receive the same interpretation, whatever the lexicon. This is
the local source of CCG's spurious ambiguity ([steedman-2000]). A chart parser may keep one
derivation per equivalence class, since reassociating `fcomp`/`fapp` (or `bcomp`/`bapp`)
nodes cannot change what a constituent means, and the matching-entry tests of
[karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance. -/

section SpuriousAmbiguity

variable {τ : α → Ty} {E W : Type} (lex : SemLexicon τ E W)

/-- Reassociating a forward-composition chain preserves its interpretation, since composition
is associative. -/
theorem Derivation.interp_fcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (hm : m ≤ Modality.diamond) (hn : n ≤ Modality.diamond)
    (d₁ : Derivation α (.rslash x m y)) (d₂ : Derivation α (.rslash y n z))
    (d₃ : Derivation α (.rslash z p w)) :
    (Derivation.fcomp hn (.fcomp hm d₁ d₂) d₃).interp lex
      = (Derivation.fcomp hm d₁ (.fcomp hn d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Composing and then applying has the interpretation of applying twice, since
`(f ∘ g) x = f (g x)`. -/
theorem Derivation.interp_fapp_fcomp {x y z : Cat α} {m n : Modality}
    (hm : m ≤ Modality.diamond) (d₁ : Derivation α (.rslash x m y))
    (d₂ : Derivation α (.rslash y n z)) (d₃ : Derivation α z) :
    (Derivation.fapp (.fcomp hm d₁ d₂) d₃).interp lex
      = (Derivation.fapp d₁ (.fapp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Reassociating a backward-composition chain preserves its interpretation. -/
theorem Derivation.interp_bcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (hm : m ≤ Modality.diamond) (hn : n ≤ Modality.diamond)
    (d₁ : Derivation α (.lslash y p z)) (d₂ : Derivation α (.lslash x n y))
    (d₃ : Derivation α (.lslash w m x)) :
    (Derivation.bcomp hm (.bcomp hn d₁ d₂) d₃).interp lex
      = (Derivation.bcomp hn d₁ (.bcomp hm d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Applying twice has the interpretation of backward-composing first and then applying. -/
theorem Derivation.interp_bapp_bcomp {x y w : Cat α} {m n : Modality}
    (hm : m ≤ Modality.diamond) (d₁ : Derivation α y) (d₂ : Derivation α (.lslash x n y))
    (d₃ : Derivation α (.lslash w m x)) :
    (Derivation.bapp (.bapp d₁ d₂) d₃).interp lex
      = (Derivation.bapp d₁ (.bcomp hm d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

end SpuriousAmbiguity

end CCG
