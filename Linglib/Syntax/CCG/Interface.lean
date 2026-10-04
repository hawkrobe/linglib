module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Ty
public import Linglib.Syntax.Category.Coordinator

/-!
# The CCG syntax-semantics interface

A CCG category determines a semantic type, ignoring slash modalities, which control
combinatory potential rather than meaning. Since a `Derivation` is indexed by its category,
its interpretation needs no run-time category checks: application is function application,
and every composition rule composes its daughters' meanings, which is Curry's combinator `B`
in Steedman's presentation. Type-raising and coordination are lexical, as in Steedman's
morpholexical treatment, so their meanings (the Montague lift, generalized conjunction) come
from the lexicon. A lexicon returns meanings at the queried category, so the interface is
sound by typing rather than by a theorem.

## Main definitions

* `catToTy`: the semantic type of a category.
* `SemLexicon`: a semantic lexicon, giving a word an optional meaning at each category.
* `Derivation.interp`: the meaning of a derivation, `none` only when a word is missing from
  the lexicon.

## Main statements

* `Derivation.interp_fcomp_assoc`, `Derivation.interp_fapp_fcomp` and their backward
  mirrors: reassociating a composition-application chain does not change its
  interpretation, the source of CCG's spurious ambiguity.

The worked derivations over a toy fragment are in `Studies/Steedman2000.lean`.

## References

* [steedman-2000]
* [steedman-2019]
* [karttunen-1989]
* [pareschi-steedman-1987]
-/

@[expose] public section

namespace CCG

open Semantics.Composition

/-! ### Type correspondence -/

/-- `catToTy c` is the semantic type of the category `c`. It ignores slash modalities, which
control combinatory potential rather than meaning. -/
def catToTy : Cat Atom → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x _ y => catToTy y ⇒ catToTy x
  | .lslash x _ y => catToTy y ⇒ catToTy x

example : catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

example : catToTy IV = (.e ⇒ .t) := rfl

/-- A forward type-raised category `T/(T\X)` denotes a function over functions from the
type of `X`. -/
@[simp] theorem catToTy_forwardTypeRaise (x t : Cat Atom) :
    catToTy (x.forwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-- A backward type-raised category `T\(T/X)` denotes the same type as its forward
counterpart. -/
@[simp] theorem catToTy_backwardTypeRaise (x t : Cat Atom) :
    catToTy (x.backwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-! ### Derivation interpretation -/

/-- A semantic lexicon gives a word an optional meaning at each category, of that category's
type. Type-raised and coordinating entries carry the meanings of type-raising and
coordination. -/
def SemLexicon (E W : Type) := String → (c : Cat Atom) → Option (Ty.Domain E W (catToTy c))

/-- `r.sem` is the meaning of the rule `r` as an operation on its daughters' meanings.
Application applies the function to the argument, composition composes the two meanings,
and second-order composition composes under one argument. -/
def Rule.sem {E W : Type} : {l r c : Cat Atom} → Rule Atom l r c →
    Ty.Domain E W (catToTy l) → Ty.Domain E W (catToTy r) → Ty.Domain E W (catToTy c)
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
def Derivation.interp {E W : Type} (lex : SemLexicon E W) :
    {c : Cat Atom} → Derivation Atom c → Option (Ty.Domain E W (catToTy c))
  | _, .lex f c => lex f c
  | _, .node ru d₁ d₂ => do some (ru.sem (← d₁.interp lex) (← d₂.interp lex))

/-! ### Spurious ambiguity

Composition is associative, so left- and right-branching derivations of the same
composition-application chain receive the same interpretation, whatever the lexicon. This is
the local source of CCG's spurious ambiguity ([steedman-2000]). A chart parser may keep one
derivation per equivalence class, since reassociating `fcomp`/`fapp` (or `bcomp`/`bapp`)
nodes cannot change what a constituent means, and the matching-entry tests of
[karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance. -/

/-- Reassociating a forward-composition chain preserves its interpretation, since composition
is associative. -/
theorem Derivation.interp_fcomp_assoc {E W : Type} (lex : SemLexicon E W)
    {x y z w : Cat Atom} {m n p : Modality}
    (hm : m ≤ Modality.diamond) (hn : n ≤ Modality.diamond)
    (d₁ : Derivation Atom (.rslash x m y)) (d₂ : Derivation Atom (.rslash y n z))
    (d₃ : Derivation Atom (.rslash z p w)) :
    (Derivation.fcomp hn (.fcomp hm d₁ d₂) d₃).interp lex
      = (Derivation.fcomp hm d₁ (.fcomp hn d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Composing and then applying has the interpretation of applying twice, since
`(f ∘ g) x = f (g x)`. -/
theorem Derivation.interp_fapp_fcomp {E W : Type} (lex : SemLexicon E W)
    {x y z : Cat Atom} {m n : Modality} (hm : m ≤ Modality.diamond)
    (d₁ : Derivation Atom (.rslash x m y)) (d₂ : Derivation Atom (.rslash y n z))
    (d₃ : Derivation Atom z) :
    (Derivation.fapp (.fcomp hm d₁ d₂) d₃).interp lex
      = (Derivation.fapp d₁ (.fapp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Reassociating a backward-composition chain preserves its interpretation. -/
theorem Derivation.interp_bcomp_assoc {E W : Type} (lex : SemLexicon E W)
    {x y z w : Cat Atom} {m n p : Modality}
    (hm : m ≤ Modality.diamond) (hn : n ≤ Modality.diamond)
    (d₁ : Derivation Atom (.lslash y p z)) (d₂ : Derivation Atom (.lslash x n y))
    (d₃ : Derivation Atom (.lslash w m x)) :
    (Derivation.bcomp hm (.bcomp hn d₁ d₂) d₃).interp lex
      = (Derivation.bcomp hn d₁ (.bcomp hm d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Applying twice has the interpretation of backward-composing first and then applying. -/
theorem Derivation.interp_bapp_bcomp {E W : Type} (lex : SemLexicon E W)
    {x y w : Cat Atom} {m n : Modality} (hm : m ≤ Modality.diamond)
    (d₁ : Derivation Atom y) (d₂ : Derivation Atom (.lslash x n y))
    (d₃ : Derivation Atom (.lslash w m x)) :
    (Derivation.bapp (.bapp d₁ d₂) d₃).interp lex
      = (Derivation.bapp d₁ (.bcomp hm d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

end CCG
