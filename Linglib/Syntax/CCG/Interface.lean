import Linglib.Syntax.CCG.Derivation
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Composition.CoordinatorOp
import Linglib.Semantics.Composition.Combinator

/-!
# CCG Syntax-Semantics Interface

This file defines the compositional interpretation of CCG derivations. Categories
encode semantic types (`catToTy`, which ignores slash modalities — they control
combinatory potential, not meaning), and because `Derivation` is intrinsically typed,
`Derivation.interp` needs no run-time category checks and no casts: application is
function application and every composition rule is a `B`-combinator composition of
the daughters' meanings ([steedman-2019]). Type-raising and coordination are lexical,
so their semantic action (`T`, generalized conjunction) enters through the lexicon.
A lexicon is well-typed by construction — it returns meanings at the queried
category — so soundness of the interface is a typing fact rather than a theorem.

## Main definitions

* `catToTy`: maps CCG categories to semantic types.
* `SemLexicon`: a semantic lexicon — for each word and category, optionally a meaning
  at that category.
* `Derivation.interp`: the meaning of a derivation of category `c`, at type
  `catToTy c`; `none` only when a word is missing from the lexicon.

## Main statements

* `Derivation.interp_fcomp_assoc`, `Derivation.interp_fapp_fcomp` (and backward
  mirrors): spurious ambiguity — reassociating a composition-application chain cannot
  change a constituent's interpretation ([steedman-2000]; the matching-entry tests of
  [karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance).

Worked toy-fragment derivations and the non-constituent-coordination semantics
theorems live in `Studies/Steedman2000.lean`.
-/

namespace CCG

open Intensional
open Intensional.Conjunction
open Combinator

/-! ### Type correspondence -/

/-- Map CCG categories to semantic types. Slash modalities are ignored: they control
combinatory potential, not meaning. -/
def catToTy : Cat Atom → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x _ y => catToTy y ⇒ catToTy x
  | .lslash x _ y => catToTy y ⇒ catToTy x

/-- Forward application preserves semantic typing:
    if X/Y combines with Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem forward_app_type_preservation (x y : Cat Atom) (m : Modality) :
    catToTy (.rslash x m y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application preserves semantic typing:
    if Y combines with X\Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem backward_app_type_preservation (x y : Cat Atom) (m : Modality) :
    catToTy (.lslash x m y) = (catToTy y ⇒ catToTy x) := rfl

/-- Type correspondence for transitive verbs -/
theorem tv_type_is_relation :
    catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

/-- Type correspondence for intransitive verbs -/
theorem iv_type_is_property :
    catToTy IV = (.e ⇒ .t) := rfl

/-- Type correspondence for forward type-raising: `T/(T\X)` denotes a function over
`X`-seeking functions. -/
theorem forward_type_raise_type (x t : Cat Atom) :
    catToTy (x.forwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-- Type correspondence for backward type-raising, identical to the forward case. -/
theorem backward_type_raise_type (x t : Cat Atom) :
    catToTy (x.backwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-! ### Derivation interpretation -/

/-- Semantic lexicon: for each word and queried category, optionally a meaning at that
category — well-typed by construction. Raised and coordinating entries carry their
semantic action here (`T`, generalized conjunction), per the morpholexical treatment
of [steedman-2019]. -/
def SemLexicon (E W : Type) := String → (c : Cat Atom) → Option (Denot E W (catToTy c))

/-- The semantic action of a rule — the "rule-to-rule relation" of [steedman-2019]:
application applies, every composition rule is a `B`-combinator composition of the
daughters\' meanings (second-order rules compose under one argument). -/
def Rule.sem {E W : Type} : {l r c : Cat Atom} → Rule Atom l r c →
    Denot E W (catToTy l) → Denot E W (catToTy r) → Denot E W (catToTy c)
  | _, _, _, .fapp, f, a => f a
  | _, _, _, .bapp, a, f => f a
  | _, _, _, .fcomp _, f, g => B f g
  | _, _, _, .bcomp _, g, f => B f g
  | _, _, _, .fcompx _, f, g => B f g
  | _, _, _, .bcompx _, g, f => B f g
  | _, _, _, .fcomp2 _, f, g => fun w z => f (g w z)
  | _, _, _, .bcomp2 _, g, f => fun w z => f (g w z)
  | _, _, _, .fcompx2 _, f, g => fun w z => f (g w z)
  | _, _, _, .bcompx2 _, g, f => fun w z => f (g w z)

/-- Interpret a derivation compositionally: leaves consult the lexicon and each rule
node acts by its `Rule.sem`. The category bookkeeping is carried by `Derivation`\'s
index, so no run-time category checks (and no casts) are needed; the result is `none`
only when a word is missing from the lexicon. -/
def Derivation.interp {E W : Type} (lex : SemLexicon E W) :
    {c : Cat Atom} → Derivation Atom c → Option (Denot E W (catToTy c))
  | _, .lex f c => lex f c
  | _, .node ru d₁ d₂ => do some (ru.sem (← d₁.interp lex) (← d₂.interp lex))

/-! ### Spurious ambiguity

Composition is semantically associative, so left- and right-branching derivations of
the same composition-application chain receive the same interpretation — with no
assumption on the lexicon. This is the local source of CCG's "spurious ambiguity"
([steedman-2000]; the matching-entry tests of [karttunen-1989] and
[pareschi-steedman-1987] exploit exactly this invariance): a chart parser may keep
one derivation per equivalence class, because reassociating `fcomp`/`fapp` (or
`bcomp`/`bapp`) nodes cannot change what a constituent means. -/

/-- Reassociating a forward-composition chain preserves interpretation: `B` is
semantically associative. -/
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

/-- Composing before applying is the same as applying twice: `B f g x = f (g x)`,
lifted to derivations. -/
theorem Derivation.interp_fapp_fcomp {E W : Type} (lex : SemLexicon E W)
    {x y z : Cat Atom} {m n : Modality} (hm : m ≤ Modality.diamond)
    (d₁ : Derivation Atom (.rslash x m y)) (d₂ : Derivation Atom (.rslash y n z))
    (d₃ : Derivation Atom z) :
    (Derivation.fapp (.fcomp hm d₁ d₂) d₃).interp lex
      = (Derivation.fapp d₁ (.fapp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Reassociating a backward-composition chain preserves interpretation — the mirror
of `interp_fcomp_assoc`. -/
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

/-- Applying twice is the same as backward-composing first — the mirror of
`interp_fapp_fcomp`. -/
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
