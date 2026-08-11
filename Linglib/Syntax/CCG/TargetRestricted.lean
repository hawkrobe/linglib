import Linglib.Syntax.CCG.Basic
import Mathlib.Data.Set.Defs

/-!
# Target-restricted CCG

This file defines the target-restricted variant of CCG — the formalism of
[vijay-shanker-weir-1994] and [weir-joshi-1988], "VW-CCG" in
[kuhlmann-koller-satta-2015]'s terminology — in which combinatory rules are
restricted per grammar, rather than by the lexicalized slash modalities of the
modern theory (`Syntax/CCG/Basic`). The restriction modelled is the one
[kuhlmann-koller-satta-2015]'s generative-capacity results turn on, a *target
restriction*: a rule fires only when the target of its primary input category (the
leftmost atom, after stripping all arguments) is a distinguished atom `s`.

Rules are the generalized-composition schema `CCG.Cat.generalizedForwardComp` /
`CCG.Cat.generalizedBackwardComp`, gated on the target: a derivation node records
only its degree and direction, per the [vijay-shanker-weir-1994] rule form — degree
0 is application, and the harmonic/crossed distinction is a consequence of the slash
directions rather than a separate rule class. The schema is modality-blind (VW-CCG
predates slash typing); grammars instantiate categories at the unrestricted
modality.

The two rule-control mechanisms differ in expressive power
([kuhlmann-koller-satta-2015]): with target restrictions VW-CCG is weakly equivalent
to TAG, without them it is strictly weaker, and the slash-typing variant is likewise
slightly less expressive than TAG. [schiffer-maletti-2021] upgrade the equivalence to
*strong* equivalence (the same tree languages, modulo relabeling) for the modern
capacity object: CCG without empty-string lexicon entries and with rules of degree at
most 2 — with unbounded degree the formalism is Turing-complete. `Grammar` is that
object (yields are token lists, so ε-entries are inexpressible by construction), and
this file is the substrate for the constructions of CCGs for non-context-free
languages in `Studies/KuhlmannKollerSatta2015`.

## Main definitions

* `CCG.TargetRestricted.target`: the target of a category — its leftmost atom.
* `CCG.TargetRestricted.Derivation`: a raw derivation tree whose nodes record degree
  and direction; `Derivation.cat s` reads off its category under the target
  restriction to `s`, and `Derivation.yield` its surface string.
* `CCG.TargetRestricted.Grammar`: the capacity object — a finite lexicon, the
  distinguished atom, and a degree bound; `Derivation.WellFormed` checks a candidate
  tree against a grammar and `Grammar.language` is the set of yields it derives.

## Implementation notes

`Derivation` is deliberately extrinsic, in contrast to the intrinsically typed
`CCG.Derivation`: the generative-capacity results quantify over candidate trees, so
well-formedness is the proposition `d.cat s = some c` rather than a typing fact.
-/

namespace CCG.TargetRestricted

open CCG

variable {α : Type*}

/-- The target of a category: its leftmost atom (strip all arguments). -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ _ => target x
  | .lslash x _ _ => target x

@[simp] theorem target_atom (a : α) : target (Cat.atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) (m : Modality) :
    target (Cat.rslash x m y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) (m : Modality) :
    target (Cat.lslash x m y) = target x := rfl

/-- A raw derivation tree over the degree-`n` composition schema: nodes record degree
and direction only; well-formedness under a target restriction is read off by
`Derivation.cat`. -/
inductive Derivation (α : Type*) where
  /-- A lexical leaf: a surface form at a category. -/
  | lex : String → Cat α → Derivation α
  /-- Forward composition of degree `n` (`>Bⁿ`; degree 0 is application). -/
  | fc : Nat → Derivation α → Derivation α → Derivation α
  /-- Backward composition of degree `n` (`<Bⁿ`; degree 0 is application). -/
  | bc : Nat → Derivation α → Derivation α → Derivation α
  deriving Repr

/-- The category derived under the target restriction to `s`: each rule fires only when
the target of its primary (functor) input is `s` (`none` otherwise, or if the schema
does not apply). -/
def Derivation.cat [DecidableEq α] (s : α) : Derivation α → Option (Cat α)
  | .lex _ c => some c
  | .fc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target a = s then Cat.generalizedForwardComp n a b else none
  | .bc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target b = s then Cat.generalizedBackwardComp n a b else none

/-- Surface string: leaf forms left to right. -/
def Derivation.yield : Derivation α → List String
  | .lex w _ => [w]
  | .fc _ l r | .bc _ l r => l.yield ++ r.yield

/-! ### Grammars and their languages -/

/-- A target-restricted CCG grammar: a finite lexicon, a distinguished atom serving as
both the target restriction and the start symbol (the [kuhlmann-koller-satta-2015]
simplification of per-rule restrictions), and a bound on composition degree
(`degree = 2` in [schiffer-maletti-2021]'s normal form). -/
structure Grammar (α : Type*) where
  /-- Lexical entries, pairing a token with a category. -/
  lexicon : List (String × Cat α)
  /-- The distinguished atom: rules fire only at this target, and the language
  collects derivations of this category. -/
  start : α
  /-- The bound on composition degree. -/
  degree : Nat

/-- The derivation draws its leaves from the grammar's lexicon and respects its
degree bound. Together with `Derivation.cat G.start`, this is derivational
well-formedness over `G`. -/
def Derivation.WellFormed (G : Grammar α) : Derivation α → Prop
  | .lex w c => (w, c) ∈ G.lexicon
  | .fc n l r => n ≤ G.degree ∧ l.WellFormed G ∧ r.WellFormed G
  | .bc n l r => n ≤ G.degree ∧ l.WellFormed G ∧ r.WellFormed G

instance Derivation.WellFormed.decidable [DecidableEq α] (G : Grammar α) :
    ∀ d : Derivation α, Decidable (d.WellFormed G)
  | .lex w c => inferInstanceAs (Decidable ((w, c) ∈ G.lexicon))
  | .fc _ l r =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ (decidable G l) (decidable G r))
  | .bc _ l r =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ (decidable G l) (decidable G r))

/-- The string language of a grammar: the yields of well-formed derivations of the
distinguished atom. Yields are token lists, so empty-string lexical entries are
inexpressible — the ε-freeness of [schiffer-maletti-2021]'s normal form holds by
construction. -/
def Grammar.language [DecidableEq α] (G : Grammar α) : Set (List String) :=
  { w | ∃ d : Derivation α,
      d.WellFormed G ∧ d.cat G.start = some (.atom G.start) ∧ d.yield = w }

end CCG.TargetRestricted
