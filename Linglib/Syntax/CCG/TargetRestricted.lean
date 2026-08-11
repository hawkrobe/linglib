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
* `CCG.TargetRestricted.Grammar`: the capacity object — a finite lexicon, the
  distinguished atom, and a bound on composition degree.
* `CCG.TargetRestricted.Grammar.Derives`: the derivability relation — `G.Derives c w`
  says the grammar derives token string `w` at category `c`; `Grammar.language` is
  the set of strings derived at the distinguished atom.

## Implementation notes

Derivability is an inductive `Prop`, mathlib's form for grammar formalisms
(`ContextFreeGrammar.Derives`), in contrast to the intrinsically typed
`CCG.Derivation` of the interpreted theory: capacity arguments quantify over all
derivations, and induction on `Derives` is exactly that quantification.
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

/-- `G.Derives c w`: the grammar derives token string `w` at category `c` — a lexical
entry, or a target-gated generalized composition of two adjacent derivations, within
the grammar's degree bound. Capacity arguments proceed by induction on this
relation. -/
inductive Grammar.Derives [DecidableEq α] (G : Grammar α) :
    Cat α → List String → Prop where
  /-- A lexical entry derives its token. -/
  | lex {w : String} {c : Cat α} : (w, c) ∈ G.lexicon → G.Derives c [w]
  /-- Forward composition of degree `n` (`>Bⁿ`; degree 0 is application), gated on the
  primary (left) target. -/
  | fc (n : Nat) {a b c : Cat α} {u v : List String} :
      G.Derives a u → G.Derives b v → n ≤ G.degree → target a = G.start →
      Cat.generalizedForwardComp n a b = some c → G.Derives c (u ++ v)
  /-- Backward composition of degree `n` (`<Bⁿ`; degree 0 is application), gated on the
  primary (right) target. -/
  | bc (n : Nat) {a b c : Cat α} {u v : List String} :
      G.Derives a u → G.Derives b v → n ≤ G.degree → target b = G.start →
      Cat.generalizedBackwardComp n a b = some c → G.Derives c (u ++ v)

/-- The string language of a grammar: the token strings derived at the distinguished
atom. Strings are token lists, so empty-string lexical entries are inexpressible —
the ε-freeness of [schiffer-maletti-2021]'s normal form holds by construction. -/
def Grammar.language [DecidableEq α] (G : Grammar α) : Set (List String) :=
  { w | G.Derives (.atom G.start) w }

end CCG.TargetRestricted
