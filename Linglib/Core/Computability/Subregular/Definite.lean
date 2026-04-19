/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Basic

/-!
# Definite and Reverse-Definite Languages (D_k, RD_k)

A language `L` is **`k`-definite** when membership is determined by the
last `k` symbols of the input @cite{rogers-pullum-2011} @cite{lambert-2022}:
any two strings agreeing on their length-`k` suffix are L-equivalent.
The dual notion, **reverse `k`-definite** (RD_k), checks the length-`k`
*prefix* instead.

These are weaker than SL_k in expressive power — they look at one fixed
position (the edge) rather than every contiguous window — but they are
foundational for the right- and left-context-only fragments of
finite-state computation. Concrete linguistic uses include word-final
neutralization (D_1 / D_2: a constraint on the last few segments) and
word-initial prosodic templates (RD_k).

## Strictly definite vs definite

The classical definite/strictly-definite distinction collapses for the
generative formulation used here: a language is definite iff it is
strictly definite (the permitted-suffix set is just the suffixes of
L-members), so we use a single `DefiniteGrammar` type and elide the
"strictly" qualifier.

## No boundary augmentation

Unlike SL/LT, D and RD do not use boundary symbols: the suffix/prefix
already privileges the edge structurally, and adding `none` markers
would just shift indexing by `k - 1`. The grammar's `permitted` set is
over the raw alphabet `α`, not `Augmented α`.

## Edge parameterization

Both D_k and RD_k are parameterized over an `Edge` (right vs left), so a
single `EdgeDefiniteGrammar` covers both classes; `DefiniteGrammar` and
`ReverseDefiniteGrammar` are abbreviations selecting the right and left
edges respectively.
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-- Which edge of the string the definite test inspects. `right` gives
classical D_k (final substring); `left` gives RD_k (initial substring). -/
inductive Edge | left | right
  deriving DecidableEq, Repr

namespace Edge

/-- Take the length-`k` substring at this edge of `xs`. `right` returns
the last `k` symbols; `left` returns the first `k`. Strings shorter than
`k` are returned in full. -/
def takeAt (e : Edge) (k : ℕ) (xs : List α) : List α :=
  match e with
  | .left  => xs.take k
  | .right => xs.drop (xs.length - k)

end Edge

/-- An **edge-definite `k`-grammar** over `α`: a set of permitted
length-(≤`k`) edge substrings. A string is accepted iff its `Edge`
length-`k` substring is permitted. -/
@[ext]
structure EdgeDefiniteGrammar (k : ℕ) (e : Edge) (α : Type*) where
  /-- The set of permitted length-(≤`k`) edge substrings. -/
  permitted : Set (List α)

namespace EdgeDefiniteGrammar

variable {k : ℕ} {e : Edge}

instance : Inhabited (EdgeDefiniteGrammar k e α) := ⟨⟨Set.univ⟩⟩

/-- The language generated: strings whose `Edge` length-`k` substring
is permitted. -/
def lang (G : EdgeDefiniteGrammar k e α) : Language α := fun w =>
  e.takeAt k w ∈ G.permitted

@[simp] lemma mem_lang (G : EdgeDefiniteGrammar k e α) (w : List α) :
    w ∈ G.lang ↔ e.takeAt k w ∈ G.permitted := Iff.rfl

end EdgeDefiniteGrammar

/-- A **`k`-definite grammar**: edge-definite at the right (final
substring). -/
abbrev DefiniteGrammar (k : ℕ) (α : Type*) := EdgeDefiniteGrammar k .right α

/-- A **reverse `k`-definite grammar**: edge-definite at the left (initial
substring). -/
abbrev ReverseDefiniteGrammar (k : ℕ) (α : Type*) := EdgeDefiniteGrammar k .left α

/-- A language `L` is **`k`-definite** at the right edge iff some
`DefiniteGrammar k α` generates exactly `L`. -/
def IsDefinite (k : ℕ) (L : Language α) : Prop :=
  ∃ G : DefiniteGrammar k α, G.lang = L

/-- A language `L` is **reverse `k`-definite** (left-edge) iff some
`ReverseDefiniteGrammar k α` generates exactly `L`. -/
def IsReverseDefinite (k : ℕ) (L : Language α) : Prop :=
  ∃ G : ReverseDefiniteGrammar k α, G.lang = L

end Core.Computability.Subregular
