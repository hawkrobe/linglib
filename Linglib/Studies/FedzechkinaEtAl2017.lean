import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Syntax.DependencyGrammar.Dominance
import Linglib.Morphology.Word.Basic

/-!
# Fedzechkina et al.: learners restructure toward short dependencies
[fedzechkina-newport-2017] [fedzechkina-newport-2012]

Artificial-language learning with two mini-languages sharing a lexicon
but differing in constituent order: one places the complex NP where the
verb's dependencies stay short, the other where the subject dependency
stretches across the intervening complex NP. Learners exposed to a
50/50 mixture converge toward the short-dependency order (about two
thirds of productions by the end of training) — a learning bias for
dependency-length-minimizing orders.

This file holds the design's critical contrast as trees: the two
orders of "the big cat chased the dog" with one complex and one simple
NP, and the fact that the preferred order has strictly smaller total
dependency length. The convergence rates and their statistics live in
the papers.
-/

namespace FedzechkinaEtAl2017

open DependencyGrammar
open Morphology (Word)

/-- Complex NP first: "the-big-cat the-dog chased" — the verb is close
    to both argument heads. -/
def complexFirst : Graph 6 :=
  .ofArcs [Word.mk' "the" .DET, Word.mk' "big" .ADJ, Word.mk' "cat" .NOUN,
           Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "chased" .VERB]
    5 [(2, 0, .det), (2, 1, .amod), (5, 2, .nsubj), (4, 3, .det), (5, 4, .obj)]

/-- Complex NP last: "the-dog the-big-cat chased" — the subject
    dependency stretches across the complex NP. -/
def complexLast : Graph 6 :=
  .ofArcs [Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "the" .DET,
           Word.mk' "big" .ADJ, Word.mk' "cat" .NOUN, Word.mk' "chased" .VERB]
    5 [(1, 0, .det), (5, 1, .nsubj), (4, 2, .det), (4, 3, .amod), (5, 4, .obj)]

example : complexFirst.IsTree ∧ complexLast.IsTree := by decide

/-- The order learners converge toward has strictly smaller total
    dependency length. -/
theorem preferred_order_shorter_deps :
    complexFirst.totalLength < complexLast.totalLength := by decide

end FedzechkinaEtAl2017
