import Linglib.Syntax.ConstructionGrammar.Idiom
import Linglib.Syntax.ConstructionGrammar.Licensing

/-!
# Kay and Fillmore (1999): The What's X Doing Y? Construction

This file formalizes the construction of [kay-fillmore-1999], *What's X doing Y?*, whose
interrogative form conventionally conveys that someone judges the scene `Y(X)` incongruous
(their gloss (39)), a meaning the paper argues is neither a conversational implicature of an
innocent question (Section 2.2) nor a proposition that negation could apply to
(Section 4.6). The construction is `wxdyConstruction`, the flat rendering of the paper's
Figure 12: BE and *doing* are fixed heads, *what* is a fixed, left-isolated and nonreferential
object, `X` is a referential subject coinstantiated with the subject of the predicate phrase
`Y`, and *doing* may not be negated, a stipulation the paper reports being unable to deduce.

The grammatical evidence for the construction in Section 2.3 is derived by the licensing
recognizer over the paper's minimal pairs: the canonical (3a) and the stative (14a) are
licensed, while the bare-stem *do* of (12a), *doing* as complement of *keep* in (13a),
*what else* in (15f), and the negated *doing* of (17b) are not, negation inside `Y` in (17c)
being fine. The coinstantiation construction of Figure 13 is recorded as a fully abstract form
with one coreference group.

## Implementation notes

The paper's semantics, the incongruity-judgment frame of Figure 12 with a contextually
anchored judge, is not represented beyond the construction's pragmatic point; its inheritance
from the left-isolation, subject–auxiliary inversion and wh-interrogative constructions of the
paper's unification grammar is recorded in prose only.

## References

* [kay-fillmore-1999]
* [fillmore-kay-oconnor-1988]
-/

namespace KayFillmore1999

open ConstructionGrammar

/-! ### The construction (Figure 12) -/

/-- The WXDY construction, the flat rendering of Figure 12: `X` and `Y` share a coreference
index (coinstantiation, Figure 13); WXDY-*what* is left-isolated and nonreferential;
*doing* cannot be negated (Section 4.6). `X` is a referential argument of the predicate `Y`
(Section 4.7), a predicate phrase of any category. -/
def wxdyConstruction : Construction Unit :=
  { name := "What's X doing Y?"
  , form :=
      [ { filler := .semantic "referential", gf := some .subj, refIdx := some 2 }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .headed "doing" .VERB, gf := some .comp, constraints := [.negMinus] }
      , { filler := .fixed "what", gf := some .obj, constraints := [.locMinus, .refEmpty] }
      , { filler := .phrasal, gf := some .pred, refIdx := some 2 } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The form has exactly one coreference group, the `X`–`Y` coinstantiation. -/
theorem wxdy_coreference_count : refGroupCount wxdyConstruction.form = 1 := by decide

/-- `X`, the first slot, and `Y`, the last, share a coreference index: `X` is the understood
subject of the predicate `Y`. -/
theorem wxdy_coinstantiation :
    wxdyConstruction.form.head?.bind (·.refIdx) = some 2 ∧
      wxdyConstruction.form.getLast?.bind (·.refIdx) = some 2 := by
  decide

/-- WXDY is a formal idiom: the `X` and `Y` slots are open. -/
theorem wxdy_formal_idiom : wxdyConstruction.IsFormalIdiom := rfl

/-- It is properly partial: BE, *doing* and *what* are fixed while `X` and `Y` are open. -/
theorem wxdy_partially_open : wxdyConstruction.specificity = .partiallyOpen := rfl

/-! ### The grammatical evidence (Section 2.3)

The paper's minimal pairs run through the licensing recognizer: tokens are daughter sequences
in the slot order `X`, BE, *doing*, *what*, `Y`, with lemma-level words. -/

/-- The parts of speech of the fixed heads. -/
def wxdyPOS : String → Option UD.UPOS
  | "be" => some .AUX
  | "doing" => some .VERB
  | _ => none

/-- (3a) *What's this scratch doing on the table?* -/
def scratchTokens : List Token :=
  [ .word "scratch", .node [.word "be"], .node [.word "doing"], .word "what",
    .node [.word "on", .word "table"] ]

/-- (14a) *What's he doing knowing the answer?*, a stative complement. -/
def stativeTokens : List Token :=
  [ .word "he", .node [.word "be"], .node [.word "doing"], .word "what",
    .node [.word "knowing", .word "answer"] ]

/-- (12a) *What does this scratch do on the table?*, with bare-stem *do*. -/
def bareStemTokens : List Token :=
  [ .word "scratch", .node [.word "do"], .node [.word "do"], .word "what",
    .node [.word "on", .word "table"] ]

/-- (13a) *What did he keep doing in the tool shed?*, *doing* as complement of *keep* rather
than of copular BE: a fine sentence, but not an instance of the construction. -/
def nonCopulaTokens : List Token :=
  [ .word "he", .node [.word "keep"], .node [.word "doing"], .word "what",
    .node [.word "in", .word "shed"] ]

/-- (15f) *What else are you doing eating cold pizza?*, with *else* on WXDY-*what*. -/
def whatElseTokens : List Token :=
  [ .word "you", .node [.word "be"], .node [.word "doing"], .node [.word "what", .word "else"],
    .node [.word "eating", .word "pizza"] ]

/-- (17b) *What are my brushes not doing soaking in water?*, with negated *doing*. -/
def negatedDoingTokens : List Token :=
  [ .word "brushes", .node [.word "be"], .node [.word "not", .word "doing"], .word "what",
    .node [.word "soaking", .word "water"] ]

/-- (17c) *What are my brushes doing not soaking in water?*, negation inside `Y`. -/
def negatedComplementTokens : List Token :=
  [ .word "brushes", .node [.word "be"], .node [.word "doing"], .word "what",
    .node [.word "not", .word "soaking", .word "water"] ]

/-- The construction licenses the canonical (3a) and the stative (14a): WXDY does not encode
progressive aspect. -/
theorem wxdy_matches_canonical :
    formMatches wxdyPOS wxdyConstruction.form scratchTokens = true ∧
      formMatches wxdyPOS wxdyConstruction.form stativeTokens = true := by
  decide

/-- The present participle is frozen: bare-stem *do* is rejected, (12a). -/
theorem wxdy_rejects_bare_stem :
    formMatches wxdyPOS wxdyConstruction.form bareStemTokens = false := by
  decide

/-- *doing* must complement copular BE: *keep doing* is no instance, (13a). -/
theorem wxdy_rejects_non_copula :
    formMatches wxdyPOS wxdyConstruction.form nonCopulaTokens = false := by
  decide

/-- WXDY-*what* does not accept *else*, (15f): the slot is lexically fixed. -/
theorem wxdy_rejects_what_else :
    formMatches wxdyPOS wxdyConstruction.form whatElseTokens = false := by
  decide

/-- Negation of *doing* is rejected, (17b), while negation inside `Y` is licensed, (17c). -/
theorem wxdy_negation_contrast :
    formMatches wxdyPOS wxdyConstruction.form negatedDoingTokens = false ∧
      formMatches wxdyPOS wxdyConstruction.form negatedComplementTokens = true := by
  decide

/-! ### Coinstantiation (Figure 13, Section 4.2) -/

/-- The coinstantiation construction, which unifies the intrinsic value of an unfulfilled
valence requirement of a predicator with the subject requirement of its controlled
complement, covering raising and control alike; it figures twice in every WXDY clause. The
flat rendering unifies a predicator's subject with its complement's subject through a shared
index. -/
def coinstantiationForm : TypedForm String :=
  [ { filler := .open_ .NOUN, gf := some .subj, refIdx := some 1 }
  , { filler := .open_ .VERB, isHead := true }
  , { filler := .open_ .VERB, gf := some .comp, refIdx := some 1 } ]

/-- Coinstantiation is fully abstract: every slot is open. -/
theorem coinstantiation_specificity :
    derivedSpecificity coinstantiationForm = .fullyAbstract := by decide

/-- It carries exactly one coreference group, the predicator's subject with the complement's. -/
theorem coinstantiation_coreference : refGroupCount coinstantiationForm = 1 := by decide

end KayFillmore1999
