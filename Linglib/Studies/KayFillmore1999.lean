import Linglib.Syntax.ConstructionGrammar.Idiom
import Linglib.Syntax.ConstructionGrammar.Licensing
import Linglib.Semantics.Presupposition.Basic
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Syntax.Minimalist.LeftPeriphery

/-!
# [kay-fillmore-1999]: *What's X Doing Y?*

"Grammatical Constructions and Linguistic Generalizations: The *What's X
doing Y?* Construction" (Language 75(1):1–33). WXDY has interrogative
*form* but expressive *function* on the incredulity reading; the
form–function mismatch is derived rather than stipulated: the literal
reading is a genuine question (speaker-ignorance satisfies the PerspP
presupposition), the incredulity reading a blocked one (speaker knowledge
contradicts it), with the presupposed proposition and the incongruity CI
typed via `PartialProp`/`TwoDimProp`. §2.3's morphosyntactic judgments
are derived by running the licensing recognizer over minimal-pair
tokens.

The paper's own inheritance hierarchy — WXDY inheriting from the
left-isolation, subject–aux-inversion, and wh-interrogative constructions
of its unification-based grammar — is recorded here only as prose;
assembling it as a checked network awaits verification of the paper's
figures.

## Main declarations

- `KayFillmore1999.wxdyConstruction`: the construction, typed form per
  Figure 12
- `KayFillmore1999.wxdy_rejects_bare_stem` (and companions): §2.3's
  morphosyntactic judgments derived by the licensing recognizer
- `KayFillmore1999.perspP_disambiguates_wxdy`: the two readings derived
- `KayFillmore1999.wxdyPresup`, `wxdyTwoDim`: typed pragmatics
-/

namespace KayFillmore1999

/-! ### The construction -/

open ConstructionGrammar

/-- The WXDY construction, as the flat projection of Figure 12's
hierarchical AVM: X and Y share a coreference index (coinstantiation,
Figure 13); WXDY-*what* is left-isolated ([loc -]) and nonreferential
([ref ∅]); *doing* cannot be negated ([neg -] — a stipulation the paper
reports being unable to deduce, §4.6). X is constrained semantically, as
a referential argument of the predicate Y (§4.7), and Y is a predicate
phrase of any category. -/
def wxdyConstruction : Construction :=
  { name := "What's X doing Y?"
  , form :=
      [ { filler := .semantic "referential", role := some "subject"
        , gf := some .subj, refIdx := some 2 }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .headed "doing" .VERB, gf := some .comp
        , constraints := [.negMinus] }
      , { filler := .fixed "what", gf := some .obj
        , constraints := [.locMinus, .refEmpty] }
      , { filler := .phrasal, role := some "predicate", gf := some .pred
        , refIdx := some 2 } ]
  , meaning := "incongruity of the presupposed situation (incredulity) or genuine activity question (literal)"
  , pragmaticFunction := "attributes incongruity to the presupposed situation" }

/-! ### Coreference (Figure 12) -/

/-- WXDY's form has exactly one coreference group: the X–Y
coinstantiation. -/
theorem wxdy_coreference_count : refGroupCount wxdyConstruction.form = 1 := by
  decide

/-- X (the first slot) and Y (the last slot) share a coreference index:
X is the understood subject of the Y predicate. -/
theorem wxdy_coinstantiation :
    wxdyConstruction.form.head?.bind (·.refIdx) = some 2 ∧
    wxdyConstruction.form.getLast?.bind (·.refIdx) = some 2 := by decide

/-! ### Morphosyntactic constraints derived (§2.3)

The paper's idiosyncratic constraints, run through the licensing
recognizer: tokens are daughter sequences in the AVM slot order
(X, BE, *doing*, *what*, Y), with lemma-level words. -/

/-- POS assignments for the fixed heads. -/
def wxdyPOS : String → Option UD.UPOS
  | "be" => some .AUX
  | "doing" => some .VERB
  | _ => none

/-- Ex. 3a, "What's this scratch doing on the table?". -/
def scratchTokens : List Token :=
  [ .word "scratch", .node [.word "be"], .node [.word "doing"]
  , .word "what", .node [.word "on", .word "table"] ]

/-- Ex. 14a, "What's he doing knowing the answer?" — a stative
complement. -/
def stativeTokens : List Token :=
  [ .word "he", .node [.word "be"], .node [.word "doing"]
  , .word "what", .node [.word "knowing", .word "answer"] ]

/-- Ex. 12a, "What does this scratch do on the table?" (ungrammatical):
bare-stem *do*. -/
def bareStemTokens : List Token :=
  [ .word "scratch", .node [.word "do"], .node [.word "do"]
  , .word "what", .node [.word "on", .word "table"] ]

/-- Ex. 13a, "What did he keep doing in the tool shed?" — *doing* as
complement of *keep* rather than of copular BE; a fine sentence, but not
an instance of the construction. -/
def nonCopulaTokens : List Token :=
  [ .word "he", .node [.word "keep"], .node [.word "doing"]
  , .word "what", .node [.word "in", .word "shed"] ]

/-- Ex. 15f, "What else are you doing eating cold pizza?"
(ungrammatical): *else* on WXDY-*what*. -/
def whatElseTokens : List Token :=
  [ .word "you", .node [.word "be"], .node [.word "doing"]
  , .node [.word "what", .word "else"]
  , .node [.word "eating", .word "pizza"] ]

/-- Ex. 17b, "What are my brushes not doing soaking in water?"
(ungrammatical): negated *doing*. -/
def negatedDoingTokens : List Token :=
  [ .word "brushes", .node [.word "be"], .node [.word "not", .word "doing"]
  , .word "what", .node [.word "soaking", .word "water"] ]

/-- Ex. 17c, "What are my brushes doing not soaking in water?": negation
inside the complement. -/
def negatedComplementTokens : List Token :=
  [ .word "brushes", .node [.word "be"], .node [.word "doing"]
  , .word "what", .node [.word "not", .word "soaking", .word "water"] ]

/-- The construction licenses the canonical example (ex. 3a) and stative
complements (ex. 14a): WXDY does not encode progressive aspect. -/
theorem wxdy_matches_canonical :
    formMatches wxdyPOS wxdyConstruction.form scratchTokens = true ∧
    formMatches wxdyPOS wxdyConstruction.form stativeTokens = true := by
  decide

/-- The present participle is frozen: bare-stem *do* is rejected
(ex. 12a). -/
theorem wxdy_rejects_bare_stem :
    formMatches wxdyPOS wxdyConstruction.form bareStemTokens = false := by
  decide

/-- *doing* must complement copular BE (ex. 13): *keep doing* is not an
instance of the construction. -/
theorem wxdy_rejects_non_copula :
    formMatches wxdyPOS wxdyConstruction.form nonCopulaTokens = false := by
  decide

/-- WXDY-*what* does not accept *else* (ex. 15f): the *what* slot is
lexically fixed. -/
theorem wxdy_rejects_what_else :
    formMatches wxdyPOS wxdyConstruction.form whatElseTokens = false := by
  decide

/-- Negation of *doing* is rejected by [neg -] (ex. 17b), while negation
inside the complement is licensed (ex. 17c). -/
theorem wxdy_negation_contrast :
    formMatches wxdyPOS wxdyConstruction.form negatedDoingTokens = false ∧
    formMatches wxdyPOS wxdyConstruction.form negatedComplementTokens = true := by
  decide

/-! ### Coinstantiation (Figure 13, §4.2) -/

/-- The coinstantiation construction (Figure 13): unifies the intrinsic
value of an unfulfilled valence requirement of a predicator with the
subject requirement of its controlled complement, covering both raising
and control. It figures twice in every WXDY clause — the flat rendering
here unifies a predicator's subject with its complement's subject via a
shared `refIdx`. -/
def coinstantiationForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "subject", gf := some .subj
    , refIdx := some 1 }
  , { filler := .open_ .VERB, role := some "predicate", isHead := true }
  , { filler := .open_ .VERB, role := some "complement", gf := some .comp
    , refIdx := some 1 } ]

/-- Coinstantiation is fully abstract: every slot is open. -/
theorem coinstantiation_specificity :
    derivedSpecificity coinstantiationForm = .fullyAbstract := by decide

/-- Coinstantiation carries exactly one coreference group (predicator
subject = complement subject). -/
theorem coinstantiation_coreference :
    refGroupCount coinstantiationForm = 1 := by decide

/-! ### Formal idiomhood -/

/-- WXDY is a formal idiom: the X and Y slots are open. -/
theorem wxdy_formal_idiom : wxdyConstruction.IsFormalIdiom := rfl

/-- WXDY is properly partial: BE, *doing*, and *what* are fixed while X
and Y are open. -/
theorem wxdy_partially_open :
    wxdyConstruction.specificity = .partiallyOpen := rfl

/-! ### Presupposition (§2.1) -/

open Semantics.Presupposition

/-- The incredulity reading presupposes the embedded proposition and has
trivial assertion: ex. 4's diner presupposes that there is a fly in the
soup — the point of the utterance is the incongruity judgment. -/
def wxdyPresup {W : Type*} (embeddedProp : W → Prop) : PartialProp W where
  presup := embeddedProp
  assertion _ := True

/-! ### Two-dimensional semantics (§2.2, §4.6) -/

open Pragmatics.Expressives

/-- The incredulity reading as a two-dimensional meaning: the embedded
proposition at issue, the incongruity judgment as a CI. The incongruity
is conventional, not conversationally implicated (§2.2, exx. 7–10). -/
def wxdyTwoDim {W : Type*} (embeddedProp incongruity : W → Prop) :
    TwoDimProp W :=
  TwoDimProp.withCI embeddedProp incongruity

/-- Negating a WXDY utterance cannot target the incongruity judgment
(§4.6, exx. 38–41): the CI survives negation of the at-issue content. -/
theorem wxdy_incongruity_survives_negation {W : Type*}
    (embeddedProp incongruity : W → Prop) :
    (TwoDimProp.neg (wxdyTwoDim embeddedProp incongruity)).ci = incongruity := by
  simp [wxdyTwoDim, TwoDimProp.withCI, TwoDimProp.neg]

/-! ### The two readings (§2.1) -/

open Minimalist.LeftPeriphery

/-- The speaker's epistemic state on the incredulity reading: the answer
is known (ex. 4's diner sees the fly), modeled as a veridical epistemic
model at the evaluation world. -/
def wxdyIncredulitySpeakerModel {W : Type*} (w : W) : EpistemicModel W :=
  veridicalModel w

/-- PerspP status separates the two readings of ex. 4: with a veridical
speaker model (incredulity) the PerspP ignorance presupposition fails and
the utterance is not a genuine question; with an ignorant speaker model
(the literal reading) it is satisfied. -/
theorem perspP_disambiguates_wxdy {W : Type*}
    (q : QUD W) (w : W) :
    perspPPresupComp (wxdyIncredulitySpeakerModel w) q w = false ∧
    perspPPresupComp ignorantModel q w = true :=
  ⟨responsive_contradicts_perspP_comp q w, rogative_allows_perspP_comp q w⟩

end KayFillmore1999
