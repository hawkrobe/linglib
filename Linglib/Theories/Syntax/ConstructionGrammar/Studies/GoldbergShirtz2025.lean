import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Core.Presupposition
import Linglib.Core.CommonGround
import Linglib.Theories.Semantics.Lexical.Expressives.Basic

/-!
# Goldberg & Shirtz (2025): PAL Constructions — Theoretical Analysis

Formalizes the PAL (Phrasal Adjective-Like) construction and its inheritance
network using Construction Grammar types from `ConstructionGrammar.Basic`.

PALs are phrases that fill word-level syntactic slots (e.g., "a grab-and-go
lunch", "a must-see movie"). Their key theoretical properties:

1. **Form motivates function**: A phrase in a word slot gets lemma-like
   interpretation — the PAL names a situation type rather than describing it.
2. **Familiarity presupposition**: PALs presuppose the situation type is in
   the common ground (Studies 1a/1b).
3. **Two-dimensional meaning**: At-issue content (head noun denotation) +
   CI content (social signaling: wit, sarcasm).
4. **Inheritance network**: PALs inherit from both NN compounds (stress,
   no plural on modifier) and Adj+N constructions (prenominal position).

## Reference

Goldberg, A. E., & Shirtz, S. (2025). PAL constructions: How phrases can act
like words. To appear in Language.
-/

namespace ConstructionGrammar.Studies.GoldbergShirtz2025

open ConstructionGrammar
open Core.Presupposition
open Core.CommonGround
open Core.Proposition
open Semantics.Lexical.Expressives

/-! ## Section 1: PAL Construction definitions -/

/-- The PAL construction: a phrase fills a word-level modifier slot.

Form: [N' PAL⁰ N] — a phrasal expression occupies a head/modifier position
that normally expects a single word.

Meaning: The PAL names a familiar situation type, presupposing shared
knowledge of that type. -/
def palConstruction : Construction :=
  { name := "PAL"
  , form := "[N' PAL⁰ N]"
  , meaning := "PAL names a familiar situation type; head N is an instance"
  , specificity := .fullyAbstract
  , pragmaticFunction := "presupposes familiarity with situation type named by PAL" }

/-- must-VERB subtype: "a must-see movie", "a must-read book". -/
def mustVerbConstruction : Construction :=
  { name := "must-VERB"
  , form := "[N' must-V⁰ N]"
  , meaning := "N is something one must V"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes shared evaluative standard" }

/-- a simple ⟨PAL⟩ subtype: "a simple meet-and-greet". -/
def aSimplePALConstruction : Construction :=
  { name := "a simple ⟨PAL⟩"
  , form := "[DP a simple [N' PAL⁰ N]]"
  , meaning := "a straightforward instance of the PAL situation type"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes familiarity; 'simple' marks routine-ness" }

/-- Don't PAL me: "Don't wink-wink me". -/
def dontPALmeConstruction : Construction :=
  { name := "Don't PAL me"
  , form := "[VP Don't [V' PAL⁰ me]]"
  , meaning := "Don't do the PAL thing to/at me"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes familiarity; imperative + social force" }

/-- the old ⟨PAL⟩ N: "the old bait-and-switch trick". -/
def theOldPALConstruction : Construction :=
  { name := "the old ⟨PAL⟩ N"
  , form := "[DP the old [N' PAL⁰ N]]"
  , meaning := "a well-known instance of the PAL situation type"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presupposes familiarity; 'old' marks conventionality" }

/-- NN compound construction (parent of PAL for stress/morphology). -/
def nnCompound : Construction :=
  { name := "NN compound"
  , form := "[N⁰ N⁰ N⁰]"
  , meaning := "compound nominal: modifier narrows head noun denotation"
  , specificity := .fullyAbstract }

/-- Adjective + Noun modification construction (parent for position). -/
def adjNModification : Construction :=
  { name := "Adj+N modification"
  , form := "[N' A⁰ N]"
  , meaning := "adjective restricts noun denotation"
  , specificity := .fullyAbstract }

/-! ## Inheritance network (Figure 5 of Goldberg & Shirtz 2025) -/

/-- The PAL constructicon: constructions + inheritance links. -/
def palConstructicon : Constructicon :=
  { constructions :=
      [ palConstruction
      , mustVerbConstruction
      , aSimplePALConstruction
      , dontPALmeConstruction
      , theOldPALConstruction
      , nnCompound
      , adjNModification ]
  , links :=
      [ -- PAL inherits from NN compound (stress, no plural on modifier)
        { parent := "NN compound"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["compound stress (primary on modifier)"
                              , "no plural marking on non-head"]
        , overriddenProperties := ["modifier is phrasal, not N⁰"] }
      , -- PAL inherits from Adj+N (prenominal modifier position)
        { parent := "Adj+N modification"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["prenominal modifier position"
                              , "restricts head noun denotation"]
        , overriddenProperties := ["modifier is phrasal, not A⁰"] }
      , -- Subtypes inherit from PAL
        { parent := "PAL"
        , child := "must-VERB"
        , mode := .normal
        , sharedProperties := ["familiarity presupposition"
                              , "phrase-in-word-slot form"]
        , overriddenProperties := ["partially lexically specified"] }
      , { parent := "PAL"
        , child := "a simple ⟨PAL⟩"
        , mode := .normal
        , sharedProperties := ["familiarity presupposition"
                              , "phrase-in-word-slot form"]
        , overriddenProperties := ["includes determiner and 'simple'"] }
      , { parent := "PAL"
        , child := "Don't PAL me"
        , mode := .normal
        , sharedProperties := ["familiarity presupposition"
                              , "phrase-in-word-slot form"]
        , overriddenProperties := ["PAL fills V slot, not modifier slot"] }
      , { parent := "PAL"
        , child := "the old ⟨PAL⟩ N"
        , mode := .normal
        , sharedProperties := ["familiarity presupposition"
                              , "phrase-in-word-slot form"]
        , overriddenProperties := ["includes 'the old'"] } ] }

/-! ## Section 2: Presupposition bridge

Connect PAL's familiarity presupposition to Core.Presupposition and
Core.CommonGround infrastructure. -/

/-- PAL presupposes the situation type is in the common ground.

The presupposition is the situation type proposition itself:
if the PAL is "grab-and-go", the presupposition is that grab-and-go
situations are a recognized category for both speaker and addressee. -/
def palPresupposition (W : Type*) (situationType : BProp W) : PrProp W :=
  { presup := situationType
  , assertion := λ _ => true }

/-- PAL two-dimensional meaning (Potts 2005 two-dimensional semantics).

- At-issue: the head noun's denotation (e.g., "lunch" in "grab-and-go lunch")
- CI: speaker presupposes shared familiarity with the situation type

This connects PAL semantics to the existing `TwoDimProp` from
`Semantics.Lexical.Expressives.Basic`. -/
def palTwoDim (W : Type*) (atIssue : BProp W) (familiar : BProp W) :
    TwoDimProp W :=
  { atIssue := atIssue
  , ci := familiar }

/-- When the situation type is in the common ground, the PAL's presupposition
is satisfied. -/
theorem pal_presup_satisfied_by_cg (W : Type*)
    (situationType : BProp W) (c : ContextSet W)
    (h : c ⊧ situationType) :
    ∀ w, c w → (palPresupposition W situationType).presup w = true :=
  h

/-- PAL CI projects through negation (inherits from TwoDimProp).

"It's not a grab-and-go lunch" still conveys familiarity with grab-and-go. -/
theorem pal_ci_projects_through_neg (W : Type*)
    (atIssue familiar : BProp W) :
    (TwoDimProp.neg (palTwoDim W atIssue familiar)).ci = familiar := rfl

/-! ## Section 3: Core theoretical claims

State the paper's central claims as propositions. These connect the
empirical data (in Phenomena/) to the theoretical analysis. -/

/-- **Claim 1**: PAL form motivates PAL function.

A phrase filling a word-level slot gets lemma-like interpretation:
the PAL names a situation type rather than compositionally describing it.
This is a form-function correlation at the heart of CxG. -/
def claim_form_motivates_function : Prop :=
  palConstruction.specificity = .fullyAbstract ∧
  palConstruction.pragmaticFunction = some "presupposes familiarity with situation type named by PAL"

/-- Claim 1 holds by construction. -/
theorem claim_form_motivates_function_holds : claim_form_motivates_function := by
  exact ⟨rfl, rfl⟩

/-- **Claim 2**: PALs presuppose the situation type is common knowledge.

Supported by Studies 1a (common knowledge) and 1b (shared background):
PALs are preferred when the situation type is mutually known. -/
def claim_pal_presupposes_familiarity : Prop :=
  ∀ (W : Type*) (sitType : BProp W),
    (palPresupposition W sitType).presup = sitType

/-- Claim 2 holds by definition of palPresupposition. -/
theorem claim_pal_presupposes_familiarity_holds :
    claim_pal_presupposes_familiarity := λ _ _ => rfl

end ConstructionGrammar.Studies.GoldbergShirtz2025
