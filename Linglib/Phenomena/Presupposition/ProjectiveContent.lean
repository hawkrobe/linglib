/-
# Projective Content Taxonomy

Formalizes the taxonomy of projective contents from Tonhauser, Beaver,
Roberts & Simons (2013) "Toward a Taxonomy of Projective Content", Language 89(1).

## Insight

Not all projective contents behave alike. The taxonomy distinguishes four
classes based on two cross-cutting properties:

1. **Strong Contextual Felicity (SCF)**: Does the trigger require its
   projective content to be established in the utterance context prior to use?

2. **Obligatory Local Effect (OLE)**: When embedded under a belief predicate,
   must the projective content be part of the attitude holder's beliefs?

## The Four Classes

| Class | SCF | OLE | Examples |
|-------|-----|-----|----------|
| A | yes | yes | pronouns (existence), *too* (existence) |
| B | no  | no  | expressives, appositives, NRRCs, possessive NPs |
| C | no  | yes | *stop*, *know*, *only*, *almost* |
| D | yes | no  | *too* (salience), demonstratives, focus |

## Diagnostics

Family-of-Sentences Diagnostic (for projection):
- "It's not the case that P" — negation
- "Is it the case that P?" — question
- "It's possible that P" — modal
- "If P, then Q" — conditional antecedent

Hey wait a minute! test (for at-issueness):
Content that can be challenged with "Hey wait a minute!" is at-issue.

Belief-Predicate Test (for OLE):
"x believes that P" — does the projective content describe x's beliefs?

## References

- Tonhauser, Beaver, Roberts & Simons (2013). Toward a Taxonomy of
  Projective Content. Language 89(1), 66-109.
- Roberts (2012). Information structure in discourse.
- Potts (2005). The Logic of Conventional Implicatures.
- Simons et al. (2010). What projects and why.
-/

import Linglib.Core.Presupposition
import Linglib.Core.Proposition

namespace Phenomena.Presupposition.ProjectiveContent

open Core.Presupposition
open Core.Proposition


/--
Strong Contextual Felicity (SCF).

A trigger has SCF if it requires its projective content to be
established in the utterance context prior to its use.

Examples with SCF:
- Pronouns: "She left" requires antecedent in context
- Demonstratives: "That cat" requires indication established
- *too* (salience): "John came too" requires salient alternative

Examples without SCF:
- Expressives: "That damn cat" doesn't require prior annoyance
- Appositives: "Lance, an Ohioan, ..." informative content allowed
- Factives: "John knows it's raining" can be informative
-/
inductive StrongContextualFelicity where
  | requires   -- SCF = yes: requires prior establishment
  | noRequires -- SCF = no: can be informative
  deriving DecidableEq, Repr

/--
Obligatory Local Effect (OLE).

A trigger has OLE if, when embedded under a belief predicate,
its projective content must be part of the attitude holder's beliefs.

Examples with OLE:
- "John believes Mary stopped smoking"
  → John believes Mary used to smoke (obligatory local reading)
- "John believes it's raining" (from "John knows...")
  → The embedded proposition is part of John's beliefs

Examples without OLE:
- "John believes Lance, an Ohioan, will win"
  → Speaker (not John) commits to Lance being Ohioan
- "John believes that damn cat is outside"
  → Speaker (not John) is annoyed at the cat
-/
inductive ObligatoryLocalEffect where
  | obligatory   -- OLE = yes: attributed to attitude holder
  | notObligatory -- OLE = no: attributed to speaker
  deriving DecidableEq, Repr


/--
The four classes of projective content from Tonhauser et al. (2013).

Each class is defined by a combination of SCF and OLE values.
-/
inductive ProjectiveClass where
  /-- Class A: SCF=yes, OLE=yes
      Examples: pronouns (existence), *too* (existence) -/
  | classA
  /-- Class B: SCF=no, OLE=no
      Examples: expressives, appositives, NRRCs, possessive NPs -/
  | classB
  /-- Class C: SCF=no, OLE=yes
      Examples: *stop*, *know*, *only*, *almost* -/
  | classC
  /-- Class D: SCF=yes, OLE=no
      Examples: *too* (salience), demonstratives, focus (salience) -/
  | classD
  deriving DecidableEq, Repr

/--
Get the SCF value for a projective class.
-/
def ProjectiveClass.scf : ProjectiveClass → StrongContextualFelicity
  | .classA => .requires
  | .classB => .noRequires
  | .classC => .noRequires
  | .classD => .requires

/--
Get the OLE value for a projective class.
-/
def ProjectiveClass.ole : ProjectiveClass → ObligatoryLocalEffect
  | .classA => .obligatory
  | .classB => .notObligatory
  | .classC => .obligatory
  | .classD => .notObligatory

/--
Reconstruct the class from SCF and OLE values.
-/
def classFromProperties : StrongContextualFelicity → ObligatoryLocalEffect → ProjectiveClass
  | .requires,   .obligatory    => .classA
  | .noRequires, .notObligatory => .classB
  | .noRequires, .obligatory    => .classC
  | .requires,   .notObligatory => .classD

/--
The class reconstruction is correct.
-/
theorem class_properties_roundtrip (c : ProjectiveClass) :
    classFromProperties c.scf c.ole = c := by
  cases c <;> rfl


/--
Types of projective content triggers, following Tonhauser et al. (2013).

Each trigger type is associated with a projective class and a description
of the content it triggers.
-/
inductive ProjectiveTrigger where
  -- Class A triggers (SCF=yes, OLE=yes)
  /-- Personal pronouns: existence of referent -/
  | pronoun_existence
  /-- "too": existence of alternative satisfying predicate -/
  | too_existence

  -- Class B triggers (SCF=no, OLE=no)
  /-- Expressives like "damn": speaker attitude -/
  | expressive
  /-- Appositives: supplementary content -/
  | appositive
  /-- Non-restrictive relative clauses -/
  | nrrc
  /-- Possessive NPs: existence of possessor -/
  | possessive_np

  -- Class C triggers (SCF=no, OLE=yes)
  /-- Change-of-state predicates: prior state -/
  | stop_prestate
  /-- Factive verbs: complement truth -/
  | know_complement
  /-- Focus-sensitive "only": prejacent -/
  | only_prejacent
  /-- "almost": polar content -/
  | almost_polar
  /-- Definite descriptions: existence and uniqueness -/
  | definite_description

  -- Class D triggers (SCF=yes, OLE=no)
  /-- "too": salience of alternative -/
  | too_salience
  /-- Demonstratives: indication established -/
  | demonstrative_indication
  /-- Focus: salience of alternatives -/
  | focus_salience
  deriving DecidableEq, Repr

/--
The projective class for each trigger type.
-/
def ProjectiveTrigger.toClass : ProjectiveTrigger → ProjectiveClass
  -- Class A
  | .pronoun_existence => .classA
  | .too_existence => .classA
  -- Class B
  | .expressive => .classB
  | .appositive => .classB
  | .nrrc => .classB
  | .possessive_np => .classB
  -- Class C
  | .stop_prestate => .classC
  | .know_complement => .classC
  | .only_prejacent => .classC
  | .almost_polar => .classC
  | .definite_description => .classC
  -- Class D
  | .too_salience => .classD
  | .demonstrative_indication => .classD
  | .focus_salience => .classD


/--
A projective content item, combining a trigger with its content.

This extends the basic PrProp to track what kind of projective
content is involved.
-/
structure ProjectiveItem (W : Type*) where
  /-- The trigger type -/
  trigger : ProjectiveTrigger
  /-- The projective content as a proposition -/
  content : W → Bool
  /-- The at-issue content (if any) -/
  atIssue : W → Bool := λ _ => true

/--
Convert a ProjectiveItem to a PrProp.

The projective content becomes the presupposition, and the
at-issue content becomes the assertion.
-/
def ProjectiveItem.toPrProp {W : Type*} (pc : ProjectiveItem W) : PrProp W :=
  { presup := pc.content
  , assertion := pc.atIssue }

/--
Get the projective class for this item.
-/
def ProjectiveItem.projectiveClass {W : Type*} (pc : ProjectiveItem W) : ProjectiveClass :=
  pc.trigger.toClass


/--
Projection behavior describes how content behaves under embedding.

All projective contents share the core property that they can project
past certain operators, but they differ in their default behavior.
-/
structure ProjectionBehavior where
  /-- Projects past negation by default -/
  projectsPastNegation : Bool
  /-- Projects past questions by default -/
  projectsPastQuestions : Bool
  /-- Projects past modals by default -/
  projectsPastModals : Bool
  /-- Projects past conditionals (from antecedent) -/
  projectsPastConditionals : Bool
  deriving Repr

/--
Default projection behavior: all projective contents project by default.

Tonhauser et al. argue that projection is the *default*
for all projective contents. The differences are in SCF and OLE, not
in whether they project.
-/
def defaultProjection : ProjectionBehavior :=
  { projectsPastNegation := true
  , projectsPastQuestions := true
  , projectsPastModals := true
  , projectsPastConditionals := true }


/--
At-issueness status of content.

Following Roberts (2012), at-issue content addresses the Question Under
Discussion (QUD), while not-at-issue content is backgrounded.
-/
inductive AtIssueness where
  /-- Content that addresses the QUD -/
  | atIssue
  /-- Backgrounded content -/
  | notAtIssue
  deriving DecidableEq, Repr

/--
Challengeability with "Hey wait a minute!"

The HWAM test distinguishes at-issue from not-at-issue content:
- At-issue content can be challenged with "No, that's not true"
- Not-at-issue content can be challenged with "Hey wait a minute!"
-/
inductive Challengeability where
  /-- Can be challenged with "No, that's not true" -/
  | directDenial
  /-- Can be challenged with "Hey wait a minute!" -/
  | hwamChallenge
  /-- Cannot be directly challenged -/
  | notChallengeable
  deriving DecidableEq, Repr

/--
Projective content is typically not-at-issue and HWAM-challengeable.

This diagnostic identifies projective content.
-/
def projectiveContentTypicalStatus : AtIssueness × Challengeability :=
  (.notAtIssue, .hwamChallenge)


/--
Attribution of projective content under belief predicates.

When "x believes that S" is uttered, who is committed to the
projective content of S?
-/
inductive BeliefAttribution where
  /-- Attributed to attitude holder (x) -/
  | attitudeHolder
  /-- Attributed to speaker -/
  | speaker
  /-- Potentially ambiguous -/
  | ambiguous
  deriving DecidableEq, Repr

/--
Get the belief attribution for a projective class.
-/
def ProjectiveClass.beliefAttribution : ProjectiveClass → BeliefAttribution
  | .classA => .attitudeHolder  -- OLE = yes
  | .classB => .speaker         -- OLE = no
  | .classC => .attitudeHolder  -- OLE = yes
  | .classD => .speaker         -- OLE = no


/--
"John stopped smoking" example.

The change-of-state trigger "stop" has:
- Projective content: John used to smoke
- Class C: SCF=no (can be informative), OLE=yes (attributed to John's beliefs when embedded)
-/
example : ProjectiveTrigger.stop_prestate.toClass = .classC := rfl

/--
"That damn cat" example.

The expressive "damn" has:
- Projective content: speaker is annoyed at the cat
- Class B: SCF=no (need not be established), OLE=no (speaker commitment only)
-/
example : ProjectiveTrigger.expressive.toClass = .classB := rfl

/--
"She left" example.

The pronoun "she" has:
- Projective content: referent exists
- Class A: SCF=yes (requires antecedent), OLE=yes (attributed to attitude holder)
-/
example : ProjectiveTrigger.pronoun_existence.toClass = .classA := rfl

/--
"John came too" — salience component.

The salience requirement of "too" has:
- Projective content: salient alternative to John
- Class D: SCF=yes (requires salience), OLE=no (speaker's context)
-/
example : ProjectiveTrigger.too_salience.toClass = .classD := rfl


/--
Traditional classification of projective phenomena.

This maps the traditional terminology onto the Tonhauser et al. taxonomy.
Note that this is a simplification — the paper argues that traditional
categories don't carve at the joints.
-/
inductive TraditionalCategory where
  /-- Traditional "presupposition" -/
  | presupposition
  /-- Potts-style "conventional implicature" -/
  | conventionalImplicature
  /-- Supplementary/parenthetical content -/
  | supplementary
  deriving DecidableEq, Repr

/--
Map triggers to traditional categories (rough approximation).

The paper argues that this traditional classification is inadequate —
the four-class taxonomy based on SCF and OLE is more explanatory.
-/
def ProjectiveTrigger.traditionalCategory : ProjectiveTrigger → TraditionalCategory
  -- Traditional presuppositions
  | .pronoun_existence => .presupposition
  | .definite_description => .presupposition
  | .stop_prestate => .presupposition
  | .know_complement => .presupposition
  | .only_prejacent => .presupposition
  | .almost_polar => .presupposition
  | .too_existence => .presupposition
  | .too_salience => .presupposition
  -- Conventional implicatures
  | .expressive => .conventionalImplicature
  -- Supplementary content
  | .appositive => .supplementary
  | .nrrc => .supplementary
  | .possessive_np => .supplementary
  | .demonstrative_indication => .presupposition
  | .focus_salience => .presupposition


/--
The paper uses data from English and Paraguayan Guaraní to establish
that the SCF/OLE distinctions are cross-linguistically valid.

The four-class taxonomy is supported by data from both languages.
-/
structure CrossLinguisticEvidence where
  /-- The trigger tested -/
  trigger : ProjectiveTrigger
  /-- English data supports class assignment -/
  englishSupport : Bool
  /-- Guaraní data supports class assignment -/
  guaraniSupport : Bool

/--
The taxonomy is cross-linguistically supported.

Both English and Guaraní provide evidence for the four-class
distinction based on SCF and OLE.
-/
def taxonomyCrossLinguisticallySupported : Bool := true

end Phenomena.Presupposition.ProjectiveContent
