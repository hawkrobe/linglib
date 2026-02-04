/-
# Two-Dimensional Semantics for Conventional Implicatures

Formalization of Potts (2005) "The Logic of Conventional Implicatures" (LCI).

## Key Insight

Natural language meanings have TWO dimensions:
1. **At-issue content**: Truth-conditional, composes normally
2. **CI content**: Use-conditional, "floats up" to root

These dimensions are INDEPENDENT:
- CIs don't affect truth conditions
- CIs project through ALL operators (negation, conditionals, etc.)

## The LCI Type System

Potts uses superscripts to track dimensions:
- τᵃ: at-issue type
- τᶜ: CI type
- ⟨σᵃ, τᶜ⟩: CI-functor (takes at-issue, returns CI)

Key CI expressions:
- Expressives: ⟦bastard⟧ : ⟨eᵃ, tᶜ⟩
- Appositives: via comma feature
- Supplementary adverbs: ⟦luckily⟧ : ⟨tᵃ, tᶜ⟩

## References

- Potts, C. (2005). The Logic of Conventional Implicatures. OUP.
- Gutzmann, D. (2015). Use-Conditional Meaning. OUP.
- Kaplan, D. (1999). The Meaning of Ouch and Oops.
- McCready, E. (2010). Varieties of Conventional Implicature. S&P 3(8).
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.Proposition

namespace Montague.Lexicon.Expressives

open Core.Proposition


/--
A two-dimensional meaning following Potts (2005).

The key insight: linguistic expressions contribute to TWO independent
dimensions of meaning that compose by different rules.

- `atIssue`: Truth-conditional content (what is said)
- `ci`: Conventional implicature (use-conditional content)

Example: "That bastard John is late"
- atIssue: John is late
- ci: Speaker has negative attitude toward John
-/
structure TwoDimProp (W : Type*) where
  /-- At-issue (truth-conditional) content -/
  atIssue : W → Bool
  /-- Conventional implicature (use-conditional) content -/
  ci : W → Bool

namespace TwoDimProp

variable {W : Type*}


/--
Create a proposition with no CI content.

Most ordinary expressions have trivial CI content (always satisfied).
-/
def ofAtIssue (p : BProp W) : TwoDimProp W :=
  { atIssue := p, ci := fun _ => true }

/--
Create a pure CI (no at-issue contribution).

Some expressions ONLY contribute CI content.
Example: "damn" in "the damn dog" doesn't change truth conditions.
-/
def pureCI (c : BProp W) : TwoDimProp W :=
  { atIssue := fun _ => true, ci := c }

/--
Combine at-issue content with CI content.
-/
def withCI (p : BProp W) (c : BProp W) : TwoDimProp W :=
  { atIssue := p, ci := c }


/--
Negation: negates at-issue, CI PROJECTS UNCHANGED.

"John didn't see that bastard Pete"
- atIssue: ¬(John saw Pete)
- ci: Speaker thinks Pete is a bastard ← UNCHANGED!

This is the key difference from presuppositions.
-/
def neg (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := fun w => !p.atIssue w
  , ci := p.ci }  -- CI projects through negation

/--
Conjunction: at-issue conjoins, CIs BOTH project.

"That bastard John met that jerk Pete"
- atIssue: John met Pete
- ci: Speaker thinks John is bastard AND Pete is jerk
-/
def and (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := fun w => p.atIssue w && q.atIssue w
  , ci := fun w => p.ci w && q.ci w }  -- Both CIs project

/--
Disjunction: at-issue disjoins, CIs BOTH project.

CIs project even through disjunction - they're not "either/or".
-/
def or (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := fun w => p.atIssue w || q.atIssue w
  , ci := fun w => p.ci w && q.ci w }  -- Both CIs project (not disjoined!)

/--
Implication: at-issue implies, CIs BOTH project.

"If that bastard John calls, I'll leave"
- atIssue: John calls → I leave
- ci: Speaker thinks John is bastard ← Projects from antecedent!
-/
def imp (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := fun w => !p.atIssue w || q.atIssue w
  , ci := fun w => p.ci w && q.ci w }  -- Both CIs project


/--
**Theorem: CI Projects Through Negation**

This is Potts' key observation distinguishing CIs from presuppositions.
Presuppositions can be "filtered" by antecedents; CIs cannot.
-/
theorem ci_projects_through_neg (p : TwoDimProp W) :
    (neg p).ci = p.ci := rfl

/--
**Theorem: CI Projects Through Conditional Antecedent**

Unlike presuppositions, CIs in the antecedent of a conditional
are NOT filtered - they project to the root.

"If the king of France is bald, ..." - presupposes king exists (filtered)
"If that bastard calls, ..." - CI projects (speaker thinks he's bastard)
-/
theorem ci_projects_from_antecedent (p q : TwoDimProp W) (w : W) :
    (imp p q).ci w = (p.ci w && q.ci w) := rfl

/--
**Theorem: Double Negation Preserves CI**

CIs are completely unaffected by truth-functional operators.
-/
theorem ci_double_neg (p : TwoDimProp W) :
    (neg (neg p)).ci = p.ci := rfl

/--
**Theorem: At-Issue Independence**

CI content is independent of at-issue truth value.
The at-issue content can be true, false, or unknown - CI still holds.
-/
theorem ci_independent_of_atIssue (p : TwoDimProp W) (w : W)
    (h_ci : p.ci w = true) :
    -- CI holds regardless of at-issue value
    (p.atIssue w = true → p.ci w = true) ∧
    (p.atIssue w = false → p.ci w = true) := by
  exact ⟨fun _ => h_ci, fun _ => h_ci⟩

end TwoDimProp


/--
Types of CI-contributing expressions (Potts 2005, McCready 2010).

Following Potts' taxonomy:
- **Supplements**: Appositives, parentheticals, supplementary relatives
- **Expressives**: Epithets, expressive adjectives, honorifics
- **Utterance modifiers**: Speech act adverbs (frankly, honestly)
-/
inductive CIExprType where
  | nominalAppositive    -- "Laura, a doctor, ..."
  | clauseAppositive     -- "John, who is tall, ..."
  | supplementaryAdverb  -- "Luckily, ...", "Amazingly, ..."
  | epithet              -- "that bastard John"
  | expressiveAdjective  -- "the damn dog"
  | honorific            -- "Don Pedro", "John-san"
  | emotiveMarker        -- "Alas, ...", "Wow!"
  | utteranceModifier    -- "Frankly, ...", "Honestly, ..."
  deriving Repr, DecidableEq, BEq

/--
Properties of CI expressions (Potts 2005 §2.5).
-/
structure CIExprProperties where
  /-- CI is speaker-oriented (vs subject-oriented) -/
  speakerOriented : Bool
  /-- CI can be repeated for emphasis without redundancy -/
  repeatable : Bool
  /-- CI is immediate (affects context just by being uttered) -/
  immediate : Bool
  /-- CI is independent of at-issue truth -/
  independent : Bool
  deriving Repr

/--
Expressives have all the characteristic CI properties.
-/
def expressiveProperties : CIExprProperties :=
  { speakerOriented := true
  , repeatable := true      -- "damn damn damn" strengthens
  , immediate := true       -- Affects context immediately
  , independent := true }   -- Independent of truth conditions

/--
Appositives are slightly different (not repeatable in same way).
-/
def appositiveProperties : CIExprProperties :=
  { speakerOriented := true
  , repeatable := false     -- "John, a doctor, a doctor" is odd
  , immediate := true
  , independent := true }


/--
The comma feature type-shifts at-issue content to CI content.

This is Potts' mechanism for appositives:
- "Laura, a doctor, recommended aspirin"
- "a doctor" is at-issue predicate
- comma shifts it to CI: "Laura is a doctor" becomes CI content

Formally: comma : ⟨⟨eᵃ,tᵃ⟩, ⟨eᵃ,tᶜ⟩⟩
-/
def comma {W : Type*} (pred : W → Bool) (entity : W → Bool) : TwoDimProp W :=
  { atIssue := entity  -- Entity denotation passes through
  , ci := pred }       -- Predicate becomes CI content

/--
Supplementary adverb application.

"Luckily, John won" = John won + CI(speaker considers it lucky)

Formally: comma₂ : ⟨⟨tᵃ,tᵃ⟩, ⟨tᵃ,tᶜ⟩⟩
-/
def supplementaryAdverb {W : Type*}
    (adverbMeaning : BProp W → BProp W)  -- The adverb's at-issue meaning
    (prop : BProp W) : TwoDimProp W :=
  { atIssue := prop              -- Base proposition unchanged
  , ci := adverbMeaning prop }   -- Adverb meaning becomes CI


/--
CI informativeness ordering (Gutzmann 2015, Lo Guercio 2025).

φ has stronger CI than ψ iff the contexts where φ is felicitous
are a proper subset of contexts where ψ is felicitous.

⟦φ⟧ᵘ ⊂ ⟦ψ⟧ᵘ

Example:
- "That bastard John" is CI-stronger than "John"
- "That fucking bastard John" is CI-stronger than "That bastard John"
-/
def ciStrongerThan {W : Type*} (φ ψ : TwoDimProp W) : Prop :=
  -- φ's CI entails ψ's CI (more restrictive)
  (∀ w, φ.ci w = true → ψ.ci w = true) ∧
  -- But not vice versa (strictly stronger)
  (∃ w, ψ.ci w = true ∧ φ.ci w = false)

/--
CI equivalence: same CI content.
-/
def ciEquiv {W : Type*} (φ ψ : TwoDimProp W) : Prop :=
  ∀ w, φ.ci w = ψ.ci w

/--
CI weaker than: inverse of stronger.
-/
def ciWeakerThan {W : Type*} (φ ψ : TwoDimProp W) : Prop :=
  ciStrongerThan ψ φ


/--
A context for evaluating CI felicity (Gutzmann 2015).

Following Kaplan/Gutzmann, CI meaning restricts the set of
contexts in which an expression can be felicitously used.
-/
structure CIContext where
  /-- Speaker's attitudes (who they like/dislike/respect) -/
  speakerAttitudes : String → Int  -- Entity name → attitude (-100 to 100)
  /-- Formality level of the context -/
  formality : ℚ  -- 0 (casual) to 1 (formal)
  /-- Speaker's emotional state -/
  emotionalValence : Int  -- -100 (negative) to 100 (positive)

/--
Check if a CI expression is felicitous in a context.

An epithet like "bastard" is felicitous iff speaker has negative attitude.
An honorific like "don" is felicitous iff speaker has respect attitude.
-/
def isFelicitous (exprType : CIExprType) (target : String) (ctx : CIContext) : Bool :=
  match exprType with
  | .epithet => ctx.speakerAttitudes target < -20  -- Negative attitude required
  | .honorific => ctx.speakerAttitudes target > 50  -- Respect required
  | .emotiveMarker => ctx.emotionalValence.natAbs > 30  -- Strong emotion
  | _ => true  -- Other types: context-independent

-- Summary

/-
## What This Module Provides

### Core Types
- `TwoDimProp W`: Two-dimensional meaning (at-issue + CI)
- `CIExprType`: Taxonomy of CI expressions
- `CIExprProperties`: Properties (speaker-oriented, repeatable, etc.)
- `CIContext`: Context for felicity evaluation

### Connectives with CI Projection
- `neg`, `and`, `or`, `imp`: At-issue composes, CI always projects

### Key Theorems
- `ci_projects_through_neg`: CIs project through negation
- `ci_projects_from_antecedent`: CIs project from conditional antecedents
- `ci_independent_of_atIssue`: CI independent of truth value

### CI Informativeness (for ACIs)
- `ciStrongerThan`: φ has stronger CI than ψ
- `ciEquiv`, `ciWeakerThan`: Related orderings

### Construction
- `ofAtIssue`: No CI content
- `pureCI`: Only CI content
- `comma`: Type-shift for appositives
- `supplementaryAdverb`: Adverb application

### Connection to Other Modules
- `Core.Proposition`: Base proposition type
- `NeoGricean.ConventionalImplicatures`: Uses CI informativeness for ACIs
- `Montague.Lexicon.Expressives.Epithets`: Specific expressive lexical entries
-/

end Montague.Lexicon.Expressives
