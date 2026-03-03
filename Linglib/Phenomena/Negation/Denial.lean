import Linglib.Core.Semantics.ContentLayer
import Linglib.Core.Empirical

/-!
# Denial in Discourse
@cite{van-der-sandt-maier-2003}

Theory-neutral empirical data on denial: how "No, S — C" sequences
selectively retract different content layers of the denied sentence.

## Three Denial Types

@cite{van-der-sandt-maier-2003} show that denial isn't a special "metalinguistic
use" of negation (@cite{horn-1989}). It's ordinary semantic negation operating
on layered representations, where the correction determines which layer is
retracted:

| Denial type | Layer targeted | Example |
|-------------|----------------|---------|
| Propositional | `fr` (at-issue) | "...isn't bald — he has hair" |
| Presuppositional | `pr` | "...isn't bald — there's no king" |
| Implicature | `imp` | "...isn't a bachelor — he's the Pope" |

The key insight: the **same negation operator** handles all three cases.
What varies is which content layer the correction conflicts with (the
"offensive" layer), determined by the `Off` function.

## Connection to Existing Infrastructure

- `ContentLayer.atIssue` = propositional denial target
- `ContentLayer.presupposition` = presuppositional denial target
- `ContentLayer.implicature` = implicature denial target
- `Challengeability.directDenial` (in `ProjectiveContent`) corresponds to
  propositional denial
- `Challengeability.hwamChallenge` corresponds to presuppositional challenge
  (related but distinct from presuppositional *denial*)
-/

namespace Phenomena.Negation.Denial

open Core.Semantics.ContentLayer

-- ════════════════════════════════════════════════════
-- § Denial Type
-- ════════════════════════════════════════════════════

/-- The type of denial, determined by which content layer is targeted.

    Each type corresponds to a `ContentLayer` via `targetLayer`. This
    is the central claim of @cite{van-der-sandt-maier-2003}: the three
    denial types are not three different operations, but one operation
    (negation + correction) targeting three different layers. -/
inductive DenialType where
  /-- Propositional denial: targets at-issue content.
      The presupposition survives; the assertion is retracted.
      "The king of France isn't bald — he has a full head of hair." -/
  | propositional
  /-- Presuppositional denial: targets presupposed content.
      The presupposition is retracted; the assertion falls with it.
      "The king of France isn't bald — there is no king of France." -/
  | presuppositional
  /-- Implicature denial: targets pragmatic enrichment.
      The literal meaning survives; the implicature is retracted.
      "The Pope isn't a bachelor — he's simply the Pope." -/
  | implicature
  deriving DecidableEq, Repr, BEq

/-- Map denial type to the content layer it targets. -/
def DenialType.targetLayer : DenialType → ContentLayer
  | .propositional => .atIssue
  | .presuppositional => .presupposition
  | .implicature => .implicature

/-- Each denial type targets a distinct layer. -/
theorem denial_types_target_distinct_layers :
    DenialType.propositional.targetLayer ≠ DenialType.presuppositional.targetLayer ∧
    DenialType.propositional.targetLayer ≠ DenialType.implicature.targetLayer ∧
    DenialType.presuppositional.targetLayer ≠ DenialType.implicature.targetLayer :=
  ⟨by decide, by decide, by decide⟩

/-- The mapping from denial types to content layers is injective:
    no two denial types target the same layer. -/
theorem targetLayer_injective (d₁ d₂ : DenialType)
    (h : d₁.targetLayer = d₂.targetLayer) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp_all [DenialType.targetLayer]

-- ════════════════════════════════════════════════════
-- § Denial Data
-- ════════════════════════════════════════════════════

/-- A denial datum: an assertion-denial-correction triple.

    Records the empirical pattern where a speaker asserts S, a hearer
    denies with "No, S — C", and the denial selectively retracts one
    content layer while preserving others. -/
structure DenialDatum where
  /-- The original assertion -/
  assertion : String
  /-- The denial (typically the negation of the assertion) -/
  denial : String
  /-- The correction that follows the denial -/
  correction : String
  /-- Which content layer the correction targets -/
  denialType : DenialType
  /-- What content is retracted by the denial -/
  retractedContent : String
  /-- What content survives the denial -/
  survivingContent : String := ""
  notes : String := ""
  deriving Repr

-- ════════════════════════════════════════════════════
-- § Propositional Denial Examples
-- ════════════════════════════════════════════════════

/-- Propositional denial: the king's baldness is retracted, but his
    existence (the presupposition of the definite) survives.

    @cite{van-der-sandt-maier-2003}: standard truth-conditional negation
    where only the at-issue content is in conflict with the correction. -/
def kingBald_propositional : DenialDatum :=
  { assertion := "The king of France is bald"
  , denial := "The king of France is not bald"
  , correction := "He has a full head of hair"
  , denialType := .propositional
  , retractedContent := "The king is bald"
  , survivingContent := "There is a king of France" }

/-- Propositional denial of a simple predication. -/
def johnLeft_propositional : DenialDatum :=
  { assertion := "John left"
  , denial := "John didn't leave"
  , correction := "He's still here"
  , denialType := .propositional
  , retractedContent := "John left"
  , survivingContent := "John exists" }

-- ════════════════════════════════════════════════════
-- § Presuppositional Denial Examples
-- ════════════════════════════════════════════════════

/-- Presuppositional denial: the correction targets the existence
    presupposition of "the king of France," not the predication.

    Same surface negation as `kingBald_propositional`, but the
    correction disambiguates: "there is no king" conflicts with
    the presupposition layer, not the assertion layer. -/
def kingBald_presuppositional : DenialDatum :=
  { assertion := "The king of France is bald"
  , denial := "The king of France is not bald"
  , correction := "There is no king of France"
  , denialType := .presuppositional
  , retractedContent := "There is a king of France"
  , notes := "Same negation as propositional; correction disambiguates" }

/-- Presuppositional denial of "manage" (effort presupposition).
    "She didn't manage to pass — she SAILED through it."

    "Manage" presupposes difficulty; the correction denies this
    presupposition while preserving the at-issue content (she passed). -/
def manage_presuppositional : DenialDatum :=
  { assertion := "She managed to pass the exam"
  , denial := "She didn't manage to pass"
  , correction := "She SAILED through it"
  , denialType := .presuppositional
  , retractedContent := "Passing required effort/was difficult"
  , survivingContent := "She passed the exam" }

/-- Presuppositional denial of "stop" (prior-state presupposition).
    "He didn't stop smoking — he never smoked."

    "Stop" presupposes prior state; the correction targets this. -/
def stop_presuppositional : DenialDatum :=
  { assertion := "John stopped smoking"
  , denial := "John didn't stop smoking"
  , correction := "He never smoked"
  , denialType := .presuppositional
  , retractedContent := "John used to smoke"
  , notes := "Change-of-state verb 'stop' presupposes prior state" }

-- ════════════════════════════════════════════════════
-- § Implicature Denial Examples
-- ════════════════════════════════════════════════════

/-- Implicature denial: the Pope IS unmarried (literal meaning survives),
    but the connotation of eligibility/availability is retracted.

    @cite{van-der-sandt-maier-2003}: "bachelor" carries an implicature
    of eligible bachelorhood beyond the literal meaning of being unmarried.
    The correction "he's simply the Pope" signals that the literal meaning
    holds but the enrichment doesn't apply. -/
def pope_bachelor : DenialDatum :=
  { assertion := "The Pope is a bachelor"
  , denial := "The Pope isn't a bachelor"
  , correction := "He's simply the Pope"
  , denialType := .implicature
  , retractedContent := "The Pope is an eligible/available unmarried man"
  , survivingContent := "The Pope is unmarried" }

/-- Implicature denial with contrastive focus.
    "That's not a DOG — it's a WOLF."

    The denial targets the domestication implicature of "dog," not the
    literal denotation (canine). Both dogs and wolves are canines; the
    correction narrows to wild canine, retracting the domestic implicature. -/
def dog_wolf : DenialDatum :=
  { assertion := "That's a dog"
  , denial := "That's not a DOG"
  , correction := "It's a WOLF"
  , denialType := .implicature
  , retractedContent := "Domestic canine"
  , survivingContent := "Canine animal"
  , notes := "Contrastive focus marks the denied layer" }

-- ════════════════════════════════════════════════════
-- § Denial Ambiguity
-- ════════════════════════════════════════════════════

/-- The king-of-France sentence is ambiguous between propositional and
    presuppositional denial — the SAME surface negation, resolved by
    the correction.

    This is the paper's central empirical argument against treating
    metalinguistic negation as a distinct operator: one negation,
    two readings, disambiguated by discourse context. -/
theorem king_denial_same_surface :
    kingBald_propositional.denial = kingBald_presuppositional.denial := rfl

/-- But they target different layers. -/
theorem king_denial_different_layers :
    kingBald_propositional.denialType ≠ kingBald_presuppositional.denialType := by
  decide

-- ════════════════════════════════════════════════════
-- § Data Collection
-- ════════════════════════════════════════════════════

def propositionalDenials : List DenialDatum :=
  [kingBald_propositional, johnLeft_propositional]

def presuppositionalDenials : List DenialDatum :=
  [kingBald_presuppositional, manage_presuppositional, stop_presuppositional]

def implicatureDenials : List DenialDatum :=
  [pope_bachelor, dog_wolf]

def allDenialData : List DenialDatum :=
  propositionalDenials ++ presuppositionalDenials ++ implicatureDenials

end Phenomena.Negation.Denial
