import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.Applicative
import Linglib.Phenomena.ArgumentStructure.Studies.Larson1988

/-!
# @cite{pylkknen-2008} — Introducing Arguments
@cite{pylkknen-2008} @cite{cuervo-2003} @cite{barss-lasnik-1986}

*Linguistic Inquiry Monographs* 49. MIT Press.

## Core Claims

1. **High vs Low Applicatives**: Applicative heads come in two semantic types.
   Low Appl merges below V, relating the applied argument to the theme
   (transfer-of-possession): `[VP V [ApplP goal [Appl theme]]]`.
   High Appl merges above VP, relating the applied argument to the event
   (benefactive): `[VoiceP agent [Voice [ApplP benef [Appl [VP V theme]]]]]`.

2. **Semantic type distinction**: High Appl denotes an individual-event
   relation `λx.λe. Appl(x,e)`. Low Appl denotes an individual-individual
   relation `λx.λy.λf.λe. f(e,x) & theme(e,x) & to-the-possession(x,y)`.

3. **Low recipient vs low source**: Low applicatives split into recipient
   (`ApplTo`: transfer *to* applied arg) and source (`ApplFrom`: transfer
   *from* applied arg). English DOC is low recipient; Korean theft
   constructions and Hebrew possessor datives are low source.

4. **C-command asymmetries**: In both configurations, the applied argument
   asymmetrically c-commands the theme. This derives the
   @cite{barss-lasnik-1986} binding asymmetries structurally.

5. **Cross-linguistic variation**: English, Japanese, and Korean have LOW
   Appl; Bantu languages (Chaga, Luganda, Venda) and Albanian have HIGH
   Appl.

## Diagnostics (Table 2.1)

| Test                                         | High | Low |
|----------------------------------------------|------|-----|
| 1. Can unergatives be applicativized?        | Yes  | No  |
| 2. Can static verbs be applicativized?       | Yes  | No  |
| 3. Depictive modification of applied arg?    | Yes  | No  |
| 4. Resultative cooccurrence with applicative?| Yes  | No  |

## Cross-references

- `Studies/Larson1988.lean`: VP shell predecessor — same c-command
  hierarchy (IO > DO) derived differently. Bridge theorem below proves
  convergence.
- `Studies/Kratzer1996.lean` Part III: Voice-based tree derivations
  (transitive, anticausative) using the same infrastructure.
-/

namespace Pylkkanen2008

open Minimalism

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def voice_ag_t  := mkLeafPhon .Voice [.V]    "Voice[AG]"  400
def appl_low_t  := mkLeafPhon .Appl  [.D]    "Appl[LOW]"  402
def appl_high_t := mkLeafPhon .Appl  [.V]    "Appl[HI]"   403
def V_sent_t    := mkLeafPhon .V     [.Appl] "sent"        404
def V_eat_t     := mkLeafPhon .V     [.D]    "eat"         405
def DP_john_t   := mkLeafPhon .D     []      "John"        406
def DP_mary_t   := mkLeafPhon .D     []      "Mary"        407
def DP_letter_t := mkLeafPhon .D     []      "a letter"    408
def DP_wife_t   := mkLeafPhon .D     []      "wife"        409
def DP_food_t   := mkLeafPhon .D     []      "food"        410

-- ============================================================================
-- § 2: Tree Derivations
-- ============================================================================

/-- Ditransitive with low applicative: "John sent Mary a letter"

    `[VoiceP John [Voice' Voice_AG [VP sent [ApplP Mary [Appl' Appl_LOW [DP a letter]]]]]]`

    Low Appl merges below V: V takes ApplP as complement. The goal
    (Mary) is in Spec-ApplP, c-commanding the theme (a letter) in
    complement of Appl. This derives the @cite{barss-lasnik-1986}
    asymmetry that IO asymmetrically c-commands DO. -/
def ditransitiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge V_sent_t
        (merge DP_mary_t
          (merge appl_low_t DP_letter_t))))

/-- High applicative benefactive (Chaga pattern): "he ate food for wife"

    `[VoiceP John [Voice' Voice_AG [ApplP wife [Appl' Appl_HIGH [VP eat [DP food]]]]]]`

    High Appl merges above VP: Appl takes VP as complement. The
    benefactive (wife) is in Spec-ApplP, relating to the event (not the
    theme). High Appl is attested in Bantu languages (Chaga, Luganda,
    Venda) and Albanian, but NOT in English. -/
def benefactiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge DP_wife_t
        (merge appl_high_t
          (merge V_eat_t DP_food_t))))

-- ============================================================================
-- § 3: C-command Predictions
-- ============================================================================

-- Ditransitive (low Appl): agent > goal > theme

/-- Agent c-commands goal. -/
theorem ditransitive_agent_ccommands_goal :
    cCommandsIn ditransitiveTree DP_john_t DP_mary_t := by native_decide

/-- Agent c-commands theme. -/
theorem ditransitive_agent_ccommands_theme :
    cCommandsIn ditransitiveTree DP_john_t DP_letter_t := by native_decide

/-- Goal c-commands theme — the @cite{barss-lasnik-1986} asymmetry
    derived structurally from V selecting ApplP. -/
theorem ditransitive_goal_ccommands_theme :
    cCommandsIn ditransitiveTree DP_mary_t DP_letter_t := by native_decide

/-- Theme does NOT c-command goal: the asymmetry is structural. -/
theorem ditransitive_theme_not_ccommands_goal :
    ¬ cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by native_decide

-- Benefactive (high Appl): benefactive > theme

/-- Benefactive c-commands theme. -/
theorem benefactive_benef_ccommands_theme :
    cCommandsIn benefactiveTree DP_wife_t DP_food_t := by native_decide

/-- Theme does NOT c-command benefactive. -/
theorem benefactive_theme_not_ccommands_benef :
    ¬ cCommandsIn benefactiveTree DP_food_t DP_wife_t := by native_decide

-- Appl head containment

/-- Low applicative marks the ditransitive. -/
theorem send_is_low_appl :
    containsB ditransitiveTree appl_low_t = true := by native_decide

/-- High applicative marks the benefactive. -/
theorem eat_is_high_appl :
    containsB benefactiveTree appl_high_t = true := by native_decide

-- ============================================================================
-- § 4: ApplType Association
-- ============================================================================

/-! The lexical items `appl_low_t` and `appl_high_t` correspond to
`ApplType` values from the theory layer. The ditransitive uses a low
recipient applicative (English DOC = transfer *to*); the benefactive
uses a high applicative (Chaga = individual-event relation). -/

/-- The low applicative head corresponds to a recipient applicative. -/
def lowApplType : ApplType := .lowRecipient

/-- The high applicative head corresponds to a high applicative. -/
def highApplType : ApplType := .high

/-- The ditransitive uses a low applicative. -/
theorem ditransitive_appl_is_low : lowApplType.IsLow := by decide

/-- The benefactive uses a high applicative. -/
theorem benefactive_appl_is_high : ¬ highApplType.IsLow := by decide

-- ============================================================================
-- § 5: Cross-linguistic Applicative Typology (Table 2.1)
-- ============================================================================

/-! ### Cross-linguistic classification (§2.1.2–§2.1.4)

@cite{pylkknen-2008} tests the high/low distinction in six languages
using four diagnostics. The diagnostics cluster into two groups,
confirming the typological split. -/

/-- A language's applicative classification with diagnostic evidence. -/
structure ApplClassification where
  language : String
  applType : ApplType
  /-- Can unergatives be applicativized? (§2.1.2) -/
  unergativeOK : Option Bool := none
  /-- Can static verbs be applicativized? (§2.1.2) -/
  staticVerbOK : Option Bool := none
  /-- Is the applied argument available for depictive modification? (§2.1.3) -/
  depictiveOK : Option Bool := none
  /-- Can resultatives cooccur with the applicative? (§2.1.4) -/
  resultativeOK : Option Bool := none
  deriving Repr, DecidableEq

/-- Do the diagnostics predict a HIGH applicative?
    At least one "yes" on unergatives or static verbs → high. -/
def diagnosticPredictsHigh (d : ApplClassification) : Bool :=
  d.unergativeOK == some true || d.staticVerbOK == some true

/-- Diagnostic prediction is consistent with the annotated classification. -/
def diagnosticsConsistent (d : ApplClassification) : Bool :=
  diagnosticPredictsHigh d == !decide d.applType.IsLow

-- Language data (§2.1.2–§2.1.4)

def english_appl : ApplClassification :=
  { language := "English", applType := .lowRecipient
  , unergativeOK := some false    -- *I ran him.
  , staticVerbOK := some false    -- *I held him the bag.
  , depictiveOK := some false     -- *John told Mary the news drunk.
  , resultativeOK := some false } -- *He painted me this flower blue.

def japanese_appl : ApplClassification :=
  { language := "Japanese", applType := .lowRecipient
  , unergativeOK := some false    -- *Taro ran for Hanako.
  , staticVerbOK := some false    -- *Taro held Hanako her bag.
  , depictiveOK := some false }   -- *depictive on applied arg

def korean_appl : ApplClassification :=
  { language := "Korean", applType := .lowRecipient
  , unergativeOK := some false    -- *Mary ran to/from John.
  , staticVerbOK := some false }  -- *John held Mary her bag.
  -- Korean lacks depictive secondary predicates entirely

def luganda_appl : ApplClassification :=
  { language := "Luganda", applType := .high
  , unergativeOK := some true     -- Mukasa walked for Katonga.
  , staticVerbOK := some true     -- Katonga held the bag for Mukasa.
  , depictiveOK := some true      -- Mustafa worked for Katonga while Katonga was sick.
  , resultativeOK := some true }  -- Mukasa painted the wall blue for Katonga.

def venda_appl : ApplClassification :=
  { language := "Venda", applType := .high
  , unergativeOK := some true     -- I will work for the lady.
  , staticVerbOK := some true }   -- I held the pot for Mukasa.
  -- Venda depictives have too broad a distribution to test

def albanian_appl : ApplClassification :=
  { language := "Albanian", applType := .high
  , unergativeOK := some true     -- I ran for him.
  , staticVerbOK := some true }   -- Agim holds my bag for Drita.
  -- Albanian depictives have too broad a distribution to test

def allLanguages : List ApplClassification :=
  [english_appl, japanese_appl, korean_appl, luganda_appl, venda_appl, albanian_appl]

-- Verification theorems

/-- Six languages are classified. -/
theorem six_languages : allLanguages.length = 6 := rfl

-- Low languages: diagnostics correctly predict NO high applicative

theorem english_not_high : diagnosticPredictsHigh english_appl = false := rfl
theorem japanese_not_high : diagnosticPredictsHigh japanese_appl = false := rfl
theorem korean_not_high : diagnosticPredictsHigh korean_appl = false := rfl

-- High languages: diagnostics correctly predict high applicative

theorem luganda_is_high : diagnosticPredictsHigh luganda_appl = true := rfl
theorem venda_is_high : diagnosticPredictsHigh venda_appl = true := rfl
theorem albanian_is_high : diagnosticPredictsHigh albanian_appl = true := rfl

/-- The diagnostics are consistent with the annotated classification
    for all six languages. -/
theorem all_diagnostics_consistent :
    allLanguages.all diagnosticsConsistent = true := by native_decide

-- ============================================================================
-- § 6: Bridge — Larson VP Shell ↔ Modern Voice/Appl
-- ============================================================================

/-! @cite{larson-1988}'s VP shell is the precursor of the modern Voice +
Applicative decomposition. While the tree shapes differ (Larson uses
one VP-shell layer; modern theory uses Voice and Appl heads), the
c-command hierarchy among DP arguments is identical: agent > goal/IO > theme/DO. -/

open Larson1988 in

/-- @cite{larson-1988}'s DOC and the modern Voice + low-Appl derivation
    produce the same c-command hierarchy: IO asymmetrically c-commands DO.

    This proves that @cite{larson-1988} and @cite{pylkknen-2008},
    despite different decompositions, converge on the same structural
    prediction for @cite{barss-lasnik-1986} asymmetries. -/
theorem larson_modern_same_hierarchy :
    -- Larson's DOC: IO > DO
    cCommandsIn docDativeShift.final DP_mary DP_letter ∧
    ¬ cCommandsIn docDativeShift.final DP_letter DP_mary ∧
    -- Modern Voice/Appl: goal > theme (same asymmetry)
    cCommandsIn ditransitiveTree DP_mary_t DP_letter_t ∧
    ¬ cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Pylkkanen2008
