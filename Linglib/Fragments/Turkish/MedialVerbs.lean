/-!
# Turkish Converbal Suffixes
@cite{goksel-kerslake-2005} @cite{kornfilt-1997}

Medial clause markers in Turkish: converbal (zarf-fiil) suffixes on the verb
stem that link clauses in a chain. Like Korean, Turkish has no switch-reference
morphology; each converbal suffix directly encodes the interclausal semantic
relation. Turkish converbs are the textbook examples of UD `VerbForm.Conv`.

Turkish converbal constructions are productive: chains can be extended by adding
medial clauses with converbal suffixes before the single final verb. The
converbal verb lacks person/number agreement (this is carried only by the final
verb), but some converbs allow tense or aspect marking.

## Inventory

| Suffix | Meaning | Negation |
|--------|---------|----------|
| -(y)ip | sequential 'and then, having done' | -meyip |
| -(y)erek | manner/simultaneous 'by doing, while doing' | -meyerek |
| -(y)ince | temporal/conditional 'when, once' | -meyince |
| -ken | simultaneous 'while (in the state)' | -mazken |
| -dikce | proportional 'as, the more...the more' | -medikce |
| -meden | negative 'without doing' | (inherently negative) |
| -AlI | temporal 'since doing' | -meyeli |
| -casina | manner 'as if' | -mezcesine |

-/

namespace Fragments.Turkish.MedialVerbs

/-- A Turkish converbal suffix entry. -/
structure ConverbEntry where
  /-- Suffix form (romanized). Allomorphs separated by /, vowel harmony
      indicated by parenthesized alternant. -/
  form : String
  /-- Semantic relation gloss. -/
  gloss : String
  /-- Whether the converb is inherently negative. -/
  inherentlyNegative : Bool
  /-- Negative form (if not inherently negative). -/
  negativeForm : Option String
  deriving Repr, BEq

-- ============================================================================
-- § Converb inventory
-- ============================================================================

/-- -(y)ip: sequential 'and then, having done'.
    The most common converb for narrative sequencing. Links temporally
    ordered events with shared or different subjects. -/
def ip : ConverbEntry :=
  { form := "-(y)ip", gloss := "and then/having done (sequential)"
    inherentlyNegative := false, negativeForm := some "-meyip" }

/-- -(y)erek: manner or simultaneous 'by doing, while doing'.
    The medial event specifies the manner or accompanies the following event. -/
def erek : ConverbEntry :=
  { form := "-(y)erek", gloss := "by doing/while doing (manner/simultaneous)"
    inherentlyNegative := false, negativeForm := some "-meyerek" }

/-- -(y)ince: temporal or conditional 'when, once, upon doing'.
    Marks the medial event as a temporal anchor or condition. -/
def ince : ConverbEntry :=
  { form := "-(y)ince", gloss := "when/once (temporal/conditional)"
    inherentlyNegative := false, negativeForm := some "-meyince" }

/-- -ken: simultaneous 'while (in the state)'.
    Attaches to the aorist or progressive stem. Marks ongoing state
    during the following event. -/
def ken : ConverbEntry :=
  { form := "-ken", gloss := "while (simultaneous state)"
    inherentlyNegative := false, negativeForm := some "-mazken" }

/-- -dikce: proportional 'as, the more...the more'.
    Marks a proportional or gradual temporal relation. -/
def dikce : ConverbEntry :=
  { form := "-dikce", gloss := "as/the more (proportional)"
    inherentlyNegative := false, negativeForm := some "-medikce" }

/-- -meden: negative converb 'without doing, before doing'.
    Inherently negative — there is no affirmative counterpart. -/
def meden : ConverbEntry :=
  { form := "-meden", gloss := "without doing (negative)"
    inherentlyNegative := true, negativeForm := none }

/-- -AlI: temporal 'since doing'.
    Marks the medial event as a temporal starting point for the main event.
    Example: *geleli üç gün oldu* 'it's been three days since (s/he) came'. -/
def ali : ConverbEntry :=
  { form := "-AlI", gloss := "since doing (temporal)"
    inherentlyNegative := false, negativeForm := some "-meyeli" }

/-- -casina: manner 'as if, as though'.
    Marks the medial event as a simulative manner description. -/
def casina : ConverbEntry :=
  { form := "-casina", gloss := "as if (simulative manner)"
    inherentlyNegative := false, negativeForm := some "-mezcesine" }

/-- All converbal suffixes. -/
def allConverbs : List ConverbEntry :=
  [ip, erek, ince, ken, dikce, meden, ali, casina]

-- ============================================================================
-- § Derived properties
-- ============================================================================

/-- Affirmative converbs (non-inherently-negative). -/
def affirmativeConverbs : List ConverbEntry :=
  allConverbs.filter (! ·.inherentlyNegative)

/-- Inherently negative converbs. -/
def negativeConverbs : List ConverbEntry :=
  allConverbs.filter (·.inherentlyNegative)

-- ============================================================================
-- § Verification theorems
-- ============================================================================

/-- 8 converbal suffixes in total. -/
theorem converb_count : allConverbs.length = 8 := rfl

/-- 7 affirmative converbs. -/
theorem affirmative_count : affirmativeConverbs.length = 7 := rfl

/-- 1 inherently negative converb (-meden). -/
theorem negative_count : negativeConverbs.length = 1 := rfl

/-- Every affirmative converb has a negative form. -/
theorem affirmative_have_neg_form :
    affirmativeConverbs.all (·.negativeForm.isSome) = true := rfl

/-- The inherently negative converb has no separate negative form. -/
theorem meden_no_neg_form : meden.negativeForm = none := rfl

/-- 7 + 1 = 8: affirmative + negative exhausts the inventory. -/
theorem polarity_partition :
    affirmativeConverbs.length + negativeConverbs.length
    = allConverbs.length := rfl

end Fragments.Turkish.MedialVerbs
