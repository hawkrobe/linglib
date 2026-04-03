import Linglib.Core.Lexical.Word
import Linglib.Core.Negation

/-!
# Zarma-Sonrai: Negation and Expletive Negation Markers
@cite{jin-koenig-2021}

Zarma-Sonrai (ISO 639-3: dje) is a Songhay language mainly spoken in
the southwestern border area of Niger. It had not been documented for
expletive negation (EN) prior to @cite{jin-koenig-2021}.

## Standard Negation

Zarma-Sonrai distinguishes two standard negation markers by aspect:
- **si** : imperfective negation (IPFV.NEG)
- **mana** / **batu** : perfective negation (PFV.NEG)

## Expletive Negation

EN negators vary by trigger class, mirroring the aspect-based split:

| Trigger class | EN negator | Gloss     | Aspect    |
|---------------|------------|-----------|-----------|
| FEAR          | si         | IPFV.NEG  | imperfective |
| AVOID         | si         | IPFV.NEG  | imperfective |
| DENY          | si         | IPFV.NEG  | imperfective |
| DELAY         | batu       | PFV.NEG   | perfective   |
| BEFORE        | mana       | PFV.NEG   | perfective   |
| CANNOT WAIT   | si + batu  | IPFV+PFV  | mixed        |

The choice of EN negator correlates with the aspectual properties of
the complement clause, not with the trigger class itself.

## Notable Absences

- WITHOUT: expressed as "q not p" (analytic, not triggering EN)
- TOO…TO: expressed as "too…so that…not" (collocation, not EN)
- MORE THAN: attested (with *da* 'than'), but EN data limited
-/

namespace Fragments.ZarmaSonrai.Negation

-- ════════════════════════════════════════════════════
-- § 1. Standard Negation
-- ════════════════════════════════════════════════════

/-- Negation marker for imperfective aspect contexts. -/
def ipfvNeg : String := "si"

/-- Negation marker for perfective aspect contexts (variant 1). -/
def pfvNeg : String := "mana"

/-- Negation marker for perfective aspect contexts (variant 2). -/
def pfvNeg2 : String := "batu"

-- ════════════════════════════════════════════════════
-- § 2. Expletive Negation Markers
-- ════════════════════════════════════════════════════

/-- Aspect governs expletive negation marker choice. -/
inductive ENAspect where
  | ipfv   -- imperfective complement → si
  | pfv    -- perfective complement → mana/batu
  deriving DecidableEq, Repr

/-- An expletive negation marker used in a specific trigger context. -/
structure ENNegator where
  /-- The negator form -/
  form : String
  /-- Aspectual context -/
  aspect : ENAspect
  /-- Whether this is a standard negation marker -/
  isStandardNeg : Bool
  deriving Repr, DecidableEq

/-- Imperfective EN negator: *si*. -/
def enIpfv : ENNegator where
  form := "si"
  aspect := .ipfv
  isStandardNeg := true

/-- Perfective EN negator: *batu*. -/
def enPfv : ENNegator where
  form := "batu"
  aspect := .pfv
  isStandardNeg := true

/-- Both EN negators are standard negation markers — Zarma-Sonrai does
    not have a dedicated expletive negator (unlike French *ne*). -/
theorem en_negators_are_standard :
    enIpfv.isStandardNeg = true ∧ enPfv.isStandardNeg = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Trigger-Specific Examples
-- ════════════════════════════════════════════════════

/-- A glossed EN example from Zarma-Sonrai. -/
structure ENExample where
  triggerClass : String
  triggerForm : String
  triggerGloss : String
  sentence : String
  gloss : String
  translation : String
  enNegator : String
  enAspect : ENAspect
  deriving Repr

/-- DELAY trigger: *batu* 'delay' (@cite{jin-koenig-2021}, ex. 22). -/
def delayExample : ENExample where
  triggerClass := "DELAY"
  triggerForm := "batu"
  triggerGloss := "delay"
  sentence := "a batu a mana graduate manang"
  gloss := "he delay he PFV.NEG graduate last.year"
  translation := "He delayed graduating last year."
  enNegator := "mana"
  enAspect := .pfv

/-- CANNOT WAIT trigger: *si batu* 'cannot wait'
    (@cite{jin-koenig-2021}, Table 5, ex. 25). -/
def cannotWaitExample : ENExample where
  triggerClass := "CANNOT WAIT"
  triggerForm := "si batu"
  triggerGloss := "IPFV.NEG wait"
  sentence := "ey si batu a ma si ka"
  gloss := "I IPFV.NEG wait he SBJV IPFV.NEG come"
  translation := "I cannot wait for him to come."
  enNegator := "si"
  enAspect := .ipfv

/-- HIDE trigger: *tugu* 'hide'. Zarma-Sonrai example
    (@cite{jin-koenig-2021}, §6.1.3, ex. 20).

    N.B. The negator *sinda* ('not.have') is a copular/possessive negative,
    not the imperfective marker *si* or perfective *mana*/*batu*. It falls
    outside the aspect-based EN negator selection system formalized in
    `enNegatorForAspect`. The `.ipfv` classification here is approximate. -/
def hideExample : ENExample where
  triggerClass := "HIDE"
  triggerForm := "tugu"
  triggerGloss := "hide"
  sentence := "a tugu ey se kang a sinda sida"
  gloss := "she hide I DAT that she not.have HIV"
  translation := "She hid from me that she was HIV positive."
  enNegator := "sinda"
  enAspect := .ipfv

def allExamples : List ENExample :=
  [delayExample, cannotWaitExample, hideExample]

-- ════════════════════════════════════════════════════
-- § 4. Aspect-Based Negator Selection
-- ════════════════════════════════════════════════════

/-- The EN negator is determined by the aspectual properties of the
    complement clause, not by the trigger class. This is a general
    property of Zarma-Sonrai negation, not specific to EN. -/
def enNegatorForAspect : ENAspect → String
  | .ipfv => ipfvNeg
  | .pfv  => pfvNeg2

theorem fear_uses_ipfv_neg : enNegatorForAspect .ipfv = "si" := rfl
theorem delay_uses_pfv_neg : enNegatorForAspect .pfv = "batu" := rfl

open Core (ENBlockingReason)

/-- Why WITHOUT and TOO…TO do not trigger EN in Zarma-Sonrai.

    WITHOUT is expressed analytically as "q not p" and TOO…TO as
    "too…so that…not" — in both cases, the negation is a necessary
    part of the meaning, not expletive (@cite{jin-koenig-2021}, §7). -/

def withoutBlocked : ENBlockingReason := .analyticNegation
def tooToBlocked : ENBlockingReason := .analyticNegation

end Fragments.ZarmaSonrai.Negation
