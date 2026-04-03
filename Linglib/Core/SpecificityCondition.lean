import Linglib.Core.Definiteness

/-!
# Specificity Condition
@cite{fiengo-higginbotham-1981} @cite{fiengo-1987} @cite{huang-1982b} @cite{shen-huang-2026}

A variable inside a specific DP cannot be bound by an operator outside
that DP. This is a binding-theoretic constraint on wh-dependencies,
independent of movement or the PIC.

## Two notions of "specificity"

@cite{fiengo-1987} ties specificity to Heim's familiarity theory of
definiteness: a specific nominal is one whose referent is "already familiar
at the current stage of the conversation." Demonstrative-marked DPs are
paradigmatically specific in this sense.

@cite{cheng-sybesma-1999} use "specificity" differently — for them it is
about whether an indefinite nominal gets a particular-individual reading.
Bounded predicates (e.g., perfective VPs) force a "specific" reading on
indefinite objects, but these DPs are NOT islands for subextraction.
@cite{shen-huang-2026} §2.2 argue that the extraction-relevant notion is
Fiengo's familiarity-based specificity, not Cheng & Sybesma's.

## Coverage

The Specificity Condition accounts for:

1. Definite island effects in wh-movement (English: @cite{chomsky-1973},
   @cite{fiengo-higginbotham-1981})
2. Definite island effects in wh-in-situ (Mandarin Chinese:
   @cite{huang-1982b}, @cite{shen-huang-2026})
3. Wh-indefinite sensitivity to demonstratives in Chinese
   (@cite{li-1992}, @cite{shen-huang-2026} Experiment 3)
4. Island effects for relativization (@cite{ross-1967})
5. Island effects for unselective binding (@cite{li-1992})

The PIC independently constrains overt movement; the Specificity Condition
independently constrains binding. Both are needed for full crosslinguistic
coverage (@cite{shen-huang-2026} §4.1).
-/

namespace Core.SpecificityCondition

open Core.Definiteness

-- ============================================================================
-- §1. Specificity
-- ============================================================================

/-- A DP is specific iff its referent is discourse-familiar in the sense of
@cite{fiengo-1987}: "already familiar at the current stage of the
conversation."

Demonstrative-marked DPs are specific; indefinite DPs (introduced with
*a/an*, *one-CL*) are nonspecific. This is the extraction-relevant notion,
not @cite{cheng-sybesma-1999}'s predicate-dependent specificity. -/
def isSpecific (d : Definiteness) : Bool :=
  match d with
  | .definite   => true
  | .indefinite => false

/-- Demonstratives project the familiarity/strong-article layer, hence
are always specific for purposes of the Specificity Condition. -/
theorem demonstratives_are_specific :
    isSpecific .definite = true := rfl

-- ============================================================================
-- §2. The Specificity Condition
-- ============================================================================

/-- The kind of operator attempting to bind into the DP. -/
inductive ExternalOperator where
  /-- Overt wh-movement leaves a trace/copy inside the DP -/
  | whTrace
  /-- Covert question operator binds an in-situ wh-phrase
      (@cite{li-1992}, @cite{aoun-li-1993}) -/
  | questionOperator
  /-- Existential closure binds a wh-indefinite
      (@cite{li-1992}: wh-phrases as indefinites) -/
  | existentialClosure
  /-- Relativization operator -/
  | relOperator
  /-- Focus operator -/
  | focusOperator
  deriving DecidableEq, Repr

/-- Whether an external operator's binding into a DP is blocked by the
Specificity Condition.

    @cite{fiengo-higginbotham-1981}: a variable inside a specific DP
    cannot be bound by an operator outside the DP.

    @cite{shen-huang-2026}: this condition applies uniformly to both
    overt wh-movement (where the "variable" is a trace) and wh-in-situ
    (where the "variable" is the in-situ wh-phrase itself, bound by
    a covert question operator).

    Returns `true` when binding is BLOCKED. -/
def blocked (_op : ExternalOperator) (dpSpecificity : Definiteness) : Bool :=
  isSpecific dpSpecificity

/-- Specificity Condition blocks binding into definite DPs. -/
theorem blocks_definite (op : ExternalOperator) :
    blocked op .definite = true := rfl

/-- Specificity Condition allows binding into indefinite DPs. -/
theorem allows_indefinite (op : ExternalOperator) :
    blocked op .indefinite = false := rfl

/-- The Specificity Condition is insensitive to operator type — it blocks
all external operators equally when the DP is specific. This is the
key prediction that distinguishes it from the PIC, which is sensitive
to movement type. -/
theorem operator_insensitive (op₁ op₂ : ExternalOperator) (d : Definiteness) :
    blocked op₁ d = blocked op₂ d := rfl

-- ============================================================================
-- §3. Interaction with wh-indefinites (@cite{li-1992})
-- ============================================================================

/-- In Chinese, wh-phrases can be interpreted as indefinites ("something",
"someone") when bound by an existential closure operator. @cite{li-1992}
reports that this indefinite reading is blocked when the wh-phrase appears
inside a demonstrative-marked (specific) DP.

    (i)  Wǒ yǐwéi tā ná-le [yì-zhāng shénme rén de xiàngpiàn]. ✓
         'I thought he took away a picture of someone.'
    (ii) *Wǒ yǐwéi tā ná-le [nà-zhāng shénme rén de xiàngpiàn]. ✗
         Intended: 'I thought he took away that picture of someone.'

@cite{shen-huang-2026} Experiment 3 confirms this contrast experimentally
(β = −0.48, s.e. = 0.15, t = −3.32, p < 0.01). -/
theorem wh_indefinite_blocked_in_specific_dp :
    blocked .existentialClosure .definite = true := rfl

theorem wh_indefinite_allowed_in_nonspecific_dp :
    blocked .existentialClosure .indefinite = false := rfl

end Core.SpecificityCondition
