import Linglib.Theories.Syntax.Minimalist.Basic

/-!
# Verbal Decomposition
@cite{cuervo-2003} @cite{wood-2015} @cite{pylkkanen-2008}

Sub-eventive verb heads that decompose verbal structure into
fine-grained event components. Following @cite{wood-2015} and
@cite{pylkkanen-2008}, CAUSE is an independent head — separate
from both Voice (which introduces the external argument) and the
root-determined event structure (vGO, vBE).

Key decompositions:
- State: [vBE]
- Activity: [vDO]
- Inchoative: [vCAUSE, vGO, vBE] (anticausative: "the door opened")
- Causative: [vDO, vCAUSE, vGO, vBE] (transitive: "John opened the door")

Voice contributes vDO (the agent's activity); CAUSE is part of the root
structure, present in both causative and anticausative alternants.

Independent of applicative heads — used by Fission, EventStructureBridge,
and the Spanish fragment.

-/

namespace Minimalist

-- ============================================================================
-- § 1: Sub-Eventive Verb Heads
-- ============================================================================

/-- Sub-eventive verb heads from @cite{cuervo-2003}, extended with
    vCAUSE following @cite{wood-2015} and @cite{pylkkanen-2008}.

    - **vDO**: Dynamic subevent where an agent does something
    - **vCAUSE**: Causal relation between subevents (independent head;
      present in both causative and anticausative alternants)
    - **vGO**: Dynamic subevent of change (inchoative component)
    - **vBE**: Stative subevent of result state -/
inductive VerbHead where
  | vDO     -- Dynamic subevent (agent does something)
  | vCAUSE  -- Causal relation between subevents (@cite{wood-2015}, @cite{pylkkanen-2008})
  | vGO     -- Dynamic subevent of change
  | vBE     -- Stative subevent of result
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Event Composition Predicates
-- ============================================================================

/-- A verb's event-structural decomposition as a list of VerbHeads.

    Key patterns:
    - State: [vBE]
    - Activity: [vDO]
    - Inchoative: [vCAUSE, vGO, vBE] (anticausative: "the door opened")
    - Causative: [vDO, vCAUSE, vGO, vBE] (transitive: "John opened the door") -/
def isInchoative (heads : List VerbHead) : Bool :=
  heads.contains .vGO && heads.contains .vBE && !heads.contains .vDO

/-- Is this a causative (external cause + change + result)? -/
def isCausative (heads : List VerbHead) : Bool :=
  heads.contains .vDO && heads.contains .vGO && heads.contains .vBE

/-- Is this a simple state (vBE only)? -/
def isState (heads : List VerbHead) : Bool :=
  heads == [.vBE]

/-- Is this a simple activity (vDO only)? -/
def isActivity (heads : List VerbHead) : Bool :=
  heads == [.vDO]

/-- Does this decomposition contain a CAUSE head? -/
def hasCause (heads : List VerbHead) : Bool :=
  heads.contains .vCAUSE

/-- Is this an anticausative (CAUSE present, but no external agent)?
    Anticausatives have the causal structure but lack an agentive vDO.
    This is the key insight from @cite{wood-2015}: CAUSE is independent
    of Voice, so it can appear without an agent. -/
def isAnticausative (heads : List VerbHead) : Bool :=
  hasCause heads && heads.contains .vGO && !heads.contains .vDO

-- ============================================================================
-- § 3: Verification Theorems
-- ============================================================================

/-- Inchoative = change + result, no external cause. -/
theorem inchoative_is_go_be : isInchoative [.vGO, .vBE] = true := by decide

/-- Inchoative with CAUSE: [vCAUSE, vGO, vBE] is still inchoative (no vDO). -/
theorem inchoative_with_cause :
    isInchoative [.vCAUSE, .vGO, .vBE] = true := by decide

/-- Causative = external cause + change + result. -/
theorem causative_is_do_go_be : isCausative [.vDO, .vGO, .vBE] = true := by decide

/-- Causative with CAUSE head. -/
theorem causative_with_cause :
    isCausative [.vDO, .vCAUSE, .vGO, .vBE] = true := by decide

/-- Inchoative is NOT causative (no vDO). -/
theorem inchoative_not_causative : isCausative [.vGO, .vBE] = false := by decide

/-- Causative is NOT inchoative (has vDO). -/
theorem causative_not_inchoative : isInchoative [.vDO, .vGO, .vBE] = false := by decide

/-- A pure state is neither inchoative nor causative. -/
theorem state_neither :
    isInchoative [.vBE] = false ∧ isCausative [.vBE] = false := by decide

/-- An activity is neither inchoative nor causative. -/
theorem activity_neither :
    isInchoative [.vDO] = false ∧ isCausative [.vDO] = false := by decide

/-- CAUSE is present in both causative and anticausative alternants. -/
theorem cause_shared_across_alternation :
    hasCause [.vDO, .vCAUSE, .vGO, .vBE] = true ∧
    hasCause [.vCAUSE, .vGO, .vBE] = true := by decide

/-- Anticausative = CAUSE + change, no agent. -/
theorem anticausative_is_cause_go :
    isAnticausative [.vCAUSE, .vGO, .vBE] = true := by decide

/-- Causative with vDO is NOT anticausative. -/
theorem causative_not_anticausative :
    isAnticausative [.vDO, .vCAUSE, .vGO, .vBE] = false := by decide

end Minimalist
