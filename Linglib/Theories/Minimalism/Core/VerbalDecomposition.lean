import Linglib.Theories.Minimalism.Core.Basic

/-!
# Verbal Decomposition (Cuervo 2003)

Sub-eventive verb heads that decompose verbal structure into
fine-grained event components. This decomposition connects directly
to the causative alternation: inchoative verbs have [vGO, vBE],
causatives add [vDO] for the external cause.

Independent of applicative heads — used by Fission, EventStructureBridge,
and the Spanish fragment.

## References

- Cuervo, M. C. (2003). *Datives at Large*. PhD dissertation, MIT.
-/

namespace Minimalism

-- ============================================================================
-- § 1: Sub-Eventive Verb Heads
-- ============================================================================

/-- Sub-eventive verb heads from Cuervo (2003).

    Spanish verbal structure decomposes into:
    - **vDO**: Dynamic subevent where an agent does something
    - **vGO**: Dynamic subevent of change (inchoative component)
    - **vBE**: Stative subevent of result state -/
inductive VerbHead where
  | vDO   -- Dynamic subevent (agent does something)
  | vGO   -- Dynamic subevent of change
  | vBE   -- Stative subevent of result
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Event Composition Predicates
-- ============================================================================

/-- A verb's event-structural decomposition as a list of VerbHeads.

    Key patterns:
    - State:         [vBE]
    - Activity:      [vDO]
    - Inchoative:    [vGO, vBE]   (anticausative: "the door opened")
    - Causative:     [vDO, vGO, vBE] (transitive: "John opened the door") -/
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

-- ============================================================================
-- § 3: Verification Theorems
-- ============================================================================

/-- Inchoative = change + result, no external cause. -/
theorem inchoative_is_go_be : isInchoative [.vGO, .vBE] = true := by native_decide

/-- Causative = external cause + change + result. -/
theorem causative_is_do_go_be : isCausative [.vDO, .vGO, .vBE] = true := by native_decide

/-- Inchoative is NOT causative (no vDO). -/
theorem inchoative_not_causative : isCausative [.vGO, .vBE] = false := by native_decide

/-- Causative is NOT inchoative (has vDO). -/
theorem causative_not_inchoative : isInchoative [.vDO, .vGO, .vBE] = false := by native_decide

/-- A pure state is neither inchoative nor causative. -/
theorem state_neither :
    isInchoative [.vBE] = false ∧ isCausative [.vBE] = false := by native_decide

/-- An activity is neither inchoative nor causative. -/
theorem activity_neither :
    isInchoative [.vDO] = false ∧ isCausative [.vDO] = false := by native_decide

end Minimalism
