import Linglib.Theories.Minimalism.Core.Basic

/-!
# Applicative Heads (Pylkkänen 2008; Cuervo 2003)

Applicative heads introduce applied arguments (benefactives, goals,
sources) into the verbal structure. The high/low distinction from
Pylkkänen (2008) determines whether the applied argument relates to
the event as a whole (high) or to the theme (low).

Cuervo (2003) decomposes Spanish verbal structure into sub-eventive
heads vDO, vGO, vBE, giving a finer-grained picture of event composition
that connects directly to the causative alternation.

## References

- Pylkkänen, L. (2008). *Introducing Arguments*. MIT Press.
- Cuervo, M. C. (2003). *Datives at Large*. PhD dissertation, MIT.
- Muñoz Pérez, C. (2026). Stylistic applicatives: A lens into the
  nature of anticausative SE. *Glossa* 11(1).
-/

namespace Minimalism

-- ============================================================================
-- § 1: Applicative Types (Pylkkänen 2008)
-- ============================================================================

/-- High vs low applicatives (Pylkkänen 2008).

    - **High**: Above VP, relates applied argument to the event
      (affected/benefactive: "I baked him a cake")
    - **Low**: Below VP, relates applied argument to the theme
      (transfer/source: "I sent him a letter") -/
inductive ApplType where
  | high   -- Above VP: affected/benefactive (Pylkkänen 2008)
  | low    -- Below VP: transfer/source (Pylkkänen 2008)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Verbal Decomposition (Cuervo 2003)
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
-- § 3: Event Composition Templates
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
-- § 4: Verification Theorems
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
