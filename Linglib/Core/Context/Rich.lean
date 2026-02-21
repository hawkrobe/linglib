import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts
import Linglib.Core.Evidence

/-!
# Rich Context

`RichContext` extends `KContext` with a domain of accessible worlds and an
evidential source. This supports two phenomena that plain `KContext` cannot
express:

1. **Domain expansion** (Condoravdi 2002, Mizuno): backward temporal shifts
   expand the set of historical alternatives because more futures branch from
   earlier times.

2. **Evidential perspective** (Cumming 2026): the evidence grounding an
   assertion has a source type (direct, hearsay, inference) that interacts
   with tense morphology.

## Key Types

- `RichContext W E P T` — KContext + `domain : Set W` + `evidence : EvidentialSource`
- `KContext.toRich` — lift with trivial domain (`Set.univ`) and default evidence
- `DomainExpanding` — property of a shift: it expands the domain
- `hpShift` — historical present temporal shift (backward time + domain expansion)

## References

- Condoravdi, M. (2002). Temporal interpretation of modals.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
- Aikhenvald, A. Y. (2004). Evidentiality. OUP.
-/

namespace Core.Context

open Core.Context (KContext ContextTower ContextShift)
open Core.Evidence

-- ════════════════════════════════════════════════════════════════
-- § Rich Context
-- ════════════════════════════════════════════════════════════════

/-- A rich context: a Kaplanian context extended with a modal domain
    (the set of worlds accessible for modal evaluation) and an evidential
    source (how the speaker knows what they assert).

    The `domain` field tracks the set of possible worlds available for
    modal/temporal quantification. Under branching time, moving backward
    in time expands this set (more futures branch from earlier times).

    The `evidence` field tracks the evidential source for the assertion,
    connecting to Cumming's (2026) tense-evidential constraints. -/
structure RichContext (W : Type*) (E : Type*) (P : Type*) (T : Type*) where
  /-- The underlying Kaplanian context -/
  base : KContext W E P T
  /-- The set of accessible worlds (modal domain) -/
  domain : Set W
  /-- The evidential source for the current assertion -/
  evidence : EvidentialSource

section RichContextOps

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- Project back to a KContext (forget domain and evidence). -/
def RichContext.toKContext (rc : RichContext W E P T) : KContext W E P T := rc.base

/-- Agent of the rich context. -/
def RichContext.agent (rc : RichContext W E P T) : E := rc.base.agent

/-- World of the rich context. -/
def RichContext.world (rc : RichContext W E P T) : W := rc.base.world

/-- Time of the rich context. -/
def RichContext.time (rc : RichContext W E P T) : T := rc.base.time

/-- Addressee of the rich context. -/
def RichContext.addressee (rc : RichContext W E P T) : E := rc.base.addressee

/-- Position of the rich context. -/
def RichContext.position (rc : RichContext W E P T) : P := rc.base.position

-- ════════════════════════════════════════════════════════════════
-- § KContext Lift
-- ════════════════════════════════════════════════════════════════

/-- Lift a `KContext` to a `RichContext` with the trivial (universal) domain
    and default direct evidence. This is the root-clause default: no modal
    restriction, speaker has direct evidence. -/
def KContext.toRich (c : KContext W E P T) : RichContext W E P T where
  base := c
  domain := Set.univ
  evidence := .direct

/-- The trivial lift has universal domain. -/
theorem KContext.toRich_domain (c : KContext W E P T) :
    c.toRich.domain = Set.univ := rfl

/-- The trivial lift preserves the base context. -/
theorem KContext.toRich_base (c : KContext W E P T) :
    c.toRich.base = c := rfl

-- ════════════════════════════════════════════════════════════════
-- § Domain-Expanding Shifts
-- ════════════════════════════════════════════════════════════════

/-- A context shift is domain-expanding if it can only enlarge the
    accessible-world set, never shrink it.

    This captures Condoravdi's (2002) observation: backward temporal
    shifts expand the historical alternatives because more futures
    branch from earlier times. -/
def DomainExpanding (σ : ContextShift (RichContext W E P T)) : Prop :=
  ∀ (rc : RichContext W E P T), rc.domain ⊆ (σ.apply rc).domain

-- ════════════════════════════════════════════════════════════════
-- § HP Shift (Historical Present)
-- ════════════════════════════════════════════════════════════════

/-- Historical present (HP) temporal shift: moves time backward and
    expands the domain to include a superset of the original worlds.

    The `expandedDomain` parameter makes the expansion explicit:
    the caller provides the larger domain, and the shift installs it.
    In the branching-time setting, this would be `historicalBase` at
    the earlier time. -/
def hpShift (newTime : T) (expandedDomain : Set W) :
    ContextShift (RichContext W E P T) where
  apply := λ rc => {
    base := { rc.base with time := newTime }
    domain := expandedDomain
    evidence := rc.evidence
  }
  label := .temporal

/-- The HP shift is domain-expanding when the provided domain is
    a superset of the original. -/
theorem hpShift_expanding (newTime : T) (expandedDomain : Set W)
    (h : ∀ (rc : RichContext W E P T), rc.domain ⊆ expandedDomain) :
    DomainExpanding (hpShift (E := E) (P := P) newTime expandedDomain) := by
  intro rc
  exact h rc

/-- HP shift preserves the agent. -/
theorem hpShift_preserves_agent (newTime : T) (expandedDomain : Set W)
    (rc : RichContext W E P T) :
    ((hpShift (E := E) (P := P) newTime expandedDomain).apply rc).agent = rc.agent := rfl

/-- HP shift changes the time. -/
theorem hpShift_changes_time (newTime : T) (expandedDomain : Set W)
    (rc : RichContext W E P T) :
    ((hpShift (E := E) (P := P) newTime expandedDomain).apply rc).time = newTime := rfl

-- ════════════════════════════════════════════════════════════════
-- § Evidential Shift
-- ════════════════════════════════════════════════════════════════

/-- Shift the evidential source. Used when an embedding operator changes
    the evidence type (e.g., hearsay report changes direct → hearsay). -/
def evidentialSourceShift (newSource : EvidentialSource) :
    ContextShift (RichContext W E P T) where
  apply := λ rc => { rc with evidence := newSource }
  label := .evidential

/-- Evidential source shift preserves the domain. -/
theorem evidentialSourceShift_preserves_domain
    (src : EvidentialSource) (rc : RichContext W E P T) :
    ((evidentialSourceShift (W := W) (E := E) (P := P) (T := T) src).apply rc).domain =
      rc.domain := rfl

end RichContextOps

end Core.Context
