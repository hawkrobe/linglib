import Linglib.Features.Prominence
import Linglib.Features.Accessibility

/-!
# Salience — Flat Dimension Typeclasses
@cite{ariel-2001} @cite{aissen-2003}

A unified interface to the salience dimensions used across linglib:

* **Accessibility** (@cite{ariel-2001}) — how mentally available a
  referent is, on the 18-level Accessibility Marking Scale.
* **Animacy** (@cite{aissen-2003}, @cite{just-2024}) — referent
  prominence by humanness.

These dimensions are *not unified into a single Salience scale* on
purpose. Animacy and accessibility correlate but diverge (humans can
be inaccessible newcomers; inanimates can be highly accessible
topics). Bundling them would obscure the divergences that the
literature carefully documents.

What this module provides instead is a **flat collection of typeclass
projections** so that downstream theories can ask "what is X's
animacy / accessibility?" without committing to a particular
representation. The trivial identity instances on the underlying
types make these classes a no-op when the data is already in the
canonical form, and a hook for extension when a theory needs to
project a richer object down onto one of the dimensions.

Per-axis typeclasses for the four Krifka IS notions (`HasGivenness`,
`HasFocus`, `HasTopic`, `HasAtIssue`) would naturally sit alongside
`HasAccessibility` and `HasAnimacy`; add them when a real
abstraction-consumer emerges, per mathlib's small-typeclass convention.
-/

set_option autoImplicit false

namespace Core.Salience

open Features.Prominence
open Features

-- ════════════════════════════════════════════════════
-- § Flat dimension classes
-- ════════════════════════════════════════════════════

/-- Things that have an accessibility level on
    @cite{ariel-2001}'s 18-level scale. -/
class HasAccessibility (α : Type) where
  accessibility : α → AccessibilityLevel

/-- Things that have an animacy level on
    @cite{aissen-2003}'s 3-level scale. -/
class HasAnimacy (α : Type) where
  animacy : α → AnimacyLevel

-- ════════════════════════════════════════════════════
-- § Identity instances on the underlying levels
-- ════════════════════════════════════════════════════

instance : HasAccessibility AccessibilityLevel where
  accessibility := id

instance : HasAnimacy AnimacyLevel where
  animacy := id

end Core.Salience
