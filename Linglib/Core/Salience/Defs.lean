import Linglib.Features.Prominence
import Linglib.Core.Discourse.Accessibility
import Linglib.Core.InformationStructure

/-!
# Salience — Flat Dimension Typeclasses
@cite{ariel-2001} @cite{aissen-2003} @cite{kratzer-selkirk-2020}

A unified interface to the three independent salience dimensions used
across linglib:

* **Accessibility** (@cite{ariel-2001}) — how mentally available a
  referent is, on the 18-level Accessibility Marking Scale.
* **Animacy** (@cite{aissen-2003}, @cite{just-2024}) — referent
  prominence by humanness.
* **Discourse status** (@cite{kratzer-selkirk-2020}) — given vs new vs
  focused.

These three dimensions are *not unified into a single Salience scale*
on purpose. Animacy and accessibility correlate but diverge (humans
can be inaccessible newcomers; inanimates can be highly accessible
topics); discourse status interacts with both but is measured along an
orthogonal axis. Bundling them would obscure the divergences that the
literature carefully documents.

What this module provides instead is a **flat collection of typeclass
projections** so that downstream theories can ask "what is X's
animacy / accessibility / status?" without committing to a particular
representation. The trivial identity instances on the underlying
types make these classes a no-op when the data is already in the
canonical form, and a hook for extension when a theory needs to
project a richer object down onto one of the dimensions.
-/

set_option autoImplicit false

namespace Core.Salience

open Features.Prominence
open Core.Discourse.Accessibility
open Core.InformationStructure

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

/-- Things that have a discourse status (given/new/focused). -/
class HasDiscourseStatus (α : Type) where
  discourseStatus : α → DiscourseStatus

-- ════════════════════════════════════════════════════
-- § Identity instances on the underlying levels
-- ════════════════════════════════════════════════════

instance : HasAccessibility AccessibilityLevel where
  accessibility := id

instance : HasAnimacy AnimacyLevel where
  animacy := id

instance : HasDiscourseStatus DiscourseStatus where
  discourseStatus := id

end Core.Salience
