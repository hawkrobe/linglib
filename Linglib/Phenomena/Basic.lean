/-
# Linglib.Phenomena.Basic (Re-export)

This module re-exports from `Linglib.Phenomena.Core.Basic` for backwards compatibility.
New code should import `Linglib.Phenomena.Core.Basic` directly.
-/

import Linglib.Phenomena.Core.Basic

-- Re-export everything
export MinimalPair (grammatical ungrammatical clauseType description citation)
export PhenomenonData (name pairs generalization)
