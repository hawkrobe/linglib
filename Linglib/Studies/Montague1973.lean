import Linglib.Fragments.English.Toy

/-!
# Montague (1973) [montague-1973]

Compositional truth conditions by direct function application: each
predication over the PTQ-style toy fragment receives its truth value
from the `ToyLexicon` denotations alone.
-/

namespace Montague1973

open Semantics.Montague
open ToyLexicon

/-! ## Intransitive predication -/

theorem john_sleeps : sleeps_sem john_sem := trivial
theorem mary_not_sleeps : ¬sleeps_sem mary_sem := id
theorem john_laughs : laughs_sem john_sem := trivial
theorem mary_laughs : laughs_sem mary_sem := trivial

/-! ## Transitive predication -/

theorem john_sees_mary : sees_sem mary_sem john_sem := trivial
theorem mary_sees_john : sees_sem john_sem mary_sem := trivial
theorem john_not_sees_john : ¬sees_sem john_sem john_sem := id
theorem john_eats_pizza : eats_sem ToyEntity.pizza john_sem := trivial
theorem john_not_eats_mary : ¬eats_sem mary_sem john_sem := id
theorem mary_eats_pizza : eats_sem ToyEntity.pizza mary_sem := trivial
theorem john_reads_book : reads_sem ToyEntity.book john_sem := trivial

/-- Predication discriminates individuals in vs. out of the extension. -/
theorem intransitive_contrast :
    sleeps_sem john_sem ∧ ¬sleeps_sem mary_sem :=
  ⟨trivial, id⟩

/-- Transitive predication discriminates ordered pairs. -/
theorem transitive_contrast :
    sees_sem mary_sem john_sem ∧ ¬sees_sem john_sem john_sem :=
  ⟨trivial, id⟩

end Montague1973
