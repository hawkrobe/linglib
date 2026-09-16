import Linglib.Syntax.Category.Verb.Defs

/-!
# The causative of a verb entry

A verb entry is causative when it records a causative, and asserts sufficiency when that
causative does (`Causative.AssertsSufficiency`), as *make* does and *cause* does not.
-/

namespace Verb

/-- The verb is a causative. -/
def IsCausative (v : Verb) : Prop := v.causative ≠ none

instance : DecidablePred IsCausative := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The verb's causative asserts sufficiency, as *make* does. -/
def AssertsSufficiency (v : Verb) : Prop := ∃ c ∈ v.causative, c.AssertsSufficiency

instance : DecidablePred AssertsSufficiency := fun _ ↦ inferInstanceAs (Decidable (∃ c ∈ _, _))

end Verb
