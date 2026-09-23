module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# The attitude of a verb entry

The readers of a verb entry's attitude: its veridicality, whether it is doxastic or
preferential, and the valence of a preferential attitude.
-/

@[expose] public section

namespace Verb

/-- The veridicality of the verb's attitude, if it has one. -/
def veridicality? (v : Verb) : Option Doxastic.Veridicality := v.attitude.map (·.veridicality)

/-- The verb is a doxastic attitude. -/
def IsDoxastic (v : Verb) : Prop := ∃ a ∈ v.attitude, a.IsDoxastic

instance : DecidablePred IsDoxastic := fun _ ↦ inferInstanceAs (Decidable (∃ a ∈ _, _))

/-- The verb is a preferential attitude. -/
def IsPreferential (v : Verb) : Prop := ∃ a ∈ v.attitude, a.IsPreferential

instance : DecidablePred IsPreferential := fun _ ↦ inferInstanceAs (Decidable (∃ a ∈ _, _))

/-- The valence of the verb's preferential attitude, if it has one. -/
def preferentialValence? (v : Verb) : Option Preferential.Valence := v.attitude.bind (·.valence)

end Verb
