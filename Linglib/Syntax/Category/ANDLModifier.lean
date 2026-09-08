/-!
# Aggressively non-D-linked wh-modifiers

*Wh-the-hell* and its kin (*the heck*, *in the world*, Mandarin *daodi*, Japanese *ittai*)
are wh-modifiers with a distribution bare wh-words lack ([pesetsky-1987]'s aggressively
non-D-linked phrases; [hoeksema-napoli-2008], [jackendoff-audring-2020] on the English
family). An entry records the one parameter on which [chan-shen-2026] separate English and
Singlish *the-hell* from Mandarin *daodi*: whether the modifier reaches its matrix scope
position only on the wh-phrase it adjoins to ([merchant-2002]) or by movement of its own
([chou-2012]). `ANDLModifier.Licensed` is the resulting scope condition, taking as a
parameter whether the host reaches that position, which a syntax of the host's question
supplies.

## References

* [pesetsky-1987]
* [merchant-2002]
* [chou-2012]
* [chan-shen-2026]
* [hoeksema-napoli-2008]
* [jackendoff-audring-2020]
-/

/-- How the modifier reaches its scope position: adjoined to the wh-head and carried by the
wh-phrase (English and Singlish *the-hell*, [merchant-2002]), or by movement of its own
(Mandarin *daodi*, [chou-2012]). -/
inductive ANDLModifier.Mobility where
  | parasitic
  | independent
  deriving DecidableEq, Repr

/-- An aggressively non-D-linked wh-modifier: form, gloss, and how it reaches its scope
position. -/
structure ANDLModifier where
  form : String
  gloss : String
  mobility : ANDLModifier.Mobility
  deriving DecidableEq, Repr

namespace ANDLModifier

/-- The modifier is licensed iff it reaches its matrix scope position: with its host, when the
host does, or on its own. -/
def Licensed (m : ANDLModifier) (hostReachesScope : Prop) : Prop :=
  hostReachesScope ∨ m.mobility = .independent

instance (m : ANDLModifier) (P : Prop) [Decidable P] : Decidable (Licensed m P) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable {m : ANDLModifier} (P : Prop)

/-- A parasitic modifier is licensed iff its host reaches the scope position. -/
theorem licensed_iff_of_parasitic (h : m.mobility = .parasitic) : Licensed m P ↔ P := by
  simp [Licensed, h]

/-- An independent modifier is licensed whatever its host does. -/
theorem licensed_of_independent (h : m.mobility = .independent) : Licensed m P :=
  Or.inr h

end ANDLModifier
