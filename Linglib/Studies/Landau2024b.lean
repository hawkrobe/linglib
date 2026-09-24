module

public import Linglib.Syntax.Minimalist.FormCopy
public import Linglib.Syntax.Control.Basic
public import Linglib.Fragments.Mixtec.SMPM.Pronouns

/-!
# Landau (2024): Empirical challenges to the Form-Copy Theory of Control

Landau assesses the Form Copy theory of obligatory control of Chomsky and colleagues, on which
the controlled subject is a silent copy of the controller: the two are merged separately as
structurally identical inscriptions, and Form Copy relates them as copies under c-command
(`Minimalist.SyntacticObject.copyRel`) within a phase. Two of his challenges follow from that
definition. Form Copy relates only structurally identical inscriptions, so it never relates a
lexical controller to a pronoun, yet in Gã, Bùlì and San Martín Peras Mixtec the controlled
subject must be an overt pronoun (`pronoun_not_mem_copyRel`). And Form Copy interprets copies
alike, which makes its dependency exhaustive, so the partial reading of a controlled subject is
not one Form Copy assigns (`not_isExhaustive_pcReading`): the theory must derive partial control
from the deletion of a *for*-subject instead, which Landau argues undergenerates.

## Implementation notes

The controlled subject of (46c) is the feminine clitic of the San Martín Peras Mixtec fragment.
The semantic clause of Form Copy, copies interpreted in exactly the same way, is exhaustive
control over the copy relation (`Control.IsExhaustive`).

## TODO

The challenges from reconstruction (§3), from the optionality of Form Copy (§4), from control
into phases (§5) and from control across the passive (§6.1).

## References

* [landau-2024b]
* [chomsky-etal-2023]
-/

@[expose] public section

namespace Landau2024b

open Minimalist SyntacticObject Control

/-- A token of the simple lexical item of category `c` selecting `sel`, pronounced `pf`. -/
def tok (c : Cat) (sel : SelStack) (pf : String) (i : ℕ) : LIToken :=
  ⟨.simple c sel (phonForm := pf), i⟩

/-! ### Controlled pronouns (46) -/

/-- *ña Juana*, the controller of (46c). -/
noncomputable def naJuana : SyntacticObject :=
  merge (leaf (tok .D [.N] "ña" 0)) (leaf (tok .N [] "Juana" 1))

/-- The controlled subject of (46c), the feminine clitic *=ñá*. -/
def nya : SyntacticObject := leaf (tok .D [] (Mixtec.SMPM.cl3 .feminine).form 2)

/-- Form Copy never makes the controlled pronoun of (46c) a copy of its lexical controller, in
any object: the two are not structurally identical. -/
theorem pronoun_not_mem_copyRel (s : SyntacticObject) : (naJuana, nya) ∉ s.copyRel :=
  fun h ↦ by simpa [naJuana, nya] using h.2.numNodes_eq

/-! ### Partial control (§7) -/

/-- *John*, the controller of (48a). -/
def john : SyntacticObject := leaf (tok .N [] "John" 0)

/-- *John* again, from a fresh token: the controlled subject of (48a) on the Form Copy theory. -/
def john' : SyntacticObject := leaf (tok .N [] "John" 3)

/-- (48a) *John arranged to meet at noon*, the controller and the controlled subject merged
separately into the theta positions of *arranged* and *meet*. -/
noncomputable def arrangedToMeet : SyntacticObject :=
  merge john (merge (leaf (tok .V [.T] "arranged" 1)) (merge (leaf (tok .T [.V] "to" 2))
    (merge john' (leaf (tok .V [] "meet at noon" 4)))))

/-- Form Copy relates the controller of (48a) to its controlled subject. -/
theorem john_mem_copyRel : (john, john') ∈ arrangedToMeet.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains]) (by simp [john, john', tok,
    StructurallyIdentical])

/-- The partial reading of (48a): the controlled subject denotes a group of John, `0`, and an
associate, `1`. -/
def pcReading (x : SyntacticObject) : Set ℕ := if x = john' then {0, 1} else {0}

/-- The partial reading is partial on the copy relation: the controlled subject's group strictly
contains John. -/
theorem isPartial_pcReading : IsPartial pcReading arrangedToMeet.copyRel :=
  ⟨john, john', john_mem_copyRel, by
    have hne : john ≠ john' := by simp [john, john', tok]
    simp only [pcReading, hne, ↓reduceIte]
    exact (Set.ssubset_iff_of_subset (by simp)).2 ⟨1, by simp, by simp⟩⟩

/-- So it is no interpretation Form Copy assigns, which gives copies one value: partial control
needs a source other than Form Copy (§7). -/
theorem not_isExhaustive_pcReading : ¬ IsExhaustive pcReading arrangedToMeet.copyRel :=
  fun h ↦ h.not_isPartial isPartial_pcReading

end Landau2024b
