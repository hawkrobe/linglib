/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# The Control Signature

[landau-2013]'s OC signature ((74), §1.3): in a control construction,
(a) the controller(s) must be co-dependent(s) of the clause, and (b)
the controlled element (or part of it) must be interpreted as a bound
variable. Constructions displaying both clauses are obligatory control;
the mirror image — neither clause — is the NOC signature (§7.1). The
familiar OC criteria are *derived*: co-dependence excludes arbitrary,
long-distance, and non-c-commanding control and forces sloppy ellipsis
readings; variable binding excludes strict readings under
*only*-binding (`Signature.admits`).

Deliberately absent, per §1.3: obligatory *de se* is NOT criterial for
OC — it is a property of the attitude tier (`Control.Tier.isAttitude`;
the per-controller *de se*/*de te* table is encoded in
`Studies/Landau2015.lean`). Per §1.4, obligatory *nullness* of the
controlled element is not criterial either — whether a language spells
the controlled subject out is a vocabulary fact
(`Minimalist.MinimalPronoun.MinPronInventory.controlForm`), independent
of the signature; overt-PRO languages (Gã, SMPM) turn on exactly this
separation.
-/

namespace Control

/-- [landau-2013]'s control signature ((74)): is the controller a
    co-dependent of the controlled clause, and is the controlled
    element read as a bound variable? The co-dependence clause admits
    implicit, split, and (via "part of it") partial control. -/
structure Signature where
  /-- (74a): the controller(s) must be co-dependent(s) of the clause. -/
  controllerCodependent : Bool
  /-- (74b): the controlled element is interpreted as a bound variable. -/
  boundVariable : Bool
  deriving DecidableEq, Repr

namespace Signature

variable {s : Signature}

/-- Obligatory control: both clauses of the signature hold. -/
def Obligatory (s : Signature) : Prop :=
  s.controllerCodependent ∧ s.boundVariable

instance : Decidable s.Obligatory :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Non-obligatory control, the signature's mirror image (§7.1):
    neither clause holds. -/
def NonObligatory (s : Signature) : Prop :=
  ¬s.controllerCodependent ∧ ¬s.boundVariable

instance : Decidable s.NonObligatory :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The signature determined by whether a clause type licenses
    noncoreferential subjects: free reference fails both clauses,
    obligatory coreference forces both. -/
def ofNoncoreferential (noncoreferential : Bool) : Signature :=
  ⟨!noncoreferential, !noncoreferential⟩

@[simp] theorem obligatory_ofNoncoreferential {b : Bool} :
    (ofNoncoreferential b).Obligatory ↔ b = false := by
  cases b <;> simp [ofNoncoreferential, Obligatory]

/-- The configurations and readings whose availability separates OC
    from NOC ([landau-2013] §1.3): each is excluded by a clause of the
    signature and available under the NOC signature (§7.1). -/
inductive Criterion where
  /-- Arbitrary control ((75a)) -/
  | arbitraryControl
  /-- A long-distance controller ((75b)) -/
  | longDistanceControl
  /-- A non-c-commanding controller ((75c)) -/
  | nonCCommandingControl
  /-- A strict reading under ellipsis ((76)) -/
  | strictEllipsis
  /-- A strict (non-bound-variable) reading under *only*-binding
      ((78)–(79)) -/
  | strictUnderOnly
  deriving DecidableEq, Repr

/-- Which criterial configurations a signature admits: co-dependence
    (74a) excludes the three antecedence configurations and strict
    ellipsis readings; variable binding (74b) excludes strict
    *only*-readings. -/
def admits (s : Signature) : Criterion → Bool
  | .strictUnderOnly => !s.boundVariable
  | _                => !s.controllerCodependent

/-- A signature is the OC signature iff it admits nothing criterial. -/
theorem obligatory_iff_admits_none :
    s.Obligatory ↔ ∀ cr, s.admits cr = false := by
  constructor
  · rintro ⟨hc, hb⟩ cr
    cases cr <;> simp_all [admits]
  · intro h
    exact ⟨by simpa [admits] using h .arbitraryControl,
           by simpa [admits] using h .strictUnderOnly⟩

/-- A signature is the NOC signature iff it admits everything
    criterial. -/
theorem nonObligatory_iff_admits_all :
    s.NonObligatory ↔ ∀ cr, s.admits cr = true := by
  constructor
  · rintro ⟨hc, hb⟩ cr
    cases cr <;> simp_all [admits]
  · intro h
    exact ⟨by simpa [admits] using h .arbitraryControl,
           by simpa [admits] using h .strictUnderOnly⟩

end Signature

end Control
