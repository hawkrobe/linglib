module

public import Linglib.Syntax.Minimalist.Ellipsis

/-!
# Benz and Salzmann 2025: N-stranding NP-ellipsis in German

This file formalizes the argument of [benz-salzmann-2025] that German has N-stranding
NP-ellipsis. [liptak-saab-2014] take the absence of such ellipsis in Spanish as evidence that the
noun does not leave NP: a postnominal PP cannot be recovered in *Juan habló con tres estudiantes de
física y yo hablé con dos*. Benz and Salzmann observe that in those examples the numeral is
contrastive and the noun is not; make the noun contrastive and recovery becomes possible in German,
English and Spanish alike. The [E] feature can then sit on n, deleting only NP while the noun
survives in its raised position — the nominal counterpart of V-stranding VP-ellipsis.

The nominal spine is `Minimalist.NominalSpinePosition`, with an adjunction position for
prenominal modifiers alongside the head positions: that distinction is what the paper's evidence
against deleting individual constituents turns on, and it is why the spine is not stated over the
`Cat` positions of the extended projection.

## Main definitions

* `nStrandingNPE`, `numPEllipsis`: [E] on n and on D, beside the substrate's
  `Minimalist.Ellipsis.nPEllipsis`, [E] on Num.
* `ePositionOfContrast`: the contrast condition on [E] placement.

## Main results

* `n_stranding_is_xStranding`: N-to-n movement instantiates X-stranding.
* `no_individual_prenominal_deletion`, `no_individual_numeral_deletion`: no [E] position deletes a
  prenominal modifier while sparing the noun.
* `postnominal_all_or_nothing`: the only [E] position recovering a postnominal dependent deletes
  every one of them.
* `contrast_governs_recovery`: a postnominal dependent is recoverable exactly when the noun is
  contrastive.
* `gender_parallels_voice`: the categorizer is external under N-stranding as Voice is under VPE.

## References

* [benz-salzmann-2025]
* [liptak-saab-2014]
* [merchant-2001]
* [merchant-2013]
-/

@[expose] public section

namespace BenzSalzmann2025

open Minimalist Minimalist.Ellipsis

/-! ### [E] positions on the nominal spine -/

/-- N-stranding NP-ellipsis: [E] on n, deleting NP alone. The noun survives in its raised
position, and prenominal modifiers, being outside n's complement, survive with it. -/
def nStrandingNPE : Ellipsis NominalSpinePosition := ⟨.n⟩

/-- NumP-ellipsis: [E] on D, leaving only the determiner. -/
def numPEllipsis : Ellipsis NominalSpinePosition := ⟨.D⟩

/-! ### N-stranding -/

/-- N-to-n movement instantiates X-stranding: the base position of the noun lies in n's
complement while n itself is external, so [E] on n deletes NP and spares the moved noun
(§1.1). -/
theorem n_stranding_is_xStranding :
    External NominalSpinePosition.n NominalSpinePosition.n ∧
      InDomain NominalSpinePosition.N NominalSpinePosition.n :=
  ⟨external_self _, by decide⟩

/-- The clausal and nominal patterns are the same theorem at the categorizer of each extended
projection: V is to v as N is to n. -/
theorem clausal_nominal_parallel :
    InDomain SpinePosition.V SpinePosition.v ∧
      InDomain NominalSpinePosition.N NominalSpinePosition.n := by decide

/-- Under N-stranding the noun's dependents go and everything above n stays: the postnominal PP of
*zwei Studenten der Physik* is recovered in *zwei Professoren*, while the numeral and determiner
are pronounced ((6a)). -/
theorem nStranding_domain :
    nStrandingNPE.Deletes .N ∧ nStrandingNPE.Spares .npAdjunct ∧ nStrandingNPE.Spares .n ∧
      nStrandingNPE.Spares .Num ∧ nStrandingNPE.Spares .D := by decide

/-! ### Against deleting individual constituents -/

/-- No [E] position deletes a prenominal modifier while sparing the noun, since the noun lies in
the complement of every head that dominates the modifier: *das schönste Auto … das schönste
Motorrad* is out on the elided-adjective reading ((25a)). -/
theorem no_individual_prenominal_deletion {p : NominalSpinePosition}
    (h : InDomain NominalSpinePosition.npAdjunct p) : InDomain NominalSpinePosition.N p :=
  ⟨(by decide : NominalSpinePosition.N < .npAdjunct).trans h.1, fun e ↦ by cases e⟩

/-- The same holds for numerals, since only [E] on D puts Num in the deletion domain, and that
deletes the noun too ((25b)). -/
theorem no_individual_numeral_deletion {p : NominalSpinePosition}
    (h : InDomain NominalSpinePosition.Num p) :
    InDomain NominalSpinePosition.N p :=
  ⟨(by decide : NominalSpinePosition.N < .Num).trans h.1, fun e ↦ by cases e⟩

/-- Deleting a postnominal dependent requires deleting the noun's whole complement, so if one
postnominal modifier is pronounced no other can be recovered ((28a)) while eliding both is fine
((28b)). -/
theorem postnominal_all_or_nothing (e : Ellipsis NominalSpinePosition) (h : e.Deletes .N) :
    ∀ p, p ≤ .N → e.Deletes p := by
  intro p hp
  cases p <;> first | exact h | exact absurd hp (by decide)

/-! ### The contrast condition -/

/-- [E] sits on n when the noun is contrastive and higher when it is not (§2.1, motivated by
(27)). -/
def ePositionOfContrast (nounContrastive : Bool) : Ellipsis NominalSpinePosition :=
  if nounContrastive then nStrandingNPE else nPEllipsis

/-- A postnominal dependent of the noun is recoverable exactly when the noun is contrastive: with
contrast the noun survives while its complement is deleted, without it the noun is deleted along
with the dependent — the difference between (6a) and Spanish (5), and between (26b) and (27). -/
theorem contrast_governs_recovery (b : Bool) :
    (ePositionOfContrast b).Deletes .N ∧ ((ePositionOfContrast b).Spares .n ↔ b = true) := by
  cases b <;> exact ⟨by decide, by decide⟩

/-! ### Ellipsis height and mismatches -/

/-- German N-stranding deletes strictly less than the Spanish configuration: the categorizer and
the prenominal modifiers survive the one and not the other. -/
theorem german_smaller_domain_than_spanish :
    nStrandingNPE.Spares .npAdjunct ∧ nPEllipsis.Deletes .npAdjunct ∧
      nStrandingNPE.Spares .n ∧ nPEllipsis.Deletes .n := by decide

/-- Gender mismatches pattern with voice mismatches: the head bearing the feature is external
exactly when [E] sits on it. Gender lives on n, which survives N-stranding but not nP-ellipsis,
as Voice survives VP-ellipsis but not sluicing (§3). -/
theorem gender_parallels_voice :
    nStrandingNPE.Spares .n ∧ nPEllipsis.Deletes .n ∧
      vpEllipsis.Tolerates .voice ∧ ¬ sluicing.Tolerates .voice := by decide

end BenzSalzmann2025
