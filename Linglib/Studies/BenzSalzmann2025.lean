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

The nominal spine instantiates the substrate's `DeletionSpine`, with an adjunction position for
prenominal modifiers alongside the head positions: that distinction is what the paper's evidence
against deleting individual constituents turns on, and it is why this spine is stated here rather
than over the `Cat` positions of the extended projection.

## Main definitions

* `NominalSpinePosition`, `NominalEllipsis`: the nominal spine and an [E] position on it.
* `nStrandingNPE`, `nPEllipsis`, `numPEllipsis`: [E] on n, on Num, and on D.
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

/-! ### The nominal spine -/

/-- Positions of the nominal extended projection, lowest first. `npAdjunct` is the site of
prenominal modifiers, inside nP but outside n's complement, the nominal counterpart of the clausal
spine's VP-adjunction site. -/
inductive NominalSpinePosition
  /-- The lexical noun and its postnominal dependents. -/
  | N
  /-- Prenominal modifiers: adjectives and, for the paper's purposes, numerals' host positions. -/
  | npAdjunct
  /-- The categorizer, which hosts gender and is the landing site of N-movement. -/
  | n
  /-- Number. -/
  | Num
  /-- The determiner. -/
  | D
  deriving DecidableEq, Repr

namespace NominalSpinePosition

/-- Height in the spine. -/
def rank : NominalSpinePosition → ℕ
  | .N => 0
  | .npAdjunct => 1
  | .n => 2
  | .Num => 3
  | .D => 4

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder NominalSpinePosition := .lift' rank rank_injective

/-- `d` lies in the complement of `p` when it is below `p`, except that prenominal modifiers are
not in n's complement, though they are in Num's. -/
def InDomain (d p : NominalSpinePosition) : Prop := d < p ∧ (d = .npAdjunct → .n < p)

instance : DecidableRel InDomain := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DeletionSpine NominalSpinePosition where
  InDomain := InDomain
  not_inDomain_self p h := lt_irrefl p h.1
  inDomain_mono _ _ _ h := fun ⟨hd, ha⟩ ↦ ⟨hd.trans_le h, fun e ↦ (ha e).trans_le h⟩

instance : DecidableRel (DeletionSpine.InDomain (α := NominalSpinePosition)) :=
  inferInstanceAs (DecidableRel InDomain)

end NominalSpinePosition

/-- An [E] feature on a head of the nominal spine; its deletion domain is that head's
complement. -/
structure NominalEllipsis where
  ePosition : NominalSpinePosition
  deriving DecidableEq, Repr

/-- `e.Deletes d` when the position `d` falls in the deletion domain. -/
def NominalEllipsis.Deletes (e : NominalEllipsis) (d : NominalSpinePosition) : Prop :=
  InDomain d e.ePosition

instance (e : NominalEllipsis) (d : NominalSpinePosition) : Decidable (e.Deletes d) :=
  inferInstanceAs (Decidable (InDomain _ _))

/-- `e.Spares d` when the position `d` survives the ellipsis. -/
def NominalEllipsis.Spares (e : NominalEllipsis) (d : NominalSpinePosition) : Prop :=
  External d e.ePosition

instance (e : NominalEllipsis) (d : NominalSpinePosition) : Decidable (e.Spares d) :=
  inferInstanceAs (Decidable (External _ _))

/-- N-stranding NP-ellipsis: [E] on n, deleting NP alone. The noun survives in its raised
position, and prenominal modifiers, being outside n's complement, survive with it. -/
def nStrandingNPE : NominalEllipsis := ⟨.n⟩

/-- nP-ellipsis: [E] on Num, the configuration [liptak-saab-2014] find in Spanish. The noun, the
categorizer and prenominal modifiers are all deleted. -/
def nPEllipsis : NominalEllipsis := ⟨.Num⟩

/-- NumP-ellipsis: [E] on D, leaving only the determiner. -/
def numPEllipsis : NominalEllipsis := ⟨.D⟩

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
theorem postnominal_all_or_nothing (e : NominalEllipsis) (h : e.Deletes .N) :
    ∀ p, p ≤ .N → e.Deletes p := by
  intro p hp
  cases p <;> first | exact h | exact absurd hp (by decide)

/-! ### The contrast condition -/

/-- [E] sits on n when the noun is contrastive and higher when it is not (§2.1, motivated by
(27)). -/
def ePositionOfContrast (nounContrastive : Bool) : NominalEllipsis :=
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
