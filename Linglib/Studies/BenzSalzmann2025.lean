import Linglib.Syntax.Minimalist.Ellipsis

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

* `NomSpinePos`, `NomEllipsisType` — the nominal spine and an [E] position on it
* `nStrandingNPE`, `nPEllipsis`, `numPEllipsis` — [E] on n, on Num, and on D
* `ePositionOfContrast` — the contrast condition on [E] placement

## Main results

* `n_stranding_is_xStranding` — N-to-n movement instantiates the generic X-stranding theorem
* `no_individual_prenominal_deletion`, `no_individual_numeral_deletion` — no [E] position deletes a
  prenominal modifier while sparing the noun
* `postnominal_all_or_nothing` — the only [E] position recovering a postnominal dependent deletes
  every one of them
* `contrast_governs_recovery` — a postnominal dependent is recoverable exactly when the noun is
  contrastive
* `gender_parallels_voice` — the categorizer is external under N-stranding as Voice is under VPE

## References

* [benz-salzmann-2025]
* [liptak-saab-2014]
* [merchant-2001]
* [merchant-2013]
-/

namespace BenzSalzmann2025

open Minimalist.Ellipsis

/-! ### The nominal spine -/

/-- Positions of the nominal extended projection, lowest first. `NP_adj` is the site of prenominal
modifiers: inside nP but outside n's complement, the nominal counterpart of the clausal spine's
`VP_adj`. -/
inductive NomSpinePos where
  /-- The lexical noun and its postnominal dependents. -/
  | N
  /-- Prenominal modifiers: adjectives and, for the paper's purposes, numerals' host positions. -/
  | NP_adj
  /-- The categorizer, which hosts gender and is the landing site of N-movement. -/
  | n
  /-- Number. -/
  | Num
  /-- The determiner. -/
  | D
  deriving DecidableEq, Repr

/-- The deletion-domain relation: `p.isBelow q` when `p` lies in `q`'s complement. Prenominal
modifiers are not in n's complement, though they are in Num's. -/
def NomSpinePos.isBelow : NomSpinePos → NomSpinePos → Bool
  | .N, .NP_adj | .N, .n | .N, .Num | .N, .D => true
  | .NP_adj, .Num | .NP_adj, .D => true
  | .n, .Num | .n, .D => true
  | .Num, .D => true
  | _, _ => false

/-- Structural height, the linear order N ≤ NP_adj ≤ n ≤ Num ≤ D. -/
def NomSpinePos.isAtOrBelow : NomSpinePos → NomSpinePos → Bool
  | .N, _ => true
  | .NP_adj, .NP_adj | .NP_adj, .n | .NP_adj, .Num | .NP_adj, .D => true
  | .n, .n | .n, .Num | .n, .D => true
  | .Num, .Num | .Num, .D => true
  | .D, .D => true
  | _, _ => false

instance : DeletionSpine NomSpinePos where
  isBelow := NomSpinePos.isBelow
  isAtOrBelow := NomSpinePos.isAtOrBelow
  isBelow_irrefl := by intro p; cases p <;> decide
  isBelow_mono := by
    intro d p₁ p₂
    cases d <;> cases p₁ <;> cases p₂ <;>
      simp_all [NomSpinePos.isBelow, NomSpinePos.isAtOrBelow]

/-- An [E] feature on a head of the nominal spine; its deletion domain is that head's
complement. -/
structure NomEllipsisType where
  ePosition : NomSpinePos
  name : String := ""
  deriving Repr

/-- Whether a position falls in the deletion domain. -/
def nomInDeletionDomain (c : NomSpinePos) (e : NomEllipsisType) : Prop :=
  inDomain c e.ePosition

instance (c : NomSpinePos) (e : NomEllipsisType) : Decidable (nomInDeletionDomain c e) := by
  unfold nomInDeletionDomain; infer_instance

/-- Whether a position survives ellipsis. -/
def nomSurvives (c : NomSpinePos) (e : NomEllipsisType) : Prop :=
  ¬ nomInDeletionDomain c e

instance (c : NomSpinePos) (e : NomEllipsisType) : Decidable (nomSurvives c e) := by
  unfold nomSurvives; infer_instance

/-- N-stranding NP-ellipsis: [E] on n, deleting NP alone. The noun survives in its raised
position, and prenominal modifiers, being outside n's complement, survive with it. -/
def nStrandingNPE : NomEllipsisType := ⟨.n, "N-stranding NP-ellipsis"⟩

/-- nP-ellipsis: [E] on Num, the configuration [liptak-saab-2014] find in Spanish. The noun, the
categorizer and prenominal modifiers are all deleted. -/
def nPEllipsis : NomEllipsisType := ⟨.Num, "nP-ellipsis"⟩

/-- NumP-ellipsis: [E] on D, leaving only the determiner. -/
def numPEllipsis : NomEllipsisType := ⟨.D, "NumP-ellipsis"⟩

/-! ### N-stranding -/

/-- N-to-n movement instantiates the generic X-stranding pattern: the base position of the noun
lies in n's complement while n itself is external, so [E] on n deletes NP and spares the moved
noun (§1.1). -/
theorem n_stranding_is_xStranding :
    ¬ inDomain NomSpinePos.n NomSpinePos.n ∧ inDomain NomSpinePos.N NomSpinePos.n :=
  xStranding NomSpinePos.n NomSpinePos.N (by decide)

/-- The clausal and nominal patterns are the same theorem at the categorizer of each extended
projection: V is to v as N is to n. -/
theorem clausal_nominal_parallel :
    inDomain SpinePos.V SpinePos.v ∧ inDomain NomSpinePos.N NomSpinePos.n := by decide

/-- Under N-stranding the noun's dependents go and everything above n stays: the postnominal PP of
*zwei Studenten der Physik* is recovered in *zwei Professoren*, while the numeral and determiner
are pronounced ((6a)). -/
theorem nStranding_domain :
    nomInDeletionDomain .N nStrandingNPE ∧ nomSurvives .NP_adj nStrandingNPE ∧
      nomSurvives .n nStrandingNPE ∧ nomSurvives .Num nStrandingNPE ∧
      nomSurvives .D nStrandingNPE := by decide

/-! ### Against deleting individual constituents -/

/-- No [E] position deletes a prenominal modifier while sparing the noun, since the noun lies in
the complement of every head that dominates the modifier: *das schönste Auto … das schönste
Motorrad* is out on the elided-adjective reading ((25a)). -/
theorem no_individual_prenominal_deletion (p : NomSpinePos)
    (h : NomSpinePos.NP_adj.isBelow p = true) : NomSpinePos.N.isBelow p = true := by
  cases p <;> simp [NomSpinePos.isBelow] at h ⊢

/-- The same for numerals: only [E] on D puts Num in the deletion domain, and that deletes the
noun too ((25b)). -/
theorem no_individual_numeral_deletion (p : NomSpinePos)
    (h : NomSpinePos.Num.isBelow p = true) : NomSpinePos.N.isBelow p = true := by
  cases p <;> simp [NomSpinePos.isBelow] at h ⊢

/-- Deleting a postnominal dependent requires deleting the noun's whole complement, so if one
postnominal modifier is pronounced no other can be recovered ((28a)) while eliding both is fine
((28b)). -/
theorem postnominal_all_or_nothing (e : NomEllipsisType) (h : nomInDeletionDomain .N e) :
    ∀ p, p.isAtOrBelow .N = true → nomInDeletionDomain p e := by
  intro p hp
  cases p <;> simp [NomSpinePos.isAtOrBelow] at hp
  exact h

/-! ### The contrast condition -/

/-- Where [E] sits, given whether the noun is contrastive: on n when it is, higher when it is not
(§2.1, motivated by (27)). -/
def ePositionOfContrast (nounContrastive : Bool) : NomEllipsisType :=
  if nounContrastive then nStrandingNPE else nPEllipsis

/-- A postnominal dependent of the noun is recoverable exactly when the noun is contrastive: with
contrast the noun survives while its complement is deleted, without it the noun is deleted along
with the dependent — the difference between (6a) and Spanish (5), and between (26b) and (27). -/
theorem contrast_governs_recovery (b : Bool) :
    nomInDeletionDomain .N (ePositionOfContrast b) ∧
      (nomSurvives .n (ePositionOfContrast b) ↔ b = true) := by
  cases b <;> exact ⟨by decide, by decide⟩

/-! ### Ellipsis height and mismatches -/

/-- German N-stranding deletes strictly less than the Spanish configuration: the categorizer and
the prenominal modifiers survive the one and not the other. -/
theorem german_smaller_domain_than_spanish :
    nomSurvives .NP_adj nStrandingNPE ∧ nomInDeletionDomain .NP_adj nPEllipsis ∧
      nomSurvives .n nStrandingNPE ∧ nomInDeletionDomain .n nPEllipsis := by decide

/-- Gender mismatches pattern with voice mismatches: the head bearing the feature is external
exactly when [E] sits on it. Gender lives on n, which survives N-stranding but not nP-ellipsis,
as Voice survives VP-ellipsis but not sluicing (§3). -/
theorem gender_parallels_voice :
    nomSurvives .n nStrandingNPE ∧ nomInDeletionDomain .n nPEllipsis ∧
      canMismatch englishVPE voiceMismatch ∧ ¬ canMismatch sluicing voiceMismatch := by decide

end BenzSalzmann2025
