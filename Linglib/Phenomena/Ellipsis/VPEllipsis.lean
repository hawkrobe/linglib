import Linglib.Core.Basic

/-!
# VP Ellipsis: Empirical Data

Theory-neutral data on VP ellipsis, focusing on voice mismatch tolerance.

VP ellipsis differs from sluicing in tolerating voice mismatches
(Merchant 2013). This asymmetry is explained by AHM 2025: VP ellipsis
requires only semantic identity (e-GIVENness), while sluicing requires
both semantic and syntactic identity (SIC).

## References

- Merchant, J. (2013). Voice and ellipsis. *Linguistic Inquiry* 44(1): 77–108.
- Anand, P., Hardt, D. & McCloskey, J. (2025). Sluicing and Syntactic Identity.
-/

namespace Phenomena.Ellipsis.VPEllipsis

/-- A VP ellipsis datum: a sentence with VP ellipsis and its properties. -/
structure VPEDatum where
  /-- The surface sentence with ellipsis -/
  sentence : String
  /-- Description of the antecedent VP -/
  antecedent : String
  /-- Description of the ellipsis site VP -/
  ellipsisSite : String
  /-- Is the sentence grammatical? -/
  grammatical : Bool
  /-- Notes on the example -/
  notes : String := ""
  /-- Source reference -/
  source : String := "Merchant 2013"
  deriving Repr

/-- Active antecedent → passive ellipsis site (grammatical under VPE). -/
def activeThenPassive : VPEDatum :=
  { sentence := "The janitor must remove the trash whenever it is apparent that it should be."
    antecedent := "remove the trash (active)"
    ellipsisSite := "be removed (passive)"
    grammatical := true
    notes := "Voice mismatch tolerated under VPE" }

/-- Passive antecedent → active ellipsis site (grammatical under VPE). -/
def passiveThenActive : VPEDatum :=
  { sentence := "The system can be used by anyone who wants to."
    antecedent := "be used (passive)"
    ellipsisSite := "use it (active)"
    grammatical := true
    notes := "Voice mismatch tolerated under VPE" }

/-- Same voice: active → active (grammatical, baseline). -/
def activeBaseline : VPEDatum :=
  { sentence := "John ate pizza, and Mary did too."
    antecedent := "ate pizza (active)"
    ellipsisSite := "ate pizza (active)"
    grammatical := true
    notes := "Same voice baseline" }

/-- Contrastive note: sluicing blocks voice mismatches that VPE allows. -/
def sluicingContrast : VPEDatum :=
  { sentence := "*The janitor must remove the trash, but he doesn't know by whom."
    antecedent := "remove the trash (active)"
    ellipsisSite := "the trash is removed by whom (passive sluice)"
    grammatical := false
    notes := "Sluicing blocks voice mismatch; SIC requires v[agentive] = v[agentive]"
    source := "Merchant 2013 / AHM 2025" }

/-- All VP ellipsis examples. -/
def allExamples : List VPEDatum :=
  [activeThenPassive, passiveThenActive, activeBaseline, sluicingContrast]

/-- Voice mismatch examples (grammatical under VPE). -/
def voiceMismatchExamples : List VPEDatum :=
  [activeThenPassive, passiveThenActive]

end Phenomena.Ellipsis.VPEllipsis
