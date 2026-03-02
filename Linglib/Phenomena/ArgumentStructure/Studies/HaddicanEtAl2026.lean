/-!
# Haddican, @cite{haddican-tamminga-dendikken-wade-2026} @cite{haddican-tamminga-dendikken-wade-2026}

English Particle Verbs Prime Double Object Constructions in Production.
*Linguistic Inquiry*. doi:10.1162/LING.a.558

Production priming experiment (N=238) testing whether PVCs prime DOCs.

## Design

Sentence completion task. Two subdesigns (Table 1, p.7):

- **Baseline**: DOC vs PD primes → DOC/PD target completions
- **PV**: PVC vs non-PVC primes → DOC/PD target completions

PVC primes used particle-object order ("put down the vase") to control
for surface string similarity with DOC targets (p.5).

## Results

PVCs prime DOCs (β=0.296, p=.005). PVC and DOC primes do not differ in
priming magnitude (β=−0.069, p=.503). Consistent with identical structural
representations under the SC analysis.

## Cross-references

- `Phenomena.WordOrder.Studies.ArnoldEtAl2000`: The same two constructions
  (dative alternation + particle placement) studied from a processing
  perspective — heaviness drives linearization while abstract structure
  drives priming.
- `Phenomena.ArgumentStructure.DativeAlternation`: Records both DOC and PD
  frames as grammatical — the precondition for the priming study.
-/

namespace Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026

/-- A priming contrast between two prime conditions. -/
structure PrimingContrast where
  primeA        : String   -- test condition
  primeB        : String   -- control condition
  target        : String   -- response measure
  aFavorsTarget : Bool     -- primeA increases target production vs primeB
  significant   : Bool     -- p < .05
  deriving Repr, BEq

/-- DOC production rate by prime condition. Table 1, p.7.
    Percentages are integers (e.g., 59 = 59%). -/
structure CellRate where
  condition : String
  docPct    : Nat       -- DOC production %
  pdPct     : Nat       -- PD production %
  deriving Repr, BEq

/-! ## Table 1 cell rates -/

def baseline_doc : CellRate := { condition := "DOC prime",     docPct := 59, pdPct := 41 }
def baseline_pd  : CellRate := { condition := "PD prime",      docPct := 49, pdPct := 51 }
def pv_pvc       : CellRate := { condition := "PVC prime",     docPct := 58, pdPct := 42 }
def pv_nonpvc    : CellRate := { condition := "non-PVC prime", docPct := 52, pdPct := 48 }

/-! ## Regression contrasts -/

/-- Baseline replication: DOC primes boost DOC production relative to
    PD primes (β=0.569, SE=0.114, p<.001). -/
def baseline : PrimingContrast :=
  { primeA := "DOC", primeB := "PD", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- Key finding: PVC primes boost DOC production relative to non-PVC
    control primes (β=0.296, SE=0.105, p=.005). -/
def pvc_primes_doc : PrimingContrast :=
  { primeA := "PVC", primeB := "non-PVC", target := "DOC"
  , aFavorsTarget := true, significant := true }

/-- PVC and DOC primes do not differ in their priming of DOCs
    (β=−0.069, SE=0.104, p=.503; combined 2×4 model, n.9). -/
def pvc_doc_equivalent : PrimingContrast :=
  { primeA := "PVC", primeB := "DOC", target := "DOC"
  , aFavorsTarget := false, significant := false }

/-! ## Verification theorems -/

/-- DOC priming is strictly stronger than PD non-priming (baseline effect). -/
theorem baseline_effect_direction :
    baseline.aFavorsTarget = true ∧ baseline.significant = true := ⟨rfl, rfl⟩

/-- PVC primes DO boost DOC production. -/
theorem pvc_effect :
    pvc_primes_doc.aFavorsTarget = true ∧ pvc_primes_doc.significant = true := ⟨rfl, rfl⟩

/-- PVC and DOC primes yield equivalent magnitude — no significant difference. -/
theorem pvc_doc_equivalence :
    pvc_doc_equivalent.significant = false := rfl

end Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026
