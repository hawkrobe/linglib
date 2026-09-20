import Linglib.Fragments.Tarifit.Phonology
import Linglib.Morphology.Root.Consonantal

/-!
# Tarifit triconsonantal roots

The thirty-eight verb roots of the CCəC target words in the Tarifit production study, as
consonantal melodies over the segments of `Fragments/Tarifit/Phonology.lean`; the
simple-imperative template that vocalizes them with a schwa between the second and third
consonants is stated with the study. Roots are named by their imperative citation form.

## References

* [afkir-zellou-2025], Tables 7 and 9
-/

namespace Tarifit

open Morphology Phonology

/-- /ðfəʕ/ -/
def dfes : ConsonantalRoot Segment := ⟨[eth, f, ayn]⟩
/-- /ðqər/ -/
def dqer : ConsonantalRoot Segment := ⟨[eth, q, r]⟩
/-- /ʁdˤər/ -/
def ghder : ConsonantalRoot Segment := ⟨[ghayn, emphaticD, r]⟩
/-- /ʁfər/ -/
def ghfer : ConsonantalRoot Segment := ⟨[ghayn, f, r]⟩
/-- /ʁrəβ/ -/
def ghreb : ConsonantalRoot Segment := ⟨[ghayn, r, beta]⟩
/-- /ħməð/ -/
def hmed : ConsonantalRoot Segment := ⟨[hbar, m, eth]⟩
/-- /nqər/ -/
def nqer : ConsonantalRoot Segment := ⟨[n, q, r]⟩
/-- /qβər/ -/
def qber : ConsonantalRoot Segment := ⟨[q, beta, r]⟩
/-- /qðəf/ -/
def qdef : ConsonantalRoot Segment := ⟨[q, eth, f]⟩
/-- /qfər/ -/
def qfer : ConsonantalRoot Segment := ⟨[q, f, r]⟩
/-- /qrəβ/ -/
def qreb : ConsonantalRoot Segment := ⟨[q, r, beta]⟩
/-- /qrəʕ/ 'rip!' -/
def qres : ConsonantalRoot Segment := ⟨[q, r, ayn]⟩
/-- /qtˤəʕ/ -/
def qtes : ConsonantalRoot Segment := ⟨[q, emphaticT, ayn]⟩
/-- /rməð/ -/
def rmed : ConsonantalRoot Segment := ⟨[r, m, eth]⟩
/-- /srəm/ -/
def srem : ConsonantalRoot Segment := ⟨[s, r, m]⟩
/-- /stˤər/ -/
def ster : ConsonantalRoot Segment := ⟨[s, emphaticT, r]⟩
/-- /χrəf/ -/
def xref : ConsonantalRoot Segment := ⟨[chi, r, f]⟩
/-- /ʒβəð/ -/
def zhbed : ConsonantalRoot Segment := ⟨[ezh, beta, eth]⟩
/-- /ʒməð/ 'freeze!' -/
def zhmed : ConsonantalRoot Segment := ⟨[ezh, m, eth]⟩
/-- /ʕβəð/ -/
def aybed : ConsonantalRoot Segment := ⟨[ayn, beta, eth]⟩
/-- /ʕrəm/ -/
def ayrem : ConsonantalRoot Segment := ⟨[ayn, r, m]⟩
/-- /ħsəβ/ 'count!' -/
def hseb : ConsonantalRoot Segment := ⟨[hbar, s, beta]⟩
/-- /ħzən/ -/
def hzen : ConsonantalRoot Segment := ⟨[hbar, z, n]⟩
/-- /ʃməθ/ -/
def shmeth : ConsonantalRoot Segment := ⟨[esh, m, theta]⟩
/-- /χzən/ -/
def xzen : ConsonantalRoot Segment := ⟨[chi, z, n]⟩
/-- /βkəm/ -/
def bkem : ConsonantalRoot Segment := ⟨[beta, k, m]⟩
/-- /ħləm/ -/
def hlem : ConsonantalRoot Segment := ⟨[hbar, l, m]⟩
/-- /ħsən/ -/
def hsen : ConsonantalRoot Segment := ⟨[hbar, s, n]⟩
/-- /nqəβ/ 'pick!' -/
def nqeb : ConsonantalRoot Segment := ⟨[n, q, beta]⟩
/-- /qməʕ/ 'suppress!' -/
def qmes : ConsonantalRoot Segment := ⟨[q, m, ayn]⟩
/-- /sʃən/ 'show!' -/
def sshen : ConsonantalRoot Segment := ⟨[s, esh, n]⟩
/-- /χnəs/ 'bend down!' -/
def xnes : ConsonantalRoot Segment := ⟨[chi, n, s]⟩
/-- /ʒməʕ/ -/
def zhmes : ConsonantalRoot Segment := ⟨[ezh, m, ayn]⟩
/-- /sχəf/ 'pass out!' -/
def sxef : ConsonantalRoot Segment := ⟨[s, chi, f]⟩
/-- /ħkəm/ 'judge!' -/
def hkem : ConsonantalRoot Segment := ⟨[hbar, k, m]⟩
/-- /ntəf/ 'pluck!' -/
def ntef : ConsonantalRoot Segment := ⟨[n, t, f]⟩
/-- /skəf/ -/
def skef : ConsonantalRoot Segment := ⟨[s, k, f]⟩
/-- /rsəq/ -/
def rseq : ConsonantalRoot Segment := ⟨[r, s, q]⟩

/-- The thirty-eight target roots. -/
def roots : List (ConsonantalRoot Segment) :=
  [dfes, dqer, ghder, ghfer, ghreb, hmed, nqer, qber, qdef, qfer, qreb, qres, qtes, rmed, srem,
    ster, xref, zhbed, zhmed, aybed, ayrem, hseb, hzen, shmeth, xzen, bkem, hlem, hsen, nqeb,
    qmes, sshen, xnes, zhmes, sxef, hkem, ntef, skef, rseq]

end Tarifit
