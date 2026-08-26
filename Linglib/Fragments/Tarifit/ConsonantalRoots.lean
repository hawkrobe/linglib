import Linglib.Fragments.Tarifit.Phonology
import Linglib.Morphology.Root.Consonantal

/-!
# Tarifit triconsonantal roots

The thirty-eight verb roots of the CCəC target words in the Tarifit production study, as
consonantal melodies over `Tarifit.Phone`; the simple-imperative template that vocalizes them
with a schwa between the second and third consonants is stated with the study. Roots are named
by their imperative citation form.

## References

* [afkir-zellou-2025], Tables 7 and 9
-/

namespace Tarifit

open Morphology

/-- /ðfəʕ/ -/
def dfes : ConsonantalRoot Phone := ⟨[.eth, .f, .ayn]⟩
/-- /ðqər/ -/
def dqer : ConsonantalRoot Phone := ⟨[.eth, .q, .r]⟩
/-- /ʁdˤər/ -/
def ghder : ConsonantalRoot Phone := ⟨[.ghayn, .dE, .r]⟩
/-- /ʁfər/ -/
def ghfer : ConsonantalRoot Phone := ⟨[.ghayn, .f, .r]⟩
/-- /ʁrəβ/ -/
def ghreb : ConsonantalRoot Phone := ⟨[.ghayn, .r, .beta]⟩
/-- /ħməð/ -/
def hmed : ConsonantalRoot Phone := ⟨[.hbar, .m, .eth]⟩
/-- /nqər/ -/
def nqer : ConsonantalRoot Phone := ⟨[.n, .q, .r]⟩
/-- /qβər/ -/
def qber : ConsonantalRoot Phone := ⟨[.q, .beta, .r]⟩
/-- /qðəf/ -/
def qdef : ConsonantalRoot Phone := ⟨[.q, .eth, .f]⟩
/-- /qfər/ -/
def qfer : ConsonantalRoot Phone := ⟨[.q, .f, .r]⟩
/-- /qrəβ/ -/
def qreb : ConsonantalRoot Phone := ⟨[.q, .r, .beta]⟩
/-- /qrəʕ/ 'rip!' -/
def qres : ConsonantalRoot Phone := ⟨[.q, .r, .ayn]⟩
/-- /qtˤəʕ/ -/
def qtes : ConsonantalRoot Phone := ⟨[.q, .tE, .ayn]⟩
/-- /rməð/ -/
def rmed : ConsonantalRoot Phone := ⟨[.r, .m, .eth]⟩
/-- /srəm/ -/
def srem : ConsonantalRoot Phone := ⟨[.s, .r, .m]⟩
/-- /stˤər/ -/
def ster : ConsonantalRoot Phone := ⟨[.s, .tE, .r]⟩
/-- /χrəf/ -/
def xref : ConsonantalRoot Phone := ⟨[.chi, .r, .f]⟩
/-- /ʒβəð/ -/
def zhbed : ConsonantalRoot Phone := ⟨[.ezh, .beta, .eth]⟩
/-- /ʒməð/ 'freeze!' -/
def zhmed : ConsonantalRoot Phone := ⟨[.ezh, .m, .eth]⟩
/-- /ʕβəð/ -/
def aybed : ConsonantalRoot Phone := ⟨[.ayn, .beta, .eth]⟩
/-- /ʕrəm/ -/
def ayrem : ConsonantalRoot Phone := ⟨[.ayn, .r, .m]⟩
/-- /ħsəβ/ 'count!' -/
def hseb : ConsonantalRoot Phone := ⟨[.hbar, .s, .beta]⟩
/-- /ħzən/ -/
def hzen : ConsonantalRoot Phone := ⟨[.hbar, .z, .n]⟩
/-- /ʃməθ/ -/
def shmeth : ConsonantalRoot Phone := ⟨[.esh, .m, .theta]⟩
/-- /χzən/ -/
def xzen : ConsonantalRoot Phone := ⟨[.chi, .z, .n]⟩
/-- /βkəm/ -/
def bkem : ConsonantalRoot Phone := ⟨[.beta, .k, .m]⟩
/-- /ħləm/ -/
def hlem : ConsonantalRoot Phone := ⟨[.hbar, .l, .m]⟩
/-- /ħsən/ -/
def hsen : ConsonantalRoot Phone := ⟨[.hbar, .s, .n]⟩
/-- /nqəβ/ 'pick!' -/
def nqeb : ConsonantalRoot Phone := ⟨[.n, .q, .beta]⟩
/-- /qməʕ/ 'suppress!' -/
def qmes : ConsonantalRoot Phone := ⟨[.q, .m, .ayn]⟩
/-- /sʃən/ 'show!' -/
def sshen : ConsonantalRoot Phone := ⟨[.s, .esh, .n]⟩
/-- /χnəs/ 'bend down!' -/
def xnes : ConsonantalRoot Phone := ⟨[.chi, .n, .s]⟩
/-- /ʒməʕ/ -/
def zhmes : ConsonantalRoot Phone := ⟨[.ezh, .m, .ayn]⟩
/-- /sχəf/ 'pass out!' -/
def sxef : ConsonantalRoot Phone := ⟨[.s, .chi, .f]⟩
/-- /ħkəm/ 'judge!' -/
def hkem : ConsonantalRoot Phone := ⟨[.hbar, .k, .m]⟩
/-- /ntəf/ 'pluck!' -/
def ntef : ConsonantalRoot Phone := ⟨[.n, .t, .f]⟩
/-- /skəf/ -/
def skef : ConsonantalRoot Phone := ⟨[.s, .k, .f]⟩
/-- /rsəq/ -/
def rseq : ConsonantalRoot Phone := ⟨[.r, .s, .q]⟩

/-- The thirty-eight target roots. -/
def roots : List (ConsonantalRoot Phone) :=
  [dfes, dqer, ghder, ghfer, ghreb, hmed, nqer, qber, qdef, qfer, qreb, qres, qtes, rmed, srem,
    ster, xref, zhbed, zhmed, aybed, ayrem, hseb, hzen, shmeth, xzen, bkem, hlem, hsen, nqeb,
    qmes, sshen, xnes, zhmes, sxef, hkem, ntef, skef, rseq]

end Tarifit
