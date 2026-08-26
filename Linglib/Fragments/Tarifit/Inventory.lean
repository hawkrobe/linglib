import Linglib.Phonology.Segmental.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Tarifit consonants and CCəC roots

The thirty-eight CCəC target words of the Tarifit production study are triconsonantal verb
roots in the simple imperative, whose prosodic template places a schwa between the second and
third consonants. Each word is given by its three surface consonants (singleton /b, d, t/
spirantize to [β, ð, θ] outside post-nasal and pharyngealized contexts), and its sonority
profile is read off the Parker scale, on which the pharyngeal /ʕ/ counts as an approximant, the
top of the study's consonant range.

## References

* [afkir-zellou-2025], Tables 7 and 9
* [parker-2002]
-/

namespace Tarifit

open Phonology

/-- The consonants occurring in the CCəC target words, as they surface. -/
inductive Consonant
  | q | k | t | tE | dE | beta | eth | theta | f | s | esh | chi | hbar | z | ezh | ghayn | ayn
  | m | n | r | l
  deriving DecidableEq, Fintype, Repr

namespace Consonant

/-- IPA transcription. -/
def ipa : Consonant → String
  | .q => "q" | .k => "k" | .t => "t" | .tE => "tˤ" | .dE => "dˤ" | .beta => "β" | .eth => "ð"
  | .theta => "θ" | .f => "f" | .s => "s" | .esh => "ʃ" | .chi => "χ" | .hbar => "ħ" | .z => "z"
  | .ezh => "ʒ" | .ghayn => "ʁ" | .ayn => "ʕ" | .m => "m" | .n => "n" | .r => "r" | .l => "l"

/-- Parker class: voiceless stops and fricatives, voiced stops and fricatives, nasals, the
liquids /r, l/, and the pharyngeal approximant /ʕ/ as a glide. -/
def sonorityClass : Consonant → Sonority.Class
  | .q | .k | .t | .tE => .vls
  | .dE => .vds
  | .theta | .f | .s | .esh | .chi | .hbar => .vlf
  | .beta | .eth | .z | .ezh | .ghayn => .vdf
  | .ayn => .glide
  | .m | .n => .nasal
  | .r | .l => .liquid

/-- Parker sonority rank. -/
def rank (c : Consonant) : ℕ := c.sonorityClass.parkerRank

/-- A voiceless obstruent. -/
def Voiceless (c : Consonant) : Prop := c.sonorityClass.Voiceless

instance : DecidablePred Voiceless := fun c => inferInstanceAs (Decidable c.sonorityClass.Voiceless)

end Consonant

/-- A CCəC target word: a triconsonantal root in the simple imperative template. -/
structure TriconWord where
  c1 : Consonant
  c2 : Consonant
  c3 : Consonant
  deriving DecidableEq, Repr

namespace TriconWord

/-- The surface form `C1C2əC3`. -/
def ipa (w : TriconWord) : String := w.c1.ipa ++ w.c2.ipa ++ "ə" ++ w.c3.ipa

/-- The onset cluster rises in sonority. -/
def Rising (w : TriconWord) : Prop := w.c1.rank < w.c2.rank

/-- The onset cluster falls in sonority. -/
def Falling (w : TriconWord) : Prop := w.c2.rank < w.c1.rank

/-- The onset cluster is a sonority plateau. -/
def Plateau (w : TriconWord) : Prop := w.c1.rank = w.c2.rank

instance (w : TriconWord) : Decidable w.Rising := inferInstanceAs (Decidable (_ < _))
instance (w : TriconWord) : Decidable w.Falling := inferInstanceAs (Decidable (_ < _))
instance (w : TriconWord) : Decidable w.Plateau := inferInstanceAs (Decidable (_ = _))

end TriconWord

/-! ### The target words -/

/-- /ðfəʕ/ -/
def dfes : TriconWord := ⟨.eth, .f, .ayn⟩
/-- /ðqər/ -/
def dqer : TriconWord := ⟨.eth, .q, .r⟩
/-- /ʁdˤər/ -/
def ghder : TriconWord := ⟨.ghayn, .dE, .r⟩
/-- /ʁfər/ -/
def ghfer : TriconWord := ⟨.ghayn, .f, .r⟩
/-- /ʁrəβ/ -/
def ghreb : TriconWord := ⟨.ghayn, .r, .beta⟩
/-- /ħməð/ -/
def hmed : TriconWord := ⟨.hbar, .m, .eth⟩
/-- /nqər/ -/
def nqer : TriconWord := ⟨.n, .q, .r⟩
/-- /qβər/ -/
def qber : TriconWord := ⟨.q, .beta, .r⟩
/-- /qðəf/ -/
def qdef : TriconWord := ⟨.q, .eth, .f⟩
/-- /qfər/ -/
def qfer : TriconWord := ⟨.q, .f, .r⟩
/-- /qrəβ/ -/
def qreb : TriconWord := ⟨.q, .r, .beta⟩
/-- /qrəʕ/ 'rip!' -/
def qres : TriconWord := ⟨.q, .r, .ayn⟩
/-- /qtˤəʕ/ -/
def qtes : TriconWord := ⟨.q, .tE, .ayn⟩
/-- /rməð/ -/
def rmed : TriconWord := ⟨.r, .m, .eth⟩
/-- /srəm/ -/
def srem : TriconWord := ⟨.s, .r, .m⟩
/-- /stˤər/ -/
def ster : TriconWord := ⟨.s, .tE, .r⟩
/-- /χrəf/ -/
def xref : TriconWord := ⟨.chi, .r, .f⟩
/-- /ʒβəð/ -/
def zhbed : TriconWord := ⟨.ezh, .beta, .eth⟩
/-- /ʒməð/ 'freeze!' -/
def zhmed : TriconWord := ⟨.ezh, .m, .eth⟩
/-- /ʕβəð/ -/
def aybed : TriconWord := ⟨.ayn, .beta, .eth⟩
/-- /ʕrəm/ -/
def ayrem : TriconWord := ⟨.ayn, .r, .m⟩
/-- /ħsəβ/ 'count!' -/
def hseb : TriconWord := ⟨.hbar, .s, .beta⟩
/-- /ħzən/ -/
def hzen : TriconWord := ⟨.hbar, .z, .n⟩
/-- /ʃməθ/ -/
def shmeth : TriconWord := ⟨.esh, .m, .theta⟩
/-- /χzən/ -/
def xzen : TriconWord := ⟨.chi, .z, .n⟩
/-- /βkəm/ -/
def bkem : TriconWord := ⟨.beta, .k, .m⟩
/-- /ħləm/ -/
def hlem : TriconWord := ⟨.hbar, .l, .m⟩
/-- /ħsən/ -/
def hsen : TriconWord := ⟨.hbar, .s, .n⟩
/-- /nqəβ/ 'pick!' -/
def nqeb : TriconWord := ⟨.n, .q, .beta⟩
/-- /qməʕ/ 'suppress!' -/
def qmes : TriconWord := ⟨.q, .m, .ayn⟩
/-- /sʃən/ 'show!' -/
def sshen : TriconWord := ⟨.s, .esh, .n⟩
/-- /χnəs/ 'bend down!' -/
def xnes : TriconWord := ⟨.chi, .n, .s⟩
/-- /ʒməʕ/ -/
def zhmes : TriconWord := ⟨.ezh, .m, .ayn⟩
/-- /sχəf/ 'pass out!' -/
def sxef : TriconWord := ⟨.s, .chi, .f⟩
/-- /ħkəm/ 'judge!' -/
def hkem : TriconWord := ⟨.hbar, .k, .m⟩
/-- /ntəf/ 'pluck!' -/
def ntef : TriconWord := ⟨.n, .t, .f⟩
/-- /skəf/ -/
def skef : TriconWord := ⟨.s, .k, .f⟩
/-- /rsəq/ -/
def rseq : TriconWord := ⟨.r, .s, .q⟩

/-- The thirty-eight CCəC target words. -/
def words : List TriconWord :=
  [dfes, dqer, ghder, ghfer, ghreb, hmed, nqer, qber, qdef, qfer, qreb, qres, qtes, rmed, srem,
    ster, xref, zhbed, zhmed, aybed, ayrem, hseb, hzen, shmeth, xzen, bkem, hlem, hsen, nqeb,
    qmes, sshen, xnes, zhmes, sxef, hkem, ntef, skef, rseq]

end Tarifit
