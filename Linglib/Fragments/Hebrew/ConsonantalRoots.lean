module

public import Linglib.Morphology.Root.Consonantal

/-!
# Modern Hebrew consonantal roots

This file defines a small inventory of Modern Hebrew consonantal roots, as `ConsonantalRoot`
values over IPA symbols, for the templatic-morphology studies. The first group is Faust's: the
roots of the QaTaT–QaTa triplet *kalat*, *kalal*, *kala*, where the identical final consonants
of *kalal* arise from a biradical root by template satisfaction in McCarthy's sense and the
final *j* of √klj surfaces only outside the past tense, and the roots of the taQTiL nouns, a
*t*-final root behind the masculine *taskit* against *j*-final roots behind the feminine
*tavnit*, *taglit*, *tadmit* and *tarmit*. The second group is Arad's: the roots of the seven
binyanim as she numbers them, P1 to P7, of her active–passive pairs in P3–P4 and P5–P6, of the
geminate slot of P3 and P7, of her roots across many patterns and of her conjugation classes.
Each author's roots are in that author's transcription.

## Main definitions

* `Hebrew.klt`, `Hebrew.kl`, `Hebrew.klj`: the roots of Faust's triplet.
* `Hebrew.dmj`, `Hebrew.bnj`, `Hebrew.glj`, `Hebrew.rmj`, `Hebrew.skt`, `Hebrew.ktv`: the
  roots of his taQTiL nouns and their bases.
* `Hebrew.lmd`, `Hebrew.spr`, `Hebrew.qlt`, `Hebrew.pll`, `Hebrew.npc`, `Hebrew.xlq`,
  `Hebrew.str`, `Hebrew.pqd`: Arad's binyan roots.
* `Hebrew.trgm`, `Hebrew.qbl`, `Hebrew.rkk`: her roots of the geminate slot.
* `Hebrew.xšb`, `Hebrew.sgr`, `Hebrew.šmn`: her roots across many patterns.
* `Hebrew.ptx`, `Hebrew.qpʔ`, `Hebrew.mss`, `Hebrew.xmm`, `Hebrew.bhr`, `Hebrew.ʔdm`: her roots
  of the conjugation classes.

## References

* [arad-2005]
* [faust-2026]
* [mccarthy-1981]
-/

@[expose] public section

namespace Hebrew

open Morphology

/-! ### The QaTaT–QaTa triplet -/

/-- √klt, the root of *kalat* 'received', the action noun *klita* and the passive participle
*kalut*. -/
def klt : ConsonantalRoot String := ⟨["k", "l", "t"]⟩

/-- √kl, the biradical root of *kalal* 'included', *klila* and *kalul*, whose identical final
consonants arise by template satisfaction. -/
def kl : ConsonantalRoot String := ⟨["k", "l"]⟩

/-- √klj, the root of *kala* 'roasted', *klija* and *kaluj*, whose final *j* surfaces only
outside the past tense. -/
def klj : ConsonantalRoot String := ⟨["k", "l", "j"]⟩

/-! ### The taQTiL nouns -/

/-- √dmj, the root of *dimuj* 'simile' and the feminine *tadmit* '(public) image'. -/
def dmj : ConsonantalRoot String := ⟨["d", "m", "j"]⟩

/-- √bnj, the root of *banuj* 'built' and the feminine *tavnit* 'mold'. -/
def bnj : ConsonantalRoot String := ⟨["b", "n", "j"]⟩

/-- √glj, the root of *galuj* 'apparent' and the feminine *taglit* 'discovery'. -/
def glj : ConsonantalRoot String := ⟨["g", "l", "j"]⟩

/-- √rmj, the root of *remija* 'cheating' and the feminine *tarmit* 'hoax'. -/
def rmj : ConsonantalRoot String := ⟨["r", "m", "j"]⟩

/-- √skt, the *t*-final root of the masculine *taskit* 'radio drama'. -/
def skt : ConsonantalRoot String := ⟨["s", "k", "t"]⟩

/-- √ktv, the root of *katuv* 'written', *kituv* 'script' and *ktiva* 'writing', the regular
comparanda of the nouns above. -/
def ktv : ConsonantalRoot String := ⟨["k", "t", "v"]⟩

/-! ### The binyan roots -/

/-- √lmd, the root of *lamad* 'learn' in P1 and its passive *nilmad* in P2. -/
def lmd : ConsonantalRoot String := ⟨["l", "m", "d"]⟩

/-- √spr, the root of *siper* 'tell' in P3 and its passive *supar* in P4. -/
def spr : ConsonantalRoot String := ⟨["s", "p", "r"]⟩

/-- √qlt, the root of *hiqlit* 'record' in P5 and its passive *huqlat* in P6. -/
def qlt : ConsonantalRoot String := ⟨["q", "l", "t"]⟩

/-- √pll, the root of *hitpalel* 'pray' in P7. -/
def pll : ConsonantalRoot String := ⟨["p", "l", "l"]⟩

/-- √npc, the root of *nipec* 'shatter' in P3 and its passive *nupac* in P4. -/
def npc : ConsonantalRoot String := ⟨["n", "p", "c"]⟩

/-- √xlq, the root of *xileq* 'divide' in P3 and its passive *xulaq* in P4. -/
def xlq : ConsonantalRoot String := ⟨["x", "l", "q"]⟩

/-- √str, the root of *histir* 'hide' in P5 and its passive *hustar* in P6. -/
def str : ConsonantalRoot String := ⟨["s", "t", "r"]⟩

/-- √pqd, the root of *hifqid* 'deposit' in P5 and its passive *hufqad* in P6. -/
def pqd : ConsonantalRoot String := ⟨["p", "q", "d"]⟩

/-- √šmr, the root of *šamar* 'guard' in P1. -/
def «šmr» : ConsonantalRoot String := ⟨["š", "m", "r"]⟩

/-! ### The geminate slot -/

/-- √trgm, the quadriliteral root of *tirgem* 'translate' in P3, whose fourth consonant takes
the geminate slot. -/
def trgm : ConsonantalRoot String := ⟨["t", "r", "g", "m"]⟩

/-- √qbl, the root of *qibel* 'receive' in P3, where the geminate *b* does not spirantize. -/
def qbl : ConsonantalRoot String := ⟨["q", "b", "l"]⟩

/-- √rkk, the root of *hitrakex* 'become soft' in P7, where the geminate *k* does not
spirantize. -/
def rkk : ConsonantalRoot String := ⟨["r", "k", "k"]⟩

/-! ### Roots across patterns -/

/-- √šmn, the root of *šemen* 'oil', *šamenet* 'cream', *šuman* 'fat', *hišmin* 'fatten' and
*šimen* 'grease'. -/
def «šmn» : ConsonantalRoot String := ⟨["š", "m", "n"]⟩

/-- √xšb, the root of *xašav* 'think', *xišev* 'calculate', *maxšev* 'computer' and *xešbon*
'arithmetic'. -/
def «xšb» : ConsonantalRoot String := ⟨["x", "š", "b"]⟩

/-- √sgr, the root of *sagar* 'close', *hisgir* 'extradite', *seger* 'closure' and *misgeret*
'frame'. -/
def sgr : ConsonantalRoot String := ⟨["s", "g", "r"]⟩

/-! ### The conjugation classes -/

/-- √ptx, the root of *patax* 'open' in P1 and its inchoative *niftax* in P2. -/
def ptx : ConsonantalRoot String := ⟨["p", "t", "x"]⟩

/-- √qpʔ, the root of *qafaʔ* 'freeze' in P1 and its causative *hiqpiʔ* in P5. -/
def «qpʔ» : ConsonantalRoot String := ⟨["q", "p", "ʔ"]⟩

/-- √mss, the root of *namas* 'melt' in P2 and its causative *hemes* in P5. -/
def mss : ConsonantalRoot String := ⟨["m", "s", "s"]⟩

/-- √xmm, the root of *ximem* 'heat' in P3 and its inchoative *hitxamem* in P7. -/
def xmm : ConsonantalRoot String := ⟨["x", "m", "m"]⟩

/-- √bhr, the root of *hivhir* 'make clear' in P5 and its inchoative *hitbaher* in P7. -/
def bhr : ConsonantalRoot String := ⟨["b", "h", "r"]⟩

/-- √ʔdm, the root of *heʔedim* 'redden, be red' in P5. -/
def «ʔdm» : ConsonantalRoot String := ⟨["ʔ", "d", "m"]⟩

end Hebrew
