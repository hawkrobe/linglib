import Linglib.Morphology.Root.Consonantal

/-!
# Modern Hebrew consonantal roots

A small inventory of Modern Hebrew consonantal roots as `ConsonantalRoot String` with
IPA-symbol segments, for templatic-morphology studies: the roots of [faust-2026]'s
QaTaT–QaTa triplet (3) and taQTiL nouns (9), and the binyan roots of [arad-2005] (3).

## References

* [faust-2026]
* [arad-2005]
* [mccarthy-1981]
-/

namespace Hebrew

open Morphology

/-! ### The roots of [faust-2026] (3), (9) -/

/-- √klt: [kalat] PST.3MSG, [klita] action noun, [kalut] passive participle `receive`. -/
def klt : ConsonantalRoot String := ⟨["k", "l", "t"]⟩

/-- √kl: [kalal] PST.3MSG, [klila] action noun, [kalul] passive participle `include`; the
identical final consonants of the QaTaT pattern arise by template satisfaction from a
biradical root ([mccarthy-1981]). -/
def kl : ConsonantalRoot String := ⟨["k", "l"]⟩

/-- √klj: [kala] PST.3MSG, [klija] action noun, [kaluj] passive participle `roast`. -/
def klj : ConsonantalRoot String := ⟨["k", "l", "j"]⟩

/-- √dmj: [dimuj] `simile`, [tadmit] `(public) image`. -/
def dmj : ConsonantalRoot String := ⟨["d", "m", "j"]⟩

/-- √bnj: [banuj] `built`, [tavnit] `mold`. -/
def bnj : ConsonantalRoot String := ⟨["b", "n", "j"]⟩

/-- √glj: [galuj] `apparent`, [taglit] `discovery`. -/
def glj : ConsonantalRoot String := ⟨["g", "l", "j"]⟩

/-- √rmj: [remija] `cheating`, [tarmit] `hoax`. -/
def rmj : ConsonantalRoot String := ⟨["r", "m", "j"]⟩

/-- √skt: [taskit] `radio drama`. -/
def skt : ConsonantalRoot String := ⟨["s", "k", "t"]⟩

/-- √ktv: [katav] `wrote`, [katuv] `written`, [kituv] `script`, [ktiva] `writing`. -/
def ktv : ConsonantalRoot String := ⟨["k", "t", "v"]⟩

/-! ### The binyan roots of [arad-2005] (3) -/

/-- √lmd — *lamad* 'learn' (P1), *nilmad* 'learn (passive)' (P2) ([arad-2005] (3)). -/
def lmd : ConsonantalRoot String := ⟨["l", "m", "d"]⟩

/-- √spr — *siper* 'tell' (P3), *supar* 'tell (passive)' (P4) ([arad-2005] (3)). -/
def spr : ConsonantalRoot String := ⟨["s", "p", "r"]⟩

/-- √qlt — *hiqlit* 'record' (P5), *huqlat* 'record (passive)' (P6)
([arad-2005] (3)). -/
def qlt : ConsonantalRoot String := ⟨["q", "l", "t"]⟩

/-- √pll — *hitpalel* 'pray' (P7) ([arad-2005] (3)). -/
def pll : ConsonantalRoot String := ⟨["p", "l", "l"]⟩

/-- √npc — *nipec* 'shatter' (P3), *nupac* (P4) ([arad-2005] (6)). -/
def npc : ConsonantalRoot String := ⟨["n", "p", "c"]⟩

/-- √xlq — *xileq* 'divide' (P3), *xulaq* (P4) ([arad-2005] (6)). -/
def xlq : ConsonantalRoot String := ⟨["x", "l", "q"]⟩

/-- √str — *histir* 'hide' (P5), *hustar* (P6) ([arad-2005] (6)). -/
def str : ConsonantalRoot String := ⟨["s", "t", "r"]⟩

/-- √pqd — *hifqid* 'deposit' (P5), *hufqad* (P6) ([arad-2005] (6)). -/
def pqd : ConsonantalRoot String := ⟨["p", "q", "d"]⟩

end Hebrew
