import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Tarifit phones

This file lists the consonants of Tarifit (Nador variety) that occur in the CCəC target words
of Afkir and Zellou's production study, as they surface in the simple imperative, together with
the schwa, and gives each its segment. Singleton /b, d, t/ spirantize to [β, ð, θ] outside
post-nasal and pharyngealized contexts. The sonority class of a phone on the Parker scale is
read off the phone by `Sonority.Class.ofSegment` and not stored.

The feature values come from the PHOIBLE chart, and a phone is its chart entry's segment
with the phone's departure merged over it. There are two departures. PHOIBLE separates
the pharyngealized stops /tˤ dˤ/ from plain /t d/ by its retracted tongue root feature alone,
which the feature system here lacks, so they take the chart entries of /t d/ and the value
[+back]. Afkir and Zellou describe the pharyngeal /ʕ/ as an approximant, where the chart has a
fricative. PHOIBLE has no Tarifit inventory.

## Main definitions

* `Tarifit.q`, `Tarifit.emphaticT` and the like: the phones, as segments. A name is the phone's
  IPA symbol where that is an identifier, and otherwise the symbol's name: `emphaticT` and
  `emphaticD` are tˤ and dˤ, `ghayn` is ʁ, `ayn` is ʕ and `hbar` is ħ.
* `Tarifit.transcriptions`, `Tarifit.ipa?`: the IPA transcription of each phone.
* `Tarifit.inventory`: the set of phones.

## References

* [afkir-zellou-2025]
* [parker-2002]
* [moran-mccloy-2019]
-/

open Phonology Data.PHOIBLE

namespace Tarifit

/-! ### Phones -/

/-- The voiceless uvular stop /q/. -/
def q : Segment := .ofChart .«q»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The pharyngealized stop /tˤ/, the chart's /t/ with [+back]. -/
def emphaticT : Segment := .ofChart .«t» (Segment.ofSpecs [(.back, true)])

/-- The pharyngealized stop /dˤ/, the chart's /d/ with [+back]. -/
def emphaticD : Segment := .ofChart .«d» (Segment.ofSpecs [(.back, true)])

/-- The voiced bilabial fricative /β/. -/
def beta : Segment := .ofChart .«β»

/-- The voiced dental fricative /ð/. -/
def eth : Segment := .ofChart .«ð»

/-- The voiceless dental fricative /θ/. -/
def theta : Segment := .ofChart .«θ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiceless postalveolar fricative /ʃ/. -/
def esh : Segment := .ofChart .«ʃ»

/-- The voiceless uvular fricative /χ/. -/
def chi : Segment := .ofChart .«χ»

/-- The voiceless pharyngeal fricative /ħ/. -/
def hbar : Segment := .ofChart .«ħ»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiced postalveolar fricative /ʒ/. -/
def ezh : Segment := .ofChart .«ʒ»

/-- The voiced uvular fricative /ʁ/. -/
def ghayn : Segment := .ofChart .«ʁ»

/-- The pharyngeal /ʕ/, an approximant where the chart has a fricative. -/
def ayn : Segment :=
  .ofChart .«ʕ» (Segment.ofSpecs [(.consonantal, false), (.sonorant, true), (.approximant, true)])

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The tap /r/. -/
def r : Segment := .ofChart .«ɾ»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The schwa /ə/. -/
def schwa : Segment := .ofChart .«ə»

/-- The phones of the CCəC target words, as they surface, each with its IPA transcription. -/
def transcriptions : List (Segment × String) :=
  [(q, "q"), (k, "k"), (t, "t"), (emphaticT, "tˤ"), (emphaticD, "dˤ"), (beta, "β"), (eth, "ð"),
    (theta, "θ"), (f, "f"), (s, "s"), (esh, "ʃ"), (chi, "χ"), (hbar, "ħ"), (z, "z"), (ezh, "ʒ"),
    (ghayn, "ʁ"), (ayn, "ʕ"), (m, "m"), (n, "n"), (r, "r"), (l, "l"), (schwa, "ə")]

/-- The phones, pairwise distinct. -/
def inventory : Finset Segment := ⟨↑(transcriptions.map (·.1)), by decide⟩

/-- The IPA transcription of a phone. -/
def ipa? (x : Segment) : Option String := transcriptions.lookup x

end Tarifit
