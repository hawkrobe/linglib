/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Root.Consonantal
import Linglib.Fragments.Tigrinya.Phonology

/-!
# Tigre vowels, gutturals, and verbal roots

Tigre shares Tigrinya's seven vowel qualities and four gutturals ([raz-1983],
[lowenstamm-prunet-1988]), so the types are Tigrinya's; the verbal roots are those of
[faust-lampitelli-2026]'s Tigre paradigms. Ejective and pharyngealized consonants carry their
modifier letter as one segment.

## References

* [raz-1983]
* [lowenstamm-prunet-1988]
* [faust-lampitelli-2026]
-/

namespace Tigre.Phonology

open Morphology

/-- The vowels, as in Tigrinya. -/
abbrev Vowel := Tigrinya.Phonology.Vowel

/-- The gutturals, as in Tigrinya. -/
abbrev Guttural := Tigrinya.Phonology.Guttural

/-- √mzn `weigh`: [tɨ-mazzɨn] 2-JUSS, [mazzɨn] IMP. -/
def weigh : ConsonantalRoot String := ⟨["m", "z", "n"]⟩

/-- √fgr `leave`: [fagr-a] PRF-3MSG, [tɨ-fgʌr] 2-JUSS, [fɨgʌr] IMP. -/
def leave : ConsonantalRoot String := ⟨["f", "g", "r"]⟩

/-- √ħtˁb `wash`: [ħatˁb-a] PRF-3MSG, [tɨ-ħɨtˁʌb] 2-JUSS. -/
def wash : ConsonantalRoot String := ⟨["ħ", "tˁ", "b"]⟩

/-- √hrb `flee`: [harb-a] PRF-3MSG; the 2-JUSS is printed [tɨ-ħɨrʌb]. -/
def flee : ConsonantalRoot String := ⟨["h", "r", "b"]⟩

/-- √kˀnsˁ `get up`: [tɨ-kˀnʌsˁ] 2-JUSS, [kˀɨnʌsˁ] IMP. -/
def getUp : ConsonantalRoot String := ⟨["kˀ", "n", "sˁ"]⟩

/-- √fgr `whip`: [tɨ-fʌggɨr] 2-IMP.M. -/
def whip : ConsonantalRoot String := ⟨["f", "g", "r"]⟩

/-- √sʔl `ask`: [tɨ-sʔɨl] 2-IMP.M. -/
def ask : ConsonantalRoot String := ⟨["s", "ʔ", "l"]⟩

/-- √tˀʕn `load`: [tɨ-tˀʕɨn] 2-IMP.M. -/
def load : ConsonantalRoot String := ⟨["tˀ", "ʕ", "n"]⟩

/-- √sħk `uncover`: [tɨ-sħɨk] 2-IMP.M. -/
def uncover : ConsonantalRoot String := ⟨["s", "ħ", "k"]⟩

/-- √sħb `pull`: [tɨ-sħɨb] 2-IMP.M. -/
def pull : ConsonantalRoot String := ⟨["s", "ħ", "b"]⟩

end Tigre.Phonology
