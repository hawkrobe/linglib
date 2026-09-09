/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.DeriveFintype
import Linglib.Morphology.Root.Consonantal

/-!
# Tigrinya vowels, gutturals, and verbal roots

The Tigrinya vowel inventory — six full qualities [a, ʌ, i, u, e, o] and the weak vowel [ɨ]
([leslau-1941], [berhane-1991], [denais-1990]) — its four gutturals, the glottals [ʔ, h] and
the pharyngeals [ʕ, ħ], and the verbal roots of [faust-lampitelli-2026]'s paradigms. Roots are
`Morphology.ConsonantalRoot String` with IPA-symbol segments, ejective and pharyngealized
consonants carrying their modifier letter as one segment.

## References

* [leslau-1941]
* [berhane-1991]
* [denais-1990]
* [buckley-1994]
* [faust-lampitelli-2026]
-/

namespace Tigrinya.Phonology

open Morphology

/-- The vowels: six full qualities and the weak [ɨ], which occurs only where its absence would
leave an impossible cluster ([buckley-1994], [denais-1990], [berhane-1991]). -/
inductive Vowel where
  /-- [a]. -/
  | a
  /-- [ʌ]. -/
  | aBare
  /-- [i]. -/
  | i
  /-- [u]. -/
  | u
  /-- [e]. -/
  | e
  /-- [o]. -/
  | o
  /-- [ɨ], the weak vowel. -/
  | weak
  deriving DecidableEq, Repr, Fintype

namespace Vowel

/-- The IPA symbol. -/
def toIPA : Vowel → String
  | .a => "a"
  | .aBare => "ʌ"
  | .i => "i"
  | .u => "u"
  | .e => "e"
  | .o => "o"
  | .weak => "ɨ"

/-- `v.IsLow`: [a] or [ʌ]. -/
def IsLow : Vowel → Prop
  | .a | .aBare => True
  | _ => False

instance : DecidablePred IsLow := λ v => by cases v <;> unfold IsLow <;> infer_instance

end Vowel

/-- The four gutturals: two glottals and two pharyngeals. -/
inductive Guttural where
  /-- [ʔ]. -/
  | glottalStop
  /-- [h]. -/
  | h
  /-- [ʕ]. -/
  | pharyngealVoiced
  /-- [ħ]. -/
  | pharyngealVoiceless
  deriving DecidableEq, Repr, Fintype

namespace Guttural

/-- The IPA symbol. -/
def toIPA : Guttural → String
  | .glottalStop => "ʔ"
  | .h => "h"
  | .pharyngealVoiced => "ʕ"
  | .pharyngealVoiceless => "ħ"

/-- The guttural written by an IPA symbol, if any. -/
def ofIPA? : String → Option Guttural
  | "ʔ" => some .glottalStop
  | "h" => some .h
  | "ʕ" => some .pharyngealVoiced
  | "ħ" => some .pharyngealVoiceless
  | _ => none

/-- `g.IsPharyngeal`: [ʕ] or [ħ]. -/
def IsPharyngeal : Guttural → Prop
  | .pharyngealVoiced | .pharyngealVoiceless => True
  | _ => False

instance : DecidablePred IsPharyngeal :=
  λ g => by cases g <;> unfold IsPharyngeal <;> infer_instance

theorem ofIPA_toIPA (g : Guttural) : ofIPA? g.toIPA = some g := by cases g <;> rfl

end Guttural

/-! ### Verbal roots -/

/-- √grf `whip`: [gʌrʌf-] DEP.PRF, [gʌrif-] PRF, [-gʌrrɨf] IMPRF. -/
def whip : ConsonantalRoot String := ⟨["g", "r", "f"]⟩

/-- √smʕ `hear`: [sʌmaʕ-] DEP.PRF, [sʌmiʕ-] PRF, [-sʌmmɨʕ] IMPRF, [sɨmaʕ] IMP.M. -/
def hear : ConsonantalRoot String := ⟨["s", "m", "ʕ"]⟩

/-- √ʔsr `arrest`: [ʔasʌr-] DEP.PRF, [ʔasir-] PRF, [-ʔassɨr] IMPRF. -/
def arrest : ConsonantalRoot String := ⟨["ʔ", "s", "r"]⟩

/-- √sħb `pull`: [saħab-] DEP.PRF, [siħib-] PRF, [-sɨħɨb] IMPRF. -/
def pull : ConsonantalRoot String := ⟨["s", "ħ", "b"]⟩

/-- √mhr `teach`: [mahar] IMP. -/
def teach : ConsonantalRoot String := ⟨["m", "h", "r"]⟩

/-- √ħrd `slaughter`: [ta-ħarrɨd] 2-IMPRF. -/
def slaughter : ConsonantalRoot String := ⟨["ħ", "r", "d"]⟩

/-- √ħdm `escape`: [ta-ħadɨm] 2-IMPRF. -/
def escape : ConsonantalRoot String := ⟨["ħ", "d", "m"]⟩

/-- √sʔl `ask`: [saʔal] IMP. -/
def ask : ConsonantalRoot String := ⟨["s", "ʔ", "l"]⟩

/-- √glh `uncover`: [gɨlah] IMP.M, [gɨlh-i] IMP-F, [mɨ-glah] GER. -/
def uncover : ConsonantalRoot String := ⟨["g", "l", "h"]⟩

/-- √nbħ `bark`: [nɨβaħ] IMP.M, [nɨbħ-i] IMP-F, [mɨ-nbaħ] GER. -/
def bark : ConsonantalRoot String := ⟨["n", "b", "ħ"]⟩

/-- √bdl `hurt`, a type B verb with medial gemination throughout: [bʌddʌl-ʌ] DEP.PRF-3MSG,
[mɨ-bɨddal] GER. -/
def hurt : ConsonantalRoot String := ⟨["b", "d", "l"]⟩

/-- √brk `bless`, a type C verb with [a] after the first radical throughout: [barʌk-ʌ]
DEP.PRF-3MSG, [mɨ-bɨrak] GER. -/
def bless : ConsonantalRoot String := ⟨["b", "r", "k"]⟩

/-- √ʕrf, unglossed in [faust-lampitelli-2026]: [ʕarifu] PRF-3MSG, [ʕɨrʌf] IMP, [ʕarʌf-]
DEP.PRF. -/
def arf : ConsonantalRoot String := ⟨["ʕ", "r", "f"]⟩

end Tigrinya.Phonology
