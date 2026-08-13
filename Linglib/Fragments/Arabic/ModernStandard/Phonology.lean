import Linglib.Data.PHOIBLE.Inventories.Arabic
import Mathlib.Data.Finset.Insert

/-!
# Modern Standard Arabic phonology

The 28 consonants of Modern Standard Arabic ([ryding-2005]) as
`Consonant`, with the labial place class `Consonant.IsLabial` consumed by
the OCP-Place co-occurrence literature. `phonemeInventory` binds the
canonical PHOIBLE doculect ([moran-mccloy-2019] ID 2157, an urban
composite of Safad, Beirut, Damascus, and Kuwait), which confirms the
consensus values /dʒ/ (ج) and /ðˤ/ (ظ) — corpus-transcription traditions
write these as g and zˤ — and differs from the classical inventory only
in dialect-phonetic detail (aspiration marks, an emphatic lateral).
-/

namespace Arabic.ModernStandard

/-- The canonical PHOIBLE inventory for ISO `arb`
([moran-mccloy-2019] ID 2157). -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Arabic.arb

/-- The 28 consonants of Modern Standard Arabic ([ryding-2005]), IPA with
`Emph` for the emphatic (superscript ˁ) series. -/
inductive Consonant where
  /-- /b/ — voiced labial stop. -/
  | b
  /-- /f/ — voiceless labial fricative. -/
  | f
  /-- /m/ — labial nasal. -/
  | m
  /-- /t/ — voiceless coronal stop. -/
  | t
  /-- /d/ — voiced coronal stop. -/
  | d
  /-- /tˁ/ — emphatic voiceless coronal stop. -/
  | tEmph
  /-- /dˁ/ — emphatic voiced coronal stop. -/
  | dEmph
  /-- /θ/ — voiceless coronal fricative. -/
  | theta
  /-- /ð/ — voiced coronal fricative. -/
  | edh
  /-- /ðˁ/ (ظ) — emphatic voiced coronal fricative; [zˁ] in many
  varieties and romanizations. -/
  | edhEmph
  /-- /s/ — voiceless coronal sibilant. -/
  | s
  /-- /z/ — voiced coronal sibilant. -/
  | z
  /-- /sˁ/ — emphatic voiceless coronal sibilant. -/
  | sEmph
  /-- /ʃ/ — voiceless palatoalveolar sibilant. -/
  | esh
  /-- /dʒ/ (ج) — voiced palatoalveolar affricate; regionally [ʒ] ~ [ɡ]. -/
  | jim
  /-- /k/ — voiceless dorsal stop. -/
  | k
  /-- /q/ — uvular stop. -/
  | q
  /-- /χ/ — voiceless uvular fricative. -/
  | chi
  /-- /ʁ/ — voiced uvular fricative. -/
  | gamma
  /-- /ħ/ — voiceless pharyngeal fricative. -/
  | hbar
  /-- /ʕ/ — voiced pharyngeal fricative. -/
  | ayin
  /-- /h/ — voiceless laryngeal fricative. -/
  | h
  /-- /ʔ/ — laryngeal stop. -/
  | glottal
  /-- /l/ — coronal lateral. -/
  | l
  /-- /r/ — coronal rhotic. -/
  | r
  /-- /n/ — coronal nasal. -/
  | n
  /-- /w/ — labial-velar glide. -/
  | w
  /-- /j/ — palatal glide. -/
  | j
  deriving DecidableEq

/-- The labial place class `{b, f, m, w}`. -/
def Consonant.IsLabial (x : Consonant) : Prop :=
  x ∈ ({.b, .f, .m, .w} : Finset Consonant)

instance : DecidablePred Consonant.IsLabial :=
  λ x => inferInstanceAs (Decidable (x ∈ ({.b, .f, .m, .w} : Finset Consonant)))

end Arabic.ModernStandard
