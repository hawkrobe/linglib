import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Process.RuleBased.Defs

/-!
# Akan Phonological Inventory (Palatalization-Relevant Segments)
@cite{mccarthy-prince-1995} @cite{schachter-fromkin-1968}

Segment inventory for the Akan velar–palatal alternation and its
interaction with reduplication (§5.1 of @cite{mccarthy-prince-1995}).

Akan palatalization: velars become corono-dorsal complex segments
(palatals) before front vowels. The segments defined here are the
minimal inventory needed to ground the OT analysis:

- `/k/`: voiceless velar stop ([+dorsal, −coronal])
- `/tɕ/`: voiceless palatal affricate ([+coronal, +dorsal, +del.rel.])
- `/a/`: low vowel ([−front] — does not trigger palatalization)
- `/ɪ/`: high front vowel ([+front] — triggers palatalization)

The feature specifications follow @cite{hayes-2009} for manner and
laryngeal features, and the corono-dorsal complex analysis of Akan
palatals from @cite{mccarthy-prince-1995} (citing Keating 1987,
Clements 1976, Hume 1992).
-/

open Phonology

namespace Fragments.Akan.Phonology

-- ============================================================================
-- § 1: Consonant Inventory
-- ============================================================================

/-- /k/: voiceless velar stop — [+dorsal, −coronal].
    The underlying segment in stems like /ka/ 'bite'. -/
def seg_k : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.delayedRelease, false),
   (Feature.dorsal, true), (Feature.coronal, false)]

/-- /tɕ/: voiceless palatal affricate — [+coronal, +dorsal, +del.rel.].
    The palatalized output of /k/ before front vowels.
    Corono-dorsal complex segment per Keating 1987 (cited in
    @cite{mccarthy-prince-1995}): palatalization spreads [+coronal,
    −anterior] from the front vowel while preserving [+dorsal]. -/
def seg_tc : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.delayedRelease, true),
   (Feature.dorsal, true), (Feature.coronal, true),
   (Feature.anterior, false), (Feature.distributed, true)]

-- ============================================================================
-- § 2: Vowel Inventory
-- ============================================================================

/-- /a/: low vowel — [−front, +back].
    Does not trigger palatalization. -/
def seg_a : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.front, false), (Feature.back, true)]

/-- /ɪ/: high front vowel — [+front, −back, +high].
    Triggers palatalization of preceding velars. The [+front] feature
    (combined with [+coronal] in Hume 1992's analysis of front vowels)
    is the trigger for PAL. -/
def seg_i : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.front, true), (Feature.back, false)]

-- ============================================================================
-- § 3: Feature Verification
-- ============================================================================

/-- /k/ is [−coronal] — the target of palatalization. -/
theorem k_minus_coronal : seg_k.hasValue Feature.coronal false = true := by native_decide

/-- /tɕ/ is [+coronal] — the output of palatalization. -/
theorem tc_plus_coronal : seg_tc.hasValue Feature.coronal true = true := by native_decide

/-- /k/ is [+dorsal]. -/
theorem k_plus_dorsal : seg_k.hasValue Feature.dorsal true = true := by native_decide

/-- /tɕ/ is [+dorsal] — corono-dorsal complex segment. -/
theorem tc_plus_dorsal : seg_tc.hasValue Feature.dorsal true = true := by native_decide

/-- /ɪ/ is [+front] — the trigger for palatalization. -/
theorem i_plus_front : seg_i.hasValue Feature.front true = true := by native_decide

/-- /a/ is [−front] — does not trigger palatalization. -/
theorem a_minus_front : seg_a.hasValue Feature.front false = true := by native_decide

/-- Palatalization is a [coronal] feature change: /k/ is [−cor], /tɕ/ is [+cor].
    The OT constraints IDENT-IO(−cor) and IDENT-BR(−cor) penalize exactly
    this feature difference. -/
theorem palatalization_is_coronal_change :
    seg_k.hasValue Feature.coronal false = true ∧
    seg_tc.hasValue Feature.coronal true = true := ⟨by native_decide, by native_decide⟩

/-- OCP(+cor) targets segments that are [+coronal]. /tɕ/ violates OCP
    when adjacent to another [+coronal] segment. /k/ does not. -/
theorem ocp_targets_palatalized :
    seg_tc.hasValue Feature.coronal true = true ∧
    seg_k.hasValue Feature.coronal true = false := ⟨by native_decide, by native_decide⟩

end Fragments.Akan.Phonology
