import Linglib.Core.Morphology.ConsonantalRoot

/-!
# Modern Hebrew Consonantal Roots

A small inventory of Modern Hebrew consonantal roots, stored as `Root String`
(IPA-symbol segments). Used by templatic-morphology studies, in particular
@cite{faust-2026}'s analysis of the QaTaT–QaTa problem and templatic intrusion.

The Faust 2026 squib turns on whether a root's final segment is the glide
[j], because [j] cannot satisfy a [+consonantal] template-final C-slot. The
inventory below records both [j]-final triradicals (the case at issue) and
non-glide-final triradicals as the contrast class.
-/

namespace Fragments.Hebrew

open Core.Morphology

-- ============================================================================
-- § 1: [j]-final triradicals (@cite{faust-2026} (3))
-- ============================================================================

/-- √klj — base of [kala] PST.3MSG `roast`, [klija] action noun,
    [kaluj] passive participle. The third radical is the glide [j],
    which fails to associate to the [+c]-specified final C-slot of
    the verbal template (@cite{faust-2026} (4)). -/
def klj : Root String := ⟨["k", "l", "j"]⟩

/-- √dmj — base of nominal [dimuj] `simile` and the taQTiL noun
    [tadmit] `(public) image` (@cite{faust-2026} (9b)). -/
def dmj : Root String := ⟨["d", "m", "j"]⟩

/-- √bnj — base of passive participle [banuj] `built` and the
    taQTiL nouns [tavnit] `mold` (and similar). Third radical [j]. -/
def bnj : Root String := ⟨["b", "n", "j"]⟩

-- ============================================================================
-- § 2: Non-glide-final triradicals (control class)
-- ============================================================================

/-- √ktv — base of [katav] PST.3MSG `wrote`, [katuv] passive
    participle `written`. Final radical [v], a true consonant; the
    QaTaT–QaTa problem does not arise. -/
def ktv : Root String := ⟨["k", "t", "v"]⟩

/-- √sbr — base of [ʃavar] PST.3MSG `broke` (Faust uses this in the
    Amharic comparison; Hebrew cognate). -/
def sbr : Root String := ⟨["ʃ", "b", "r"]⟩

-- ============================================================================
-- § 3: Sanity properties
-- ============================================================================

/-- Every Hebrew root in this inventory is triradical. -/
theorem klj_triradical : klj.triradical = true := rfl
theorem dmj_triradical : dmj.triradical = true := rfl
theorem bnj_triradical : bnj.triradical = true := rfl
theorem ktv_triradical : ktv.triradical = true := rfl
theorem sbr_triradical : sbr.triradical = true := rfl

/-- The final segment of √klj is the glide [j] (the QaTaT–QaTa trigger). -/
theorem klj_final_is_j : klj.finalSegment = some "j" := rfl

end Fragments.Hebrew
