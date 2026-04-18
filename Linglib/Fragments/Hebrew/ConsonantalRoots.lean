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

/-- √klt — base of [kalat] PST.3MSG `receive`, [klita] action noun,
    [kalut] passive participle (@cite{faust-2026} (3a)). The full
    triradical control case: every radical surfaces in every form,
    no glide-related issue arises. -/
def klt : Root String := ⟨["k", "l", "t"]⟩

/-- √kll — base of [kalal] PST.3MSG `include`, [klila] action noun,
    [kalul] passive participle (@cite{faust-2026} (3b)). The
    final-radical-of-final-slot case: the second /l/ is the *final*
    root segment, so its association to the template-final C-slot
    does NOT violate \*Misalignment. This is the QaTaT pattern that
    contrasts with the QaTa pattern of (3c) under the same template. -/
def kll : Root String := ⟨["k", "l", "l"]⟩

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
theorem klt_triradical : klt.triradical = true := rfl
theorem kll_triradical : kll.triradical = true := rfl
theorem dmj_triradical : dmj.triradical = true := rfl
theorem bnj_triradical : bnj.triradical = true := rfl
theorem ktv_triradical : ktv.triradical = true := rfl
theorem sbr_triradical : sbr.triradical = true := rfl

/-- The final segment of √klj is the glide [j] (the QaTaT–QaTa trigger). -/
theorem klj_final_is_j : klj.finalSegment = some "j" := rfl

/-- The final segment of √klt is the consonant [t] — distinguishes the
    full-triradical control case (3a) from the [j]-final case (3c). -/
theorem klt_final_is_t : klt.finalSegment = some "t" := rfl

/-- The final segment of √kll is /l/, identical to its medial — but
    \*Misalignment cares about *root index*, not surface identity, so
    spreading the final /l/ to template-final is legitimate. -/
theorem kll_final_is_l : kll.finalSegment = some "l" := rfl

end Fragments.Hebrew
