/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Root

/-!
# Tigrinya Phonological Inventory and Verbal Roots
[leslau-1941] [berhane-1991] [buckley-1994]
[buckley-1997-vowel-length] [denais-1990]
[lowenstamm-prunet-1985] [faust-lampitelli-2026]

Theory-neutral IPA inventory and the verbal roots used in the
[faust-lampitelli-2026] guttural-synersis analysis.

Per fragment-schema discipline (CLAUDE.md), this file carries only
*consensus typological metadata* — IPA strings, the consonantal-root
inventory, and the unanimous facts about which segments are gutturals.
The Element-Theory decomposition of these segments (e.g. that
pharyngeals are headed by |A|, [ʌ] is non-headed |A|, [a] is headed |A|)
is paper-specific theoretical apparatus and lives in
`Studies/FaustLampitelli2026.lean` as a per-segment
projection, not in this fragment.

## Vowel inventory

Following [leslau-1941], [berhane-1991], [denais-1990],
and the paper's §2.1: Tigrinya has **six full vowel qualities**
[a, ʌ, i, u, e, o] plus a **weak vowel [ɨ]**. The weak vowel is
considered epenthetic by [buckley-1994], [denais-1990],
[berhane-1991] and the paper, occurring only where its absence
would yield a phonotactic violation.

## Guttural inventory

The paper §2.1: "the consonantal inventories of both languages include
a class of sounds known as gutturals. In both languages, that group
includes two glottals [ʔ, h] and two pharyngeals [ʕ, ħ]." The
extended ET inventory in eq. (20) lists [χ, ʁ] as well, but the
paper's footnote 14 confirms they are unattested in Tigrinya/Tigre.
This file lists only the four attested gutturals.

## Cross-reference: PHOIBLE 2.0

[moran-mccloy-2019] inventory ID 1350 (`tigr1271`, Tigrinya,
source `ph`) confirms both the 7-vowel inventory `{a, e, i, o, u, ɨ,
ʌ}` and the 4-guttural inventory `{ʔ, h, ʕ, ħ}` exactly as
described above. The paper's footnote-14 claim that the uvulars
[χ, ʁ] are unattested is confirmed: neither is in the PHOIBLE
Tigrinya inventory. This fragment is therefore consensus typology
across the paper's empirical sources (Berhane, Buckley, Denais,
Leslau) and PHOIBLE's `ph` donor.

## Naming convention

Lean identifiers cannot contain the IPA characters ʔ, ʕ, ħ, ʌ, ɨ.
Constructors and root definitions therefore use ASCII names with the
docstring stating the IPA form. Roots are semantic-named (e.g. `whip`
rather than `√grf`) for readability, with the consonantal melody
recorded in the body and explained in the docstring.

## Verbal roots

Tigrinya verbs are templatic ([faust-lampitelli-2023]): a triradical
(or biradical/quadriradical) consonantal root combines with a vocalic
template. The paper uses a small inventory exemplifying the four
scenarios its analysis treats:

* roots with no guttural radical (control class)
* roots with a final-position guttural
* roots with a medial-position guttural
* roots with weak |I|-final radicals (the bi-morphemic /iIu/ → [ju]
  syneresis case)

Roots are stored as `Morphology.Root String` per the existing
Hebrew/Amharic pattern.
-/

namespace Tigrinya.Phonology

open Morphology

-- ============================================================================
-- § 1: Vowel inventory (theory-neutral IPA)
-- ============================================================================

/-- The Tigrinya vowel inventory: six full qualities + weak [ɨ].
    Following [berhane-1991], [denais-1990],
    [leslau-1941].

    Constructor naming: ASCII names (since Lean identifiers cannot
    contain the IPA characters ʌ, ɨ); the IPA form is given in each
    docstring and recovered via `toIPA`. -/
inductive Vowel where
  /-- IPA [a] — headed low vowel (paper eq. 21). Co-occurs with
      adjacent gutturals via the lowering process (paper eq. 4). -/
  | a
  /-- IPA [ʌ] — non-headed low vowel (the unmarked low vowel; paper
      eq. 21). The vowel underlyingly preceding gutturals; surfaces
      as [a] when a guttural is adjacent. -/
  | aBare
  /-- IPA [i] — high front vowel. -/
  | i
  /-- IPA [u] — high back rounded vowel. -/
  | u
  /-- IPA [e] — mid front vowel. -/
  | e
  /-- IPA [o] — mid back rounded vowel. -/
  | o
  /-- IPA [ɨ] — weak (epenthetic) vowel. Phonetic realization of an
      empty nucleus per paper eq. (22) + [buckley-1994],
      [faust-2024]. -/
  | weak
  deriving DecidableEq, Repr

namespace Vowel

/-- IPA string of a vowel. -/
def toIPA : Vowel → String
  | .a     => "a"
  | .aBare => "ʌ"
  | .i     => "i"
  | .u     => "u"
  | .e     => "e"
  | .o     => "o"
  | .weak  => "ɨ"

/-- The vowel is low ([a] or [ʌ]). Both contain |A| in ET; in Hayes
    binary terms, both are [+low]. The headedness contrast between
    them is paper-specific apparatus. -/
def IsLow : Vowel → Prop
  | .a | .aBare => True
  | _           => False

instance : DecidablePred IsLow
  | .a | .aBare => isTrue trivial
  | .i | .u | .e | .o | .weak => isFalse not_false

/-- The vowel is high ([i] or [u]). -/
def IsHigh : Vowel → Prop
  | .i | .u => True
  | _       => False

instance : DecidablePred IsHigh
  | .i | .u => isTrue trivial
  | .a | .aBare | .e | .o | .weak => isFalse not_false

/-- The vowel is the epenthetic/weak [ɨ]. -/
def IsEpenthetic : Vowel → Prop
  | .weak => True
  | _     => False

instance : DecidablePred IsEpenthetic
  | .weak => isTrue trivial
  | .a | .aBare | .i | .u | .e | .o => isFalse not_false

end Vowel

-- ============================================================================
-- § 2: Guttural inventory
-- ============================================================================

/-- The four gutturals attested in Tigrinya per [faust-lampitelli-2026]
    §2.1: two glottals [ʔ, h] and two pharyngeals [ʕ, ħ]. The uvulars
    [χ, ʁ] from the extended ET inventory (paper eq. 20) are
    unattested in Tigrinya/Tigre (paper n. 14). -/
inductive Guttural where
  /-- IPA [ʔ] glottal stop. -/
  | glottalStop
  /-- IPA [h] voiceless glottal fricative. -/
  | h
  /-- IPA [ʕ] voiced pharyngeal fricative. Pharyngeal — headed by
      |A| in paper eq. 20. -/
  | pharyngealVoiced
  /-- IPA [ħ] voiceless pharyngeal fricative. Pharyngeal — headed
      by |A| in paper eq. 20. -/
  | pharyngealVoiceless
  deriving DecidableEq, Repr

namespace Guttural

/-- IPA string of a guttural. -/
def toIPA : Guttural → String
  | .glottalStop         => "ʔ"
  | .h                   => "h"
  | .pharyngealVoiced    => "ʕ"
  | .pharyngealVoiceless => "ħ"

/-- The guttural is a pharyngeal. Pharyngeals (ħ, ʕ) and laryngeals
    (ʔ, h) are differently classed in the paper's eq. 20: pharyngeals
    are headed by |A|, laryngeals are not. The headedness analysis
    itself lives in the study file; this predicate is the
    consensus-typology classification. -/
def IsPharyngeal : Guttural → Prop
  | .pharyngealVoiced | .pharyngealVoiceless => True
  | _                                        => False

instance : DecidablePred IsPharyngeal
  | .pharyngealVoiced | .pharyngealVoiceless => isTrue trivial
  | .glottalStop | .h => isFalse not_false

/-- The guttural is a laryngeal (glottal). -/
def IsLaryngeal : Guttural → Prop
  | .glottalStop | .h => True
  | _                 => False

instance : DecidablePred IsLaryngeal
  | .glottalStop | .h => isTrue trivial
  | .pharyngealVoiced | .pharyngealVoiceless => isFalse not_false

/-- The four-element list of attested Tigrinya gutturals. -/
def all : List Guttural :=
  [.glottalStop, .h, .pharyngealVoiced, .pharyngealVoiceless]

end Guttural

-- ============================================================================
-- § 3: Verbal Roots (the F&L 2026 working set)
-- ============================================================================

/-- √grf — 'whip'. Triradical, no gutturals. The control case for
    syneresis: paper PRF [gʌrif-e] (eq. 8a), no syncope across V-initial
    suffixes. Used throughout the paper as the non-guttural baseline. -/
def whip : Root String := ⟨["g", "r", "f"]⟩

/-- √smʕ — 'hear'. Triradical, final-position pharyngeal /ʕ/. Paper
    DEP.PRF [sʌmaʕ-] (eq. 4b), IMP.M [simaʕ] vs IMP.F [simʕ-i] (eq.
    10c) — syneresis applies when /ʌ/ + /ʕ/ are open-syllable
    adjacent before a vowel-initial suffix. -/
def hear : Root String := ⟨["s", "m", "ʕ"]⟩

/-- √sħb — 'pull'. Triradical, medial-position pharyngeal /ħ/. Paper
    DEP.PRF row in eq. 4d shows `saħab` (no hyphen on this row); eq.
    15d shows the variant `sahab- (~ sɨħab-)`. The opaque-syneresis
    case (paper §2.3 eq. 16): /sʌħʌb/ → fusion + lowering → /s_ħab/
    → epenthesis [siħab] or trans-guttural harmony [sahab]. -/
def pull : Root String := ⟨["s", "ħ", "b"]⟩

/-- √ʔsr — 'arrest'. Triradical, initial-position glottal stop. Paper
    DEP.PRF [ʔasʌr-] (eq. 4c), PRF [ʔasir-] — illustrates how the
    initial guttural interacts with stem vocalization. -/
def arrest : Root String := ⟨["ʔ", "s", "r"]⟩

/-- √stI — 'drink'. Bi-morphemic weak-final root: the third radical is
    the element /I/, which surfaces as [j] before vowels (paper eq.
    8b). The PRF paradigm exhibits |I|-syneresis: /sʌtI-u/ → [sʌtj-u]
    (the /i/ vocalization fuses with the /I/ radical and only the
    glide surfaces). The parallel motivating the paper's |A|-syneresis
    analysis. The capital "I" in the third position marks it as the
    underlying ET element (not a vowel /i/). -/
def drink : Root String := ⟨["s", "t", "I"]⟩

/-- √mhr — 'teach'. Triradical, medial-position glottal /h/. Paper IMP
    [mahar] (eq. 7e); PASS-PRF [ti-mihir] ~ [ti-mɨhir] (eq. 17c) —
    the latter shows the unexpected /CʌGV/ → [CɨGV] pattern of eq.
    (17), where the V-position is retained as epenthetic [ɨ]. -/
def teach : Root String := ⟨["m", "h", "r"]⟩

/-- √hrd — 'slaughter'. Triradical, initial /h/. Paper 2-PRF
    [ta-harrid] (eq. 7b) — the initial guttural triggers TGH so the
    prefix vowel surfaces as [a] instead of [i]. -/
def slaughter : Root String := ⟨["h", "r", "d"]⟩

/-- √hdm — 'escape'. Paper 2-PRF [ta-hadim] (eq. 7c) — same TGH
    pattern as `slaughter`. -/
def escape : Root String := ⟨["h", "d", "m"]⟩

/-- √sʔl — 'ask'. Triradical, medial /ʔ/. Paper IMP [saʔal] (eq. 7f)
    + 2-IMPRF [ti-siʔil] / PASS-PRF [tisiʔil ~ ti-sɨʔil] (eq. 17d) —
    the [ɨ] alternant in PASS-PRF is the eq. (17) retention pattern. -/
def ask : Root String := ⟨["s", "ʔ", "l"]⟩

/-- √glh — 'uncover'. Triradical, final-position /h/. Paper IMP.M
    [gilah] / IMP.F [gilh-i] (eq. 10d) — final-guttural syneresis case. -/
def uncover : Root String := ⟨["g", "l", "h"]⟩

/-- √nbħ — 'bark'. Triradical, final-position /ħ/. Paper IMP.M
    [niβah] / IMP.F [nibh-i] (eq. 10b) — the IMP.M shows the
    lowering of the underlying /ʌ/ to [a] before the final guttural,
    while IMP.F shows syneresis (the /ʌ/ vacates V₂). -/
def bark : Root String := ⟨["n", "b", "ħ"]⟩

/-- √brk — 'bless'. Triradical, no guttural. Type-C verb (paper p.
    12, with [a] after first radical throughout the inflection).
    Paper DEP.PRF [barʌk-ʌ] / GER [mi-bɨrak] (eq. 18c). The
    cooccurrence-restriction case: two heteromorphemic low elements
    are reduced non-locally across non-guttural /r/, with the first
    /a/ replaced by [ɨ] in the gerund — and the paper notes this is
    NOT phonotactically motivated since *[mibrak] would not pose a
    phonotactic problem (page 12). -/
def bless : Root String := ⟨["b", "r", "k"]⟩

end Tigrinya.Phonology
