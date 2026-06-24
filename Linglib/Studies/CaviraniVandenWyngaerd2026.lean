/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.ElementTheory

/-!
# Cavirani & Vanden Wyngaerd (2026): Czech palatalisation
[cavirani-vandenwyngaerd-2026]

Czech has three palatalisation patterns triggered by different suffixes. The
trigger is not the suffix's front vowel but a set of **floating elements** the
suffix carries; the triggers (`PAL₁` ⊏ `PAL₂` ⊏ `PAL₃`, "small/medium/big")
stand in a **containment relation** — PAL₁ adds |I|, PAL₂ adds |H| + |I|, PAL₃
adds |H| + headed |I̲| — which is exactly the substrate's `Segment.Refines` order
(`palataliser_chain`).

Floating elements `dock` onto a base; the substance-free `interpret : Segment →
CzechPhone` reproduces the paper's tables (`velar_derivations`,
`coronal_derivations`), is non-injective (`interpret_not_injective`), and reads
the |I|-vs-|I̲| contrast differently on velars vs /s/. Labial output-invisibility
and lateral resistance follow from the |U|⊕|I| antagonism
(`labial_output_invisible`, `lateral_resists`).

## Scope

Representational output only — which elements end up in which node. The strict-CV
skeleton and government/licensing driving the slot-by-slot derivations
([lowenstamm-1996], [scheer-2004]), the glide-vs-invisible labial split, and the
/m/ → [mɲ] nasal spreading are not modelled. (`Studies/FaustLampitelli2026.lean`
inlines a `StrictCV` substrate; this is its second consumer — a shared graduation
is the natural next step.)
-/

namespace CaviraniVandenWyngaerd2026

open ElementTheory

/-! ### Plain consonants (Tables 9, 11, 13; voiceless members only)

The dot convention is manner node `.` place node. /r/ has |A| in the *manner*
node whereas /s/ has |A| in the *place* node — the contrast the geometry is for. -/

/-- /k/ = |ʔ| — a placeless velar stop. -/
def k : Segment := ⟨MR.simplex .glottal, .empty, .empty⟩
/-- /x/ = |H| — a placeless velar fricative. -/
def x : Segment := ⟨MR.simplex .H, .empty, .empty⟩
/-- /t/ = |ʔ.A| — coronal stop (|ʔ| manner, |A| place). -/
def t : Segment := ⟨MR.simplex .glottal, MR.simplex .A, .empty⟩
/-- /s/ = |H.AI| — coronal fricative (|H| manner, |A I| place). -/
def s : Segment := ⟨MR.simplex .H, MR.numeration {.A, .I}, .empty⟩
/-- /n/ = |L.A| — coronal nasal (|L| manner, |A| place). -/
def n : Segment := ⟨MR.simplex .L, MR.simplex .A, .empty⟩
/-- /r/ = |A| — a rhotic, |A| in the *manner* node. -/
def r : Segment := ⟨MR.simplex .A, .empty, .empty⟩

/-- /p/ = |ʔ.U| — labial stop (|ʔ| manner, |U| place). -/
def p : Segment := ⟨MR.simplex .glottal, MR.simplex .U, .empty⟩
/-- /f/ = |H.U| — labial fricative. -/
def f : Segment := ⟨MR.simplex .H, MR.simplex .U, .empty⟩
/-- /m/ = |L.U| — labial nasal. -/
def m : Segment := ⟨MR.simplex .L, MR.simplex .U, .empty⟩
/-- /l/ = |A.U| — the lateral; its |U| place makes it pattern with the labials
    [cavirani-vandenwyngaerd-2026]. -/
def l : Segment := ⟨MR.simplex .A, MR.simplex .U, .empty⟩

/-! ### The three palatalisers (Table 8) and their suffixes -/

/-- **PAL₁** ("small"): a floating |I| in the place node. -/
def PAL₁ : Segment := ⟨.empty, MR.simplex .I, .empty⟩
/-- **PAL₂** ("medium"): floating |H| (manner) + |I| (place). -/
def PAL₂ : Segment := ⟨MR.simplex .H, MR.simplex .I, .empty⟩
/-- **PAL₃** ("big"): floating |H| (manner) + headed |I̲| (place). -/
def PAL₃ : Segment := ⟨MR.simplex .H, MR.headedSimplex .I, .empty⟩

/-- The palatalising suffixes; look-alikes split by their floating element, not
    their vowel (`-ý`/`-í` are both [iː] but only `-í` palatalises). -/
inductive Suffix
  /-- `-ě` LOC/DAT.F.SG, e.g. `louka` 'meadow' ~ `louce`. -/
  | locDatFSg
  /-- `-ěj` comparative, e.g. `divoký` 'wild' ~ `divočejší`. -/
  | comparative
  /-- `-i` causative, e.g. `trpký` 'bitter' ~ `ztrpčil`. -/
  | causative
  /-- `-ěn` passive participle, e.g. `nutit` 'force' ~ `nucen`. -/
  | passPtcp
  deriving DecidableEq, Repr

/-- The palataliser each suffix carries (§4.2 / Table 8). -/
def Suffix.palataliser : Suffix → Segment
  | .locDatFSg   => PAL₁
  | .comparative => PAL₂
  | .causative   => PAL₂
  | .passPtcp    => PAL₃

/-! ### Palatalisation -/

/-- Palatalisation: the floating palataliser `dock`s onto the base node-by-node
    ([cavirani-vandenwyngaerd-2026] §4.3, convention (13)). -/
def palatalise (base pal : Segment) : Segment := base.dock pal

/-! ### The palataliser containment chain -/

/-- **PAL₁ ⊏ PAL₂ ⊏ PAL₃** in the refinement order [cavirani-vandenwyngaerd-2026]:
    PAL₁ ⊏ PAL₂ adds |H|; PAL₂ ⊏ PAL₃ heads |I|. -/
theorem palataliser_chain : PAL₁ ≤ PAL₂ ∧ PAL₂ ≤ PAL₃ := by decide

/-- The three palatalisers are distinct. -/
theorem palatalisers_distinct : PAL₁ ≠ PAL₂ ∧ PAL₂ ≠ PAL₃ ∧ PAL₁ ≠ PAL₃ := by decide

/-- The chain is therefore strict: PAL₁ ⊏ PAL₂ ⊏ PAL₃. -/
theorem palataliser_chain_strict : PAL₁ < PAL₂ ∧ PAL₂ < PAL₃ :=
  ⟨lt_of_le_of_ne palataliser_chain.1 palatalisers_distinct.1,
   lt_of_le_of_ne palataliser_chain.2 palatalisers_distinct.2.1⟩

/-! ### Phonetic interpretation and derivation tables (Tables 11, 13) -/

/-- The voiceless Czech phones; ASCII for IPA: `tsh`=[t͡ʃ], `sh`=[ʃ], `nj`=[ɲ],
    `rj`=[r̝]. -/
inductive CzechPhone
  | k | x | t | s | n | r          -- plain
  | ts | tsh | c | sh | nj | rj    -- palatalised
  deriving DecidableEq, Repr

/-- Substance-free phonetic interpretation (lexical access, [backley-2011]-style;
    [cavirani-vandenwyngaerd-2026] §4.1); domain is the non-labial inventory. -/
def interpret (seg : Segment) : CzechPhone :=
  if seg.manner.HasElement .glottal then                         -- stop / affricate
    if seg.place.HasElement .I then
      if seg.place.HasElement .A then
        if seg.place.IsHead .I then .ts else .c                  -- |…A I̲|→ts, |…A I|→c
      else
        if seg.manner.HasElement .H then .tsh else .ts           -- |ʔH.I|→tʃ, |ʔ.I|→ts
    else
      if seg.place.HasElement .A then .t else .k                 -- plain |ʔ.A|→t, |ʔ|→k
  else if seg.manner.HasElement .L then                          -- nasal
    if seg.place.HasElement .I then .nj else .n
  else if seg.manner.HasElement .A then                          -- liquid (|A| in manner)
    if seg.place.HasElement .I then .rj else .r
  else if seg.manner.HasElement .H then                          -- fricative
    if seg.place.HasElement .I then
      if seg.place.HasElement .A ∧ ¬ seg.place.IsHead .I then .s else .sh  -- |H.AI|→s, else ʃ
    else .x
  else .x

/-- The plain consonants interpret as themselves. -/
theorem plain_interpretation :
    interpret k = .k ∧ interpret x = .x ∧ interpret t = .t ∧
    interpret s = .s ∧ interpret n = .n ∧ interpret r = .r := by decide

/-- **Velar derivations** (Table 11): /k/ ts ~ tʃ ~ tʃ; /x/ neutralises to [ʃ]. -/
theorem velar_derivations :
    interpret (palatalise k PAL₁) = .ts ∧
    interpret (palatalise k PAL₂) = .tsh ∧
    interpret (palatalise k PAL₃) = .tsh ∧
    interpret (palatalise x PAL₁) = .sh ∧
    interpret (palatalise x PAL₂) = .sh ∧
    interpret (palatalise x PAL₃) = .sh := by decide

/-- **Coronal derivations** (Table 13): /t/ c ~ c ~ ts; /s/ s ~ s ~ ʃ; /n/, /r/
    uniform [ɲ], [r̝]. -/
theorem coronal_derivations :
    interpret (palatalise t PAL₁) = .c ∧
    interpret (palatalise t PAL₂) = .c ∧
    interpret (palatalise t PAL₃) = .ts ∧
    interpret (palatalise s PAL₁) = .s ∧
    interpret (palatalise s PAL₂) = .s ∧
    interpret (palatalise s PAL₃) = .sh ∧
    interpret (palatalise n PAL₁) = .nj ∧
    interpret (palatalise n PAL₂) = .nj ∧
    interpret (palatalise n PAL₃) = .nj ∧
    interpret (palatalise r PAL₁) = .rj ∧
    interpret (palatalise r PAL₂) = .rj ∧
    interpret (palatalise r PAL₃) = .rj := by decide

/-! ### Small / medium / big (Table 4b) -/

/-- Surface phone of a suffix's palataliser applied to a base. -/
def applySuffix (base : Segment) (suf : Suffix) : CzechPhone :=
  interpret (palatalise base suf.palataliser)

/-- The suffixes' outcomes on the diagnostic velar /k/: `-ě` [ts]; `-ěj`/`-i`
    [tʃ]; `-ěn` [tʃ] — look-alikes splitting by floating element, not vowel. -/
theorem suffix_outcomes_on_k :
    applySuffix k .locDatFSg = .ts ∧
    applySuffix k .comparative = .tsh ∧
    applySuffix k .causative = .tsh ∧
    applySuffix k .passPtcp = .tsh := by decide

/-- /k/ diagnoses **small vs medium**: PAL₁ [ts] ≠ PAL₂ [tʃ]. -/
theorem k_small_vs_medium :
    interpret (palatalise k PAL₁) ≠ interpret (palatalise k PAL₂) := by decide

/-- /t/ diagnoses **medium vs big**: PAL₂ [c] ≠ PAL₃ [ts]. -/
theorem t_medium_vs_big :
    interpret (palatalise t PAL₂) ≠ interpret (palatalise t PAL₃) := by decide

/-- The three patterns are genuinely three (separated by /k/ and /t/). -/
theorem three_distinct_patterns :
    (∃ base, interpret (palatalise base PAL₁) ≠ interpret (palatalise base PAL₂)) ∧
    (∃ base, interpret (palatalise base PAL₂) ≠ interpret (palatalise base PAL₃)) :=
  ⟨⟨k, k_small_vs_medium⟩, ⟨t, t_medium_vs_big⟩⟩

/-! ### The substance-free payoff -/

/-- **`interpret` is non-injective** (Table 12): palatalised /x/ (|H.I|) and
    big-palatalised /s/ (|H.A I̲|) are different structures, both [ʃ]. -/
theorem interpret_not_injective :
    interpret (palatalise x PAL₁) = .sh ∧
    interpret (palatalise s PAL₃) = .sh ∧
    (palatalise x PAL₁).place.elements ≠ (palatalise s PAL₃).place.elements := by
  decide

/-- Headedness of |I| is **invisible on velars**: PAL₂ and PAL₃ differ in the
    place head but both surface as [tʃ]. -/
theorem headedness_invisible_on_velars :
    interpret (palatalise k PAL₂) = interpret (palatalise k PAL₃) ∧
    (palatalise k PAL₂).place.head ≠ (palatalise k PAL₃).place.head := by decide

/-- …yet the same |I|-vs-|I̲| difference is **visible on /s/**: [s] vs [ʃ]. -/
theorem headedness_visible_on_coronal_s :
    interpret (palatalise s PAL₂) ≠ interpret (palatalise s PAL₃) := by decide

/-! ### Labial output-invisibility and lateral resistance (the |U|⊕|I| clash) -/

/-- A **colour clash**: |U| and |I| (antagonistic) both in the place node — which
    Czech forbids ([cavirani-vandenwyngaerd-2026] §4.3.3, after [janku-2022]). -/
def PlaceColourClash (seg : Segment) : Prop := ¬ seg.place.AntagonismFree

instance (seg : Segment) : Decidable (PlaceColourClash seg) := by
  unfold PlaceColourClash; infer_instance

/-- **Labial output-invisibility**: docking |I| onto a labial (place |U|) would
    forge the forbidden |U I| place — so labials never fully palatalise. -/
theorem labial_output_invisible : PlaceColourClash (palatalise p PAL₁) := by decide

/-- /f/ and /m/ clash too — all labials carry |U| in place. -/
theorem all_labials_clash :
    PlaceColourClash (palatalise f PAL₁) ∧ PlaceColourClash (palatalise m PAL₁) := by
  decide

/-- **Lateral resistance**: /l/ carries |U| in place, so it clashes like the
    labials — why /l/ never palatalises ([cavirani-vandenwyngaerd-2026] §4.3.4). -/
theorem lateral_resists : PlaceColourClash (palatalise l PAL₁) := by decide

/-- A velar (placeless) keeps an antagonism-free place node — so velars
    palatalise freely. -/
theorem velar_no_clash : (palatalise k PAL₁).place.AntagonismFree := by decide

/-- The clash is colour-specific: coronals (place |A I|) stay antagonism-free. -/
theorem coronal_no_clash :
    (palatalise t PAL₁).place.AntagonismFree ∧ (palatalise s PAL₁).place.AntagonismFree := by
  decide

end CaviraniVandenWyngaerd2026
