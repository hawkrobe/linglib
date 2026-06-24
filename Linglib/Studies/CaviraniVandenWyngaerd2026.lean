/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.ElementTheory

/-!
# Cavirani & Vanden Wyngaerd (2026): A representational analysis of Czech palatalisation
[cavirani-vandenwyngaerd-2026]

Czech has three patterns of palatalisation, each triggered by a different set of
suffixes. The paper's central claim is that the trigger is **not** the front
vowel of the suffix but a set of **floating melodic elements** that the suffix
carries, and that the three triggers — which the paper calls PAL₁, PAL₂, PAL₃
("small", "medium", "big" palatalisation) — stand in a **containment relation**:

| palataliser | adds       | example suffix          |
| PAL₁        | I          | `-ě` (LOC/DAT.F.SG)     |
| PAL₂        | H.I        | `-ěj` (CMPR), `-i` (CAUS) |
| PAL₃        | H.I̲ (headed I) | `-ěn` (PASS.PTCP)   |

(In the dot notation, the element(s) before the dot sit in the manner node and
those after it in the place node.) PAL₁ ⊏ PAL₂ adds the manner element |H|;
PAL₂ ⊏ PAL₃ promotes the place element |I| to headed |I̲|. The increasing
elemental complexity is *exactly* the [element-theoretic refinement order]
(`ElementTheory.Segment.Refines`) of the substrate.

## What this file formalizes

* **§1** the plain Czech consonant inventory as `Segment`s (paper Tables 9, 11,
  13; voiceless members only, per the paper's simplification);
* **§2** the three palatalisers and the suffix morphemes that carry them
  (Table 8);
* **§3** `palatalise` — floating elements dock onto the base, per-node;
* **§4** `palataliser_chain`: PAL₁ ⊏ PAL₂ ⊏ PAL₃ (the headline);
* **§5** the substance-free phonetic interpretation `interpret : Segment →
  CzechPhone` (lexical access; [backley-2011]-style), and the velar/coronal
  derivation tables (Tables 11, 13);
* **§6** the small/medium/big distinction (Table 4b), diagnosed by /k/ and /t/;
* **§7** the substance-free payoff: `interpret` is non-injective (one phone, many
  structures — Table 12), and the |I|-vs-|I̲| contrast is phonetically *invisible*
  on velars yet *visible* on /s/;
* **§8** labial **output invisibility** and **lateral resistance**, both derived
  from the |U|⊕|I| antagonism (`ElementTheory.Antagonistic`): a place node that
  already hosts |U| cannot also host the palatalising |I|.

## What this file does NOT formalize

* The strict-CV skeleton and the government/licensing lateral relations that
  drive the *derivations* (which root node a floating element docks at, when a
  final empty V is a proper governor). The paper develops these in strict CV
  ([lowenstamm-1996], [scheer-2004]); here we model the *representational
  output* — which elements end up in which node — not the slot-by-slot
  association. (`Studies/FaustLampitelli2026.lean` inlines a `StrictCV`
  substrate; a shared graduation is the natural next step, this being its second
  consumer.)
* Whether a blocked labial palataliser surfaces as a glide [j] (CMPR `-ěj`) or
  is fully output-invisible (CAUS `-i`, PASS.PTCP `-ěn`): the paper ties this to
  the CV profile of the suffix (whether its initial vowel is associated with a
  V-slot), which is the strict-CV part set aside above. We model the shared
  cause — the colour clash — not the suffix-specific outcome.
* The nasal-spreading detail /m/ + palataliser → [mɲ] (paper §4.3.3): the |L| of
  /m/ spreads to a following C-slot, surfacing as a separate [ɲ]. Modelling the
  extra segment needs the strict-CV adjacency; we capture only that /m|'s place
  |U| blocks the palatalising |I| (the output-invisibility part).
-/

namespace CaviraniVandenWyngaerd2026

open ElementTheory

-- ============================================================================
-- § 1: The plain Czech consonant inventory (Tables 9, 11, 13)
-- ============================================================================

/-! Element decompositions, voiceless members only (the paper sets voicing
aside: a voiced consonant adds |L| in the laryngeal node, which is orthogonal to
palatalisation). The dot convention: manner node `.` place node. Velars are
**placeless** ([cavirani-vandenwyngaerd-2026] §4.3.1). /r/ has |A| in the
*manner* node (it is a liquid), whereas /s/ has |A| in the *place* node — the
contrast that the node geometry is needed for. -/

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
/-- /r/ = |A| — a rhotic, |A| in the *manner* node and nothing in place. -/
def r : Segment := ⟨MR.simplex .A, .empty, .empty⟩

/-- /p/ = |ʔ.U| — labial stop (|ʔ| manner, |U| place). -/
def p : Segment := ⟨MR.simplex .glottal, MR.simplex .U, .empty⟩
/-- /f/ = |H.U| — labial fricative. -/
def f : Segment := ⟨MR.simplex .H, MR.simplex .U, .empty⟩
/-- /m/ = |L.U| — labial nasal. -/
def m : Segment := ⟨MR.simplex .L, MR.simplex .U, .empty⟩
/-- /l/ = |A.U| — the lateral. It patterns with the labials because it contains
    |U| in its place node ([cavirani-vandenwyngaerd-2026] §4.3.4), which is why
    it resists palatalisation. -/
def l : Segment := ⟨MR.simplex .A, MR.simplex .U, .empty⟩

-- ============================================================================
-- § 2: The three palatalisers (Table 8) and their suffix morphemes
-- ============================================================================

/-- **PAL₁** ("small"): a floating |I| that docks in the place node. -/
def PAL₁ : Segment := ⟨.empty, MR.simplex .I, .empty⟩
/-- **PAL₂** ("medium"): floating |H| (manner) + |I| (place). -/
def PAL₂ : Segment := ⟨MR.simplex .H, MR.simplex .I, .empty⟩
/-- **PAL₃** ("big"): floating |H| (manner) + headed |I̲| (place). The headed |I|
    is the only difference from PAL₂. -/
def PAL₃ : Segment := ⟨MR.simplex .H, MR.headedSimplex .I, .empty⟩

/-- The suffixes that trigger palatalisation. Empirically, look-alike suffixes
    can differ in their palatalising element (the paper's core point): the hard
    vs soft agreement markers `-ý`/`-í` have identical vowels [iː] but only `-í`
    palatalises (`mladý` 'young.M.SG' vs `mladí` 'young.M.ANIM.PL'). -/
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

/-- Which palataliser each suffix carries (the paper's analysis, §4.2 / Table 8;
    the raw alternations are Tables 1–3). The comparative and causative both
    carry PAL₂; the passive participle carries the stronger PAL₃. -/
def Suffix.palataliser : Suffix → Segment
  | .locDatFSg   => PAL₁
  | .comparative => PAL₂
  | .causative   => PAL₂
  | .passPtcp    => PAL₃

-- ============================================================================
-- § 3: Palatalisation — floating elements dock onto the base
-- ============================================================================

/-- **Palatalisation**: the floating palataliser elements scan the base and
    dock, node by node ([cavirani-vandenwyngaerd-2026] §4.3, the association
    convention (13)) — the substrate's `Segment.dock` (per-node element-union,
    the palatalising |I̲| of PAL₃ overriding as the place head). -/
def palatalise (base pal : Segment) : Segment := base.dock pal

-- ============================================================================
-- § 4: The palataliser containment chain (the headline)
-- ============================================================================

/-- **PAL₁ ⊏ PAL₂ ⊏ PAL₃** — the three palatalisers form a chain in the
    elemental refinement order ([cavirani-vandenwyngaerd-2026]: small ⊏ medium ⊏
    big). PAL₁ ⊏ PAL₂ adds the manner element |H|; PAL₂ ⊏ PAL₃ promotes the
    place |I| to headed |I̲|. -/
theorem palataliser_chain : PAL₁ ≤ PAL₂ ∧ PAL₂ ≤ PAL₃ := by decide

/-- The three palatalisers are genuinely distinct (increasing complexity). -/
theorem palatalisers_distinct : PAL₁ ≠ PAL₂ ∧ PAL₂ ≠ PAL₃ ∧ PAL₁ ≠ PAL₃ := by decide

/-- The chain is therefore **strict**: PAL₁ ⊏ PAL₂ ⊏ PAL₃. -/
theorem palataliser_chain_strict : PAL₁ < PAL₂ ∧ PAL₂ < PAL₃ :=
  ⟨lt_of_le_of_ne palataliser_chain.1 palatalisers_distinct.1,
   lt_of_le_of_ne palataliser_chain.2 palatalisers_distinct.2.1⟩

-- ============================================================================
-- § 5: Phonetic interpretation and the derivation tables (Tables 11, 13)
-- ============================================================================

/-- The voiceless Czech phones appearing in the palatalisation tables. ASCII
    constructor names stand in for the IPA: `tsh` = [t͡ʃ], `sh` = [ʃ],
    `nj` = [ɲ], `rj` = [r̝]. -/
inductive CzechPhone
  | k | x | t | s | n | r          -- plain
  | ts | tsh | c | sh | nj | rj    -- palatalised
  deriving DecidableEq, Repr

/-- **Substance-free phonetic interpretation** (lexical access,
    [backley-2011]-style; [cavirani-vandenwyngaerd-2026] §4.1). A Czech
    consonant's surface phone is read off the elements in its manner and place
    nodes. The interpretation is *language-particular* and *context-dependent*:
    the |I|-vs-|I̲| distinction is read differently on velars (no effect) than on
    coronal /s/ ([s] vs [ʃ]) — see §7. Its domain is the **non-labial**
    inventory: labials are output-invisible (§8) and not interpreted here. -/
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

/-- The plain consonants are interpreted as themselves. -/
theorem plain_interpretation :
    interpret k = .k ∧ interpret x = .x ∧ interpret t = .t ∧
    interpret s = .s ∧ interpret n = .n ∧ interpret r = .r := by decide

/-- **Velar derivations** (Table 11): /k/ shows the full small/medium/big split
    (ts ~ tʃ ~ tʃ), /x/ neutralises to [ʃ] throughout. -/
theorem velar_derivations :
    interpret (palatalise k PAL₁) = .ts ∧
    interpret (palatalise k PAL₂) = .tsh ∧
    interpret (palatalise k PAL₃) = .tsh ∧
    interpret (palatalise x PAL₁) = .sh ∧
    interpret (palatalise x PAL₂) = .sh ∧
    interpret (palatalise x PAL₃) = .sh := by decide

/-- **Coronal derivations** (Table 13). /t/: c ~ c ~ ts (big is the odd one
    out). /s/: s ~ s ~ ʃ (only big has a visible effect). /n/ and /r/ palatalise
    uniformly to [ɲ] and [r̝]. -/
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

-- ============================================================================
-- § 6: Small / medium / big (Table 4b)
-- ============================================================================

/-- Surface phone produced by applying a suffix's palataliser to a base. -/
def applySuffix (base : Segment) (suf : Suffix) : CzechPhone :=
  interpret (palatalise base suf.palataliser)

/-- The actual suffixes' outcomes on the diagnostic velar /k/: `-ě` (LOC/DAT.F.SG)
    gives small [ts]; `-ěj` (CMPR) and `-i` (CAUS) give medium [tʃ]; `-ěn`
    (PASS.PTCP) gives big [tʃ] — look-alike front-vowel suffixes splitting by the
    floating element they carry, not by their vowel. -/
theorem suffix_outcomes_on_k :
    applySuffix k .locDatFSg = .ts ∧
    applySuffix k .comparative = .tsh ∧
    applySuffix k .causative = .tsh ∧
    applySuffix k .passPtcp = .tsh := by decide

/-- /k/ is the diagnostic for **small vs medium**: PAL₁ gives [ts] but PAL₂
    gives [tʃ]. -/
theorem k_small_vs_medium :
    interpret (palatalise k PAL₁) ≠ interpret (palatalise k PAL₂) := by decide

/-- /t/ is the diagnostic for **medium vs big**: PAL₂ gives [c] but PAL₃ gives
    [ts]. -/
theorem t_medium_vs_big :
    interpret (palatalise t PAL₂) ≠ interpret (palatalise t PAL₃) := by decide

/-- The three patterns are genuinely three: there is a base separating small
    from medium (/k/) and a base separating medium from big (/t/), so no two of
    the palatalisers are interpretationally collapsible. -/
theorem three_distinct_patterns :
    (∃ base, interpret (palatalise base PAL₁) ≠ interpret (palatalise base PAL₂)) ∧
    (∃ base, interpret (palatalise base PAL₂) ≠ interpret (palatalise base PAL₃)) :=
  ⟨⟨k, k_small_vs_medium⟩, ⟨t, t_medium_vs_big⟩⟩

-- ============================================================================
-- § 7: The substance-free payoff
-- ============================================================================

/-- **`interpret` is non-injective** (Table 12: "/ʃ/ corresponds to four
    different underlying representations"). Palatalised /x/ (|H.I|) and big-
    palatalised /s/ (|H.A I̲|) are *different* element structures that the
    phonetic module maps onto the *same* phone [ʃ] — the hallmark of
    substance-free phonology. -/
theorem interpret_not_injective :
    interpret (palatalise x PAL₁) = .sh ∧
    interpret (palatalise s PAL₃) = .sh ∧
    (palatalise x PAL₁).place.elements ≠ (palatalise s PAL₃).place.elements := by
  decide

/-- The headedness of |I| is **phonetically invisible on velars**: |ʔH.I| (PAL₂)
    and |ʔH.I̲| (PAL₃) are different representations (different place head) but
    both surface as [tʃ]. -/
theorem headedness_invisible_on_velars :
    interpret (palatalise k PAL₂) = interpret (palatalise k PAL₃) ∧
    (palatalise k PAL₂).place.head ≠ (palatalise k PAL₃).place.head := by decide

/-- …yet the *same* |I|-vs-|I̲| difference is **visible on /s/**: |H.AI| (PAL₂)
    surfaces as [s] while |H.A I̲| (PAL₃) surfaces as [ʃ]. One structural
    distinction, two context-dependent interpretations. -/
theorem headedness_visible_on_coronal_s :
    interpret (palatalise s PAL₂) ≠ interpret (palatalise s PAL₃) := by decide

-- ============================================================================
-- § 8: Labial output invisibility and lateral resistance (the |U|⊕|I| clash)
-- ============================================================================

/-- A **colour clash** in the place node: |U| and |I| — an antagonistic pair
    ([backley-2011] §5.3.4) — both present. Czech does not allow a complex |I U|
    place ([cavirani-vandenwyngaerd-2026] §4.3.3, after [janku-2022]), so a
    place node carrying |U| cannot also host the palatalising |I|; the
    palataliser is then output-invisible (or surfaces as a separate glide). -/
def PlaceColourClash (seg : Segment) : Prop := ¬ seg.place.AntagonismFree

instance (seg : Segment) : Decidable (PlaceColourClash seg) := by
  unfold PlaceColourClash; infer_instance

/-- **Labial output invisibility**: docking the palatalising |I| onto a labial
    (place |U|) would create the forbidden |U I| place — the representational
    reason labials never fully palatalise. -/
theorem labial_output_invisible : PlaceColourClash (palatalise p PAL₁) := by decide

/-- The fricative /f/ and nasal /m/ behave the same way — all labials carry |U|
    in place. -/
theorem all_labials_clash :
    PlaceColourClash (palatalise f PAL₁) ∧ PlaceColourClash (palatalise m PAL₁) := by
  decide

/-- **Lateral resistance**: /l/ carries |U| in place too, so it clashes exactly
    as the labials do — the paper's explanation for why /l/ never palatalises
    ([cavirani-vandenwyngaerd-2026] §4.3.4). -/
theorem lateral_resists : PlaceColourClash (palatalise l PAL₁) := by decide

/-- By contrast, a velar (placeless) takes the palatalising |I| into an
    **antagonism-free** place node — which is why velars palatalise freely. -/
theorem velar_no_clash : (palatalise k PAL₁).place.AntagonismFree := by decide

/-- The clash is colour-specific: it is exactly the |U|–|I| antagonism. The
    coronals, whose place hosts |A| (and |I|), keep an antagonism-free place
    node under palatalisation. -/
theorem coronal_no_clash :
    (palatalise t PAL₁).place.AntagonismFree ∧ (palatalise s PAL₁).place.AntagonismFree := by
  decide

end CaviraniVandenWyngaerd2026
