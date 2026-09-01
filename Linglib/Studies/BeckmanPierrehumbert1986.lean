import Linglib.Features.Prosody
import Linglib.Phonology.Tone.Register
import Linglib.Fragments.Japanese.Prosody
import Linglib.Data.Examples.BeckmanPierrehumbert1986

/-!
# Beckman & Pierrehumbert (1986): Intonational Structure in Japanese and English

Japanese and English share a sparse-tone prosodic hierarchy: pitch accents
group into accentual phrases (at most one accent each), accentual phrases
into intermediate phrases, and those into intonation phrases. Bitonal pitch
accents trigger catathesis — pitch-range compression whose domain is the
intermediate phrase — in both languages; the languages differ in where
accents come from (lexical vs postlexical), in inventory size (one shape vs
six), and in catathesis timing (within vs after the trigger). Catathesis is
encoded as register downstep on `Tone`'s register tier: each bitonal accent
contributes a downstep feature, `Tone.realizePitch` yields the descending
staircase, and the intermediate-phrase boundary resets the register.

## Main statements

* `catathesis_terracing`, `split_ips_pitch_independent`: chained bitonal
  accents produce the staircase (Figs. 11, 13), and an intermediate-phrase
  boundary resets the register (Fig. 17).
* `unaccented_no_catathesis`: an unaccented phrase's phrasal H + boundary L
  does not trigger catathesis — the trigger is the accent's HL, unlike
  African downdrift (§3.1).
* `japanese_smaller_inventory`, `japanese_accents_all_bitonal`: the two
  systems differ in accent inventory and specification, not in
  architecture (§2.1, §6).

## References

* [beckman-pierrehumbert-1986]: Intonational structure in Japanese and
  English. *Phonology Yearbook* 3.
* [pierrehumbert-1980]: The Phonology and Phonetics of English Intonation.
-/

namespace BeckmanPierrehumbert1986

open Features.Prosody
open Tone

/-! ### The accentual phrase (§2.2) -/

/-- An accentual phrase: the lowest level of prosodic phrasing defined by
the intonation pattern. In Japanese, delimited by a phrasal H and boundary
L, containing at most one pitch accent — an unaccented AP has the rising
L–H shape but no accentual fall (§2.2). In English the unit is less firmly
established: the domain of a single pitch accent (§2.4). Culminativity is
structural — a single `accent` field; grouping two accented words into one
AP deletes the second accent (§2.3, Fig. 6). -/
structure AccentualPhrase where
  /-- Pitch accent type (null if unaccented). -/
  accent : PitchAccent
  /-- Number of words grouped in this phrase. -/
  nWords : Nat
  deriving Repr, DecidableEq

/-- An AP is accented iff it has a non-null accent. -/
def AccentualPhrase.isAccented (ap : AccentualPhrase) : Bool :=
  ap.accent != .null

/-! ### Catathesis as register downstep (§3) -/

/-- Register specifications for a sequence of APs: each bitonal accent
contributes a register downstep; null or monotonal accents contribute
nothing. The descending staircase of catathesis chains (Figs. 11, 13) is
register terracing under `Tone.realizePitch`. -/
def catathesisToRegisterSpecs (aps : List AccentualPhrase) : List TRN :=
  aps.map (λ ap => if ap.accent.isBitonal then TRN.downstep else TRN.empty)

/-- Two chained bitonal accents produce a two-step staircase (§3, Fig. 11). -/
theorem catathesis_terracing (n : Int) :
    realizePitch n [TRN.downstep, TRN.downstep] = [n - 1, n - 1 - 1] := rfl

/-- Catathesis lowers pitch below the starting level. -/
theorem catathesis_lowers (n : Int) :
    (realizePitch n [TRN.downstep]).head? = some (n - 1) := rfl

/-- Number of catathesis applications in a sequence of APs. -/
def catathesisCount (aps : List AccentualPhrase) : Nat :=
  (aps.filter (·.accent.isBitonal)).length

/-- No bitonal accents, no catathesis: unaccented sequences show no
compression. -/
theorem no_bitonal_no_catathesis (aps : List AccentualPhrase)
    (h : ∀ ap ∈ aps, ap.accent.isBitonal = false) :
    catathesisCount aps = 0 := by
  simp only [catathesisCount]
  rw [List.filter_eq_nil_iff.mpr (by intro a ha; simp [h a ha])]
  simp

/-- Catathesis is triggered by the accent's HL, not by any HL sequence:
every unaccented AP carries a phrasal H + boundary L, yet only accented
APs trigger — the contrast with African downdrift (§3.1). -/
theorem unaccented_no_catathesis :
    PitchAccent.null.isBitonal = false := rfl

/-! ### The intermediate phrase (§4) -/

/-- An intermediate phrase: accentual phrases terminated by a phrase
accent. In Japanese the ip is the catathesis domain, can be a single AP,
and seldom contains more than three; its boundary is marked by pause or
glottalization (§4.1). In English, the phrase accent of
[pierrehumbert-1980] is reanalyzed as the ip-terminal tone, the boundary
tone as IP-terminal (§4.3). -/
structure IntermediatePhrase where
  /-- Accentual phrases within this ip. -/
  aps : List AccentualPhrase
  /-- Phrase accent: terminal tone of the ip. -/
  phraseAccent : PhraseAccent
  /-- An ip contains at least one AP. -/
  aps_nonempty : aps ≠ [] := by decide
  deriving Repr

/-- An intonation phrase: one or more intermediate phrases terminated by a
boundary tone (§4.2–4.3). -/
structure IntonationPhrase where
  /-- Intermediate phrases within this IP. -/
  ips : List IntermediatePhrase
  /-- Boundary tone: terminal tone of the IP. -/
  boundaryTone : BoundaryTone
  /-- Non-empty. -/
  ips_nonempty : ips ≠ [] := by decide
  deriving Repr

/-- The terminal contour of an IP: the final ip's phrase accent plus the
IP boundary tone — the §4.3 decomposition of [pierrehumbert-1980]'s
terminal sequence. -/
def IntonationPhrase.terminalContour (ip : IntonationPhrase) : TerminalContour :=
  let lastIp := ip.ips.getLast ip.ips_nonempty
  ⟨lastIp.phraseAccent, ip.boundaryTone⟩

/-- Register specs within a single ip: one catathesis chain. -/
def ipRegisterSpecs (ip : IntermediatePhrase) : List TRN :=
  catathesisToRegisterSpecs ip.aps

/-- Register specs across an IP: each ip resets the register — the
structural form of "catathesis is blocked by ip boundaries" (§4.1, §4.4;
Fig. 17 vs Figs. 12–13). -/
def ipRegisterSpecsAcrossIps (ips : List IntermediatePhrase) : List (List TRN) :=
  ips.map ipRegisterSpecs

/-! ### The two intonation systems (§2, §3.3, §6) -/

/-- Where catathesis takes effect relative to its trigger (§3.2–3.3): in
Japanese within the accent itself (the trailing L is already compressed),
in English only after the second tone of the bitonal accent. -/
inductive CatathesisTiming where
  | withinAccent
  | afterAccent
  deriving Repr, DecidableEq

/-- A language's intonation-system parameters (§6): how accents are
specified, the contrastive accent shapes, whether unaccented words exist,
whether the AP boundary L is always present, and catathesis timing. -/
structure IntonationSystem where
  accentSpec : AccentSpecification
  /-- Contrastive pitch-accent shapes (excluding null). -/
  accentShapes : List PitchAccent
  /-- Lexically unaccented words/phrases exist. -/
  hasUnaccented : Bool
  /-- The AP boundary L is always present. -/
  apBoundaryLAlwaysPresent : Bool
  catathesisTiming : CatathesisTiming
  deriving Repr

/-- Accent-inventory size, derived from the shape list. -/
def IntonationSystem.accentInventorySize (sys : IntonationSystem) : Nat :=
  sys.accentShapes.length

/-- Japanese (§2, §6): lexical accent location, one shape, unaccented words
common, boundary L always present, catathesis within the accent. -/
def japanese : IntonationSystem :=
  { accentSpec := .lexical
    accentShapes := [.H_star_plus_L]
    hasUnaccented := true
    apBoundaryLAlwaysPresent := true
    catathesisTiming := .withinAccent }

/-- English (§2, §6): postlexical accent shape, six contrastive shapes,
every content word accentable, no AP boundary tone, catathesis after the
accent. -/
def english : IntonationSystem :=
  { accentSpec := .postlexical
    accentShapes := [.H_star, .L_star, .H_star_plus_L,
                     .H_plus_L_star, .L_star_plus_H, .L_plus_H_star]
    hasUnaccented := false
    apBoundaryLAlwaysPresent := false
    catathesisTiming := .afterAccent }

/-- Japanese accent location is lexical; English accent shape is
postlexical (§2.1, §2.5). -/
theorem accent_specification_differs :
    japanese.accentSpec = .lexical ∧ english.accentSpec = .postlexical :=
  ⟨rfl, rfl⟩

/-- Japanese has a smaller accent inventory than English, derived from the
shape lists (one vs six). -/
theorem japanese_smaller_inventory :
    japanese.accentInventorySize < english.accentInventorySize := by decide

/-- All Japanese accents are bitonal, so every accented AP triggers
catathesis. -/
theorem japanese_accents_all_bitonal :
    japanese.accentShapes.all (·.isBitonal) = true := rfl

/-- Not all English accents are bitonal — H* and L* are monotonal, so an
accent need not trigger catathesis. -/
theorem english_has_monotonal :
    english.accentShapes.all (·.isBitonal) = false := rfl

/-- Catathesis timing separates the systems (§3.3). -/
theorem catathesis_timing_differs :
    japanese.catathesisTiming = .withinAccent ∧
      english.catathesisTiming = .afterAccent := ⟨rfl, rfl⟩

-- Two supra-phrasal processes operate above the ip (§5): final lowering
-- (pitch-range compression near the end of a declarative; its domain is
-- discourse-controlled, not a fixed phonological unit) and declination
-- (gradual time-dependent lowering, ~10 Hz/sec for the strongest subject,
-- absent for one). Both exist in Japanese and probably in English; neither
-- is catathesis, which is structurally bounded by the ip.

/-! ### Worked configurations (Figs. 5, 11, 13, 17) -/

/-- An accented AP (*uma'i*, *mo'riya-no*). -/
def accentedAP : AccentualPhrase := ⟨.H_star_plus_L, 1⟩

/-- An unaccented AP (*amai*, *toriya-no mawari-no*). -/
def unaccentedAP : AccentualPhrase := ⟨.null, 1⟩

/-- Accented + unaccented AP in one ip (Fig. 5): catathesis applies once,
placing the second AP in a lowered range. -/
def twoAP_ip : IntermediatePhrase :=
  { aps := [accentedAP, unaccentedAP], phraseAccent := .L }

theorem twoAP_ip_specs :
    ipRegisterSpecs twoAP_ip = [TRN.downstep, TRN.empty] := rfl

/-- From baseline 4, the accented AP is downstepped to 3 and the unaccented
AP stays there. -/
theorem twoAP_ip_pitch :
    realizePitch 4 (ipRegisterSpecs twoAP_ip) = [3, 3] := by decide

/-- Two accented APs and an unaccented one in a single ip: the
two-application chains of Fig. 13. -/
def threeAP_ip : IntermediatePhrase :=
  { aps := [accentedAP, accentedAP, unaccentedAP], phraseAccent := .L }

theorem threeAP_ip_specs :
    ipRegisterSpecs threeAP_ip = [TRN.downstep, TRN.downstep, TRN.empty] := rfl

/-- Pitch realization 4 → 3 → 2 → 2: the descending staircase. -/
theorem threeAP_ip_pitch :
    realizePitch 4 (ipRegisterSpecs threeAP_ip) = [3, 2, 2] := by decide

/-- The same APs split across two ips: the second ip starts at full range
(Fig. 17's blocked catathesis). -/
def split_ips : List IntermediatePhrase :=
  [{ aps := [accentedAP], phraseAccent := .L },
   { aps := [accentedAP, unaccentedAP], phraseAccent := .L }]

theorem split_ips_specs :
    ipRegisterSpecsAcrossIps split_ips
      = [[TRN.downstep], [TRN.downstep, TRN.empty]] := rfl

/-- Each ip realizes from its own baseline: [3] then [3, 3] — the register
does not leak across the boundary. -/
theorem split_ips_pitch_independent :
    (split_ips.map (realizePitch 4 ∘ ipRegisterSpecs)) = [[3], [3, 3]] := by
  decide

/-- Without the boundary the same APs form one chain, [3, 2, 2]: the second
accented AP would be a step lower than with the reset. -/
theorem catathesis_without_boundary :
    realizePitch 4
        (catathesisToRegisterSpecs [accentedAP, accentedAP, unaccentedAP])
      = [3, 2, 2] := by decide

/-! ### Monotonicity of catathesis -/

/-- More bitonal accents give pointwise lower-or-equal pitch. -/
theorem more_catathesis_lower_pitch :
    List.Forall₂ (· ≤ ·)
      (realizePitch 4 [TRN.downstep, TRN.downstep, TRN.empty])
      (realizePitch 4 [TRN.downstep, TRN.empty, TRN.empty]) := by decide

/-- A fresh ip starting from the reset baseline 4 sits pointwise above the
same specs continued from a compressed baseline 3 — blocking raises pitch
(`Tone.realizePitch_baseline_mono` carries the general fact). -/
theorem catathesis_blocking_concrete :
    List.Forall₂ (· ≤ ·)
      (realizePitch 3 [TRN.downstep, TRN.empty])
      (realizePitch 4 [TRN.downstep, TRN.empty]) := by decide

/-- Catathesis specs never raise the register: catathesis is monotonically
compressive. -/
theorem catathesis_specs_no_raising (aps : List AccentualPhrase)
    (s : TRN) (hs : s ∈ catathesisToRegisterSpecs aps) :
    s = TRN.empty ∨ s = TRN.downstep := by
  simp only [catathesisToRegisterSpecs, List.mem_map] at hs
  obtain ⟨ap, _, rfl⟩ := hs
  rcases Bool.eq_false_or_eq_true (ap.accent.isBitonal) with h | h <;> simp [h]

/-! ### Japanese accentual phrases from the lexicon

An AP over grouped word entries is accented iff some word is lexically
accented, its shape always H*+L, with grouping deleting all but one accent
(§2.3, Fig. 6) — built from the `Fragments.Japanese.Prosody` word
entries. -/

section JapaneseAP
open Japanese.Prosody

/-- The accentual phrase over grouped word entries: accented (always H*+L
in Japanese) iff some word is lexically accented (§2.2–2.3). -/
def AccentualPhrase.ofWords (ws : List ProsodicEntry) : AccentualPhrase :=
  { accent := if ws.any (·.isAccented) then .H_star_plus_L else .null
    nWords := ws.length }

/-- An AP of words triggers catathesis iff some word is accented, since the
only accent shape H*+L is bitonal (§3.1). -/
theorem ofWords_isBitonal (ws : List ProsodicEntry) :
    (AccentualPhrase.ofWords ws).accent.isBitonal = ws.any (·.isAccented) := by
  unfold AccentualPhrase.ofWords
  split <;> simp_all [PitchAccent.isBitonal]

/-- *uma'i mame'* 'delicious beans' forms an accented AP (Figs. 6, 9), so
it triggers catathesis on what follows (Figs. 12–13's `a` points). -/
theorem umai_mame_bitonal :
    (AccentualPhrase.ofWords [umai, mame]).accent.isBitonal = true := rfl

/-- *amai ame* 'sweet candy' forms an unaccented AP, so it triggers no
catathesis (the *amai ame* materials of Figs. 18–21, `u` points). -/
theorem amai_ame_not_bitonal :
    (AccentualPhrase.ofWords [amai, ameCandy]).accent.isBitonal = false := rfl

end JapaneseAP

end BeckmanPierrehumbert1986
