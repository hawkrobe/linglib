import Linglib.Features.Prosody
import Linglib.Phonology.Tone.Register
import Linglib.Fragments.Japanese.Prosody
import Linglib.Data.Examples.BeckmanPierrehumbert1986

/-!
# Intonational structure in Japanese and English

[beckman-pierrehumbert-1986] give Japanese and English one sparse-tone prosodic hierarchy:
pitch accents group into accentual phrases with at most one accent each, accentual phrases
into intermediate phrases, and those into intonation phrases, the phrase accent of
[pierrehumbert-1980] becoming the terminal tone of the intermediate phrase and the boundary
tone that of the intonation phrase. In both languages a bitonal accent triggers catathesis,
the compression of the pitch range for everything that follows within the intermediate
phrase, so chained accents descend a staircase and a phrase boundary resets the register; an
unaccented phrase's phrasal H and boundary L do not trigger it, which separates catathesis
from African downdrift. The languages differ in where accents come from, lexical location in
Japanese against postlexical shape in English, in the inventory of shapes, one against six,
and in whether the compression takes effect within the accent or after it. Final lowering
and declination act above the intermediate phrase and are not catathesis.

## Implementation notes

Catathesis is register downstep on the tonal register tier: each bitonal accent contributes
a downstep node and `Tone.realizePitch` realizes the sequence as the running sum, so the
staircase, the boundary reset, and the comparison with an unbroken chain are theorems of the
register substrate rather than numbers read off figures. The Japanese accentual phrase is
built from the prosodic fragment's word entries.

## References

* [beckman-pierrehumbert-1986]
* [pierrehumbert-1980]
-/

namespace BeckmanPierrehumbert1986

open Features.Prosody Tone

/-! ### Accentual phrases and catathesis -/

/-- An accentual phrase: the lowest level of the hierarchy, carrying at most one pitch accent
(`null` when unaccented). -/
structure AccentualPhrase where
  accent : PitchAccent
  /-- The words grouped into the phrase. -/
  nWords : ℕ
  deriving Repr, DecidableEq

/-- The phrase carries an accent. -/
def AccentualPhrase.IsAccented (ap : AccentualPhrase) : Prop := ap.accent ≠ .null

instance (ap : AccentualPhrase) : Decidable ap.IsAccented := inferInstanceAs (Decidable (_ ≠ _))

/-- The register nodes of a sequence of accentual phrases: a downstep for each bitonal
accent and nothing otherwise. -/
def registerSpecs (aps : List AccentualPhrase) : List TRN :=
  aps.map λ ap => if ap.accent.isBitonal then TRN.downstep else TRN.empty

/-- The number of catathesis triggers in a sequence. -/
def catathesisCount (aps : List AccentualPhrase) : ℕ :=
  (aps.filter (·.accent.isBitonal)).length

variable (b : Int) (aps aps₁ aps₂ : List AccentualPhrase) (ap : AccentualPhrase)

@[simp] private theorem pitchEffect_downstep : TRN.downstep.pitchEffect = -1 := rfl
@[simp] private theorem pitchEffect_empty : TRN.empty.pitchEffect = 0 := rfl
@[simp] theorem catathesisCount_nil : catathesisCount [] = 0 := rfl

theorem catathesisCount_cons :
    catathesisCount (ap :: aps) = (if ap.accent.isBitonal then 1 else 0) + catathesisCount aps := by
  simp only [catathesisCount, List.filter_cons]
  split <;> ((try simp only [List.length_cons]); omega)

/-- No bitonal accent, no catathesis. -/
theorem catathesisCount_eq_zero_iff :
    catathesisCount aps = 0 ↔ ∀ ap ∈ aps, ap.accent.isBitonal = false := by
  simp [catathesisCount, List.filter_eq_nil_iff]

/-- Catathesis only compresses: no node of a sequence raises the register. -/
theorem pitchEffect_registerSpecs_nonpos {t : TRN} (h : t ∈ registerSpecs aps) :
    t.pitchEffect ≤ 0 := by
  simp only [registerSpecs, List.mem_map] at h
  obtain ⟨ap, _, rfl⟩ := h
  split <;> decide

/-- The net shift of a sequence: one step down per bitonal accent. -/
theorem sum_pitchEffect_registerSpecs :
    ((registerSpecs aps).map TRN.pitchEffect).sum = -(catathesisCount aps : Int) := by
  induction aps with
  | nil => rfl
  | cons ap aps ih =>
    simp only [registerSpecs, List.map_cons, List.sum_cons, catathesisCount_cons] at ih ⊢
    rw [ih]
    split <;> (simp only [pitchEffect_downstep, pitchEffect_empty]; omega)

/-- The staircase: each accentual phrase is realized one step below the baseline for every
bitonal accent up to and including it. -/
theorem realizePitch_registerSpecs {i : ℕ} (hi : i < aps.length) :
    (realizePitch b (registerSpecs aps))[i]? = some (b - catathesisCount (aps.take (i + 1))) := by
  induction aps generalizing b i with
  | nil => simp at hi
  | cons ap aps ih =>
    cases i with
    | zero =>
      simp only [registerSpecs, List.map_cons, realizePitch_cons, List.getElem?_cons_zero,
        List.take_succ_cons, List.take_zero, catathesisCount_cons, catathesisCount_nil,
        Option.some.injEq]
      split <;> (simp only [pitchEffect_downstep, pitchEffect_empty]; omega)
    | succ i =>
      simp only [registerSpecs, List.map_cons, realizePitch_cons, List.getElem?_cons_succ,
        List.take_succ_cons, catathesisCount_cons]
      rw [show realizePitch (b + (if ap.accent.isBitonal then TRN.downstep else TRN.empty).pitchEffect)
        (List.map (fun ap => if ap.accent.isBitonal then TRN.downstep else TRN.empty) aps) =
        realizePitch (b + (if ap.accent.isBitonal then TRN.downstep else TRN.empty).pitchEffect)
        (registerSpecs aps) from rfl, ih _ (by simpa using hi)]
      split <;> (simp only [pitchEffect_downstep, pitchEffect_empty, Option.some.injEq]; omega)

/-- One chain: a sequence followed by another is the first followed by the second
continued from the compressed register. -/
theorem realizePitch_registerSpecs_append :
    realizePitch b (registerSpecs (aps₁ ++ aps₂)) =
      realizePitch b (registerSpecs aps₁) ++
        realizePitch (b - catathesisCount aps₁) (registerSpecs aps₂) := by
  have h : registerSpecs (aps₁ ++ aps₂) = registerSpecs aps₁ ++ registerSpecs aps₂ :=
    List.map_append ..
  rw [h, realizePitch_append, sum_pitchEffect_registerSpecs, Int.sub_eq_add_neg]

/-- An intermediate-phrase boundary resets the register, so every level after it is at
least what continuing the chain would give. -/
theorem boundary_raises :
    List.Forall₂ (· ≤ ·) (realizePitch (b - catathesisCount aps₁) (registerSpecs aps₂))
      (realizePitch b (registerSpecs aps₂)) :=
  realizePitch_baseline_mono _ (by omega)

/-! ### Intermediate and intonation phrases -/

/-- An intermediate phrase: accentual phrases closed by a phrase accent, the domain of
catathesis. -/
structure IntermediatePhrase where
  aps : List AccentualPhrase
  phraseAccent : PhraseAccent
  aps_nonempty : aps ≠ [] := by decide
  deriving Repr

/-- An intonation phrase: intermediate phrases closed by a boundary tone. -/
structure IntonationPhrase where
  ips : List IntermediatePhrase
  boundaryTone : BoundaryTone
  ips_nonempty : ips ≠ [] := by decide
  deriving Repr

/-- The terminal contour of an intonation phrase: the last intermediate phrase's phrase
accent and the boundary tone, [pierrehumbert-1980]'s terminal sequence decomposed. -/
def IntonationPhrase.terminalContour (ip : IntonationPhrase) : TerminalContour :=
  ⟨(ip.ips.getLast ip.ips_nonempty).phraseAccent, ip.boundaryTone⟩

/-- The register nodes of one intermediate phrase: a single chain. -/
def ipRegisterSpecs (ip : IntermediatePhrase) : List TRN := registerSpecs ip.aps

/-- The register nodes of an intonation phrase, one chain per intermediate phrase: each
starts again from the baseline. -/
def ipRegisterSpecsAcrossIps (ips : List IntermediatePhrase) : List (List TRN) :=
  ips.map ipRegisterSpecs

/-! ### The two systems -/

/-- Where the compression takes effect relative to its trigger: within the accent itself
(Japanese, whose trailing L is already compressed) or only after it (English). -/
inductive CatathesisTiming where
  | withinAccent
  | afterAccent
  deriving Repr, DecidableEq

/-- A language's intonation system: how accents are specified, the contrastive accent
shapes, whether lexically unaccented words exist, whether the accentual-phrase boundary L is
always present, and when catathesis takes effect. -/
structure IntonationSystem where
  accentSpec : AccentSpecification
  accentShapes : List PitchAccent
  hasUnaccented : Bool
  apBoundaryLAlwaysPresent : Bool
  catathesisTiming : CatathesisTiming
  deriving Repr

/-- Japanese: lexical accent location, the one shape H*+L, unaccented words, a boundary L in
every accentual phrase, compression within the accent. -/
def japanese : IntonationSystem :=
  { accentSpec := .lexical
    accentShapes := [.H_star_plus_L]
    hasUnaccented := true
    apBoundaryLAlwaysPresent := true
    catathesisTiming := .withinAccent }

/-- English: postlexical accent shape, six shapes, every content word accentable, no
accentual-phrase boundary tone, compression after the accent. -/
def english : IntonationSystem :=
  { accentSpec := .postlexical
    accentShapes := [.H_star, .L_star, .H_star_plus_L,
                     .H_plus_L_star, .L_star_plus_H, .L_plus_H_star]
    hasUnaccented := false
    apBoundaryLAlwaysPresent := false
    catathesisTiming := .afterAccent }

/-- Every Japanese accent triggers catathesis, since its one shape is bitonal; an English
accent need not, since H* and L* are monotonal. -/
theorem triggers_differ :
    (∀ a ∈ japanese.accentShapes, registerSpecs [⟨a, 1⟩] = [TRN.downstep]) ∧
      ∃ a ∈ english.accentShapes, registerSpecs [⟨a, 1⟩] = [TRN.empty] := by
  decide

/-- An accented accentual phrase (*uma'i*, *mo'riya-no*). -/
def accentedAP : AccentualPhrase := ⟨.H_star_plus_L, 1⟩

/-- An unaccented accentual phrase (*amai*, *toriya-no mawari-no*). -/
def unaccentedAP : AccentualPhrase := ⟨.null, 1⟩

/-! ### Japanese accentual phrases from the lexicon -/

section JapaneseAP
open Japanese.Prosody

/-- The accentual phrase over grouped word entries: accented, always H*+L, iff some word is
lexically accented, grouping deleting all but one accent. -/
def AccentualPhrase.ofWords (ws : List ProsodicEntry) : AccentualPhrase :=
  { accent := if ws.any (·.isAccented) then .H_star_plus_L else .null
    nWords := ws.length }

/-- A phrase of words triggers catathesis iff some word is accented. -/
theorem ofWords_isBitonal (ws : List ProsodicEntry) :
    (AccentualPhrase.ofWords ws).accent.isBitonal = ws.any (·.isAccented) := by
  unfold AccentualPhrase.ofWords
  split <;> simp_all [PitchAccent.isBitonal]

end JapaneseAP

end BeckmanPierrehumbert1986
