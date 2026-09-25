module

public import Linglib.Syntax.Minimalist.VerbSecond
public import Linglib.Fragments.Norwegian.V2
public import Linglib.Fragments.English.V2
public import Linglib.Fragments.German.V2
public import Linglib.Fragments.Danish.V2
public import Linglib.Data.Examples.Westergaard2009

/-!
# Westergaard (2009): The Acquisition of Word Order: Micro-Cues, Information Structure, and Economy

This file formalizes the syntactic model of [westergaard-2009]. Verb second is not one
parameter but a setting per clause-type head of a split ForceP: a language's grammar is the
set of heads the finite verb moves to (`Minimalist.V2Grammar`), and Table 3.1's six Germanic
varieties are the verb-second grammars of the Norwegian, English, German and Danish
fragments. What children acquire are
micro-cues, pieces of I-language structure stating, for one head, what its specifier holds and
whether the verb fills it (`MicroCue`); a grammar expresses a cue when its setting for that
head is the cue's, so that Table 3.2's cues separate the five grammars (`table_3_2`). In the
Tromsø dialect the monosyllabic *wh*-words *ka*, *kem* and *kor* are heads and sit in Int°
themselves, which blocks verb movement there (`TromsøWh.status`); the V2 that still occurs is
verb movement to a lower Top° whose [−foc] feature a given subject checks from the specifier
and a focused subject leaves for the verb (`order`), so that these questions are V2 exactly
when the subject is new (`isV2_order_iff`).

## Implementation notes

The cues of §4 are recorded as data; the two structures of §3.3 are linearized as
*wh*–subject–verb or *wh*–verb–subject by which element checks Top°. The cues (57) and (60)
for verb movement to I°, which Westergaard motivates with Icelandic and which no head of the
split ForceP carries, the cue for English inflectional elements, *som*-insertion,
focus-sensitive adverbs, *kanskje*, and the acquisition chapters are not formalized.

## References

* [westergaard-2009]
* [rizzi-1997]
-/

@[expose] public section

namespace Westergaard2009

open Minimalist

/-! ### Micro-parameters (Table 3.1) -/

/-- Nordmøre Norwegian is the mirror image of Standard English on Decl° and Int°. -/
theorem nordmore_english_mirror :
    .Decl ∈ Norwegian.Nordmore.verbSecond ∧ .Int ∉ Norwegian.Nordmore.verbSecond ∧
      .Decl ∉ English.verbSecond ∧ .Int ∈ English.verbSecond := by
  decide

/-- Only German has verb movement to Fin°; every variety has it to Pol°. -/
theorem fin_german_pol_all :
    .Fin ∈ German.verbSecond ∧ .Fin ∉ Norwegian.verbSecond ∧ .Fin ∉ English.verbSecond ∧
      .Fin ∉ Norwegian.Nordmore.verbSecond ∧ .Fin ∉ English.Belfast.verbSecond ∧
      .Fin ∉ Danish.verbSecond ∧ .Pol ∈ Norwegian.verbSecond ∧
      .Pol ∈ English.verbSecond ∧ .Pol ∈ Norwegian.Nordmore.verbSecond ∧
      .Pol ∈ English.Belfast.verbSecond ∧
      .Pol ∈ German.verbSecond ∧ .Pol ∈ Danish.verbSecond := by
  decide

/-! ### Micro-cues (§4) -/

/-- The specifier of the cue's head holds nothing, a non-subject phrase, or a *wh*-element. -/
inductive Filler
  | none | xp | wh
  deriving DecidableEq, Repr

/-- A micro-cue: for one head, what its specifier holds and whether the finite verb fills it. -/
structure MicroCue where
  target : ForceHead
  spec : Filler
  verbInHead : Bool
  deriving DecidableEq, Repr

/-- The cue (45) is V2 in *wh*-questions. -/
def cueIntV2 : MicroCue := ⟨.Int, .wh, true⟩

/-- The cue (46) is V2 in declaratives. -/
def cueDeclV2 : MicroCue := ⟨.Decl, .xp, true⟩

/-- The cue (49) is V2 in yes/no-questions. -/
def cuePolV2 : MicroCue := ⟨.Pol, .none, true⟩

/-- The cue (52) is V2 in exclamatives. -/
def cueExclV2 : MicroCue := ⟨.Excl, .wh, true⟩

/-- The cue (53) is V2 in embedded questions. -/
def cueWhV2 : MicroCue := ⟨.Wh, .wh, true⟩

/-- The cue (54) is V2 in imperatives. -/
def cueImpV2 : MicroCue := ⟨.Imp, .none, true⟩

/-- The cue (58) is non-V2 in exclamatives. -/
def cueExclNonV2 : MicroCue := ⟨.Excl, .wh, false⟩

/-- The cue (59) is non-V2 in embedded questions. -/
def cueWhNonV2 : MicroCue := ⟨.Wh, .wh, false⟩

/-- A grammar expresses a cue when its setting for the cue's head is the cue's. -/
def Expresses (lang : V2Grammar) (c : MicroCue) : Prop := c.target ∈ lang ↔ c.verbInHead = true

/-- A cue and the cue for its absence are never both expressed. -/
theorem not_expresses_both (lang : V2Grammar) {c c' : MicroCue} (ht : c.target = c'.target)
    (hv : c.verbInHead ≠ c'.verbInHead) : ¬ (Expresses lang c ∧ Expresses lang c') :=
  fun ⟨h, h'⟩ ↦ hv (by
    unfold Expresses at h h'
    rw [ht] at h
    cases hc : c.verbInHead <;> cases hc' : c'.verbInHead <;> simp_all)

/-- Table 3.2 shows that four cues separate the five grammars. -/
theorem table_3_2 :
    (Expresses Norwegian.verbSecond cueIntV2 ∧ Expresses Norwegian.verbSecond cueDeclV2 ∧
        ¬ Expresses Norwegian.verbSecond cueExclV2 ∧
        ¬ Expresses Norwegian.verbSecond cueWhV2) ∧
      (Expresses English.verbSecond cueIntV2 ∧ ¬ Expresses English.verbSecond cueDeclV2 ∧
        ¬ Expresses English.verbSecond cueExclV2 ∧
        ¬ Expresses English.verbSecond cueWhV2) ∧
      (¬ Expresses Norwegian.Nordmore.verbSecond cueIntV2 ∧
        Expresses Norwegian.Nordmore.verbSecond cueDeclV2 ∧
        ¬ Expresses Norwegian.Nordmore.verbSecond cueExclV2 ∧
        ¬ Expresses Norwegian.Nordmore.verbSecond cueWhV2) ∧
      (Expresses English.Belfast.verbSecond cueIntV2 ∧
        ¬ Expresses English.Belfast.verbSecond cueDeclV2 ∧
        ¬ Expresses English.Belfast.verbSecond cueExclV2 ∧
        Expresses English.Belfast.verbSecond cueWhV2) ∧
      (Expresses Danish.verbSecond cueIntV2 ∧ Expresses Danish.verbSecond cueDeclV2 ∧
        Expresses Danish.verbSecond cueExclV2 ∧ ¬ Expresses Danish.verbSecond cueWhV2) := by
  simp [Expresses, cueIntV2, cueDeclV2, cueExclV2, cueWhV2]

/-- The Norwegian children hear the cues for non-V2 in exclamatives and embedded questions. -/
theorem norwegian_nonV2_cues :
    Expresses Norwegian.verbSecond cueExclNonV2 ∧
      Expresses Norwegian.verbSecond cueWhNonV2 := by
  simp [Expresses, cueExclNonV2, cueWhNonV2]

/-! ### *Wh*-heads and information structure (§3.2, §3.3) -/

/-- A *wh*-element is a head, sitting in Int⁰ itself, or a phrase in its specifier. -/
inductive WhStatus
  | head
  | phrase
  deriving DecidableEq, Repr

/-- A monosyllabic *wh*-word is a head, a longer one a phrase. -/
def WhStatus.ofSyllables (n : ℕ) : WhStatus := if n ≤ 1 then .head else .phrase

/-- A *wh*-head sits in Int⁰ itself and blocks verb movement to it; a phrase in the specifier
blocks nothing. -/
def WhStatus.Blocks (w : WhStatus) (f : ForceHead) : Prop := w = .head ∧ f = .Int

instance : DecidableRel WhStatus.Blocks := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The *wh*-elements of the Tromsø dialect. -/
inductive TromsøWh
  | ka | kem | kor | korfor | korsen | katti
  deriving DecidableEq, Repr, Fintype

/-- Their syllable counts. -/
def TromsøWh.syllables : TromsøWh → ℕ
  | .ka | .kem | .kor => 1
  | .korfor | .korsen | .katti => 2

/-- The status of each *wh*-word, by its syllable count. -/
def TromsøWh.status (w : TromsøWh) : WhStatus := .ofSyllables w.syllables

/-- *ka*, *kem* and *kor* are heads and block verb movement to Int°; the others are phrases
and block nothing. -/
theorem tromsøWh_blocking :
    ∀ w : TromsøWh, w.status.Blocks .Int ↔ w.syllables = 1 := by
  decide

/-- Which element checks the [−foc] feature of Top° in a monosyllabic *wh*-question: a
[−foc] subject from the specifier (32), otherwise the finite verb in the head (31). -/
inductive Checker
  | subject | verb
  deriving DecidableEq, Repr

/-- The checker, by whether the subject is focused. -/
def checker (subjectFoc : Bool) : Checker := if subjectFoc then .verb else .subject

/-- The words whose order the two structures fix. -/
inductive Word
  | wh | subject | verb
  deriving DecidableEq, Repr

/-- The surface order puts the *wh*-head in Int°, then the specifier and head of TopP, then the
rest of the clause. -/
def order (subjectFoc : Bool) : List Word :=
  match checker subjectFoc with
  | .subject => [.wh, .subject, .verb]
  | .verb => [.wh, .verb, .subject]

/-- Verb second holds when the finite verb is the second word. -/
def IsV2 (l : List Word) : Prop := l[1]? = some .verb

instance (l : List Word) : Decidable (IsV2 l) := inferInstanceAs (Decidable (_ = _))

/-- A monosyllabic *wh*-question is V2 exactly when its subject is new information. -/
theorem isV2_order_iff (subjectFoc : Bool) : IsV2 (order subjectFoc) ↔ subjectFoc = true := by
  cases subjectFoc <;> decide

end Westergaard2009
