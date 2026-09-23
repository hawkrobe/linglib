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
varieties are the profiles of the fragments (`table_3_1`). What children acquire are
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
*wh*–subject–verb or *wh*–verb–subject by which element checks Top°. The cue for English
inflectional elements, *som*-insertion, focus-sensitive adverbs, *kanskje*, and the
acquisition chapters are not formalized.

## References

* [westergaard-2009]
* [rizzi-1997]
-/

@[expose] public section

namespace Westergaard2009

open Minimalist
open Norwegian English German Danish

/-! ### Micro-parameters (Table 3.1) -/

/-- Table 3.1 gives the grammars of the six varieties. -/
theorem table_3_1 :
    stdNorwegian = ({.Decl, .Int, .Pol} : V2Grammar) ∧
      stdEnglish = ({.Int, .Pol} : V2Grammar) ∧
      nordmoreNorwegian = ({.Decl, .Pol} : V2Grammar) ∧
      belfastEnglish = ({.Int, .Pol, .Imp, .Wh} : V2Grammar) ∧
      german = ({.Decl, .Int, .Pol, .Fin} : V2Grammar) ∧
      danish = ({.Decl, .Int, .Pol, .Excl} : V2Grammar) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Nordmøre Norwegian is the mirror image of Standard English on Decl° and Int°. -/
theorem nordmore_english_mirror :
    .Decl ∈ nordmoreNorwegian ∧ .Int ∉ nordmoreNorwegian ∧ .Decl ∉ stdEnglish ∧
      .Int ∈ stdEnglish := by
  decide

/-- Only German has verb movement to Fin°; every variety has it to Pol°. -/
theorem fin_german_pol_all :
    .Fin ∈ german ∧ .Fin ∉ stdNorwegian ∧ .Fin ∉ stdEnglish ∧
      .Fin ∉ nordmoreNorwegian ∧ .Fin ∉ belfastEnglish ∧ .Fin ∉ danish ∧
      .Pol ∈ stdNorwegian ∧ .Pol ∈ stdEnglish ∧ .Pol ∈ nordmoreNorwegian ∧
      .Pol ∈ belfastEnglish ∧ .Pol ∈ german ∧ .Pol ∈ danish := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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

/-- The cue (57) is verb movement to a head below the CP domain in embedded declaratives. -/
def cueFinV2 : MicroCue := ⟨.Fin, .xp, true⟩

/-- The cues (58)–(60) are non-V2 in exclamatives, embedded questions and embedded declaratives. -/
def cueExclNonV2 : MicroCue := ⟨.Excl, .wh, false⟩

def cueWhNonV2 : MicroCue := ⟨.Wh, .wh, false⟩

def cueFinNonV2 : MicroCue := ⟨.Fin, .xp, false⟩

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
    (Expresses stdNorwegian cueIntV2 ∧ Expresses stdNorwegian cueDeclV2 ∧
        ¬ Expresses stdNorwegian cueExclV2 ∧ ¬ Expresses stdNorwegian cueWhV2) ∧
      (Expresses stdEnglish cueIntV2 ∧ ¬ Expresses stdEnglish cueDeclV2 ∧
        ¬ Expresses stdEnglish cueExclV2 ∧ ¬ Expresses stdEnglish cueWhV2) ∧
      (¬ Expresses nordmoreNorwegian cueIntV2 ∧ Expresses nordmoreNorwegian cueDeclV2 ∧
        ¬ Expresses nordmoreNorwegian cueExclV2 ∧ ¬ Expresses nordmoreNorwegian cueWhV2) ∧
      (Expresses belfastEnglish cueIntV2 ∧ ¬ Expresses belfastEnglish cueDeclV2 ∧
        ¬ Expresses belfastEnglish cueExclV2 ∧ Expresses belfastEnglish cueWhV2) ∧
      (Expresses danish cueIntV2 ∧ Expresses danish cueDeclV2 ∧
        Expresses danish cueExclV2 ∧ ¬ Expresses danish cueWhV2) := by
  simp [Expresses, cueIntV2, cueDeclV2, cueExclV2, cueWhV2]

/-- The Norwegian children hear the cues for non-V2 in exclamatives, embedded questions and
embedded declaratives. -/
theorem stdNorwegian_nonV2_cues :
    Expresses stdNorwegian cueExclNonV2 ∧ Expresses stdNorwegian cueWhNonV2 ∧
      Expresses stdNorwegian cueFinNonV2 := by
  simp [Expresses, cueExclNonV2, cueWhNonV2, cueFinNonV2]

/-! ### *Wh*-heads and information structure (§3.2, §3.3) -/

/-- A *wh*-element is a head, sitting in Int⁰ itself, or a phrase in its specifier. -/
inductive WhStatus
  | head
  | phrase
  deriving DecidableEq, Repr

/-- A monosyllabic *wh*-word is a head, a longer one a phrase. -/
def WhStatus.ofSyllables (n : ℕ) : WhStatus := if n ≤ 1 then .head else .phrase

/-- A *wh*-head occupying a question head blocks verb movement to it, Int⁰ in matrix and Wh⁰ in
embedded questions; a phrase in the specifier blocks nothing. -/
def WhStatus.Blocks : WhStatus → ForceHead → Prop
  | .head, .Int | .head, .Wh => True
  | _, _ => False

instance : DecidableRel WhStatus.Blocks := fun w f ↦ by
  cases w <;> cases f <;> unfold WhStatus.Blocks <;> infer_instance

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
