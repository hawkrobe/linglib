module

public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Reference.Definiteness

/-!
# Modern Standard Arabic case

Modern Standard Arabic has three cases, the nominative (*rafʿ*), the genitive (*jarr*) and the
accusative (*naSb*), marked by a suffix at the end of a noun or adjective: in the base
declension *-u*, *-i* and *-a*, followed on an indefinite by nunation, a final *-n*
([ryding-2005] ch. 7 §5, p. 166). The spoken varieties do not mark case (p. 166), so the case
system is that of the written language.

Ryding sorts nouns and adjectives into eight declensions by how they mark case and definiteness
(§5.4, pp. 182–183). The triptote gives each case its own suffix. The dual, the two sound
plurals and the indefinite diptote have one form for the genitive and the accusative, and "are
considered to exhibit all three cases; it is just that the genitive and accusative have exactly
the same form" (§5.4.2, p. 187). The defectives have one form for the nominative and the genitive
(§5.4.3, p. 197), and the indeclinables and the invariables one form for all three cases
(§§5.4.4–5.4.5, pp. 199–200). The functions of each case are listed in §5.3.

## Main declarations

* `Arabic.ModernStandard.Case`: the three cases, in the order of the grammars.
* `Arabic.ModernStandard.Declension`: the eight declensions.
* `Arabic.ModernStandard.Noun`, `nouns`: a noun of each declension from Ryding's tables, by the
  form of each case, definite and indefinite.
* `bayt_form_injective`: the triptote *bayt* 'house' distinguishes the three cases.
* `gen_acc_syncretic_iff`, `nom_gen_syncretic_iff`, `nom_acc_syncretic_iff`: the declensions
  whose forms merge each pair of cases.

## Implementation notes

The forms are Ryding's transliterations from the paradigm tables of §5.4 (pp. 184–201), with the
hyphens printed there. Ryding numbers the declensions but gives the two sound plurals different
numbers on p. 183 and p. 187, so the declensions go by name here.

## References

* [ryding-2005]
-/

@[expose] public section

namespace Arabic.ModernStandard

open Reference (Definiteness)

/-- The three cases, in the order of the grammars. -/
inductive Case where
  /-- The nominative, *rafʿ*. -/
  | nom
  /-- The genitive, *jarr*. -/
  | gen
  /-- The accusative, *naSb*. -/
  | acc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | gen => .gen
  | acc => .acc

/-- The eight declensions ([ryding-2005] §5.4). -/
inductive Declension where
  /-- A suffix for each case: *-u*, *-i*, *-a*. -/
  | triptote
  /-- The dual suffix, nominative *-aani*, genitive and accusative *-ayni*. -/
  | dual
  /-- The sound feminine plural in *-aat*, with *-u* and *-i* but no *-a*. -/
  | soundFemininePlural
  /-- The sound masculine plural, nominative *-uuna*, genitive and accusative *-iina*. -/
  | soundMasculinePlural
  /-- No nunation and, when indefinite, *-a* for the genitive as for the accusative. -/
  | diptote
  /-- Stems ending in a semivowel, with one form for the nominative and the genitive. -/
  | defective
  /-- Nouns in *ʾalif maqSuura* that mark definiteness but not case. -/
  | indeclinable
  /-- Nouns that mark neither case nor definiteness. -/
  | invariable
  deriving DecidableEq, Repr

/-- The forms of the three cases, in the order of the grammars. -/
def forms (nom gen acc : String) : Case → String
  | .nom => nom
  | .gen => gen
  | .acc => acc

/-- A noun by the form of each case, definite and indefinite. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The declension. -/
  declension : Declension
  /-- The form of each case, definite or indefinite. -/
  form : Definiteness → Case → String

/-- *bayt* 'house', triptote (p. 184). -/
def bayt : Noun where
  gloss := "house"
  declension := .triptote
  form
    | .definite => forms "al-bayt-u" "al-bayt-i" "al-bayt-a"
    | .indefinite => forms "bayt-u-n" "bayt-i-n" "bayt-a-n"

/-- *bayt-aani* 'two houses', dual (p. 188). -/
def baytaani : Noun where
  gloss := "two houses"
  declension := .dual
  form
    | .definite => forms "al-bayt-aani" "al-bayt-ayni" "al-bayt-ayni"
    | .indefinite => forms "bayt-aani" "bayt-ayni" "bayt-ayni"

/-- *intixaabaat* 'elections', sound feminine plural (p. 191). -/
def intixaabaat : Noun where
  gloss := "elections"
  declension := .soundFemininePlural
  form
    | .definite => forms "al-intixaabaat-u" "al-intixaabaat-i" "al-intixaabaat-i"
    | .indefinite => forms "intixaabaat-u-n" "intixaabaat-i-n" "intixaabaat-i-n"

/-- *muwaaTin-uuna* 'citizens', sound masculine plural (p. 190). -/
def muwaatinuuna : Noun where
  gloss := "citizens"
  declension := .soundMasculinePlural
  form
    | .definite => forms "al-muwaaTin-uuna" "al-muwaaTin-iina" "al-muwaaTin-iina"
    | .indefinite => forms "muwaaTin-uuna" "muwaaTin-iina" "muwaaTin-iina"

/-- *SaHraaʾ* 'desert', diptote (p. 193). -/
def sahraa : Noun where
  gloss := "desert"
  declension := .diptote
  form
    | .definite => forms "al-SaHraaʾ-u" "al-SaHraaʾ-i" "al-SaHraaʾ-a"
    | .indefinite => forms "SaHraaʾ-u" "SaHraaʾ-a" "SaHraaʾ-a"

/-- *muHaam-in* 'lawyer', defective (p. 198). -/
def muhaamin : Noun where
  gloss := "lawyer"
  declension := .defective
  form
    | .definite => forms "al-muHaamii" "al-muHaamii" "al-muHaamiya"
    | .indefinite => forms "muHaam-in" "muHaam-in" "muHaamiy-an"

/-- *mustashfan* 'hospital', indeclinable (p. 199). -/
def mustashfan : Noun where
  gloss := "hospital"
  declension := .indeclinable
  form
    | .definite => fun _ ↦ "al-mustashfaa"
    | .indefinite => fun _ ↦ "mustashfan"

/-- *shakwaa* 'complaint', invariable (p. 201). -/
def shakwaa : Noun where
  gloss := "complaint"
  declension := .invariable
  form
    | .definite => fun _ ↦ "al-shakwaa"
    | .indefinite => fun _ ↦ "shakwaa"

/-- A noun of each declension. -/
def nouns : List Noun :=
  [bayt, baytaani, intixaabaat, muwaatinuuna, sahraa, muhaamin, mustashfan, shakwaa]

/-! ### Syncretism -/

/-- The triptote distinguishes the three cases, definite and indefinite, and so establishes them
for the declensions that merge them. -/
theorem bayt_form_injective (d : Definiteness) : Function.Injective (bayt.form d) := by
  revert d; decide

/-- The genitive and the accusative fall together in the dual, the sound plurals, the
indeclinables and the invariables, and in the diptote when it is indefinite. -/
theorem gen_acc_syncretic_iff :
    ∀ n ∈ nouns, ∀ d, n.form d .gen = n.form d .acc ↔
      n.declension ∈ [.dual, .soundFemininePlural, .soundMasculinePlural, .indeclinable,
        .invariable] ∨ n.declension = .diptote ∧ d = .indefinite := by
  decide

/-- The nominative and the genitive fall together in the defectives, the indeclinables and the
invariables. -/
theorem nom_gen_syncretic_iff :
    ∀ n ∈ nouns, ∀ d, n.form d .nom = n.form d .gen ↔
      n.declension ∈ [.defective, .indeclinable, .invariable] := by
  decide

/-- The nominative and the accusative fall together only where all three cases do. -/
theorem nom_acc_syncretic_iff :
    ∀ n ∈ nouns, ∀ d, n.form d .nom = n.form d .acc ↔
      n.declension ∈ [.indeclinable, .invariable] := by
  decide

end Arabic.ModernStandard
