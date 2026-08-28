import Linglib.Syntax.Category.Auxiliary.Constructions
import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Syntax.Negation
import Linglib.Data.Examples.Anderson2006a
import Mathlib.Data.Finset.Basic

/-!
# Anderson 2006: auxiliary verb constructions

An auxiliary verb construction pairs an auxiliary with a lexical verb that stays the semantic
head, and languages differ in which element hosts the inflection: the auxiliary (English *have
eaten*), the lexical verb (Pipil *weli ni-nehnemi*), both with the same categories (Gorum), the
two dividing the categories (Jakaltek, absolutive on the auxiliary and ergative on the lexical
verb), or dividing them with some doubled (Hemba, Doyayo, Pipil). The five macro-patterns are
distinguished by the inflectional head alone, and across the split/doubled languages the doubled
category is overwhelmingly the subject. Negative auxiliaries head constructions of every pattern:
aux-headed in Udihe, split in Kokota, lex-headed in Kwerba, doubled in 'Iipay. Doyayo, filed as
lex-headed although its auxiliary partially encodes subject person through tone, comes out split
by the inflectional-head criterion.

## Main definitions

* `InflectionalMarking`: which categories each element carries;
  `InflectionalMarking.pattern` reads the macro-pattern (13) off it.

## References

* [anderson-2006a]
* [bybee-1985] — the category inventory
-/

namespace Anderson2006a

open AuxiliaryVerbs Data.Examples Morphology Syntax.Negation

/-! ### Where the inflection is marked -/

/-- Which inflectional categories each element of an auxiliary verb construction carries. -/
structure InflectionalMarking where
  onAux : Finset MorphCategory
  onLex : Finset MorphCategory
  deriving DecidableEq

/-- The inflectional head fixes the macro-pattern (13): only the auxiliary marked, only the
lexical verb, both with the same categories, the two disjoint, or overlapping. -/
def InflectionalMarking.pattern (m : InflectionalMarking) : InflectionPattern :=
  if m.onLex = ∅ then .auxHeaded
  else if m.onAux = ∅ then .lexHeaded
  else if m.onAux = m.onLex then .doubled
  else if Disjoint m.onAux m.onLex then .split
  else .splitDoubled

/-- The categories doubled on both elements. -/
def InflectionalMarking.doubled (m : InflectionalMarking) : Finset MorphCategory :=
  m.onAux ∩ m.onLex

/-! ### The book's examples -/

/-- The category names used in the example rows; Gorum's affectedness is outside the
inventory. -/
def MorphCategory.ofString? : String → Option MorphCategory
  | "subj" => some (.agreement .subj)
  | "obj" => some (.agreement .obj)
  | "tense" => some .tense
  | "aspect" => some .aspect
  | "mood" => some .mood
  | "negation" => some .negation
  | _ => none

/-- The categories a row lists under a feature key. -/
def categories (r : LinguisticExample) (key : String) : Finset MorphCategory :=
  (r.paperFeatures.filterMap fun kv =>
    if kv.1 = key then MorphCategory.ofString? kv.2 else none).toFinset

/-- The inflectional marking a row records, when it records one. -/
def InflectionalMarking.ofRow? (r : LinguisticExample) : Option InflectionalMarking :=
  if r.paperFeatures.any (fun kv => kv.1 = "on_aux" || kv.1 = "on_lex") then
    some ⟨categories r "on_aux", categories r "on_lex"⟩
  else none

def InflectionPattern.ofString? : String → Option InflectionPattern
  | "auxHeaded" => some .auxHeaded
  | "lexHeaded" => some .lexHeaded
  | "doubled" => some .doubled
  | "split" => some .split
  | "splitDoubled" => some .splitDoubled
  | _ => none

/-- The book's pattern label for each example is what (13) reads off its marking — except
where the auxiliary's marking is only partial. -/
theorem rows_pattern :
    ∀ r ∈ Examples.all, r.feature? "aux_marking" = none →
      ∀ m ∈ (InflectionalMarking.ofRow? r).toList,
        ∀ p ∈ ((r.feature? "infl_pattern").bind InflectionPattern.ofString?).toList,
          m.pattern = p := by
  decide +kernel

/-- Doyayo (15a): the auxiliary partially encodes subject person through tone while the
lexical verb carries tense, which (13) classifies as split; the book files it under
lex-headed. -/
theorem doyayo_split :
    ∀ m ∈ (InflectionalMarking.ofRow? Examples.doyayo_lexheaded).toList, m.pattern = .split := by
  decide +kernel

/-- Every one of the five patterns is instantiated by some example's marking. -/
theorem all_patterns_attested (p : InflectionPattern) :
    ∃ r ∈ Examples.all, ∃ m ∈ (InflectionalMarking.ofRow? r).toList, m.pattern = p := by
  cases p <;> decide +kernel

/-- Chapter 5: in split/doubled patterns the doubled category is overwhelmingly the subject —
every split/doubled example doubles subject agreement and nothing else. -/
theorem splitDoubled_doubles_subject :
    ∀ r ∈ Examples.all, ∀ m ∈ (InflectionalMarking.ofRow? r).toList,
      m.pattern = .splitDoubled → m.doubled = {.agreement .subj} := by
  decide +kernel

/-! ### Negative auxiliaries -/

/-- Negative auxiliaries head constructions of more than one pattern (§1.7.2): Udihe (49) is
aux-headed, as `Strategy.expectedInflectionPattern` expects of a verbal negator, and Kwerba
(52) is lex-headed, so that expectation is a tendency rather than a law. -/
theorem negative_auxiliary_patterns :
    (∃ r ∈ Examples.all, r.feature? "strategy" = some "negVerb" ∧
      (r.feature? "infl_pattern").bind InflectionPattern.ofString? =
        Strategy.negVerb.expectedInflectionPattern) ∧
    ∃ r ∈ Examples.all, r.feature? "strategy" = some "negVerb" ∧
      (r.feature? "infl_pattern").bind InflectionPattern.ofString? = some .lexHeaded := by
  decide +kernel

end Anderson2006a
