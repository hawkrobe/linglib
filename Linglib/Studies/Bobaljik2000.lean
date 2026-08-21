import Linglib.Morphology.DistributedMorphology.ComplexHead
import Linglib.Data.Examples.Bobaljik2000

/-! # Bobaljik 2000: the ins and outs of contextual allomorphy

[bobaljik-2000] argues from Itelmen agreement that Vocabulary Insertion is
cyclic from the root outward and rewrites a morpheme's features as it
discharges them, so that conditioning is asymmetric: an inner morpheme may
look outward at the syntactic features of morphemes not yet realized, but an
outer morpheme cannot look inward at features already discharged. The Class II
marker between the root and object agreement is conditioned by the class of the
root inside it and by the person of both arguments outside it, object
agreement by the subject outside it, and the subject prefix — last to be
inserted — by nothing inside. This file runs that derivation over the complex
head with hierarchical locality and rewriting, and shows the asymmetry as a
consequence: with non-deletion, the inner agreement features would still be
visible to the prefix.

## Main results

* `itelmen_rows`: the four forms (9)–(10) from one Vocabulary.
* `prefix_sees_no_agreement`: at the subject prefix, the rewritten object
  agreement is invisible; `nondeletion_exposes` that only rewriting hides it.
* `outward_features_only`: the Class II marker conditioned by both arguments
  sees their features, not exponents.

## References

[bobaljik-2000], [halle-marantz-1993].
-/

namespace Bobaljik2000

open DistributedMorphology
open Data.Examples (LinguisticExample)
open scoped DistributedMorphology.VocabularyItem

inductive Feature where
  | root (s : String) | classII | tense | classMarker
  | agrO | agrS | obj3 | first | second | sg | pl
  deriving DecidableEq, Repr

open Feature

/-- Present -s; the Class II marker -ki- under a first-person subject acting on a
third-person object and -c- under a second-singular one; object agreement -cen
under a first-person subject and -in under a second-singular; the subject
prefix t- for first singular, null for second singular. -/
def vocab : List (VocabularyItem Feature String) :=
  [[tense] ⟷ "s",
   ⟨⟨[classMarker], [], [[agrO, obj3], [agrS, first]]⟩, "ki"⟩,
   ⟨⟨[classMarker], [], [[agrO, obj3], [agrS, second, sg]]⟩, "c"⟩,
   ⟨⟨[agrO, obj3], [], [[agrS, first]]⟩, "cen"⟩,
   ⟨⟨[agrO, obj3], [], [[agrS, second, sg]]⟩, "in"⟩,
   [agrS, first, sg] ⟷ "t", [agrS, second, sg] ⟷ ""]

/-- √-T-(II)-AgrO-AgrS, the Class II marker present for a Class II root. -/
def word (r : String) (classII? : Bool) (subj obj : List Feature) : ComplexHead Feature String :=
  ⟨⟨root r :: if classII? then [classII] else [], some r, .after⟩,
   [⟨[tense], none, .after⟩] ++
     (if classII? then [⟨[classMarker], none, .after⟩] else []) ++
     [⟨agrO :: obj, none, .after⟩, ⟨agrS :: subj, none, .before⟩]⟩

def insert (dis : ComplexHead.Discharge) (w : ComplexHead Feature String) :
    ComplexHead Feature String :=
  w.insertAll (· = "") vocab .hierarchical (λ _ => []) dis

def morphs (w : ComplexHead Feature String) : List String :=
  (insert .rewriting w).exponents.filter (· ≠ "")

def parseArg : String → Option (List Feature)
  | "1sg" => some [first, sg]
  | "2sg" => some [second, sg]
  | "3sg" => some [obj3, sg]
  | "3pl" => some [obj3, pl]
  | _ => none

def ofRow (ex : LinguisticExample) : Option (ComplexHead Feature String × List String) := do
  let subj ← parseArg (← ex.feature? "subj")
  let obj ← parseArg (← ex.feature? "obj")
  pure (word (← ex.feature? "root") ((← ex.feature? "rootClass") = "II") subj obj,
    ["m1", "m2", "m3", "m4", "m5"].filterMap ex.feature?)

def rows : List (ComplexHead Feature String × List String) :=
  Examples.all.filterMap ofRow

/-- The forms (9)–(10). -/
theorem itelmen_rows : ∀ r ∈ rows, morphs r.1 = r.2 := by decide

/-- (9b): `t-t-s-ki-cen`. -/
def bring : ComplexHead Feature String := word "t" true [first, sg] [obj3, pl]

/-- When the subject prefix is reached under rewriting, the object agreement
inside it has discharged its features: nothing of `agrO` remains to condition
the prefix, the asymmetry of (12). -/
theorem prefix_sees_no_agreement :
    agrO ∉ (((insert .rewriting bring).insertUpTo (· = "") vocab .hierarchical (λ _ => [])
      .rewriting 3).contextAt (· = "") .hierarchical (λ _ => []) 3).leftCtx.flatten := by
  decide

/-- Under non-deletion the same context carries `agrO`: symmetric conditioning,
as in [halle-marantz-1993], would let the prefix see inward. -/
theorem nondeletion_exposes :
    agrO ∈ ((bring.insertUpTo (· = "") vocab .hierarchical (λ _ => []) .nondeletion 3).contextAt
      (· = "") .hierarchical (λ _ => []) 3).leftCtx.flatten := by
  decide

/-- The Class II marker, second to be inserted, sees both agreement morphemes
outside it bare: their features, at hierarchical distance one and two. -/
theorem outward_features_only :
    ((bring.insertUpTo (· = "") vocab .hierarchical (λ _ => []) .rewriting 1).contextAt (· = "")
      .hierarchical (λ _ => []) 1).rightCtx = [[agrO, obj3, pl], [agrS, first, sg]] := by
  decide

end Bobaljik2000
