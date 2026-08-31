import Linglib.Morphology.DistributedMorphology.ComplexHead
import Linglib.Data.Examples.Bobaljik2000

/-! # Bobaljik 2000: the ins and outs of contextual allomorphy

[bobaljik-2000] argues from Chukotko-Kamchatkan agreement that Vocabulary
Insertion is cyclic from the root outward and rewrites a morpheme's features
as it discharges them, so conditioning is asymmetric: outward sensitivity
reaches morphosyntactic features not yet realized, inward sensitivity only
diacritics and the vocabulary items already inserted. In Itelmen the Class II
marker is conditioned by the root's class diacritic inside it and the person
of both arguments outside it, object agreement by the subject outside it, and
the subject prefix — last to be inserted — by nothing inside. In Chukchi the
third-person prefix ne- is bled exactly when the suffix -nin has been
inserted; the paper's (23) shows the two structures are feature-identical
inside the prefix, so the trigger is the vocabulary item itself, a sensitivity
cyclicity forces to be inwards.

## Main results

* `itelmen_rows`: the four forms (9)–(10) from one Vocabulary, the Class II
  marker's presence decided by insertion against the root's diacritic.
* `prefix_sees_no_agreement`: at the subject prefix, the rewritten object
  agreement is invisible; `nondeletion_exposes` that only rewriting hides it.
* `outward_features_only`, `inward_diacritic_not_tense`: outward context is
  bare morphosyntactic features; inward context is diacritics and inserted
  items, not discharged features.
* `nin_bleeds_prefix`, `ditransitive_retains_prefix`,
  `prefix_context_features_identical`: the Chukchi bleeding derived from one
  Vocabulary, triggered by the item -nin, not by object features.

## References

[bobaljik-2000], [halle-marantz-1993].
-/

namespace Bobaljik2000

open DistributedMorphology
open Data.Examples (LinguisticExample)
open scoped DistributedMorphology.VocabularyItem

inductive Feature where
  | root (s : String) | classII | tense | classMarker
  | agrO | agrS | item (s : String) | first | second | third | sg | pl
  deriving DecidableEq, Repr

open Feature

/-- The morphophonological features an exponent contributes to context: its
identity. Inward context after rewriting therefore carries diacritics and
inserted vocabulary items, never discharged morphosyntactic features. -/
def itemFeatures (e : String) : List Feature := [item e]

/-- Insertion from the inside out under hierarchical locality, null exponents
filtered from the surface string. -/
def morphs (voc : List (VocabularyItem Feature String)) (w : ComplexHead Feature String) :
    List String :=
  (w.insertAll (· = "") voc .hierarchical itemFeatures .rewriting).exponents.filter (· ≠ "")

/-- The context head `i` presents when inside-out insertion reaches it. -/
def stepContext (voc : List (VocabularyItem Feature String)) (w : ComplexHead Feature String)
    (dis : ComplexHead.Discharge) (i : ℕ) : Neighborhood (List Feature) :=
  (w.insertUpTo (· = "") voc .hierarchical itemFeatures dis i).contextAt
    (· = "") .hierarchical itemFeatures i

/-! ### (9)–(12): Itelmen -/

/-- Present -s; the Class II marker, conditioned inward by the root's class
diacritic (two morphemes in — the tense suffix intervenes), -ki- under a
first-person subject acting on a third-person object and -c- under a
second-singular one; object agreement -cen under a first-person subject and
-in under a second-singular; the subject prefix t- for first singular, null
for second singular. -/
def vocab : List (VocabularyItem Feature String) :=
  [[tense] ⟷ "s",
   ⟨⟨[classMarker], [[], [classII]], [[agrO, third], [agrS, first]]⟩, "ki"⟩,
   ⟨⟨[classMarker], [[], [classII]], [[agrO, third], [agrS, second, sg]]⟩, "c"⟩,
   ⟨⟨[agrO, third], [], [[agrS, first]]⟩, "cen"⟩,
   ⟨⟨[agrO, third], [], [[agrS, second, sg]]⟩, "in"⟩,
   [agrS, first, sg] ⟷ "t", [agrS, second, sg] ⟷ ""]

/-- √-T-(II)-AgrO-AgrS. The class position is present throughout — the paper
leaves open whether the node is syntactic or added post-syntactically — and
only roots carrying the Class II diacritic license an exponent there. -/
def word (r : String) (classII? : Bool) (subj obj : List Feature) : ComplexHead Feature String :=
  ⟨⟨root r :: if classII? then [classII] else [], some r, .after⟩,
   [⟨[tense], none, .after⟩, ⟨[classMarker], none, .after⟩,
    ⟨agrO :: obj, none, .after⟩, ⟨agrS :: subj, none, .before⟩]⟩

def parseArg : String → Option (List Feature)
  | "1sg" => some [first, sg]
  | "2sg" => some [second, sg]
  | "3sg" => some [third, sg]
  | "3pl" => some [third, pl]
  | _ => none

def ofRow (ex : LinguisticExample) : Option (ComplexHead Feature String × List String) := do
  let subj ← parseArg (← ex.feature? "subj")
  let obj ← parseArg (← ex.feature? "obj")
  pure (word (← ex.feature? "root") ((← ex.feature? "rootClass") = "II") subj obj,
    ["m1", "m2", "m3", "m4", "m5"].filterMap ex.feature?)

def rows : List (ComplexHead Feature String × List String) :=
  Examples.all.filterMap ofRow

/-- The forms (9)–(10): the Class II marker appears in the (b) forms alone,
because only there does insertion find the diacritic inward. -/
theorem itelmen_rows : ∀ r ∈ rows, morphs vocab r.1 = r.2 := by decide

/-- (9b): `t-t-s-ki-cen`. -/
def bring : ComplexHead Feature String := word "t" true [first, sg] [third, pl]

/-- When the subject prefix is reached under rewriting, the object agreement
inside it has discharged its features: nothing of `agrO` remains to condition
the prefix, the asymmetry of (12). -/
theorem prefix_sees_no_agreement :
    agrO ∉ (stepContext vocab bring .rewriting 3).leftCtx.flatten := by
  decide

/-- Under non-deletion the same context carries `agrO`: symmetric conditioning,
as in [halle-marantz-1993], would let the prefix see inward. -/
theorem nondeletion_exposes :
    agrO ∈ (stepContext vocab bring .nondeletion 3).leftCtx.flatten := by
  decide

/-- The Class II marker, second to be inserted, sees both agreement morphemes
outside it bare: their features, at hierarchical distance one and two. -/
theorem outward_features_only :
    (stepContext vocab bring .rewriting 1).rightCtx
      = [[agrO, third, pl], [agrS, first, sg]] := by
  decide

/-- Inward, the same step sees the root's class diacritic but not the
discharged tense feature: inward sensitivity reaches diacritics and inserted
items only. -/
theorem inward_diacritic_not_tense :
    classII ∈ (stepContext vocab bring .rewriting 1).leftCtx.flatten ∧
      tense ∉ (stepContext vocab bring .rewriting 1).leftCtx.flatten := by
  constructor <;> decide

/-! ### (19)–(28): Chukchi — sensitivity to the item, not its features

Unlike Itelmen, the Chukchi third-person transitive subject prefix ne- is
absent exactly when the object suffix is -nin, the allomorph conditioned by a
third-singular subject ((20), (24)). The bleeding cannot be conditioned by
object features: those are discharged before the prefix is reached, and (23)'s
two structures are feature-identical inside the prefix. It is conditioned by
the inserted item -nin itself — visible inward as a morphophonological fact —
so the ditransitive (26), where dative agreement preempts -nin under the same
third-singular subject, retains the prefix. Forms follow the paper's
segmentation in (19), (24) and (26). -/

/-- Past I transitive verb: √-AgrO-AgrS, no overt tense, no class. -/
def chukchi (r : String) (subj obj : List Feature) : ComplexHead Feature String :=
  ⟨⟨[root r], some r, .after⟩,
   [⟨agrO :: obj, none, .after⟩, ⟨agrS :: subj, none, .before⟩]⟩

/-- (24) plus the prefixes: -nin under a third-singular subject, elsewhere
-(e)n; -t for a second-singular object; the third-person subject prefix ne-,
bled by a zero item conditioned inward on the inserted item -nin. -/
def chukchiVocab : List (VocabularyItem Feature String) :=
  [⟨⟨[agrO, third], [], [[agrS, third, sg]]⟩, "nin"⟩,
   [agrO, third] ⟷ "en",
   [agrO, second, sg] ⟷ "t",
   ⟨⟨[agrS, third], [[item "nin"]], []⟩, ""⟩,
   [agrS, third] ⟷ "ne"]

/-- (23), left: a third-singular subject acting on a third-singular object. -/
def seeBy3sg : ComplexHead Feature String := chukchi "u" [third, sg] [third, sg]

/-- (23), right: a third-plural subject, same object. -/
def seeBy3pl : ComplexHead Feature String := chukchi "u" [third, pl] [third, sg]

/-- (19c): the -nin allomorph, selected outward by the third-singular subject,
bleeds the prefix. -/
theorem nin_bleeds_prefix : morphs chukchiVocab seeBy3sg = ["u", "nin"] := by decide

/-- (19i): the elsewhere allomorph leaves the prefix in place. -/
theorem elsewhere_retains_prefix : morphs chukchiVocab seeBy3pl = ["ne", "u", "en"] := by decide

/-- (26): dative agreement preempts -nin under the same third-singular
subject, and the prefix survives — the trigger is the item, not the syntax. -/
theorem ditransitive_retains_prefix :
    morphs chukchiVocab (chukchi "jl" [third, sg] [second, sg]) = ["ne", "jl", "t"] := by
  decide

/-- (23): under rewriting the two structures present feature-identical inner
contexts to the prefix, so no rule conditioned on object features can
distinguish where ne- is bled — the impossible Pseudo-Chukchi of (28a). -/
theorem prefix_context_features_identical :
    ((seeBy3sg.insertUpTo (· = "") chukchiVocab .hierarchical itemFeatures .rewriting 1).contextAt
        (· = "") .hierarchical (λ _ => []) 1).leftCtx =
      ((seeBy3pl.insertUpTo (· = "") chukchiVocab .hierarchical itemFeatures .rewriting 1).contextAt
        (· = "") .hierarchical (λ _ => []) 1).leftCtx := by
  decide

/-- The inserted items do distinguish the two contexts: the bleeding is
conditionable inward, but only as sensitivity to the vocabulary item. -/
theorem prefix_context_item_distinct :
    (stepContext chukchiVocab seeBy3sg .rewriting 1).leftCtx
      ≠ (stepContext chukchiVocab seeBy3pl .rewriting 1).leftCtx := by
  decide

end Bobaljik2000
