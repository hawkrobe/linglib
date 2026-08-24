import Linglib.Semantics.Definiteness.Maximality
import Linglib.Semantics.Mereology
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Genericity.MeaningPreservation
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.German.Determiners
import Linglib.Fragments.Mandarin.Determiners
import Linglib.Fragments.Thai.Determiners
import Linglib.Fragments.Shan.Determiners
import Linglib.Fragments.Shan.Nouns
import Linglib.Studies.Jenks2018

/-!
# Moroney (2021): definiteness and quantification in Shan

[moroney-2021] shows that Shan (Southwestern Tai) bare nouns express both unique and
anaphoric definiteness, instantiating an unmarked cell that [jenks-2018]'s definiteness
typology had no slot for. Because Shan has no articles, no covert type-shift is blocked — ι,
ι^x and ∩ are all available to bare nouns — while the optional demonstratives *nâj/nân*
only add spatial content. The cell is derived from `Shan.Determiners.inventory`, the
bare-noun reading distribution from `MeaningPreservation.selectShift` over
`Shan.Nouns.blocking`, and the refutation is stated against
`Jenks2018.jenksAttestedStrategies`.

Her comparison of Shan and English bare nouns (Table 2.3) finds them alike on the
low-scope existential, kind and generic readings, alike in lacking a high-scope existential,
and different only on the definite reading; that difference is derived here
(`shan_iota_english_none`) rather than tabulated. On the mass/count side she adopts
[deal-2017]'s generalized homogeneity — a predicate is g-homogeneous when it is cumulative
and, among other options, lacks minimal parts — and argues that Shan count nouns, like
English *furniture*, are cumulative but have identifiable atomic parts
(`maa_cumulative_not_divisive`). The demonstratives are the definite with the
referent's closeness to the speaker added: *nâj* presupposes a unique `P` in the situation
and refers to it if it is close (`demDenotation`, her (147)–(148)).

## References

* [moroney-2021]
* [deal-2017], [jenks-2018], [schwarz-2013]
-/

namespace Moroney2021

open Semantics.Definiteness (russellIotaList)
open Semantics.Kinds
open Features.Deixis (Feature)
open Mereology (CUM)

/-! ### Type-shift selection -/

/-- The type-shift context of a Shan number-neutral bare noun: nothing is blocked
(`Shan.Nouns.blocking`), and only the predicate's kind-compatibility varies. -/
def shanCtx (downDefined : Bool) : MeaningPreservation.TypeShiftContext :=
  { number := .neutral
  , downDefined := downDefined
  , iotaBlocked := Shan.Nouns.blocking.iotaBlocked
  , iotaAnaphoricBlocked := false
  , existsBlocked := Shan.Nouns.blocking.existsBlocked
  , instantiationAccessible := true }

/-- With a non-kind predicate a Shan bare noun type-shifts by ι — the definite reading —
while an English bare singular gets no shift at all, since *the* and *a* block ι and ∃. -/
theorem shan_iota_english_none :
    MeaningPreservation.selectShift (shanCtx false) = some .iota ∧
      MeaningPreservation.selectShift
        { number := .sg, downDefined := false, iotaBlocked := true, iotaAnaphoricBlocked := true
        , existsBlocked := true, instantiationAccessible := true } = none :=
  ⟨rfl, rfl⟩

/-- With a kind-compatible predicate ∩ is selected while ι and ι^x remain available — the
definite/kind ambiguity of Shan bare nouns. -/
theorem shan_kind_ambiguity :
    MeaningPreservation.selectShift (shanCtx true) = some .down ∧
      .iota ∈ MeaningPreservation.availableShifts (shanCtx true) ∧
      .iotaAnaphoric ∈ MeaningPreservation.availableShifts (shanCtx true) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- Shan's ι^x is unblocked, so bare nouns reach anaphoric definiteness; blocking ι^x —
Thai's demonstrative — removes exactly that reading. -/
theorem shan_thai_anaphoric_contrast :
    .iotaAnaphoric ∈ MeaningPreservation.availableShifts (shanCtx false) ∧
      .iotaAnaphoric ∉ MeaningPreservation.availableShifts
        { shanCtx false with iotaAnaphoricBlocked := true } := by
  constructor <;> decide

/-- ι outranks ∃ under Meaning Preservation: ∃ is available but never selected when ι is, so
Shan bare nouns default to definite or kind readings and the existential reading arises only
through existential closure at vP — whence the missing high-scope existential. -/
theorem shan_exists_is_last_resort :
    (MeaningPreservation.availableShifts (shanCtx false)).head? = some .iota ∧
      .exists ∈ MeaningPreservation.availableShifts (shanCtx false) :=
  ⟨rfl, by decide⟩

/-! ### The typology, derived per language -/

/-- Each language's marking strategy, computed by `Determiner.Inventory.markingStrategy`
from its declared inventory: the four languages fill all four cells of the revised
typology. -/
theorem derive_all_languages :
    English.Determiners.inventory.markingStrategy = .generallyMarked ∧
      German.Determiners.inventory.markingStrategy = .bipartite ∧
      Thai.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
      Shan.Determiners.inventory.markingStrategy = .unmarked :=
  ⟨English.Determiners.marking, German.Determiners.marking, Thai.Determiners.marking,
    Shan.Determiners.marking⟩

/-- The [schwarz-2013]-style article-type projection of the same inventories. -/
theorem derive_article_types :
    English.Determiners.inventory.articleType = .weakOnly ∧
      German.Determiners.inventory.articleType = .weakAndStrong ∧
      Thai.Determiners.inventory.articleType = .weakOnly ∧
      Shan.Determiners.inventory.articleType = .none_ := by
  decide

/-- `ArticleType` is lossy where `DefMarkingStrategy` is not: English and Mandarin differ in
strategy yet collapse to the same article type. -/
theorem articleType_lossy :
    English.Determiners.inventory.markingStrategy ≠
        Mandarin.Determiners.inventory.markingStrategy ∧
      English.Determiners.inventory.articleType = Mandarin.Determiners.inventory.articleType := by
  decide

/-- Shan has no determiner realizing anaphoric definiteness, yet expresses it — through bare
nouns (unblocked ι^x) and the optional demonstratives, which it does realize. -/
theorem shan_anaphoric_without_article :
    ¬ Shan.Determiners.inventory.Realizes .anaphoric ∧
      Shan.Determiners.inventory.Realizes .demonstrative := by
  constructor <;> decide

/-- English realizes anaphoric definiteness through syncretic *the* and German through its
dedicated strong article. -/
theorem english_german_anaphoric_realized :
    English.Determiners.inventory.Realizes .anaphoric ∧
      German.Determiners.inventory.Realizes .anaphoric := by
  decide

/-- Shan's derived strategy falls outside [jenks-2018]'s attested set — the fourth,
unmarked cell. -/
theorem shan_refutes_jenks_typology :
    Shan.Determiners.inventory.markingStrategy ∉ Jenks2018.jenksAttestedStrategies := by
  rw [Shan.Determiners.marking]; decide

/-! ### Shan count nouns are cumulative but not homogeneous -/

/-- The first clause of [deal-2017]'s generalized homogeneity: `P` lacks minimal parts when
every `P`-element has a proper `P`-part. -/
def LacksMinimalParts {α : Type*} [Preorder α] (P : α → Prop) : Prop :=
  ∀ x, P x → ∃ y < x, P y

/-- Dog-pluralities over two dogs: the nonempty subsets. -/
abbrev isDog (x : Finset (Fin 2)) : Prop := x.Nonempty

/-- Shan *mǎa* 'dog' patterns with English *furniture*: the sum of dogs is dogs, but the
individual dogs are minimal, so the predicate is cumulative without being homogeneous. -/
theorem maa_cumulative_not_divisive : CUM isDog ∧ ¬ LacksMinimalParts isDog := by
  refine ⟨fun _ hx _ _ => hx.mono Finset.subset_union_left, fun h => ?_⟩
  obtain ⟨y, hy, hne⟩ := h {0} (Finset.singleton_nonempty 0)
  exact hne.ne_empty ((Finset.subset_singleton_iff.1 hy.le).resolve_right hy.ne)

/-! ### Demonstratives add spatial content -/

/-- The bare definite description: the unique referent satisfying the restrictor, the
uniqueness reading available to Shan bare nouns. -/
def bareDefinite {E : Type*} (domain : List E) (restrictor : E → Bool) : Option E :=
  russellIotaList domain restrictor

/-- The demonstrative denotation of Moroney's (147)–(148): the bare definite, presupposing a
unique referent, further required to satisfy the demonstrative's spatial content
(`ιx[P(x) ∧ CLOSE.TO.SPEAKER(x)]`). -/
def demDenotation {E : Type*} (domain : List E) (d : DemonstrativeDeterminer)
    (restrictor : E → Bool) (spatialPred : Feature → E → Bool) : Option E :=
  (bareDefinite domain restrictor).filter (spatialPred d.deictic)

/-- The demonstrative refers exactly when the bare definite does and its referent has the
demonstrative's spatial property, so *nâj/nân* are optional wherever the bare noun already
provides the definite reading. -/
theorem demDenotation_eq_some_iff {E : Type*} (domain : List E) (d : DemonstrativeDeterminer)
    (restrictor : E → Bool) (spatialPred : Feature → E → Bool) (e : E) :
    demDenotation domain d restrictor spatialPred = some e ↔
      bareDefinite domain restrictor = some e ∧ spatialPred d.deictic e = true :=
  Option.filter_eq_some_iff

end Moroney2021
