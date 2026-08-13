import Linglib.Semantics.Definiteness.Defs
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
# Moroney (2021): Definiteness and Quantification — Evidence from Shan

[moroney-2021] shows that Shan (Southwestern Tai, Kra-Dai) bare nouns express
both unique and anaphoric definiteness, instantiating an unmarked cell that
[jenks-2018]'s definiteness typology had no slot for. Because Shan has no
articles, no covert type-shift is blocked — ι, ι^x, and ∩ are all available
to bare nouns — while the optional demonstratives *nâj/nân* merely add
spatial content. The cell is derived from `Shan.Determiners.inventory`, the
bare-noun reading distribution from `MeaningPreservation.selectShift` over
`Shan.Nouns.blocking`, and the refutation is stated against
`Jenks2018.jenksAttestedStrategies`.

## References

* [moroney-2021]
-/

namespace Moroney2021

open Semantics.Definiteness (russellIotaList)
open Semantics.Kinds
open Features.Deixis (Feature)

/-! ### Bare-noun readings (Table 2.3) -/

/-- The five candidate readings of a bare noun. -/
inductive BareNounInterp where
  /-- Low-scope ∃, introduced by Derived Predicate Predication at vP
      ([moroney-2021] (85)), hence below negation. -/
  | lowExistential
  /-- Wide-scope ∃ above negation — unavailable to bare nouns, since DPP
      applies no higher than vP. -/
  | highExistential
  /-- Definite, via the ι type-shift. -/
  | definite
  /-- Kind, via the ∩ type-shift. -/
  | kind
  /-- Generic, via GEN over situations. -/
  | generic
  deriving DecidableEq, Repr

/-- One Table 2.3 row: whether a reading is available to Shan and English
    count and mass bare nouns. -/
structure InterpAvailability where
  interp : BareNounInterp
  shanCount : Bool
  shanMass : Bool
  englishCount : Bool
  englishMass : Bool
  deriving Repr, DecidableEq

/-- Table 2.3: Shan and English bare nouns share the low-∃, kind, and
    generic readings, both lack the high-∃ reading, and part ways only on
    the definite reading. -/
def interpretationTable : List InterpAvailability :=
  [ { interp := .lowExistential
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true }
  , { interp := .highExistential
    , shanCount := false, shanMass := false
    , englishCount := false, englishMass := false }
  , { interp := .definite
    , shanCount := true, shanMass := true
    , englishCount := false, englishMass := false }
  , { interp := .kind
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true }
  , { interp := .generic
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true } ]

/-- The definite reading is the sole point where Shan and English bare
    nouns differ. -/
theorem definite_is_sole_difference :
    (interpretationTable.filter
      (fun d => d.shanCount != d.englishCount || d.shanMass != d.englishMass)
    ).map (·.interp) = [.definite] := by decide

/-! ### Type-shift selection -/

/-- The type-shift context of a Shan number-neutral bare noun: nothing is
    blocked (`Shan.Nouns.blocking`), and only the predicate's
    kind-compatibility varies. -/
def shanCtx (downDefined : Bool) : MeaningPreservation.TypeShiftContext :=
  { number := .neutral
  , downDefined := downDefined
  , iotaBlocked := Shan.Nouns.blocking.iotaBlocked
  , iotaAnaphoricBlocked := false
  , existsBlocked := Shan.Nouns.blocking.existsBlocked
  , instantiationAccessible := true }

/-- With a non-kind predicate a Shan bare noun type-shifts by ι — the
    definite reading — while an English bare singular gets no shift at all,
    since *the* and *a* block ι and ∃. -/
theorem shan_iota_english_none :
    MeaningPreservation.selectShift (shanCtx false) = some .iota ∧
    MeaningPreservation.selectShift
      { number := .sg, downDefined := false
      , iotaBlocked := true, iotaAnaphoricBlocked := true
      , existsBlocked := true, instantiationAccessible := true } = none :=
  ⟨rfl, rfl⟩

/-- With a kind-compatible predicate ∩ is selected while ι and ι^x remain
    available — the definite/kind ambiguity of Shan bare nouns. -/
theorem shan_kind_ambiguity :
    MeaningPreservation.selectShift (shanCtx true) = some .down ∧
    .iota ∈ MeaningPreservation.availableShifts (shanCtx true) ∧
    .iotaAnaphoric ∈ MeaningPreservation.availableShifts (shanCtx true) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- Shan's ι^x is unblocked, so bare nouns reach anaphoric definiteness;
    blocking ι^x — Thai's demonstrative — removes exactly that reading. -/
theorem shan_thai_anaphoric_contrast :
    .iotaAnaphoric ∈ MeaningPreservation.availableShifts (shanCtx false) ∧
    .iotaAnaphoric ∉ MeaningPreservation.availableShifts
      { shanCtx false with iotaAnaphoricBlocked := true } := by
  constructor <;> decide

/-- ι outranks ∃ under Meaning Preservation: ∃ is available but never
    selected when ι is, so Shan bare nouns default to definite or kind
    readings, and the existential reading arises only through DPP at vP —
    whence the missing high-∃ row of Table 2.3. -/
theorem shan_exists_is_last_resort :
    (MeaningPreservation.availableShifts (shanCtx false)).head? = some .iota ∧
    .exists ∈ MeaningPreservation.availableShifts (shanCtx false) :=
  ⟨rfl, by decide⟩

/-! ### The typology, derived per language (Tables 4.1 and 4.4) -/

/-- Each Table 4.4 language's marking strategy, computed by
    `Determiner.Inventory.markingStrategy` from its declared inventory: the
    four languages fill all four cells of the revised typology. -/
theorem derive_all_languages :
    English.Determiners.inventory.markingStrategy = .generallyMarked ∧
    German.Determiners.inventory.markingStrategy = .bipartite ∧
    Thai.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
    Shan.Determiners.inventory.markingStrategy = .unmarked :=
  ⟨English.Determiners.marking, German.Determiners.marking,
   Thai.Determiners.marking, Shan.Determiners.marking⟩

/-- The [schwarz-2013]-style article-type projection of the same
    inventories. -/
theorem derive_article_types :
    English.Determiners.inventory.articleType = .weakOnly ∧
    German.Determiners.inventory.articleType = .weakAndStrong ∧
    Thai.Determiners.inventory.articleType = .weakOnly ∧
    Shan.Determiners.inventory.articleType = .none_ := by decide

/-- `ArticleType` is lossy where `DefMarkingStrategy` is not: English and
    Mandarin differ in strategy yet collapse to the same article type. -/
theorem articleType_lossy :
    English.Determiners.inventory.markingStrategy ≠
      Mandarin.Determiners.inventory.markingStrategy ∧
    English.Determiners.inventory.articleType =
      Mandarin.Determiners.inventory.articleType := by decide

/-! ### Shan count nouns are fake-mass nouns (§2.3.1) -/

/-- A four-element mereology: dogs `a`, `b`, their sum `ab`, and a leg `c`
    below the sum that is not a dog. -/
inductive FakeMassEntity where
  | a | b | c | ab
  deriving DecidableEq, Fintype, Repr

private def fmLe : FakeMassEntity → FakeMassEntity → Bool
  | _, .ab => true
  | .a, .a => true
  | .b, .b => true
  | .c, .c => true
  | _, _ => false

private def fmSup : FakeMassEntity → FakeMassEntity → FakeMassEntity
  | .a, .a => .a
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .ab

instance : SemilatticeSup FakeMassEntity where
  le x y := fmLe x y = true
  le_refl := by decide
  le_antisymm := by decide
  le_trans := by decide
  sup := fmSup
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

/-- Dogs: the atoms `a`, `b` and their sum `ab`; the leg `c` is not a dog. -/
def isDog : FakeMassEntity → Prop
  | .c => False
  | _ => True

instance : DecidablePred isDog := fun x => by
  cases x <;> unfold isDog <;> infer_instance

/-- Shan bare count nouns pattern with English furniture-type nouns
    ([moroney-2021] §2.3.1): cumulative — the sum of dogs is dogs — but not
    g-homogeneous, since the leg below the sum has no dog part. -/
theorem isDog_fakeMass : Mereology.FakeMass isDog := by
  constructor
  · intro x hx y hy
    cases x <;> cases y <;> first | exact trivial | exact hx.elim
  · intro h
    have hlt : (FakeMassEntity.c : FakeMassEntity) < .ab :=
      lt_of_le_of_ne (show fmLe .c .ab = true from rfl) (by decide)
    obtain ⟨z, hzc, hPz⟩ := h .ab .c trivial hlt
    cases z with
    | a => exact absurd hzc (show ¬(fmLe .a .c = true) by decide)
    | b => exact absurd hzc (show ¬(fmLe .b .c = true) by decide)
    | c => exact hPz
    | ab => exact absurd hzc (show ¬(fmLe .ab .c = true) by decide)

/-! ### Demonstratives add spatial content (§2.4.3) -/

/-- The demonstrative denotation of [moroney-2021] (147)–(148), a referent
    selector with the demonstrative's spatial content added to the
    restrictor: `⟦DEM⟧(P) = ιx[P(x) ∧ SPATIAL(x)]`, where `russellIotaList`
    carries the uniqueness presupposition. -/
def demDenotation {E : Type} (domain : List E) (d : DemonstrativeDeterminer)
    (restrictor : E → Bool) (spatialPred : Feature → E → Bool) : Option E :=
  russellIotaList domain (fun e => restrictor e && spatialPred d.deictic e)

/-- The bare definite description is the unfiltered referent selector, the
    uniqueness-based reading available to Shan bare nouns. -/
def bareDefinite {E : Type} (domain : List E) (restrictor : E → Bool) :
    Option E :=
  russellIotaList domain restrictor

/-- When the bare description selects a referent that satisfies the
    demonstrative's spatial predicate, the demonstrative selects the same
    referent, so *nâj*/*nân* are optional in such contexts — the bare noun
    already provides the definite reading via unblocked ι. -/
theorem dem_refines_bare {E : Type} (domain : List E)
    (restrictor : E → Bool) (spatialPred : Feature → E → Bool)
    (d : DemonstrativeDeterminer) (e : E)
    (hBare : bareDefinite domain restrictor = some e)
    (hSpatial : spatialPred d.deictic e = true) :
    demDenotation domain d restrictor spatialPred = some e := by
  rw [bareDefinite, Semantics.Definiteness.russellIotaList_eq_some_iff] at hBare
  rw [demDenotation, Semantics.Definiteness.russellIotaList_eq_some_iff]
  have : domain.filter (fun e' => restrictor e' && spatialPred d.deictic e') =
         (domain.filter restrictor).filter (fun e' => spatialPred d.deictic e') := by
    rw [List.filter_filter]
    congr 1; funext e'; exact Bool.and_comm _ _
  rw [this, hBare]; simp [hSpatial]

/-! ### Realization: anaphoric definiteness without an anaphoric article -/

/-- Shan has no determiner realizing anaphoric definiteness, yet expresses
    it — through bare nouns (unblocked ι^x) and the optional
    demonstratives. -/
theorem shan_anaphoric_not_realized_via_article :
    ¬ Shan.Determiners.inventory.Realizes .anaphoric := by decide

/-- Shan does realize the demonstrative kind — the *nâj*/*nân* paradigm. -/
theorem shan_demonstrative_realized :
    Shan.Determiners.inventory.Realizes .demonstrative := by decide

/-- English realizes anaphoric definiteness through syncretic *the* and
    German through its dedicated strong article, while Shan has no realizing
    form at all. -/
theorem english_german_anaphoric_realized :
    English.Determiners.inventory.Realizes .anaphoric ∧
    German.Determiners.inventory.Realizes .anaphoric := by decide

/-! ### Refuting Jenks's attested-cell prediction -/

/-- Shan's derived strategy falls outside [jenks-2018]'s attested set — the
    discovery of the fourth, unmarked cell. -/
theorem shan_refutes_jenks_typology :
    Shan.Determiners.inventory.markingStrategy
      ∉ Jenks2018.jenksAttestedStrategies := by
  rw [Shan.Determiners.marking]; decide

end Moroney2021
