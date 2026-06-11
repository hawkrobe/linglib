import Linglib.Data.Examples.Steedman2000
import Linglib.Fragments.English.Toy
import Linglib.Phenomena.Ellipsis.Gapping
import Linglib.Phenomena.WordOrder.CrossSerial
import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.CrossSerial
import Linglib.Syntax.CCG.Interface
import Linglib.Syntax.CCG.Scope

/-!
# Steedman 2000: The Syntactic Process

CCG predictions from [steedman-2000], one section per phenomenon:

- **Word order**: slash direction in lexical categories enforces English
  SVO.
- **Non-constituent coordination**: type-raising + composition make "John
  likes" a constituent (`S/NP`), and generalized conjunction delivers the
  conjunctive interpretation (modeled on the book's "Anna married, and I
  detest, Manny").
- **Gapping**: [ross-1970]'s word-order/gapping-direction generalization,
  recovered from the type-raising directions a language's verb categories
  license.
- **Cross-serial dependencies**: Dutch verb clusters ([bresnan-etal-1982])
  with cross-serial NP-verb bindings (the substrate direction-flips the
  book's crossed-composition analysis — see the section header).
- **Verb clusters and quantifier scope** (§6.8): verb-raising orders are
  scope-ambiguous, verb-projection-raising orders surface-only; predictions
  are computed via `CCG.Scope.analyzeDerivation` and checked against the
  §6.8 judgments in `Linglib.Data.Examples.Steedman2000` ([bayer-1996],
  [kayne-1998], [haegeman-van-riemsdijk-1986], [haegeman-1992] are
  credited per example in the JSON).
-/

namespace Steedman2000

open CCG

/-! ### Word order

Slash direction encodes word order: `TV = (S\NP)/NP` looks right for the
object NP first, then the resulting `S\NP` looks left for the subject,
enforcing SVO. -/

def mary_eats_pizza : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

def he_sees_her : DerivStep :=
  .bapp (.lex ⟨"he", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"her", NP⟩))

def the_cat_eats_pizza : DerivStep :=
  .bapp (.fapp (.lex ⟨"the", Det⟩) (.lex ⟨"cat", N⟩))
        (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

theorem mary_eats_pizza_cat : mary_eats_pizza.cat = some S := rfl
theorem he_sees_her_cat : he_sees_her.cat = some S := rfl
theorem the_cat_eats_pizza_cat : the_cat_eats_pizza.cat = some S := rfl

/-! ### Non-constituent coordination -/

section Coordination

open Semantics.Montague

/-- CCG derives "John likes and Mary hates beans" (modeled on the book's
"Anna married, and I detest, Manny") with category S: "John likes" is a
constituent `S/NP` via type-raising + composition. -/
theorem john_likes_and_mary_hates_beans_cat :
    john_likes_and_mary_hates_beans.cat = some S := rfl

def john_sleeps_and_mary_sleeps : DerivStep :=
  .coord
    (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
    (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩))

#guard john_sleeps.opCount == 1
#guard john_sleeps_and_mary_sleeps.opCount == 3
#guard john_likes_and_mary_hates_beans.opCount == 8

/-- Non-constituent coordination requires more combinatory operations than
standard coordination. Reading operation count as processing difficulty is
this formalization's linking hypothesis, not a claim of [steedman-2000]. -/
theorem opCount_standardCoord_lt_nonConstituentCoord :
    john_sleeps_and_mary_sleeps.opCount < john_likes_and_mary_hates_beans.opCount := by
  decide

theorem opCount_simple_lt_standardCoord :
    john_sleeps.opCount < john_sleeps_and_mary_sleeps.opCount := by
  decide

/-- Toy semantic lexicon over the toy English fragment ("likes"/"hates"
reuse `sees_sem` as placeholder denotations). -/
def toySemLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  | "beans", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "likes", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "hates", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | _, _ => none

theorem getMeaning_john_sleeps :
    getMeaning (john_sleeps.interp toySemLexicon) = some True := rfl

theorem getMeaning_john_sees_mary :
    getMeaning (CCG.john_sees_mary.interp toySemLexicon) = some True := rfl

#guard (CCG.john_tr.interp toySemLexicon).isSome

/-- "John sees Mary" with a type-raised subject: the raised subject
`CCG.john_tr : S/(S\NP)` uses forward application, and the derivation
produces the same truth value as the canonical one. -/
def john_sees_mary_via_tr : DerivStep :=
  .fapp CCG.john_tr (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

theorem getMeaning_john_sees_mary_via_tr :
    getMeaning (john_sees_mary_via_tr.interp toySemLexicon) = some True := rfl

#guard (CCG.john_likes.interp toySemLexicon).isSome
#guard (john_likes_and_mary_hates.interp toySemLexicon).isSome
#guard (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome

/-- The predicate "John likes and Mary hates" (category `S/NP`) evaluated
at an entity. -/
def coordMeaningAt (e : ToyEntity) : Option Prop :=
  (getPredicateMeaning (john_likes_and_mary_hates.interp toySemLexicon)).map (· e)

/-- The pointwise conjunction of "John likes" and "Mary hates" at an entity. -/
def pointwiseConjAt (e : ToyEntity) : Option Prop :=
  match getPredicateMeaning (john_likes.interp toySemLexicon),
        getPredicateMeaning (mary_hates.interp toySemLexicon) with
  | some m₁, some m₂ => some (m₁ e ∧ m₂ e)
  | _, _ => none

/-- Generalized conjunction delivers the conjunctive interpretation:
⟦John likes and Mary hates⟧(e) = ⟦John likes⟧(e) ∧ ⟦Mary hates⟧(e). -/
theorem coordMeaningAt_eq_pointwiseConjAt :
    ∀ e : ToyEntity, coordMeaningAt e = pointwiseConjAt e := fun _ => rfl

/-- The truth conditions of "John likes and Mary hates beans" are the
conjunction of the two predications (in the toy model, likes = hates = sees). -/
theorem getMeaning_john_likes_and_mary_hates_beans :
    getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon) =
      some (ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.john ∧
            ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.mary) := rfl

/-- The spelled-out paraphrase "John likes beans and Mary hates beans". -/
def john_likes_beans_and_mary_hates_beans : DerivStep :=
  .coord
    (.bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"likes", TV⟩) (.lex ⟨"beans", NP⟩)))
    (.bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"hates", TV⟩) (.lex ⟨"beans", NP⟩)))

/-- The non-constituent coordination and its spelled-out paraphrase receive
the same truth conditions — the book's claim that the composed derivation
yields the same predicate-argument structure as the canonical one. -/
theorem nonConstituentCoord_eq_spelledOut :
    getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon) =
      getMeaning (john_likes_beans_and_mary_hates_beans.interp toySemLexicon) := rfl

end Coordination

/-! ### Gapping

[ross-1970]'s generalization — gapping direction tracks word order —
which [steedman-2000] derives from the Principles of Adjacency,
Consistency, and Inheritance together with the order-preserving constraint
on type-raising. The predicted pattern below is stated over the
word-order predicates of `Phenomena.Ellipsis.Gapping`; deriving it from
the slash directions of `CCG.Gapping`'s gapped categories is TODO.
(Dutch licensing both directions is `Phenomena.Ellipsis.Gapping.mixed_allows_both`.) -/

section Gapping

open Phenomena.Ellipsis.Gapping

/-- The gapping directions CCG predicts for a word order: forward gapping
needs a leftward-looking gapped conjunct, available through backward
type-raising over rightward-seeking verbs (`T\(T/NP)`); backward gapping
needs forward raising over leftward-seeking verbs (`T/(T\NP)`). -/
def predictedGappingPattern (order : WordOrder) : GappingPattern :=
  ⟨HasRightwardVerbs order, HasLeftwardVerbs order⟩

/-- The CCG-predicted pattern coincides with Ross's generalization. -/
theorem predictedGappingPattern_iff_rossOriginal :
    ∀ order : WordOrder,
      ((predictedGappingPattern order).allowsForward ↔
        (rossOriginal order).allowsForward) ∧
      ((predictedGappingPattern order).allowsBackward ↔
        (rossOriginal order).allowsBackward) := by
  intro order
  cases order <;> exact ⟨Iff.rfl, Iff.rfl⟩

/-- SVO patterns with VSO: both license forward but not backward gapping. -/
theorem predictedGappingPattern_svo_iff_vso :
    ((predictedGappingPattern .SVO).allowsForward ↔
      (predictedGappingPattern .VSO).allowsForward) ∧
    ((predictedGappingPattern .SVO).allowsBackward ↔
      (predictedGappingPattern .VSO).allowsBackward) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- English (SVO) has no leftward-looking transitive verb category, so the
rightward-looking gapped conjunct a backward gap needs cannot be built:
"*Warren, potatoes and Dexter ate bread" (instantiating Steedman's
`*SO and SVO` schema; the book's attested forward counterpart is "Dexter
ate bread and Warren, potatoes"). -/
theorem no_backward_gapping_in_english :
    ¬ HasLeftwardVerbs .SVO := id

end Gapping

/-! ### Cross-serial dependencies

Dutch verb clusters ([bresnan-etal-1982]) with cross-serial NP-verb
bindings. Caveat: the book's analysis gives the cluster verbs leftward NP
slots and composes them by forward *crossed* composition; the substrate
derivations in `CCG.CrossSerial` flip the NP slots rightward so plain
B/B² suffice (flagged there as not matching Dutch surface order). The
binding permutation — the empirical target — is unaffected. -/

section CrossSerial

open CCG.CrossSerial
open Phenomena.WordOrder.CrossSerial
open Features (VerbClusterBinding)

/-- A CCG derivation annotated with which NP binds to which verb.
TODO: compute `binding` from `deriv`'s composition structure instead of
annotating it by hand. -/
structure AnnotatedDerivation where
  /-- Number of NP-verb pairs -/
  n : Nat
  deriv : CCG.Classical.Derivation
  /-- Surface words -/
  words : List String
  /-- The NP-verb binding permutation -/
  binding : VerbClusterBinding n
  deriving Repr

/-- "Jan Piet zag zwemmen" with cross-serial bindings: Jan is the subject
of "zag", Piet the argument picked up by "zwemmen". -/
def dutch_jan_piet_zag_zwemmen : AnnotatedDerivation :=
  { n := 2
  , deriv := jan_zag_zwemmen_piet
  , words := ["Jan", "Piet", "zag", "zwemmen"]
  , binding := VerbClusterBinding.identity 2
  }

/-- "Jan Piet Marie zag helpen zwemmen": the verb cluster composes into a
3-place predicate absorbing Marie (outermost slot → zwemmen), Piet
(inner slot → helpen), and Jan (subject → zag) — the cross-serial
binding pattern. (Direction-flipped from the book's crossed-composition
analysis; see the section header.) -/
def dutch_jan_piet_marie_zag_helpen_zwemmen : AnnotatedDerivation :=
  { n := 3
  , deriv := jan_piet_marie_zag_helpen_zwemmen_deriv
  , words := ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"]
  , binding := VerbClusterBinding.identity 3
  }

/-- The annotated binding agrees with the empirical datum. -/
theorem dutch_jan_piet_zag_zwemmen_binding :
    dutch_jan_piet_zag_zwemmen.binding = dutch_2np_2v.binding := rfl

theorem dutch_jan_piet_marie_zag_helpen_zwemmen_binding :
    dutch_jan_piet_marie_zag_helpen_zwemmen.binding = dutch_3np_3v.binding := rfl

end CrossSerial

/-! ### Verb clusters and quantifier scope (§6.8)

Scope tracks word order: in the verb-raising order the cluster forms by
composition, so a quantified argument combines with a function containing
the tensed verb and can take scope over it; in the verb-projection-raising
order it combines with the embedded verb alone. The derivations below are
schematic `DerivStep` trees (the toy `Cat` lacks the crossed composition
real Dutch clusters need); they capture the composed-cluster vs.
applied-cluster contrast driving the account. -/

section Quantification

open CCG.Scope ScopeTheory Data.Examples

/-- Word order in a West Germanic verb cluster ([steedman-2000] §6.8). -/
inductive VerbOrder where
  /-- Object precedes the whole verb cluster: NP … V_emb V_matrix. -/
  | verbRaising
  /-- Object follows the matrix verb: V_matrix … NP V_emb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

/-- Verb-raising order, schematized on Dutch (99a): the cluster
*probeert te zingen* forms by composition before taking the object. -/
def verbRaisingDeriv : DerivStep :=
  .bapp (.lex ⟨"veel liederen", NP⟩)
    (.fcomp (.lex ⟨"probeert", IV / IV⟩) (.lex ⟨"te zingen", IV \ NP⟩))

/-- Verb-projection-raising order, schematized on Dutch (99b): the matrix
verb applies to an already-saturated embedded VP, so the quantified
object never combines with a function containing the tensed verb. -/
def verbProjectionRaisingDeriv : DerivStep :=
  .fapp (.lex ⟨"probeert", IV / IV⟩)
    (.bapp (.lex ⟨"veel liederen", NP⟩) (.lex ⟨"te zingen", IV \ NP⟩))

/-- The CCG derivation shape each verb order forces. -/
def schematicDeriv : VerbOrder → DerivStep
  | .verbRaising => verbRaisingDeriv
  | .verbProjectionRaising => verbProjectionRaisingDeriv

theorem analyzeDerivation_verbRaisingDeriv :
    analyzeDerivation verbRaisingDeriv = .composed := rfl

theorem analyzeDerivation_verbProjectionRaisingDeriv :
    analyzeDerivation verbProjectionRaisingDeriv = .directApp := rfl

/-- Scope availability as CCG predicts it: analyze the derivation the
word order forces and read availability off its derivation type. -/
def predictedAvailability (vo : VerbOrder) : BinaryScopeAvailability :=
  derivationTypeToAvailability (analyzeDerivation (schematicDeriv vo))

/-- Read the §6.8 word-order classification off an example's
`paperFeatures`. -/
def wordOrderOf (ex : LinguisticExample) : Option VerbOrder :=
  match ex.paperFeatures.lookup "wordOrder" with
  | some "verbRaising" => some .verbRaising
  | some "verbProjectionRaising" => some .verbProjectionRaising
  | _ => none

/-- Observed scope availability: the judgment on the example's "inverse"
reading (the "surface" reading is acceptable throughout §6.8). -/
def observedAvailability (ex : LinguisticExample) : Option BinaryScopeAvailability :=
  match ex.readings.lookup "inverse" with
  | some .acceptable => some .ambiguous
  | some .unacceptable => some .surfaceOnly
  | _ => none

/-- The §6.8 data as (word order, observed availability) pairs. -/
def scopeData : List (VerbOrder × BinaryScopeAvailability) :=
  Examples.all.filterMap λ ex =>
    (wordOrderOf ex).bind λ vo => (observedAvailability ex).map λ av => (vo, av)

-- Drift sentry: today every example in the JSON is a §6.8 scope example
-- carrying both annotations; this fires if one without them is added.
#guard scopeData.length == Examples.all.length

/-- The CCG prediction matches every §6.8 judgment. -/
theorem predictedAvailability_eq_observed :
    ∀ d ∈ scopeData, predictedAvailability d.1 = d.2 := by
  decide

end Quantification

end Steedman2000
