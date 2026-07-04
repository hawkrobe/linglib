import Linglib.Data.Examples.Steedman2000
import Linglib.Syntax.Anaphora.Basic
import Linglib.Fragments.English.Toy
import Linglib.Fragments.English.Coordination
import Linglib.Studies.BresnanEtAl1982
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
  with cross-serial NP-verb bindings, via the book's leftward argument
  categories and forward crossed composition.
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
  .coord .j
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
  .coord .j
    (.bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"likes", TV⟩) (.lex ⟨"beans", NP⟩)))
    (.bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"hates", TV⟩) (.lex ⟨"beans", NP⟩)))

/-- The non-constituent coordination and its spelled-out paraphrase receive
the same truth conditions — the book's claim that the composed derivation
yields the same predicate-argument structure as the canonical one. -/
theorem nonConstituentCoord_eq_spelledOut :
    getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon) =
      getMeaning (john_likes_beans_and_mary_hates_beans.interp toySemLexicon) := rfl

/-! ### The coordinator's `role` is truth-conditionally load-bearing

`interp` reads the coordinator's `role` off the `.coord` node — it no longer hardcodes
conjunction — so *which* coordinator a derivation uses is part of its truth conditions.
Using the actual English fragment coordinators, conjoining a true sentence `p` and a false
sentence `q` with `and_` (`role = .j`) gives `p ∧ q` (false), while `or_` (`role = .disj`)
gives `p ∨ q` (true). They differ, so the marking's `role` field is load-bearing — flipping
`English.Coordination.and_.role` to `.disj` would break the theorem below, rather than no
theorem depending on it. -/

/-- Minimal lexicon: sentence `p` is true, `q` is false. -/
private def pqLex : SemLexicon Unit Unit := fun w _ =>
  match w with
  | "p" => some ⟨.atom .S, True⟩
  | "q" => some ⟨.atom .S, False⟩
  | _ => none

private def dp : DerivStep := .lex ⟨"p", .atom .S⟩
private def dq : DerivStep := .lex ⟨"q", .atom .S⟩

/-- The coordinator's `role` flips the truth conditions: English `and_` yields `p ∧ q`,
    `or_` yields `p ∨ q`, and these differ at `p = ⊤`, `q = ⊥`. Flipping a fragment
    coordinator's `role` collapses the inequality, so the `role` marking is not decorative. -/
theorem coord_role_load_bearing :
    getMeaning ((DerivStep.coord English.Coordination.and_.role dp dq).interp pqLex) ≠
    getMeaning ((DerivStep.coord English.Coordination.or_.role dp dq).interp pqLex) := by
  have hand : getMeaning ((DerivStep.coord English.Coordination.and_.role dp dq).interp pqLex)
      = some (True ∧ False) := rfl
  have hor : getMeaning ((DerivStep.coord English.Coordination.or_.role dp dq).interp pqLex)
      = some (True ∨ False) := rfl
  rw [hand, hor, ne_eq, Option.some.injEq, eq_iff_iff]
  exact fun h => (h.mpr (Or.inl trivial)).2

end Coordination

/-! ### Gapping

[ross-1970]'s generalization — gapping direction tracks word order —
which [steedman-2000] derives from the Principles of Adjacency,
Consistency, and Inheritance together with the order-preserving constraint
on type-raising. Deriving `predictedGappingPattern` from the slash
directions of `CCG.Gapping`'s gapped categories is TODO.
(Dutch licensing both directions is `mixed_allows_both`.) -/

section Gapping

/-- Basic word order of a transitive clause (S = subject, V = verb,
O = object). -/
inductive WordOrder where
  | SOV
  | SVO
  | VSO
  | VOS
  | OVS
  | OSV
  deriving DecidableEq, Repr

/-- Direction of gapping in a coordinate structure: forward gapping leaves
the gap in the non-initial conjunct ("Dexter ate bread, and Warren,
potatoes"); backward gapping leaves it in the non-final conjunct
(Japanese "Ken-ga Naomi-o, Erika-ga Sara-o tazuneta"). -/
inductive GappingDirection where
  | forward
  | backward
  deriving DecidableEq, Repr

/-- The gapping directions a language allows. -/
structure GappingPattern where
  allowsForward : Prop
  allowsBackward : Prop
  [decAllowsForward : Decidable allowsForward]
  [decAllowsBackward : Decidable allowsBackward]

attribute [instance] GappingPattern.decAllowsForward GappingPattern.decAllowsBackward

def GappingPattern.forwardOnly : GappingPattern := ⟨True, False⟩
def GappingPattern.backwardOnly : GappingPattern := ⟨False, True⟩
def GappingPattern.both : GappingPattern := ⟨True, True⟩
def GappingPattern.neither : GappingPattern := ⟨False, False⟩

/-- [ross-1970]'s generalization: verb-final orders gap backward, the
rest gap forward. -/
def rossOriginal : WordOrder → GappingPattern
  | .SOV => .backwardOnly
  | .VSO => .forwardOnly
  | .SVO => .forwardOnly
  | .VOS => .forwardOnly
  | .OVS => .backwardOnly
  | .OSV => .backwardOnly

/-- The order's transitive verbs seek (at least one of) their arguments
rightward. -/
def HasRightwardVerbs : WordOrder → Prop
  | .VSO => True
  | .SVO => True
  | .VOS => True
  | _ => False

instance : DecidablePred HasRightwardVerbs := fun w => by
  cases w <;> unfold HasRightwardVerbs <;> infer_instance

/-- The order's transitive verbs seek their arguments leftward. -/
def HasLeftwardVerbs : WordOrder → Prop
  | .SOV => True
  | .OVS => True
  | .OSV => True
  | _ => False

instance : DecidablePred HasLeftwardVerbs := fun w => by
  cases w <;> unfold HasLeftwardVerbs <;> infer_instance

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

/-- Main- vs subordinate-clause word order, for languages whose two clause
types diverge. -/
structure ClauseOrderProfile where
  mainClause : WordOrder
  subClause : WordOrder
  deriving Repr

/-- Steedman's revision of [ross-1970]: gapping availability tracks the
lexical availability of verb categories, not a single "underlying" word
order — forward gapping needs rightward-combining verbs, backward gapping
leftward-combining verbs in either clause type. -/
def rossRevised (profile : ClauseOrderProfile) : GappingPattern :=
  ⟨HasRightwardVerbs profile.mainClause,
   HasLeftwardVerbs profile.mainClause ∨ HasLeftwardVerbs profile.subClause⟩

/-- Dutch: SVO main clauses, SOV subordinate clauses. The mixed profile
licenses both gapping directions — forward in main clauses ("Wil jij een
ijsje en Marietje limonade?"), backward in subordinate clauses ("...dat
Jan Syntactic Structures en Piet Aspects gelezen heeft"). -/
def dutch : ClauseOrderProfile := ⟨.SVO, .SOV⟩

/-- A mixed-order language like Dutch licenses both gapping directions. -/
theorem mixed_allows_both :
    (rossRevised dutch).allowsForward ∧ (rossRevised dutch).allowsBackward :=
  ⟨trivial, Or.inr trivial⟩

/-- Steedman's taxonomy of elliptical constructions. -/
inductive EllipsisType where
  /-- "Dexter ate bread, and Warren, potatoes" -/
  | gapping
  /-- "Dexter ran away, and Warren (too)" -/
  | stripping
  /-- "Dexter ate bread, and Warren did too" -/
  | vpEllipsis
  /-- "Dexter did something, but I don't know what" -/
  | sluicing
  deriving DecidableEq, Repr

/-- Gapping and stripping are syntactically mediated via CCG; VP ellipsis
and sluicing are purely anaphoric. -/
def isSyntacticallyMediated : EllipsisType → Prop
  | .gapping => True
  | .stripping => True
  | .vpEllipsis => False
  | .sluicing => False

instance : DecidablePred isSyntacticallyMediated := fun x => by
  cases x <;> unfold isSyntacticallyMediated <;> infer_instance

/-- Only the syntactically mediated ellipsis types exhibit word-order
constraints; VP ellipsis and sluicing pattern alike across languages. -/
def HasWordOrderConstraints : EllipsisType → Prop
  | .gapping => True
  | .stripping => True
  | .vpEllipsis => False
  | .sluicing => False

instance : DecidablePred HasWordOrderConstraints := fun x => by
  cases x <;> unfold HasWordOrderConstraints <;> infer_instance

/-- All four of Steedman's elliptical constructions are *surface* anaphora in
Hankamer & Sag's sense ([hankamer-sag-1976]): each deletes internal structure
under identity with a linguistic antecedent. Steedman's taxonomy contains no
deep anaphor (no *do so*-type pro-form), so the depth axis is constant
`.surface` over it. -/
instance : Anaphor.HasDepth EllipsisType := ⟨fun _ => .surface⟩

/-- **Cross-framework non-alignment.** Steedman's CCG cut `isSyntacticallyMediated`
(gapping/stripping derived by category composition; VP-ellipsis/sluicing handled
anaphorically) is *not* Hankamer & Sag's deep/surface cut. VP-ellipsis is the
paradigm *surface* anaphor ([hankamer-sag-1976]; Landau's own surface baseline in
[landau-2026]) yet CCG treats it as non-mediated — so the two frameworks partition
the very same constructions differently. -/
theorem surface_not_syntacticallyMediated :
    Anaphor.HasDepth.IsSurface EllipsisType.vpEllipsis ∧
      ¬ isSyntacticallyMediated .vpEllipsis := by decide

end Gapping

/-! ### Cross-serial dependencies

Dutch verb clusters ([bresnan-etal-1982]) with cross-serial NP-verb
bindings, using the surface-faithful derivations of `CCG.CrossSerial`:
cluster verbs carry leftward NP slots and the cluster composes by forward
crossed composition, per the book's own Dutch fragment, so the yield
matches the attested word order. -/

section CrossSerial

open CCG.CrossSerial
open BresnanEtAl1982
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
of "zag", Piet the argument bound into the cluster. -/
def dutch_jan_piet_zag_zwemmen : AnnotatedDerivation :=
  { n := 2
  , deriv := jan_piet_zag_zwemmen_sub
  , words := ["Jan", "Piet", "zag", "zwemmen"]
  , binding := VerbClusterBinding.identity 2
  }

/-- "Jan Piet Marie zag helpen zwemmen": `zag >B× (helpen zwemmen)` makes
the cluster a leftward-seeking 3-place predicate; Marie binds `helpen`'s
slot, Piet `zag`'s object slot, Jan the subject — the cross-serial
binding pattern, in the attested word order. -/
def dutch_jan_piet_marie_zag_helpen_zwemmen : AnnotatedDerivation :=
  { n := 3
  , deriv := jan_piet_marie_zag_helpen_zwemmen_sub
  , words := ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"]
  , binding := VerbClusterBinding.identity 3
  }

/-- The annotated binding agrees with the empirical datum. -/
theorem dutch_jan_piet_zag_zwemmen_binding :
    dutch_jan_piet_zag_zwemmen.binding = dutch_2np_2v.binding := rfl

theorem dutch_jan_piet_marie_zag_helpen_zwemmen_binding :
    dutch_jan_piet_marie_zag_helpen_zwemmen.binding = dutch_3np_3v.binding := rfl

/-- The derivations spell out exactly the annotated surface words. -/
theorem dutch_jan_piet_zag_zwemmen_yield :
    dutch_jan_piet_zag_zwemmen.deriv.yield = dutch_jan_piet_zag_zwemmen.words := by
  decide

theorem dutch_jan_piet_marie_zag_helpen_zwemmen_yield :
    dutch_jan_piet_marie_zag_helpen_zwemmen.deriv.yield
      = dutch_jan_piet_marie_zag_helpen_zwemmen.words := by decide

end CrossSerial

/-! ### Verb clusters and quantifier scope (§6.8)

Scope tracks word order: in the verb-raising order the cluster forms by
composition, so a quantified argument combines with a function containing
the tensed verb and can take scope over it; in the verb-projection-raising
order it combines with the embedded verb alone. The derivations below are
category-checked `DerivStep` trees: the verb-raising cluster forms by
forward crossed composition (`CCG.forwardCompX`), the
verb-projection-raising order by plain application — the composed-cluster
vs. applied-cluster contrast driving the account. (The toy `Cat` still
drops the book's features, e.g. the `VP₋SUB` restriction on `>B×`.) -/

section Quantification

open CCG.Scope ScopeTheory Data.Examples

/-- Word order in a West Germanic verb cluster ([steedman-2000] §6.8). -/
inductive VerbOrder where
  /-- Object precedes the whole verb cluster: NP … V_emb V_matrix. -/
  | verbRaising
  /-- Object follows the matrix verb: V_matrix … NP V_emb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

/-- Verb-raising order, Dutch (99a): the cluster *probeert te zingen*
forms by crossed composition before taking the object to its left. -/
def verbRaisingDeriv : DerivStep :=
  .bapp (.lex ⟨"veel liederen", NP⟩)
    (.fcompx (.lex ⟨"probeert", IV / IV⟩) (.lex ⟨"te zingen", IV \ NP⟩))

/-- Verb-projection-raising order, Dutch (99b): the matrix verb applies to
an already-saturated embedded VP, so the quantified object never combines
with a function containing the tensed verb. -/
def verbProjectionRaisingDeriv : DerivStep :=
  .fapp (.lex ⟨"probeert", IV / IV⟩)
    (.bapp (.lex ⟨"veel liederen", NP⟩) (.lex ⟨"te zingen", IV \ NP⟩))

/-- The CCG derivation shape each verb order forces. -/
def schematicDeriv : VerbOrder → DerivStep
  | .verbRaising => verbRaisingDeriv
  | .verbProjectionRaising => verbProjectionRaisingDeriv

/-- Both derivations are category-valid and derive the same category. -/
theorem verbRaisingDeriv_cat : verbRaisingDeriv.cat = some IV := rfl

theorem verbProjectionRaisingDeriv_cat :
    verbProjectionRaisingDeriv.cat = some IV := rfl

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

-- Drift sentry: every example in the JSON is either a ch. 7 gapping
-- stimulus or a §6.8 scope example carrying both annotations; this
-- fires if a row that is neither is added.
#guard Examples.all.all λ ex =>
  (ex.paperFeatures.lookup "phenomenon" == some "gapping") ||
  ((wordOrderOf ex).isSome && (observedAvailability ex).isSome)

/-- The CCG prediction matches every §6.8 judgment. -/
theorem predictedAvailability_eq_observed :
    ∀ d ∈ scopeData, predictedAvailability d.1 = d.2 := by
  decide

end Quantification

/-! ### Truth-conditional pipeline

The complete CCG → Montague pipeline over the toy fragment: derivations
interpreted compositionally, each checked against the toy model. -/

section TruthConditions

open CCG
open Semantics.Montague

-- CCG Derivations for Test Sentences

/-- "John sleeps" - backward application -/
def ccg_john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "Mary sleeps" - backward application -/
def ccg_mary_sleeps : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "John laughs" - backward application -/
def ccg_john_laughs : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "Mary laughs" - backward application -/
def ccg_mary_laughs : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "John sees Mary" - forward then backward application -/
def ccg_john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

/-- "Mary sees John" - forward then backward application -/
def ccg_mary_sees_john : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"John", NP⟩))

/-- "John eats pizza" - forward then backward application -/
def ccg_john_eats_pizza : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

-- Extended Semantic Lexicon (matching the toy model)

/-- Extended lexicon with all entities and predicates -/
def extendedLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  | "pizza", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  | "book", .atom .NP => some ⟨NP, ToyEntity.book⟩
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "reads", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.reads_sem⟩
  | _, _ => none

/-- Get meaning (as Prop) from CCG derivation -/
def ccgMeaning (d : DerivStep) : Option Prop :=
  getMeaning (d.interp extendedLexicon)

-- Pipeline Theorems: CCG Derives Correct Truth Conditions

/-- CCG correctly predicts "John sleeps" is true -/
theorem ccg_predicts_john_sleeps :
    ccgMeaning ccg_john_sleeps = some True := rfl

/-- CCG correctly predicts "Mary sleeps" is false -/
theorem ccg_predicts_mary_sleeps :
    ccgMeaning ccg_mary_sleeps = some False := rfl

/-- CCG correctly predicts "John laughs" is true -/
theorem ccg_predicts_john_laughs :
    ccgMeaning ccg_john_laughs = some True := rfl

/-- CCG correctly predicts "Mary laughs" is true -/
theorem ccg_predicts_mary_laughs :
    ccgMeaning ccg_mary_laughs = some True := rfl

/-- CCG correctly predicts "John sees Mary" is true -/
theorem ccg_predicts_john_sees_mary :
    ccgMeaning ccg_john_sees_mary = some True := rfl

/-- CCG correctly predicts "Mary sees John" is true -/
theorem ccg_predicts_mary_sees_john :
    ccgMeaning ccg_mary_sees_john = some True := rfl

end TruthConditions

end Steedman2000
