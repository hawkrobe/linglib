import Linglib.Data.Examples.Steedman2000
import Linglib.Syntax.Anaphora.Basic
import Linglib.Fragments.English.Toy
import Linglib.Fragments.English.Coordination
import Linglib.Studies.BresnanEtAl1982
import Linglib.Syntax.CCG.Derivation
import Linglib.Syntax.CCG.Grammar
import Linglib.Syntax.CCG.Interface
import Linglib.Syntax.CCG.Intonation
import Linglib.Features.ScopeTypes

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
  are read off the derivations' structure (`Derivation.HasComp`) and checked against the
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

def mary_eats_pizza : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))

def he_sees_her : Derivation Atom S :=
  .bapp (.lex "he" NP) (.fapp (.lex "sees" TV) (.lex "her" NP))

def the_cat_eats_pizza : Derivation Atom S :=
  .bapp (.fapp (.lex "the" Det) (.lex "cat" N))
        (.fapp (.lex "eats" TV) (.lex "pizza" NP))

def john_sleeps : Derivation Atom S :=
  .bapp (.lex "John" NP) (.lex "sleeps" IV)

def john_sees_mary : Derivation Atom S :=
  .bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "Mary" NP))

/-! ### Non-constituent coordination -/

section Coordination

open Semantics.Montague Combinator

/-- The type-raised subject "John", `S/(S\NP)` — a lexical leaf, since type-raising
is morpholexical in the modern theory ([steedman-2019]; the book's syntactic `>T`
yields the same category). -/
def john_tr : Derivation Atom (S / (S \ NP)) := .lex "John" (S / (S \ NP))

/-- "John likes": the type-raised subject composed with the transitive verb — a
constituent of category `S/NP`. -/
def john_likes : Derivation Atom (S / NP) := .fcomp (by decide) john_tr (.lex "likes" TV)

def mary_tr : Derivation Atom (S / (S \ NP)) := .lex "Mary" (S / (S \ NP))
def mary_hates : Derivation Atom (S / NP) := .fcomp (by decide) mary_tr (.lex "hates" TV)

/-- The lexical conjunction category coordinating constituents of category `c`:
`(X \⋆ X) /⋆ X`, whose `star` slashes confine it to application ([steedman-2019]). -/
def conj (c : Cat Atom) : Cat Atom := (c \⋆ c) /⋆ c

/-- "John likes and Mary hates": coordination of two `S/NP` constituents via the
lexical conjunction — "and" is an ordinary leaf, not a rule. -/
def john_likes_and_mary_hates : Derivation Atom (S / NP) :=
  .bapp john_likes (.fapp (.lex "and" (conj (S / NP))) mary_hates)

def john_likes_and_mary_hates_beans : Derivation Atom S :=
  .fapp john_likes_and_mary_hates (.lex "beans" NP)

/-- The derivation spells out the full surface string, coordinator included. -/
theorem john_likes_and_mary_hates_beans_yield :
    john_likes_and_mary_hates_beans.yield
      = ["John", "likes", "and", "Mary", "hates", "beans"] := rfl

def john_sleeps_and_mary_sleeps : Derivation Atom S :=
  .bapp (.bapp (.lex "John" NP) (.lex "sleeps" IV))
    (.fapp (.lex "and" (conj S)) (.bapp (.lex "Mary" NP) (.lex "sleeps" IV)))

example : john_sleeps.opCount = 1 := rfl
example : john_sleeps_and_mary_sleeps.opCount = 4 := rfl
example : john_likes_and_mary_hates_beans.opCount = 5 := rfl

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
  | "John", .atom .NP => some ToyEntity.john
  | "Mary", .atom .NP => some ToyEntity.mary
  | "beans", .atom .NP => some ToyEntity.pizza
  -- morpholexically raised subjects ([steedman-2019]): `T` applied in the lexicon
  | "John", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (T ToyEntity.john)
  | "Mary", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (T ToyEntity.mary)
  | "sleeps", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.sleeps_sem
  | "laughs", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.laughs_sem
  | "sees", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.sees_sem
  | "eats", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.eats_sem
  | "likes", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.sees_sem
  | "hates", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.sees_sem
  -- sentential conjunction, a lexical entry
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (fun q p => p ∧ q)
  -- generalized conjunction at `S/NP` ([partee-rooth-1983]), a lexical entry
  | "and", .rslash (.lslash (.rslash (.atom .S) _ (.atom .NP)) _
        (.rslash (.atom .S) _ (.atom .NP))) _ (.rslash (.atom .S) _ (.atom .NP)) =>
      some (fun q p x => p x ∧ q x)
  | _, _ => none

theorem interp_john_sleeps :
    john_sleeps.interp toySemLexicon = some True := rfl

theorem interp_john_sees_mary :
    john_sees_mary.interp toySemLexicon = some True := rfl

example : (john_tr.interp toySemLexicon).isSome = true := rfl

/-- "John sees Mary" with a type-raised subject: the raised subject
`john_tr : S/(S\NP)` uses forward application, and the derivation
produces the same truth value as the canonical one. -/
def john_sees_mary_via_tr : Derivation Atom S :=
  .fapp john_tr (.fapp (.lex "sees" TV) (.lex "Mary" NP))

theorem interp_john_sees_mary_via_tr :
    john_sees_mary_via_tr.interp toySemLexicon = some True := rfl

example : (john_likes.interp toySemLexicon).isSome = true := rfl
example : (john_likes_and_mary_hates.interp toySemLexicon).isSome = true := rfl
example : (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome = true := rfl

/-- The predicate "John likes and Mary hates" (category `S/NP`) evaluated
at an entity. -/
def coordMeaningAt (e : ToyEntity) : Option Prop :=
  (john_likes_and_mary_hates.interp toySemLexicon).map (· e)

/-- The pointwise conjunction of "John likes" and "Mary hates" at an entity. -/
def pointwiseConjAt (e : ToyEntity) : Option Prop :=
  match john_likes.interp toySemLexicon, mary_hates.interp toySemLexicon with
  | some m₁, some m₂ => some (m₁ e ∧ m₂ e)
  | _, _ => none

/-- Generalized conjunction delivers the conjunctive interpretation:
⟦John likes and Mary hates⟧(e) = ⟦John likes⟧(e) ∧ ⟦Mary hates⟧(e). -/
theorem coordMeaningAt_eq_pointwiseConjAt :
    ∀ e : ToyEntity, coordMeaningAt e = pointwiseConjAt e := fun _ => rfl

/-- The truth conditions of "John likes and Mary hates beans" are the
conjunction of the two predications (in the toy model, likes = hates = sees). -/
theorem interp_john_likes_and_mary_hates_beans :
    john_likes_and_mary_hates_beans.interp toySemLexicon =
      some (ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.john ∧
            ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.mary) := rfl

/-- The spelled-out paraphrase "John likes beans and Mary hates beans". -/
def john_likes_beans_and_mary_hates_beans : Derivation Atom S :=
  .bapp (.bapp (.lex "John" NP) (.fapp (.lex "likes" TV) (.lex "beans" NP)))
    (.fapp (.lex "and" (conj S))
      (.bapp (.lex "Mary" NP) (.fapp (.lex "hates" TV) (.lex "beans" NP))))

/-- The non-constituent coordination and its spelled-out paraphrase receive
the same truth conditions — the book's claim that the composed derivation
yields the same predicate-argument structure as the canonical one. -/
theorem nonConstituentCoord_eq_spelledOut :
    john_likes_and_mary_hates_beans.interp toySemLexicon =
      john_likes_beans_and_mary_hates_beans.interp toySemLexicon := rfl

/-! ### The coordinator's `role` is truth-conditionally load-bearing

`interp` reads the coordinator's `role` off the `.coord` node — it no longer hardcodes
conjunction — so *which* coordinator a derivation uses is part of its truth conditions.
Using the actual English fragment coordinators, conjoining a true sentence `p` and a false
sentence `q` with `and_` (`role = .j`) gives `p ∧ q` (false), while `or_` (`role = .disj`)
gives `p ∨ q` (true). They differ, so the marking's `role` field is load-bearing — flipping
`English.Coordination.and_.role` to `.disj` would break the theorem below, rather than no
theorem depending on it. -/

/-- Minimal lexicon: sentence `p` is true, `q` is false. -/
private def pqLex : SemLexicon Unit Unit := fun w c =>
  match w, c with
  | "p", .atom .S => some True
  | "q", .atom .S => some False
  -- the coordinators' meanings are `Coordinator.op` of the English fragment's roles,
  -- instantiated at `Prop` — the marking's `role` selects the Boolean operation
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p => Coordinator.op English.Coordination.and_.role p q)
  | "or", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p => Coordinator.op English.Coordination.or_.role p q)
  | _, _ => none

private def dp : Derivation Atom S := .lex "p" S
private def dq : Derivation Atom S := .lex "q" S

/-- The coordinator's `role` flips the truth conditions: English `and_` yields `p ∧ q`,
    `or_` yields `p ∨ q`, and these differ at `p = ⊤`, `q = ⊥`. Flipping a fragment
    coordinator's `role` collapses the inequality, so the `role` marking is not decorative. -/
theorem coord_role_load_bearing :
    (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex ≠
    (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex := by
  have hand : (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex
      = some (True ∧ False) := rfl
  have hor : (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex
      = some (True ∨ False) := rfl
  rw [hand, hor, ne_eq, Option.some.injEq, eq_iff_iff]
  exact fun h => (h.mpr (Or.inl trivial)).2

end Coordination

/-! ### Gapping

[ross-1970]'s generalization — gapping direction tracks word order —
which [steedman-2000] derives from the Principles of Adjacency,
Consistency, and Inheritance together with the order-preserving constraint
on type-raising. The constituency half is derived below — the gapped conjunct is a
typechecked derivation (`gappedConjunct`); deriving the `predictedGappingPattern`
table itself from per-order verb categories is TODO.
(Dutch licensing both directions is `mixed_allows_both`.) -/

section Gapping

/-- The gapped conjunct "Warren, potatoes" is a constituent ([steedman-2000] ch. 7):
backward type-raising both remnants and backward-composing them yields
`S\((S/NP)/NP)` — a leftward-looking function over VSO-style transitive verbs, which
is why forward gapping leaves the verb to the left. Deriving it is typechecking. -/
def gappedConjunct : Derivation Atom (S \ ((S / NP) / NP)) :=
  .bcomp (by decide) (.lex "Warren" ((S / NP) \ ((S / NP) / NP)))
    (.lex "potatoes" (S \ (S / NP)))

theorem gappedConjunct_yield : gappedConjunct.yield = ["Warren", "potatoes"] := rfl

/-- The mirror cluster for backward gapping (Japanese "Ken-ga Naomi-o"): forward
type-raising and forward composition yield `S/((S\NP)\NP)`, a rightward-looking
function over SOV transitive verbs — the verb must follow. -/
def backwardGappedConjunct : Derivation Atom (S / ((S \ NP) \ NP)) :=
  .fcomp (by decide) (.lex "Ken-ga" (S / (S \ NP)))
    (.lex "Naomi-o" ((S \ NP) / ((S \ NP) \ NP)))

theorem backwardGappedConjunct_yield :
    backwardGappedConjunct.yield = ["Ken-ga", "Naomi-o"] := rfl

/-- Stripping ("Dexter ran away, and Warren (too)") is the single-remnant case: one
backward-raised subject, `S\(S/NP)`. -/
def strippedConjunct : Derivation Atom (S \ (S / NP)) :=
  .lex "Warren" (S \ (S / NP))

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

Dutch verb clusters ([bresnan-etal-1982]) with cross-serial NP-verb bindings, over a
target-restricted grammar (`dutchGrammar`: every rule fires at primary target `S`).
Two constructions are given as `Derives` facts — the relation carries category and
string at once. The *verb-raising* derivations (rightward `/NP` slots, harmonic
`B`/`B²`) encode the cross-serial binding pattern at a non-Dutch string (see
`jan_zag_zwemmen_piet_derives`); the *surface-faithful* derivations (leftward `\NP`
slots, forward crossed composition, following the book's own Dutch fragment — ch. 6;
appendix summary) derive the attested "Jan Piet (Marie) zag (helpen) zwemmen". -/

section CrossSerial

open BresnanEtAl1982
open Features (VerbClusterBinding)

/-! ### Categories for Dutch verb clusters -/

/-- Verb phrase (infinitival). -/
def VP : Cat Atom := S \ NP

/-- Perception verb: `(S\NP)/(S\NP)` (e.g. "zag" = saw). -/
def PercV : Cat Atom := (S \ NP) / VP

/-- Infinitival verb needing its (raised) subject: `(S\NP)/NP`. In Dutch verb-raising the
infinitive's subject surfaces in an object-like position, picked up via composition. -/
def InfSubj : Cat Atom := (S \ NP) / NP

/-- Verb-raising control verb `((S\NP)/NP)/(S\NP)`: each restructuring verb provides an
extra `/NP` slot for its own raised subject, in addition to its VP complement. This is
what threads multiple argument slots through a 3+-verb cluster:
- `zwemmen : (S\NP)/NP`           — base: needs subject
- `helpen  : ((S\NP)/NP)/(S\NP)`  — VR: needs complement, passes an `/NP`
- `zag     : (S\NP)/(S\NP)`       — matrix: standard perception verb -/
def ControlVR : Cat Atom := ((S \ NP) / NP) / (S \ NP)

/-- Subordinate-clause perception verb `((S\NP)\NP)/VP`: infinitival
complement to the right, object and subject NPs to the left (book:
`zag := ((S₊SUB\NP)\NP)/VP₋SUB`; the toy `Cat` drops the features).
`Sub` = subordinate-clause head — contrast `InfSubj`, whose `/NP` is a
raised-subject slot. -/
def PercVSub : Cat Atom := ((S \ NP) \ NP) / VP

/-- Infinitival head with a raised object, `(VP\NP)/VP` (book:
`zien := (VP\NP)/VP₋SUB`). -/
def InfHeadSub : Cat Atom := (VP \ NP) / VP

/-- The Dutch fragment as a target-restricted grammar: the lexical entries the
derivations below draw on, target and start `S`, degree bound 2. -/
def dutchGrammar : Grammar Atom :=
  .targetRestricted
    [("Jan", NP), ("Piet", NP), ("Marie", NP),
     ("zag", PercV), ("zag", PercVSub),
     ("helpen", ControlVR), ("helpen", InfHeadSub),
     ("zwemmen", VP), ("zwemmen", InfSubj)]
    .S 2

/-! ### Lexical entries, as derivability facts -/

theorem jan_derives : dutchGrammar.Derives NP ["Jan"] := .lex (by decide)
theorem piet_derives : dutchGrammar.Derives NP ["Piet"] := .lex (by decide)
theorem marie_derives : dutchGrammar.Derives NP ["Marie"] := .lex (by decide)
theorem zag_vr_derives : dutchGrammar.Derives PercV ["zag"] := .lex (by decide)
theorem zwemmen_vr_derives : dutchGrammar.Derives InfSubj ["zwemmen"] := .lex (by decide)
theorem helpen_vr_derives : dutchGrammar.Derives ControlVR ["helpen"] := .lex (by decide)
theorem zag_sub_derives : dutchGrammar.Derives PercVSub ["zag"] := .lex (by decide)
theorem helpen_sub_derives : dutchGrammar.Derives InfHeadSub ["helpen"] := .lex (by decide)
theorem zwemmen_bare_derives : dutchGrammar.Derives VP ["zwemmen"] := .lex (by decide)

/-! ### Verb-raising derivations

`B`/`B²` thread the raised argument slots through the cluster — the cross-serial
*binding* pattern — but the rightward `/NP` slots spell the arguments out after the
cluster, so the derived strings do **not** match Dutch surface order. -/

/-- `zag >B² (helpen >B zwemmen)`: the cluster is a 3-place predicate
`((S\NP)/NP)/NP` wanting Jan (`\NP`), Piet (`/NP`) and Marie (`/NP`). -/
theorem verb_cluster_derives :
    dutchGrammar.Derives (((S \ NP) / NP) / NP) ["zag", "helpen", "zwemmen"] :=
  .fc 2 zag_vr_derives
    (.fc 1 helpen_vr_derives zwemmen_vr_derives ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- The 2-verb verb-raising derivation derives `S` — at the string
"Jan zag zwemmen Piet", which is **not** Dutch ("Jan Piet zag zwemmen"): the
verb-raising categories capture the binding but not the linear order. The
surface-faithful derivations below get both. -/
theorem jan_zag_zwemmen_piet_derives :
    dutchGrammar.Derives S ["Jan", "zag", "zwemmen", "Piet"] :=
  .bc 0 jan_derives
    (.fc 0 (.fc 1 zag_vr_derives zwemmen_vr_derives ⟨by decide, rfl⟩ rfl)
      piet_derives ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-! ### Surface-faithful derivations (leftward argument categories)

[steedman-2000]'s own analysis (ch. 6; appendix summary of the Dutch fragment) gives
subordinate-clause cluster verbs *leftward* NP slots and composes the cluster by
forward **crossed** composition, so the NPs precede the whole cluster and the derived
strings are the attested "Jan Piet (Marie) zag (helpen) zwemmen". -/

/-- The crossed cluster `zag >B× (helpen zwemmen)` is a leftward-seeking 3-place
predicate. -/
theorem crossed_cluster_derives :
    dutchGrammar.Derives (((S \ NP) \ NP) \ NP) ["zag", "helpen", "zwemmen"] :=
  .fc 1 zag_sub_derives
    (.fc 0 helpen_sub_derives zwemmen_bare_derives ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- "(dat) Jan Piet zag zwemmen": `zag` applies to bare `zwemmen` and the NPs attach
leftward — the 2-verb cluster needs no composition, and the string is the attested
order (contrast `jan_zag_zwemmen_piet_derives`). -/
theorem two_np_sub_derives :
    dutchGrammar.Derives S ["Jan", "Piet", "zag", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives
      (.fc 0 zag_sub_derives zwemmen_bare_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- "(dat) Jan Piet Marie zag helpen zwemmen": the three NPs attach leftward to the
crossed cluster — Marie to `helpen`'s slot, Piet to `zag`'s object slot, Jan as
subject: the cross-serial binding falls out of the category threading, in the
attested word order. -/
theorem three_np_sub_derives :
    dutchGrammar.Derives S ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives
      (.bc 0 marie_derives crossed_cluster_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-! ### Binding annotations -/

/-- A derived Dutch string annotated with which NP binds to which verb; carrying the
derivability fact ties the words to the grammar. TODO: compute `binding` from a
derivation's composition structure instead of annotating it by hand. -/
structure AnnotatedDerivation where
  /-- Number of NP-verb pairs -/
  n : Nat
  /-- Surface words -/
  words : List String
  /-- The NP-verb binding permutation -/
  binding : Features.VerbClusterBinding n
  /-- The grammar derives the words at `S`. -/
  derives : dutchGrammar.Derives S words

/-- "Jan Piet zag zwemmen" with cross-serial bindings: Jan is the subject
of "zag", Piet the argument bound into the cluster. -/
def dutch_jan_piet_zag_zwemmen : AnnotatedDerivation :=
  { n := 2
  , words := ["Jan", "Piet", "zag", "zwemmen"]
  , binding := VerbClusterBinding.identity 2
  , derives := two_np_sub_derives
  }

/-- "Jan Piet Marie zag helpen zwemmen", the cross-serial binding pattern in the
attested word order. -/
def dutch_jan_piet_marie_zag_helpen_zwemmen : AnnotatedDerivation :=
  { n := 3
  , words := ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"]
  , binding := VerbClusterBinding.identity 3
  , derives := three_np_sub_derives
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
intrinsically typed `Derivation` trees: the verb-raising cluster forms by
forward crossed composition (`.fcompx`), the
verb-projection-raising order by plain application — the composed-cluster
vs. applied-cluster contrast driving the account. (The toy `Cat` still
drops the book's features, e.g. the `VP₋SUB` restriction on `>B×`.) -/

section Quantification

open ScopeTheory Data.Examples

/-- Word order in a West Germanic verb cluster ([steedman-2000] §6.8). -/
inductive VerbOrder where
  /-- Object precedes the whole verb cluster: NP … V_emb V_matrix. -/
  | verbRaising
  /-- Object follows the matrix verb: V_matrix … NP V_emb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

/-- Verb-raising order, Dutch (99a): the cluster *probeert te zingen*
forms by crossed composition before taking the object to its left. -/
def verbRaisingDeriv : Derivation Atom IV :=
  .bapp (.lex "veel liederen" NP)
    (.fcompx (by decide) (.lex "probeert" (IV / IV)) (.lex "te zingen" (IV \ NP)))

/-- Verb-projection-raising order, Dutch (99b): the matrix verb applies to
an already-saturated embedded VP, so the quantified object never combines
with a function containing the tensed verb. -/
def verbProjectionRaisingDeriv : Derivation Atom IV :=
  .fapp (.lex "probeert" (IV / IV))
    (.bapp (.lex "veel liederen" NP) (.lex "te zingen" (IV \ NP)))

/-- The CCG derivation shape each verb order forces. -/
def schematicDeriv : VerbOrder → Derivation Atom IV
  | .verbRaising => verbRaisingDeriv
  | .verbProjectionRaising => verbProjectionRaisingDeriv

theorem verbRaisingDeriv_hasComp : verbRaisingDeriv.HasComp := by decide

theorem verbProjectionRaisingDeriv_applicationOnly :
    ¬verbProjectionRaisingDeriv.HasComp := by decide

/-- Scope availability as CCG predicts it — the account's linking hypothesis: a
cluster built with composition or type-raising is scope-ambiguous, an
application-only cluster surface-only. [steedman-2000] notes this overgenerates as
stated (§4.4 refines it). -/
def predictedAvailability (vo : VerbOrder) : BinaryScopeAvailability :=
  if (schematicDeriv vo).HasComp then .ambiguous else .surfaceOnly

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
example : Examples.all.all (λ ex =>
    (ex.paperFeatures.lookup "phenomenon" == some "gapping") ||
    ((wordOrderOf ex).isSome && (observedAvailability ex).isSome)) = true := by decide

/-- The CCG prediction matches every §6.8 judgment. -/
theorem predictedAvailability_eq_observed :
    ∀ d ∈ scopeData, predictedAvailability d.1 = d.2 := by
  decide

end Quantification

/-! ### Intonation and information structure

The book's ch. 5 story: alternative derivations of one string are alternative
information structures, disambiguated by tune. "(ANNA married)(MANNY)" carves the
composed derivation into an L+H* LH% theme and an H* LL% rheme; prosodic phrases are
tune-marked constituents, so only CCG constituents can be phrases (the Sense Unit
Condition, [selkirk-1984]; [steedman-2000] ch. 2). -/

section Intonation

open CCG.Intonation Features.Prosody

/-- Accents for "(ANNA married)(MANNY)": theme accent on "Anna", rheme accent on
"Manny", "married" unaccented. -/
def annaMannyAccents : AccentAssignment := fun w =>
  match w with
  | "Anna" => .L_plus_H_star
  | "Manny" => .H_star
  | _ => .null

/-- "ANNA married": the composed theme constituent, category `S/NP`. -/
def anna_married : Derivation Atom (S / NP) :=
  .fcomp (by decide) (.lex "Anna" (S / (S \ NP))) (.lex "married" TV)

/-- The theme constituent projects `θ`: the theme accent on "Anna" unifies with
unaccented "married". -/
theorem anna_married_theme :
    anna_married.infoFeature annaMannyAccents = some .θ := rfl

/-- The rheme "MANNY" projects `ρ`. -/
theorem manny_rheme :
    (Derivation.lex "Manny" NP).infoFeature annaMannyAccents = some .ρ := rfl

/-- Folding the rheme into the theme's constituent clashes: with these accents the
whole sentence projects no coherent single marking, so the tune forces the
[Anna married][Manny] phrasing — intonation disambiguates the derivational
ambiguity. -/
theorem theme_rheme_clash :
    (Derivation.fapp anna_married (.lex "Manny" NP)).infoFeature annaMannyAccents
      = none := rfl

/-- The utterance as two tune-marked phrases. -/
def annaMannyUtterance : List ProsodicPhrase :=
  [⟨_, anna_married, themeTune⟩, ⟨_, .lex "Manny" NP, rhemeTune⟩]

/-- The extracted information structure: the theme is the `S/NP` constituent
"ANNA married", the rheme is "MANNY". -/
theorem annaMannyUtterance_infoStructure :
    (extractInfoStructure annaMannyUtterance).map (fun i => (i.theme.map (·.cat), i.rheme.cat))
      = some (some (S / NP), NP) := rfl

end Intonation

/-! ### Truth-conditional pipeline

The complete CCG → Montague pipeline over the toy fragment: derivations
interpreted compositionally, each checked against the toy model. -/

section TruthConditions

open CCG
open Semantics.Montague

-- CCG Derivations for Test Sentences ("John sleeps" and "John sees Mary"
-- are the file-level derivations above)

/-- "Mary sleeps" - backward application -/
def ccg_mary_sleeps : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.lex "sleeps" IV)

/-- "John laughs" - backward application -/
def ccg_john_laughs : Derivation Atom S :=
  .bapp (.lex "John" NP) (.lex "laughs" IV)

/-- "Mary laughs" - backward application -/
def ccg_mary_laughs : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.lex "laughs" IV)

/-- "Mary sees John" - forward then backward application -/
def ccg_mary_sees_john : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.fapp (.lex "sees" TV) (.lex "John" NP))

/-- "John eats pizza" - forward then backward application -/
def ccg_john_eats_pizza : Derivation Atom S :=
  .bapp (.lex "John" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))

-- Extended Semantic Lexicon (matching the toy model)

/-- Extended lexicon with all entities and predicates -/
def extendedLexicon : SemLexicon ToyEntity Unit := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ToyEntity.john
  | "Mary", .atom .NP => some ToyEntity.mary
  | "pizza", .atom .NP => some ToyEntity.pizza
  | "book", .atom .NP => some ToyEntity.book
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.sleeps_sem
  | "laughs", .lslash (.atom .S) _ (.atom .NP) => some ToyLexicon.laughs_sem
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.sees_sem
  | "eats", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.eats_sem
  | "reads", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some ToyLexicon.reads_sem
  | _, _ => none

/-- Get meaning (as Prop) from CCG derivation -/
def ccgMeaning (d : Derivation Atom S) : Option Prop :=
  d.interp extendedLexicon

-- Pipeline Theorems: CCG Derives Correct Truth Conditions

/-- CCG correctly predicts "John sleeps" is true -/
theorem ccg_predicts_john_sleeps :
    ccgMeaning john_sleeps = some True := rfl

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
    ccgMeaning john_sees_mary = some True := rfl

/-- CCG correctly predicts "Mary sees John" is true -/
theorem ccg_predicts_mary_sees_john :
    ccgMeaning ccg_mary_sees_john = some True := rfl

end TruthConditions

end Steedman2000
