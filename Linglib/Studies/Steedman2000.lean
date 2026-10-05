module

public import Linglib.Data.Examples.Steedman2000
public import Linglib.Semantics.Composition.Toy
public import Linglib.Fragments.English.Coordination
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Syntax.CCG.Derivation
public import Linglib.Syntax.CCG.Grammar
public import Linglib.Syntax.CCG.Interface
public import Linglib.Syntax.CCG.Intonation
public import Linglib.Studies.BeckmanPierrehumbert1986

/-!
# Steedman (2000): The Syntactic Process

In Steedman's combinatory categorial grammar the slash directions of lexical categories fix
word order, and composition and type-raising make strings such as a subject and a
transitive verb into constituents. This file derives the book's analyses of non-constituent
coordination, gapping, Dutch cross-serial dependencies, scope in verb clusters and
intonational phrasing over the library's CCG, and interprets the derivations over a toy
English model.

## Main results

* `nonConstituentCoord_eq_spelledOut`: "John sees and Mary eats pizza" has the truth
  conditions of its spelled-out paraphrase.
* `coord_role_load_bearing`: the coordinator's role, not a rule of the grammar, fixes the
  Boolean operation of a coordination.
* `cluster_sov`, `cluster_vso`, `cluster_svo`: the arguments of a verb-final verb form a
  rightward-looking cluster, those of a verb-initial verb a leftward-looking one, and those
  of a verb-medial verb none, so verb-final languages gap backward and verb-initial ones
  forward, Ross's generalization.
* `english_gap`: English gaps forward, since the revealing rule exposes a virtual
  verb-initial verb whose cluster is the gapped conjunct.
* `dutch_main_cluster`, `dutch_sub_cluster`: Dutch main clauses gap forward and subordinate
  clauses backward.
* `three_np_sub_derives`: forward crossed composition derives the Dutch cross-serial order.
* `inverse_acceptable_iff_hasComp`: in the book's examples an inverse scope reading is
  acceptable exactly when the verb cluster is built by composition.
* `theme_rheme_clash`, `annaMannyUtterance_infoStructure`: a theme accent and a rheme accent
  do not unify, so the tune forces the phrasing "(ANNA married)(MANNY)".

## Implementation notes

Type-raising is lexical in the library's CCG, so the book's syntactic raising rule appears as
raised lexical entries. A raised name denotes the book's type-raising combinator `T` applied
to the name, which at result category `S` is the Montague lift `Quantifier.NP.individual`,
and coordination at `S/NP` is Partee and Rooth's generalized conjunction. The order-preserving
raising of an argument is computed at the plain modality. The toy `Cat` drops the book's
features (subordination, antecedent government, agreement), so the Dutch fragment carries
only the categories its derivations use, and the restriction of forward crossed composition
to bare infinitival complements is not encoded. The book's tunes follow Pierrehumbert's
decomposition of an intonation phrase into pitch accent, phrase accent and boundary tone,
which Beckman and Pierrehumbert supply (`ipToTune`).

## References

* [steedman-2000]
* [ross-1970]
* [bresnan-etal-1982]
* [bayer-1996]
* [kayne-1998]
* [haegeman-van-riemsdijk-1986]
* [haegeman-1992]
* [selkirk-1984]
* [partee-rooth-1983]
* [beckman-pierrehumbert-1986]
-/

@[expose] public section

namespace Steedman2000

open CCG

/-! ### Word order

Slash direction encodes word order: `TV = (S\NP)/NP` looks right for the object and the
resulting `S\NP` left for the subject, which enforces SVO. -/

def mary_eats_pizza : Derivation Atom S :=
  .bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))

def john_sleeps : Derivation Atom S :=
  .bapp (.lex "John" NP) (.lex "sleeps" IV)

def john_sees_mary : Derivation Atom S :=
  .bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "Mary" NP))

/-! ### Non-constituent coordination -/

section Coordination

open HeimKratzer

/-- The type-raised subject "John" is a lexical leaf of category `S/(S\NP)`. -/
def john_tr : Derivation Atom (S / (S \ NP)) := .lex "John" (S / (S \ NP))

def mary_tr : Derivation Atom (S / (S \ NP)) := .lex "Mary" (S / (S \ NP))

/-- "John sees" is the type-raised subject composed with the transitive verb, a constituent of
category `S/NP`. -/
def john_sees : Derivation Atom (S / NP) := .fcomp (by decide) john_tr (.lex "sees" TV)

def mary_eats : Derivation Atom (S / NP) := .fcomp (by decide) mary_tr (.lex "eats" TV)

/-- `conj c` is the category `(c \⋆ c) /⋆ c` of a conjunction coordinating constituents of
category `c`. Its `star` slashes confine it to application. -/
def conj (c : Cat Atom) : Cat Atom := (c \⋆ c) /⋆ c

/-- "John sees and Mary eats" coordinates two `S/NP` constituents through the lexical
conjunction, as in the book's "Anna married, and I detest". -/
def john_sees_and_mary_eats : Derivation Atom (S / NP) :=
  .bapp john_sees (.fapp (.lex "and" (conj (S / NP))) mary_eats)

def john_sees_and_mary_eats_pizza : Derivation Atom S :=
  .fapp john_sees_and_mary_eats (.lex "pizza" NP)

/-- The derivation spells out the full surface string, coordinator included. -/
theorem john_sees_and_mary_eats_pizza_yield :
    john_sees_and_mary_eats_pizza.yield = ["John", "sees", "and", "Mary", "eats", "pizza"] :=
  rfl

/-- `semLexicon` interprets the toy English fragment. It gives meanings to names, type-raised
names, verbs, and conjunctions at `S` and at `S/NP`. -/
def semLexicon : SemLexicon ToyEntity Unit := fun word cat ↦
  match word, cat with
  | "John", .atom .NP => some ToyEntity.john
  | "Mary", .atom .NP => some ToyEntity.mary
  | "pizza", .atom .NP => some ToyEntity.pizza
  | "book", .atom .NP => some ToyEntity.book
  | "John", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (Quantifier.NP.individual ToyEntity.john)
  | "Mary", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (Quantifier.NP.individual ToyEntity.mary)
  | "sleeps", .lslash (.atom .S) _ (.atom .NP) => some Toy.sleeps
  | "laughs", .lslash (.atom .S) _ (.atom .NP) => some Toy.laughs
  | "sees", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.sees
  | "eats", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.eats
  | "reads", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.reads
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (fun q p ↦ p ∧ q)
  | "and", .rslash (.lslash (.rslash (.atom .S) _ (.atom .NP)) _
        (.rslash (.atom .S) _ (.atom .NP))) _ (.rslash (.atom .S) _ (.atom .NP)) =>
      some (fun q p x ↦ p x ∧ q x)
  | _, _ => none

/-- "John sees Mary" with a type-raised subject produces the same truth value as the
canonical derivation. -/
def john_sees_mary_via_tr : Derivation Atom S :=
  .fapp john_tr (.fapp (.lex "sees" TV) (.lex "Mary" NP))

theorem interp_john_sees_mary_via_tr :
    john_sees_mary_via_tr.interp semLexicon = john_sees_mary.interp semLexicon := rfl

/-- At each entity the coordinated `S/NP` predicate is the conjunction of the two conjoined
predicates. -/
theorem coord_interp_pointwise (e : ToyEntity) :
    (john_sees_and_mary_eats.interp semLexicon).map (· e) =
      (match john_sees.interp semLexicon, mary_eats.interp semLexicon with
        | some m₁, some m₂ => some (m₁ e ∧ m₂ e)
        | _, _ => none) := rfl

/-- The spelled-out paraphrase is "John sees pizza and Mary eats pizza". -/
def john_sees_pizza_and_mary_eats_pizza : Derivation Atom S :=
  .bapp (.bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "pizza" NP)))
    (.fapp (.lex "and" (conj S))
      (.bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))))

/-- The non-constituent coordination and its spelled-out paraphrase receive the same truth
conditions, since the composed derivation yields the canonical predicate-argument
structure. -/
theorem nonConstituentCoord_eq_spelledOut :
    john_sees_and_mary_eats_pizza.interp semLexicon =
      john_sees_pizza_and_mary_eats_pizza.interp semLexicon := rfl

/-- A lexicon in which sentence `p` is true and `q` false, with the English coordinators
interpreted by the Boolean operation of their role. -/
def pqLex : SemLexicon Unit Unit := fun w c ↦
  match w, c with
  | "p", .atom .S => some True
  | "q", .atom .S => some False
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p ↦ English.Coordination.and_.denote {p, q})
  | "or", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p ↦ English.Coordination.or_.denote {p, q})
  | _, _ => none

def dp : Derivation Atom S := .lex "p" S
def dq : Derivation Atom S := .lex "q" S

/-- With a true and a false conjunct, coordination by `and` and by `or` receive different
truth values, so the coordinator is part of a derivation's truth conditions. -/
theorem coord_role_load_bearing :
    (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex ≠
    (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex := by
  have hand : (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex
      = some (True ∧ False) := congrArg some (sInf_pair (a := True) (b := False))
  have hor : (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex
      = some (True ∨ False) := congrArg some (sSup_pair (a := True) (b := False))
  rw [hand, hor, ne_eq, Option.some.injEq, eq_iff_iff]
  exact fun h ↦ (h.mpr (Or.inl trivial)).2

end Coordination

/-! ### Gapping -/

section Gapping

/-- `raiseArg c` raises the argument of the function category `c` order-preservingly over
`c`. The argument of `X\A` raises to `X/(X\A)` and that of `X/A` to `X\(X/A)`. -/
def raiseArg : Cat Atom → Option (Cat Atom)
  | .lslash x _ a => some (Cat.forwardTypeRaise a x)
  | .rslash x _ a => some (Cat.backwardTypeRaise a x)
  | .atom _ => none

/-- `hcomp` is harmonic composition, the order-preserving rules `>B` and `<B`. -/
def hcomp : Cat Atom → Cat Atom → Option (Cat Atom)
  | .rslash x _ y, .rslash y' n z => if y = y' then some (.rslash x n z) else none
  | .lslash y' n z, .lslash x _ y => if y = y' then some (.lslash x n z) else none
  | _, _ => none

/-- `cluster v` is the category of the argument cluster over the transitive verb category
`v`. The verb's two arguments are raised over the functions that seek them and composed
harmonically, in whichever order the rules allow. -/
def cluster (v : Cat Atom) : Option (Cat Atom) :=
  match v with
  | .lslash inner _ _ | .rslash inner _ _ => do
      let r₁ ← raiseArg inner
      let r₂ ← raiseArg v
      hcomp r₁ r₂ <|> hcomp r₂ r₁
  | .atom _ => none

/-- A Japanese transitive verb is verb-final, of category `(S\NP)\NP`. -/
def japaneseTV : Cat Atom := (S \ NP) \ NP

/-- An Irish transitive verb is verb-initial, of category `(S/NP)/NP`. -/
def irishTV : Cat Atom := (S / NP) / NP

/-- Over a verb-final verb the cluster looks rightward for the verb, since the arguments
raise and compose forward. The verb therefore follows the coordinated clusters, which is
backward gapping (the book's chapter 7 (4)). -/
theorem cluster_sov : cluster japaneseTV = some (S / japaneseTV) := by decide

/-- Over a verb-initial verb the cluster looks leftward, so the verb precedes the clusters,
forward gapping (chapter 7 (19)). -/
theorem cluster_vso : cluster irishTV = some (S \ irishTV) := by decide

/-- A verb-medial verb has no cluster, since its arguments raise in opposite directions and no
harmonic rule composes them. -/
theorem cluster_svo : cluster TV = none := by decide

/-- The backward-gapped conjunct "Ken-ga Naomi-o" is derived by forward raising and forward
composition. -/
def backwardGappedConjunct : Derivation Atom (S / japaneseTV) :=
  .fcomp (by decide) (.lex "Ken-ga" (S / (S \ NP)))
    (.lex "Naomi-o" ((S \ NP) / japaneseTV))

theorem backwardGappedConjunct_yield :
    backwardGappedConjunct.yield = ["Ken-ga", "Naomi-o"] := rfl

/-- The forward-gapped conjunct "Warren, potatoes" is derived by backward raising and backward
composition over a verb-initial verb. -/
def gappedConjunct : Derivation Atom (S \ irishTV) :=
  .bcomp (by decide) (.lex "Warren" ((S / NP) \ irishTV)) (.lex "potatoes" (S \ (S / NP)))

theorem gappedConjunct_yield : gappedConjunct.yield = ["Warren", "potatoes"] := rfl

/-- `RightwardInto t c` holds when `c` is a rightward function into `t`, the book's `t/$`. -/
def RightwardInto (t : Cat Atom) : Cat Atom → Prop
  | .rslash x _ _ => RightwardInto t x
  | .lslash x m y => Cat.lslash x m y = t
  | .atom a => Cat.atom a = t

/-- `RightwardInto t` is decided by recursion on the category. -/
def RightwardInto.decidable (t : Cat Atom) : ∀ c, Decidable (RightwardInto t c)
  | .rslash x _ _ => RightwardInto.decidable t x
  | .lslash x m y => inferInstanceAs (Decidable (Cat.lslash x m y = t))
  | .atom a => inferInstanceAs (Decidable (Cat.atom a = t))

instance (t : Cat Atom) : DecidablePred (RightwardInto t) := RightwardInto.decidable t

/-- `reveal x y` is the virtual-conjunct revealing rule of chapter 7 (61). It decomposes a
left conjunct of category `x` into a rightward function `y` into `S` and the residue `x \ y`,
so the residue looks leftward whatever `y` is. -/
def reveal (x y : Cat Atom) : Cat Atom × Cat Atom := (y, x \ y)

/-- In English gapping (chapter 7 (62)) the left conjunct reveals a virtual verb-initial verb
and a residue that is the cluster over it, with which the gapped right conjunct coordinates.
No verb-final verb can be revealed, so English gaps forward only. -/
theorem english_gap :
    RightwardInto S irishTV ∧ (reveal S irishTV).2 = (S \ irishTV) ∧
      cluster irishTV = some (S \ irishTV) ∧ ¬ RightwardInto S japaneseTV := by
  decide

/-- Dutch main-clause transitive verbs take both arguments rightward, so main clauses gap
forward (chapter 7 (21)). -/
theorem dutch_main_cluster : cluster ((S / NP) / NP) = some (S \ ((S / NP) / NP)) := by
  decide

/-- Dutch subordinate-clause transitive verbs take both arguments leftward, so subordinate
clauses gap backward (chapter 7 (11)). -/
theorem dutch_sub_cluster : cluster ((S \ NP) \ NP) = some (S / ((S \ NP) \ NP)) := by
  decide

/-- A stripped conjunct is a single remnant, one backward-raised subject of category
`S\(S/NP)`. -/
def strippedConjunct : Derivation Atom (S \ (S / NP)) := .lex "Warren" (S \ (S / NP))

/-- `EllipsisType` enumerates the book's elliptical constructions. -/
inductive EllipsisType
  /-- "Dexter ate bread, and Warren, potatoes" -/
  | gapping
  /-- "Dexter ran away, and Warren (too)" -/
  | stripping
  /-- "Dexter ate bread, and Warren did too" -/
  | vpEllipsis
  /-- "Dexter did something, but I don't know what" -/
  | sluicing
  deriving DecidableEq, Repr

/-- Gapping and stripping are mediated by the combinatory syntax, and VP ellipsis and
sluicing by a separate anaphoric mechanism, since their categories are not otherwise in the
grammar. -/
def SyntacticallyMediated : EllipsisType → Prop
  | .gapping | .stripping => True
  | .vpEllipsis | .sluicing => False

instance : DecidablePred SyntacticallyMediated := fun x ↦ by
  cases x <;> unfold SyntacticallyMediated <;> infer_instance

end Gapping

/-! ### Cross-serial dependencies

Dutch verb clusters ([bresnan-etal-1982]) over a target-restricted grammar: subordinate-clause
verbs take NP arguments leftward and infinitival complements rightward, and the cluster forms
by forward crossed composition, so the NPs precede the whole cluster in the attested order
"Jan Piet (Marie) zag (helpen) zwemmen". -/

section CrossSerial

/-- An infinitival verb phrase has category `S\NP`. -/
def VP : Cat Atom := S \ NP

/-- A subordinate-clause perception verb has category `((S\NP)\NP)/VP`, taking its
infinitival complement to the right and its object and subject to the left. -/
def PercVSub : Cat Atom := ((S \ NP) \ NP) / VP

/-- An infinitival head with a raised object has category `(VP\NP)/VP`. -/
def InfHeadSub : Cat Atom := (VP \ NP) / VP

/-- `dutchGrammar` is the Dutch fragment as a target-restricted grammar with target `S` and
degree bound 2. -/
def dutchGrammar : Grammar Atom :=
  .targetRestricted
    [("Jan", NP), ("Piet", NP), ("Marie", NP), ("zag", PercVSub), ("helpen", InfHeadSub),
     ("zwemmen", VP)]
    .S 2

theorem jan_derives : dutchGrammar.Derives NP ["Jan"] := .lex (by decide)
theorem piet_derives : dutchGrammar.Derives NP ["Piet"] := .lex (by decide)
theorem marie_derives : dutchGrammar.Derives NP ["Marie"] := .lex (by decide)
theorem zag_derives : dutchGrammar.Derives PercVSub ["zag"] := .lex (by decide)
theorem helpen_derives : dutchGrammar.Derives InfHeadSub ["helpen"] := .lex (by decide)
theorem zwemmen_derives : dutchGrammar.Derives VP ["zwemmen"] := .lex (by decide)

/-- The crossed cluster "zag helpen zwemmen" is a leftward-seeking three-place predicate. -/
theorem crossed_cluster_derives :
    dutchGrammar.Derives (((S \ NP) \ NP) \ NP) ["zag", "helpen", "zwemmen"] :=
  .fc 1 zag_derives (.fc 0 helpen_derives zwemmen_derives ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- In "(dat) Jan Piet zag zwemmen" the two-verb cluster needs no composition and the NPs
attach leftward. -/
theorem two_np_sub_derives : dutchGrammar.Derives S ["Jan", "Piet", "zag", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives (.fc 0 zag_derives zwemmen_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

/-- In "(dat) Jan Piet Marie zag helpen zwemmen" the three NPs attach leftward to the crossed
cluster, Marie to the slot of "helpen", Piet to the object slot of "zag", Jan as subject, the
cross-serial binding in the attested order. -/
theorem three_np_sub_derives :
    dutchGrammar.Derives S ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"] :=
  .bc 0 jan_derives
    (.bc 0 piet_derives (.bc 0 marie_derives crossed_cluster_derives ⟨by decide, rfl⟩ rfl)
      ⟨by decide, rfl⟩ rfl)
    ⟨by decide, rfl⟩ rfl

end CrossSerial

/-! ### Verb clusters and quantifier scope

In the verb-raising order the cluster forms by composition, so a quantified argument combines
with a function containing the tensed verb and can take scope over it; in the
verb-projection-raising order it combines with the embedded verb alone. -/

section Quantification


/-- `VerbOrder` is the word order of a West Germanic verb cluster. -/
inductive VerbOrder
  /-- The object precedes the whole verb cluster. -/
  | verbRaising
  /-- The object follows the matrix verb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

/-- In the Dutch verb-raising order (99a) the cluster "probeert te zingen" forms by crossed
composition before taking the object to its left. -/
def verbRaisingDeriv : Derivation Atom IV :=
  .bapp (.lex "veel liederen" NP)
    (.fcompx (by decide) (.lex "probeert" (IV / IV)) (.lex "te zingen" (IV \ NP)))

/-- In the Dutch verb-projection-raising order (99b) the matrix verb applies to a saturated
embedded VP, so the quantified object never combines with a function containing the tensed
verb. -/
def verbProjectionRaisingDeriv : Derivation Atom IV :=
  .fapp (.lex "probeert" (IV / IV))
    (.bapp (.lex "veel liederen" NP) (.lex "te zingen" (IV \ NP)))

/-- `schematicDeriv o` is the derivation shape that the verb order `o` forces. -/
def schematicDeriv : VerbOrder → Derivation Atom IV
  | .verbRaising => verbRaisingDeriv
  | .verbProjectionRaising => verbProjectionRaisingDeriv

theorem verbRaisingDeriv_hasComp : verbRaisingDeriv.HasComp := by decide

theorem verbProjectionRaisingDeriv_applicationOnly :
    ¬verbProjectionRaisingDeriv.HasComp := by decide

/-- `wordOrderOf ex` reads the verb order of the example `ex` off its features. -/
def wordOrderOf (ex : Datum) : Option VerbOrder :=
  match ex.paperFeatures.lookup "wordOrder" with
  | some "verbRaising" => some .verbRaising
  | some "verbProjectionRaising" => some .verbProjectionRaising
  | _ => none

/-- `scopeData` pairs each scope example's word order with the judgment on its inverse
reading, on which the quantified object outscopes the tensed verb. -/
def scopeData : List (VerbOrder × Judgment) :=
  Examples.all.filterMap fun ex ↦
    (wordOrderOf ex).bind fun vo ↦ (ex.readings.lookup "inverse").map (vo, ·)

/-- The inverse reading is acceptable exactly where the cluster is built with composition, in
every judgment of the book's examples (96) to (100), credited in the data to [bayer-1996],
[kayne-1998], [haegeman-van-riemsdijk-1986] and [haegeman-1992]. -/
theorem inverse_acceptable_iff_hasComp :
    ∀ d ∈ scopeData, d.2 = .acceptable ↔ (schematicDeriv d.1).HasComp := by
  decide

/-- The data hold a verb-projection-raising example whose inverse reading is rejected, so the
account's restriction to composed clusters is tested. -/
theorem exists_verbProjectionRaising_unacceptable :
    ∃ d ∈ scopeData, d.1 = .verbProjectionRaising ∧ d.2 = .unacceptable := by
  decide

end Quantification

/-! ### Intonation and information structure

Alternative derivations of one string are alternative information structures, disambiguated
by tune: "(ANNA married)(MANNY)" carves the composed derivation into a theme and a rheme, and
prosodic phrases are tune-marked constituents, so only constituents of the grammar can be
phrases, the Sense Unit Condition of [selkirk-1984]. -/

section Intonation

open CCG.Intonation Prosody

/-- The accents of "(ANNA married)(MANNY)" are a theme accent on "Anna" and a rheme accent on
"Manny", with "married" unaccented. -/
def annaMannyAccents : AccentAssignment := fun w ↦
  match w with
  | "Anna" => some (.leading .L .H)
  | "Manny" => some (.mono .H)
  | _ => none

/-- "ANNA married" is the composed theme constituent, of category `S/NP`. -/
def anna_married : Derivation Atom (S / NP) :=
  .fcomp (by decide) (.lex "Anna" (S / (S \ NP))) (.lex "married" TV)

/-- The theme constituent projects `θ`, since the theme accent on "Anna" unifies with
unaccented "married". -/
theorem anna_married_theme :
    anna_married.infoFeature annaMannyAccents = some .θ := rfl

/-- The rheme "MANNY" projects `ρ`. -/
theorem manny_rheme :
    (Derivation.lex "Manny" NP).infoFeature annaMannyAccents = some .ρ := rfl

/-- Folding the rheme into the theme's constituent clashes. The whole sentence projects no
single marking, so the tune forces the phrasing "[Anna married][Manny]". -/
theorem theme_rheme_clash :
    (Derivation.fapp anna_married (.lex "Manny" NP)).infoFeature annaMannyAccents
      = none := rfl

/-- The utterance consists of two tune-marked phrases. -/
def annaMannyUtterance : List ProsodicPhrase :=
  [⟨_, anna_married, themeTune⟩, ⟨_, .lex "Manny" NP, rhemeTune⟩]

/-- The information structure extracted from the utterance has the `S/NP` constituent
"ANNA married" as theme and "MANNY" as rheme. -/
theorem annaMannyUtterance_infoStructure :
    (extractInfoStructure annaMannyUtterance).map (fun i ↦ (i.theme.map (·.cat), i.rheme.cat))
      = some (some (S / NP), NP) := rfl

end Intonation

/-! ### Truth conditions

Derivations interpreted compositionally over the toy model: a true sentence and a false one. -/

section TruthConditions

def mary_sleeps : Derivation Atom S := .bapp (.lex "Mary" NP) (.lex "sleeps" IV)

theorem ccg_predicts_john_sleeps : ∃ p, john_sleeps.interp semLexicon = some p ∧ p :=
  ⟨_, rfl, rfl⟩

theorem ccg_predicts_mary_sleeps : ∃ p, mary_sleeps.interp semLexicon = some p ∧ ¬ p :=
  ⟨_, rfl, nofun⟩

theorem ccg_predicts_john_sees_mary : ∃ p, john_sees_mary.interp semLexicon = some p ∧ p :=
  ⟨_, rfl, .inl ⟨rfl, rfl⟩⟩

end TruthConditions

/-! ### The tune terminal as an intonation-phrase terminal -/

section BPTerminal

open Prosody BeckmanPierrehumbert1986 CCG.Intonation

/-- `ipToTune ip accent` is the tune with pitch accent `accent` whose terminal contour is the
final phrase accent and boundary tone of the intonation phrase `ip`. -/
def ipToTune (ip : IntonationPhrase) (accent : PitchAccent) : Tune :=
  ⟨accent, ip.terminalContour⟩

theorem ipToTune_terminal (ip : IntonationPhrase) (accent : PitchAccent) :
    (ipToTune ip accent).terminal = ip.terminalContour := rfl

/-- A declarative intonation phrase has an L phrase accent and an L% boundary. -/
def declarativeIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .L }

/-- A continuation-rise intonation phrase has an L phrase accent and an H% boundary. -/
def continuationIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .H }

/-- The declarative phrase carries the rheme tune's terminal and the continuation-rise phrase
the theme tune's. -/
theorem bp_terminals_match_tunes :
    declarativeIP.terminalContour = rhemeTune.terminal ∧
      continuationIP.terminalContour = themeTune.terminal := by decide

end BPTerminal

end Steedman2000
