module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Witness
public import Linglib.Data.Examples.Cooper2023

/-!
# Cooper's type theory with records

Cooper's theory of types with records has Lean's own type theory as its metatheory: the
judgement `a : T` is the ambient typing, a type is true when inhabited, a record type is a
structure whose structural subtypes are the structures with more fields, and the
intensionality of types with the same witnesses is the ambient theory's as well. On this
basis the file follows the book's chapters: the contents of proper names, the indefinite
article and the copula, with *a is a P* witnessed exactly when `P(a)` is (Ch. 3), and
parametric content (Ch. 4); modal type systems with their restrictive and inclusive notions,
necessity and possibility relative to a background type and a topos in place of an
accessibility relation, and intensionality as the matching of types against an agent's
long-term memory, religious beliefs and desires through points of view (Ch. 6); restricted
properties and their two purifications, the frequentist probability of a witness set and its
estimate from an experience base, and the witness conditions whose witnesses carry what
discourse anaphora picks up (Ch. 7); and parametric contents over a context type of pronoun
labels, on which storage and retrieval derive the scope readings, anaphoric combination
with the sentence boundary and reflexivisation derive Principles B and A, and localisation
derives the weak and strong donkey readings (Ch. 8). A selection of the book's English
examples are the rows of `Data/Examples/Cooper2023.json`, against which the anaphora sets
the substrate derives for each quantifier are checked.

## Implementation notes

* A property is `E → Type` with Cooper's record `[x : Ind]` collapsed to its individual, and
  a ptype `p(a)` a type of situations, so the common-noun content is the identity and
  unnamed. Relabelling is absorbed into the function witnessing a subtyping, and
  compatibility and the topos conditions are read in the ambient possibility.
* The indefinite article and *no* are the particular witness conditions of Ch. 7 over
  properties, while the general conditions take the restrictor as a decidable predicate,
  entering only through the witness-set type `qʷ(P)` as in (59a), and the dogs fragment lifts
  its predicates to properties. Cooper's witness sets are related to those of
  [barwise-cooper-1981] (`Quantifier.NP.Witness`) by `witnessType_iff_witness`; modal type
  systems and Breitholtz's topoi stay here, having no second consumer.
* The proportional cardinality relations are cross-multiplied against a threshold `n / d` and
  require a nonempty extension, where Cooper leaves the ratio undefined. The thresholds
  `θ_q(P)` are free parameters rather than a function of the quantifier and property, so
  that *few* and *a few* share theirs (34) only where a statement says so
  (`few_and_aFew_iff`).
* A negated type `¬T` (Ch. 7, (69)) is read as the function type `T → Empty`.
* A context type records the labels a content requires of the assignments to stored
  quantifiers, pronouns, local pronouns and reflexives; the wh-phrase and gap assignments of
  (82) and the incrementation of labels at combination are omitted, labels being chosen
  distinct by hand. Context specification `c[𝔰.xᵢ = a]` is the one primitive behind
  retrieval, reflexivisation and cross-sentential resolution.
* Restriction and alignment of a property's domain (Ch. 8, (51)–(52)) are further
  restrictions through which the body is read, so purification applies to them uniformly.

## TODO

* Inclusive possibility is stated as the book prints (2d), an implication under an
  existential, which any possibility in which the type does not occur satisfies; the
  intended clause is presumably a conjunction.
* The closure of a content type under the operations (Ch. 8, (21), (89)) and the
  combination of content types (23)–(24) are not modelled: each reading is derived by
  composing the operations by hand.
* The number of a pronoun is not modelled, so the contrast between *it* and *they* with a
  universal antecedent, (46b)–(46e), is recorded in the rows but not derived.
* A reflexive inside a verb phrase (*The guru revealed Kim to himself*) and picture noun
  phrases are outside the treatment, as in the book.
* The anaphora-set table credits the general condition for *few* (79)–(80) with REFSET, as
  Cooper does (p. 315), but the witness set of (59b) contains the objects with both
  properties rather than being contained in them, and may hold objects with the first
  property alone; the claim goes beyond what (59b) provides.
* Purification is determiner-independent, so both donkey readings are predicted for every
  determiner; the experimental record of [denic-sudo-2022] on non-monotonic determiners and
  the question-based selection of [champollion-bumford-henderson-2019] are the tests to
  state.

## References

* [R. Cooper, *From Perception to Communication* (2023)][cooper-2023]
* [J. Barwise, R. Cooper, *Generalized Quantifiers and Natural Language*
  (1981)][barwise-cooper-1981]
* [L. M. Moxey, A. J. Sanford, *Quantifiers and Focus* (1987)][moxey-sanford-1987]
* [A. Kratzer, *What 'must' and 'can' must and can mean* (1977)][kratzer-1977]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [E. Breitholtz, *Enthymemes and Topoi in Dialogue* (2020)][breitholtz-2020]
* [G. Chierchia, *Dynamics of Meaning* (1995)][chierchia-1995b]
* [M. Kanazawa, *Weak vs. Strong Readings of Donkey Sentences* (1994)][kanazawa-1994]
* [A. Ranta, *Type-Theoretical Grammar* (1994)][ranta-1994]
* [R. Montague, *The Proper Treatment of Quantification in Ordinary English* (1973)][montague-1973]
* [M. Denić, Y. Sudo, *Donkey Anaphora in Non-Monotonic Environments* (2022)][denic-sudo-2022]
* [L. Champollion, D. Bumford, R. Henderson, *Donkeys under Discussion*
  (2019)][champollion-bumford-henderson-2019]
-/

@[expose] public section

namespace Cooper2023

open Quantifier Quantifier.GQ Quantifier.NP

variable {E : Type}

/-! ## Types, properties and contents (Chs. 1, 3, 4) -/

/-! ### Structural subtyping (§1.4.3.5) -/

/-- The type of situations with a boy and a dog, (53a). -/
structure BoyAndDog (E : Type) (Boy Dog : E → Type) where
  x : E
  c₁ : Boy x
  y : E
  c₂ : Dog y

/-- The type of situations in which the boy hugs the dog, (53b): a subtype of (53a) by having
more fields, the projection being `toBoyAndDog`. -/
structure BoyHugsDog (E : Type) (Boy Dog : E → Type) (Hug : E → E → Type)
    extends BoyAndDog E Boy Dog where
  e : Hug x y

/-! ### Properties, quantifiers and their contents (§3.4) -/

/-- A property (30): the individuals' types of situations. -/
abbrev Ppty (E : Type) := E → Type

/-- A quantifier: a function from properties to types, Montague's ⟨⟨e,t⟩,t⟩. -/
abbrev Quant (E : Type) := Ppty E → Type

/-- `SemPropName(a)` (33): the quantifier applying its property to the individual. -/
def SemPropName (a : E) : Quant E := fun P ↦ P a

/-- The particular witness condition for `exist(P, Q)` (Ch. 7, (63)): an individual with the
first property and the second. Its `x`-field is what singular anaphora picks up in *A dog is
barking. It is right outside my window* (Ch. 7, (64)). -/
structure ParticularWCExist (P Q : Ppty E) where
  /-- The individual. -/
  x : E
  /-- Its having the first property. -/
  pWit : P x
  /-- Its having the second. -/
  qWit : Q x

/-- The particular witness condition for `no(P, Q)` (Ch. 7, (70)): every witness of the first
property precludes the second, a function into the negated type (69). -/
structure ParticularWCNo (P Q : Ppty E) where
  /-- The preclusion of the second property by each witness of the first. -/
  f : (a : E) → P a → Q a → Empty

/-- `exist(P, Q)` is witnessed iff the extensions of `P` and `Q` overlap. -/
theorem nonempty_particularWCExist_iff {P Q : Ppty E} :
    Nonempty (ParticularWCExist P Q) ↔ ∃ a, Nonempty (P a) ∧ Nonempty (Q a) :=
  ⟨fun ⟨w⟩ ↦ ⟨w.x, ⟨w.pWit⟩, ⟨w.qWit⟩⟩, fun ⟨a, ⟨p⟩, ⟨q⟩⟩ ↦ ⟨⟨a, p, q⟩⟩⟩

/-- A witness of the particular condition for `exist` verifies the classical `some`. -/
theorem some_of_particularWCExist {P Q : Ppty E} (w : ParticularWCExist P Q) :
    GQ.some (fun a ↦ Nonempty (P a)) (fun a ↦ Nonempty (Q a)) :=
  ⟨w.x, ⟨w.pWit⟩, ⟨w.qWit⟩⟩

/-- A witness of the particular condition for `no` verifies the classical `no`. -/
theorem no_sem_of_particularWCNo {P Q : Ppty E} (w : ParticularWCNo P Q) :
    no (fun a ↦ Nonempty (P a)) (fun a ↦ Nonempty (Q a)) :=
  fun a ⟨p⟩ ⟨q⟩ ↦ (w.f a p q).elim

/-- `SemIndefArt` (37): a restrictor property to the existential quantifier over it, whose
witness under the particular condition of Ch. 7 (63) is an individual with the restrictor
and the scope. -/
def SemIndefArt (restr : Ppty E) : Quant E := ParticularWCExist restr

/-- (55): `exist(P, Q)` is witnessed iff the property extensions of `P` and `Q` overlap. -/
theorem nonempty_semIndefArt_iff (restr scope : Ppty E) :
    Nonempty (SemIndefArt restr scope) ↔ ∃ a, Nonempty (restr a) ∧ Nonempty (scope a) :=
  nonempty_particularWCExist_iff

/-- `SemBe` (78), Montague's copula: the property of being the quantifier's witness. -/
def SemBe (Q : Quant E) : Ppty E := fun x ↦ Q fun y ↦ PLift (x = y)

/-- The universal quantifier as a function from the restrictor's witnesses to the scope's,
the function witness of §7.2.4 after [ranta-1994], which, as Cooper notes at (27), yields no
witness set for plural anaphora; the set-based condition (72) is `GeneralWCIncr` with
`CardRel.every`. -/
def SemUniversal (restr scope : Ppty E) : Type := (x : E) → restr x → scope x

/-- `no(P, Q)` under its particular witness condition (Ch. 7, (70)): every witness of the
restrictor precludes the scope. -/
def SemNo (restr scope : Ppty E) : Type := ParticularWCNo restr scope

/-- (92): *a is a P*, the copula over the indefinite article, is witnessed iff `P(a)` is, so
the compositional content and the construction-based content of (86)–(87) are distinct but
equivalent types. -/
theorem nonempty_semBe_semIndefArt_iff (P : Ppty E) (a : E) :
    Nonempty (SemBe (SemIndefArt P) a) ↔ Nonempty (P a) :=
  ⟨fun ⟨⟨_, h, ⟨rfl⟩⟩⟩ ↦ ⟨h⟩, fun ⟨h⟩ ↦ ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

/-- (94c): *a P is a*, the quantifiers in the other order, is witnessed iff `P(a)` is as
well; only the construction expresses `P(a)` itself, and (89) *A conductor is Dudamel* is
odd. -/
theorem nonempty_semIndefArt_semBe_semPropName_iff (P : Ppty E) (a : E) :
    Nonempty (SemIndefArt P (SemBe (SemPropName a))) ↔ Nonempty (P a) :=
  ⟨fun ⟨⟨_, h, ⟨rfl⟩⟩⟩ ↦ ⟨h⟩, fun ⟨h⟩ ↦ ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

/-- A monotone increasing quantifier. -/
def Quant.IsMonIncr (Q : Quant E) : Prop :=
  ∀ P P' : Ppty E, (∀ x, P x → P' x) → Nonempty (Q P) → Nonempty (Q P')

/-- A parametric content (§4.3, (14)): a background type, the context it requires, and a
foreground function from contexts of that type to contents. -/
structure Parametric (C : Type*) where
  /-- The background: the type of contexts the content requires. -/
  bg : Type
  /-- The foreground: the content in each such context. -/
  fg : bg → C

/-- A parametric property. -/
abbrev PPpty (E : Type) := Parametric (Ppty E)

/-! #### The Dudamel fragment

*Dudamel is a conductor* (82c), the existential quantifier under the copula, is witnessed
by Dudamel's conducting, and *Beethoven is a conductor* is not. -/

namespace Dudamel

/-- The individuals. -/
inductive Ind
  | dudamel | beethoven
  deriving DecidableEq, Repr

/-- The ptype `conductor(x)`: Dudamel conducts. -/
inductive Conductor : Ind → Type
  | mk : Conductor .dudamel

/-- *is a conductor* (81c). -/
def IsAConductor : Ppty Ind := SemBe (SemIndefArt Conductor)

/-- *Dudamel is a conductor* is true. -/
def dudamelIsAConductor : SemPropName .dudamel IsAConductor := ⟨.dudamel, .mk, ⟨rfl⟩⟩

/-- *Beethoven is a conductor* is false. -/
theorem beethovenIsAConductor_isEmpty : IsEmpty (SemPropName .beethoven IsAConductor) :=
  ⟨fun | ⟨.dudamel, _, ⟨h⟩⟩ => nomatch h | ⟨.beethoven, h, _⟩ => nomatch h⟩

end Dudamel

/-! ## Modality and intensionality without possible worlds (Ch. 6)

A modal type system (§1.4.3.5, (54); §6.3) is a family of possibilities sharing their types
but differing in which objects witness them; equivalence, subtyping, necessity and
possibility are defined over all possibilities, (1), or over those in which the types occur,
(2). Necessity and possibility in language are relativised, as in Kratzer's semantics, to a
background type and a topos, a dependent type from situations to types standing in for the
accessibility relation, (20)–(24). Intensionality replaces sets of worlds by types (§6.5):
an attitude holds when the type of the agent's long-term memory, religious beliefs or
desires matches its complement modulo relabelling, directly or through a point of view,
(39)–(92). -/

/-! ### Modal type systems (§6.3) -/

/-- A possibility: which types occur in it and which objects witness them. -/
structure Possibility (Ty Obj : Type) where
  /-- The types of the possibility's type system. -/
  occurs : Ty → Prop
  /-- The objects witnessing each type in the possibility. -/
  witnesses : Ty → Obj → Prop

/-- A modal system of types (§1.4.3.5, (54)): a family of possibilities over shared types. -/
abbrev ModalSystem (M Ty Obj : Type) := M → Possibility Ty Obj

namespace ModalSystem

variable {M Ty Obj : Type} (ms : ModalSystem M Ty Obj) (T₁ T₂ : Ty)

/-- The extension of `T` in the possibility `p`, (1a). -/
def extension (p : M) (T : Ty) : Set Obj := {a | (ms p).witnesses T a}

/-- `T` occurs in the type system of the possibility `p`. -/
def Occurs (p : M) (T : Ty) : Prop := (ms p).occurs T

/-- Restrictive equivalence (1a): the same extension in every possibility. -/
def EquivR : Prop := ∀ p, ms.extension p T₁ = ms.extension p T₂

/-- Restrictive subtyping (1b). -/
def SubtypeR : Prop := ∀ p, ms.extension p T₁ ⊆ ms.extension p T₂

/-- Restrictive necessity (1c): witnessed in every possibility. -/
def NecR (T : Ty) : Prop := ∀ p, (ms.extension p T).Nonempty

/-- Restrictive possibility (1d): witnessed in some possibility. -/
def PossR (T : Ty) : Prop := ∃ p, (ms.extension p T).Nonempty

/-- Inclusive equivalence (2a): the same extension wherever both types occur. -/
def EquivI : Prop :=
  ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ms.extension p T₁ = ms.extension p T₂

/-- Inclusive subtyping (2b). -/
def SubtypeI : Prop :=
  ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ms.extension p T₁ ⊆ ms.extension p T₂

/-- Inclusive necessity (2c): witnessed wherever the type occurs. -/
def NecI (T : Ty) : Prop := ∀ p, ms.Occurs p T → (ms.extension p T).Nonempty

/-- Inclusive possibility (2d), as the book prints it. -/
def PossI (T : Ty) : Prop := ∃ p, ms.Occurs p T → (ms.extension p T).Nonempty

/-- The restrictive notions entail the inclusive ones (§6.3). -/
theorem equivI_of_equivR (h : ms.EquivR T₁ T₂) : ms.EquivI T₁ T₂ := fun p _ _ ↦ h p

theorem subtypeI_of_subtypeR (h : ms.SubtypeR T₁ T₂) : ms.SubtypeI T₁ T₂ := fun p _ _ ↦ h p

theorem necI_of_necR {T : Ty} (h : ms.NecR T) : ms.NecI T := fun p _ ↦ h p

theorem possI_of_possR {T : Ty} (h : ms.PossR T) : ms.PossI T := h.imp fun _ hp _ ↦ hp

end ModalSystem

/-! ### Modality with topoi (§6.4)

The witness conditions for `nec` and `poss` go through four versions; the last, (23)–(24),
takes a topos in place of Kratzer's ideal, and, as Cooper notes, has no counterpart of the
ordering source. -/

/-- A topos (20): a dependent type from situations of a background type to types. -/
abbrev Topos := Parametric Type

/-- Compatibility (17): something is of both types. -/
def Compatible (T₁ T₂ : Type) : Prop := Nonempty (T₁ × T₂)

/-- A witness of `nec(T, B, τ)` (23): a situation of the background type `B`, `B` a subtype
of the topos's domain, and the type the topos returns for it a subtype of `T`. -/
structure Nec (T B : Type) (τ : Topos) where
  /-- The situation. -/
  sit : B
  /-- The background type as a subtype of the topos's domain. -/
  sub : B → τ.bg
  /-- The type the topos returns as a subtype of `T`. -/
  incl : τ.fg (sub sit) → T

/-- A witness of `poss(T, B, τ)` (24): as `Nec`, with the returned type compatible with `T`. -/
structure Poss (T B : Type) (τ : Topos) where
  /-- The situation. -/
  sit : B
  /-- The background type as a subtype of the topos's domain. -/
  sub : B → τ.bg
  /-- The type the topos returns is compatible with `T`. -/
  compat : Compatible (τ.fg (sub sit)) T

/-- Necessity yields possibility when the topos returns an inhabited type. -/
def Nec.toPoss {T B : Type} {τ : Topos} (h : Nec T B τ) (hne : Nonempty (τ.fg (h.sub h.sit))) :
    Poss T B τ :=
  ⟨h.sit, h.sub, hne.map fun w ↦ (w, h.incl w)⟩

/-! #### *Mary should eat her broccoli* (25)–(31)

The base situation (26) has the broccoli on Mary's plate and Mary loving it; the deontic
topos (28a) sends a situation of a child with food on her plate to her eating it, the bouletic
topos (28b) a situation of a child loving some food to her eating it, and
`nec([e:eat(m,b)], T_broc, τ)` is witnessed by either, (29)–(30). -/

namespace Dinner

/-- The individuals. -/
inductive Ind
  | broccoli | mary | plate
  deriving DecidableEq, Repr

/-- The ptypes of the base situation (26), each witnessed by its fact. -/
inductive Broccoli : Ind → Type
  | mk : Broccoli .broccoli

/-- Mary is a child. -/
inductive Child : Ind → Type
  | mk : Child .mary

/-- The plate is a plate. -/
inductive Plate : Ind → Type
  | mk : Plate .plate

/-- Mary has the plate. -/
inductive Have : Ind → Ind → Type
  | mk : Have .mary .plate

/-- The broccoli is on the plate. -/
inductive On : Ind → Ind → Type
  | mk : On .broccoli .plate

/-- Mary loves the broccoli. -/
inductive Love : Ind → Ind → Type
  | mk : Love .mary .broccoli

/-- Mary eats the broccoli. -/
inductive Eat : Ind → Ind → Type
  | mk : Eat .mary .broccoli

/-- Food, of which broccoli is a subtype, (27). -/
inductive Food : Ind → Type
  | ofBroccoli {x : Ind} : Broccoli x → Food x

/-- The base situation type (26), its manifest fields fixed here by the ptypes' witnesses. -/
structure Base where
  x : Ind
  c₁ : Broccoli x
  y : Ind
  c₂ : Child y
  z : Ind
  c₃ : Plate z
  e₁ : Have y z
  e₂ : On x z
  e₃ : Love y x

/-- The background of the deontic topos (28a): a child with food on her plate. -/
structure OnPlate where
  x : Ind
  c₁ : Food x
  y : Ind
  c₂ : Child y
  z : Ind
  c₃ : Plate z
  e₁ : Have y z
  e₂ : On x z

/-- The background of the bouletic topos (28b): a child loving some food. -/
structure Loves where
  x : Ind
  c₁ : Food x
  y : Ind
  c₂ : Child y
  e₃ : Love y x

/-- The deontic topos τ₁ (28a). -/
def deontic : Topos := ⟨OnPlate, fun r ↦ Eat r.y r.x⟩

/-- The bouletic topos τ₂ (28b). -/
def bouletic : Topos := ⟨Loves, fun r ↦ Eat r.y r.x⟩

/-- The base situation: the broccoli on Mary's plate, which she loves. -/
def base : Base := ⟨.broccoli, .mk, .mary, .mk, .plate, .mk, .mk, .mk, .mk⟩

/-- (29a): eating the broccoli is necessary under the deontic topos, the base type a subtype
of the topos's domain by (27) and the topos returning the type itself (30). -/
def necDeontic : Nec (Eat .mary .broccoli) Base deontic where
  sit := base
  sub b := ⟨b.x, .ofBroccoli b.c₁, b.y, b.c₂, b.z, b.c₃, b.e₁, b.e₂⟩
  incl := id

/-- (29b): and under the bouletic topos. -/
def necBouletic : Nec (Eat .mary .broccoli) Base bouletic where
  sit := base
  sub b := ⟨b.x, .ofBroccoli b.c₁, b.y, b.c₂, b.e₃⟩
  incl := id

end Dinner

/-! ### Intensionality (§6.5) -/

/-- Subtyping modulo relabelling (39), `T₁ ⊑⇝ T₂`. -/
def RelabeledSubtype (T₁ T₂ : Type) : Prop := Nonempty (T₁ → T₂)

/-- An agent's total information state (91), long-term memory, religious beliefs and desires
as types, with the point-of-view relation on types, (55), (80). -/
structure InfoState (Agent : Type) where
  /-- The type of the agent's long-term memory. -/
  ltm : Agent → Type
  /-- The type of the agent's religious beliefs. -/
  rbel : Agent → Type
  /-- The type of the agent's desires. -/
  des : Agent → Type
  /-- `pov M T`: `M` is a complete point of view on `T`, the asymmetric merge of `T` with an
  alternative type on some of its labels. -/
  pov : Type → Type → Prop

/-- An information type `I` matches `T` directly, or through a complete point of view `M` on
a type `I` matches, `M` matching `T`, (58), (80), (92). -/
def InfoState.Matches {Agent : Type} (s : InfoState Agent) (I T : Type) : Prop :=
  RelabeledSubtype I T ∨ ∃ T₁ M, RelabeledSubtype I T₁ ∧ s.pov M T₁ ∧ RelabeledSubtype M T

/-! #### Postulated subtyping: buying and selling, (35), (44)–(47), (50) -/

/-- A selling situation. -/
structure SellEvent (E : Type) where
  seller : E
  thing : E
  buyer : E

/-- A buying situation. -/
structure BuyEvent (E : Type) where
  buyer : E
  thing : E
  seller : E

/-- The postulate (50b), `sell(a, b, c) ⊑ buy(c, b, a)`, holding only in the possibilities the
postulate restricts attention to, unlike the structural (50a), `BoyHugsDog.toBoyAndDog`. -/
def SellEvent.toBuyEvent (e : SellEvent E) : BuyEvent E := ⟨e.buyer, e.thing, e.seller⟩

/-- Its converse (47). -/
def BuyEvent.toSellEvent (e : BuyEvent E) : SellEvent E := ⟨e.seller, e.thing, e.buyer⟩

section Attitudes

variable {Agent : Type} (s : InfoState Agent) (a : Agent)

/-- `believe(a, T)` (40): the type of `a`'s long-term memory matches `T`. -/
def Believe (T : Type) : Prop := RelabeledSubtype (s.ltm a) T

/-- (41): belief is closed under relabelling. -/
theorem believe_equiv {T T' : Type} (h : Believe s a T) (e : T ≃ T') : Believe s a T' :=
  h.map (e ∘ ·)

/-- Belief is closed under subtyping, structural or postulated. -/
theorem believe_of_subtype {T₁ T₂ : Type} (h : Believe s a T₁) (f : T₁ → T₂) :
    Believe s a T₂ :=
  h.map (f ∘ ·)

/-- (44)–(47): whoever believes that Kim bought sex from Sam believes that Sam sold sex to
Kim, the postulate holding across belief. -/
theorem believe_sell_of_believe_buy (h : Believe s a (BuyEvent E)) : Believe s a (SellEvent E) :=
  believe_of_subtype s a h BuyEvent.toSellEvent

/-- `believe(a, T)` with a point of view (58). -/
def BelievePov (T : Type) : Prop := s.Matches (s.ltm a) T

/-- `rbelieve(a, T)`, characterised after (74): the type of `a`'s religious beliefs matches
`T`. -/
def RBelieve (T : Type) : Prop := RelabeledSubtype (s.rbel a) T

/-- `want†(a, T)` (92): `a`'s desires match `T`. -/
def WantDagger (T : Type) : Prop := s.Matches (s.des a) T

end Attitudes

/-- `worship(a, Q)` (75), (81): `a`'s religious beliefs match the quantifier exported over
`worship†`, intentionality and specificity without existence. -/
def Worship (s : InfoState E) (dagger : E → E → Type) (a : E) (Q : Quant E) : Prop :=
  s.Matches (s.rbel a) (Q (dagger a))

/-- `want_P(a, P)` (90a): wanting to have a property. -/
def WantP (s : InfoState E) (a : E) (P : Ppty E) : Prop := WantDagger s a (P a)

/-- `want_Q(a, Q)` (90b): wanting a quantifier's worth of things is wanting to have them. -/
def WantQ (s : InfoState E) (have_ : E → E → Type) (a : E) (Q : Quant E) : Prop :=
  WantDagger s a (Q (have_ a))

/-! #### Hesperus and Phosphorus, (52)–(53) -/

/-- The ancients' long-term memory (52): a body named Hesperus rising in the evening and a
body named Phosphorus rising in the morning. -/
structure TwoStars (E : Type) (Hesperus Phosphorus Evening Morning : E → Type) where
  x : E
  c₁ : Hesperus x
  e₁ : Evening x
  y : E
  c₂ : Phosphorus y
  e₂ : Morning y

/-- After learning that they are one body (53): the manifest field, a subtype of (52) by the
projection `toTwoStars`. -/
structure OneStar (E : Type) (Hesperus Phosphorus Evening Morning : E → Type)
    extends TwoStars E Hesperus Phosphorus Evening Morning where
  same : y = x

/-! #### Intensional transitive verbs, (63)–(66), (87) -/

/-- A transitive verb whose predicate takes a quantifier (64), with the variant `p†` between
individuals. -/
structure TransVerb (E : Type) where
  /-- The ptype of the verb over an individual and a quantifier. -/
  pred : E → Quant E → Type
  /-- The variant `p†` over two individuals. -/
  dagger : E → E → Type

/-- (65): an extensional verb's ptype is equivalent to the quantifier exported over `p†`. -/
def TransVerb.IsExtensional (v : TransVerb E) : Prop :=
  ∀ a Q, Nonempty (v.pred a Q ≃ Q (v.dagger a))

/-- (66): a successful search is a finding. -/
structure SuccessfulSeek (E : Type) (seek find : E → Quant E → Type) where
  /-- The ptype of an event's success. -/
  successful : Type → Type
  /-- The subtyping `successful(seek(a, Q)) ⊑ find(a, Q)`. -/
  findOfSuccessful : ∀ a Q, successful (seek a Q) → find a Q

/-- (87): booking a monotone increasing quantifier's worth of tables requires tables to be,
without requiring a specific one. -/
def BookRequiresBeing (book : E → Quant E → Type) (be : Ppty E) : Prop :=
  ∀ a Q, Q.IsMonIncr → Nonempty (book a Q) → Nonempty (Q be)

/-! #### Restrictive against inclusive necessity

Two possibilities over the types `rain` and `snow`: snow is witnessed only in the first, so it
is possible but not necessary; and when snow does not occur in the second at all, it is
inclusively but not restrictively necessary, so the entailment of §6.3 does not reverse. -/

namespace Weather

/-- The types. -/
inductive Ty
  | rain | snow
  deriving DecidableEq

/-- The objects. -/
inductive Obj
  | a | b
  deriving DecidableEq

/-- Both types occur in both possibilities; rain is witnessed in both, snow in the first. -/
def system : ModalSystem Bool Ty Obj
  | true => ⟨fun _ ↦ True, fun | .rain, .a => True | .snow, .b => True | _, _ => False⟩
  | false => ⟨fun _ ↦ True, fun | .rain, .a => True | _, _ => False⟩

/-- As `system`, but snow does not occur in the second possibility. -/
def restricted : ModalSystem Bool Ty Obj
  | true => ⟨fun _ ↦ True, fun | .rain, .a => True | .snow, .b => True | _, _ => False⟩
  | false => ⟨(· = .rain), fun | .rain, .a => True | _, _ => False⟩

theorem necR_rain : system.NecR .rain := fun | true => ⟨.a, trivial⟩ | false => ⟨.a, trivial⟩

theorem possR_snow : system.PossR .snow := ⟨true, .b, trivial⟩

theorem not_necR_snow : ¬ system.NecR .snow := fun h ↦ nomatch h false

theorem restricted_necI_snow : restricted.NecI .snow
  | true, _ => ⟨.b, trivial⟩
  | false, h => nomatch h

theorem restricted_not_necR_snow : ¬ restricted.NecR .snow := fun h ↦ nomatch h false

end Weather

/-! ## Witness-based quantification (Ch. 7)

A property may be restricted by conditions in its domain beyond the required `x`-field,
(7b), and purification lowers the restriction into the body existentially, `𝔓` (12), or
universally, `𝔓∀` (13). The cardinality conditions on witness sets (20)–(35) have
frequentist probabilistic forms (41)–(58), estimable from an agent's experience base of
remembered judgements (37)–(40). The particular witness conditions for `exist` (63) and
`no` (70) are types equivalent to the general ones (59) whose witnesses carry what discourse
anaphora picks up. -/

/-- A restricted property (7b): conditions on the individual in the domain, and the body. -/
structure Restricted (E : Type) where
  /-- The restriction: the conditions the domain places on the individual. -/
  restr : E → Type
  /-- The body: the type returned for an individual meeting the restriction. -/
  body : (x : E) → restr x → Type

/-- A property is pure (7a) when its restriction is trivial. -/
def Restricted.IsPure (P : Restricted E) : Prop := ∀ x, Nonempty (Unique (P.restr x))

/-- Purification `𝔓(P)` (12): the restriction lowered into the body under the local context. -/
def Purify (P : Restricted E) : Ppty E := fun x ↦ (c : P.restr x) × P.body x c

/-- Universal purification `𝔓∀(P)` (13): the body under every way of meeting the
restriction. -/
def PurifyUniv (P : Restricted E) : Ppty E := fun x ↦ (c : P.restr x) → P.body x c

/-- Alignment of paths in the domain (Ch. 8, (51)–(52)): a manifest field identifying two
paths is a further restriction of the domain, through which the body is read. -/
def Restricted.align (P : Restricted E) (R : E → Type) (f : ∀ x, R x → P.restr x) :
    Restricted E :=
  ⟨R, fun x c ↦ P.body x (f x c)⟩

/-- Property restriction `P|ℱ` (Ch. 5, (98)): the domain narrowed by a property, the
alignment along the projection. -/
def Restricted.restrictBy (P : Restricted E) (R : Ppty E) : Restricted E :=
  P.align (fun x ↦ R x × P.restr x) fun _ ↦ Prod.snd

theorem nonempty_purify_iff (P : Restricted E) (x : E) :
    Nonempty (Purify P x) ↔ ∃ c : P.restr x, Nonempty (P.body x c) :=
  nonempty_sigma

theorem nonempty_purifyUniv_iff (P : Restricted E) (x : E) :
    Nonempty (PurifyUniv P x) ↔ ∀ c : P.restr x, Nonempty (P.body x c) :=
  Classical.nonempty_pi

/-- For a pure property the two purifications agree: `𝔓` and `𝔓∀` differ only under a
non-trivial restriction. -/
theorem Restricted.IsPure.nonempty_purify_iff_nonempty_purifyUniv {P : Restricted E}
    (h : P.IsPure) (x : E) : Nonempty (Purify P x) ↔ Nonempty (PurifyUniv P x) := by
  rw [nonempty_purify_iff, nonempty_purifyUniv_iff]
  obtain ⟨u⟩ := h x
  exact ⟨fun ⟨c, hc⟩ c' ↦ (u.uniq c).trans (u.uniq c').symm ▸ hc, fun hall ↦ ⟨u.default, hall _⟩⟩

/-! ### Types of witness sets (§7.2.4)

A witness set `X` of type `qʷ(P)` meets two conditions, (20)–(35): it is a subset of the
property extension `[↓P]`, which (20a) makes the link to the witness sets of
[barwise-cooper-1981], and its cardinality stands in a relation fixed by `q` to that of
`[↓P]`. A witness set of `qʷ(P)` is then a witness set in the sense of [barwise-cooper-1981]
for the quantifier comparing `|P ∩ S|` with `|P|` by the same relation
(`witnessType_iff_witness`). -/

/-- The cardinality clause of a type of witness sets: a relation between `|X|` and `|[↓P]|`. -/
abbrev CardRel := ℕ → ℕ → Prop

namespace CardRel

/-- `existʷ` (21): a singleton. Cooper notes the departure from [barwise-cooper-1981], whose
witness sets for *a* have at least one member. -/
def exist : CardRel := fun x _ ↦ x = 1

/-- `exist_plʷ` (22), plural *some*: at least two. -/
def existPl : CardRel := fun x _ ↦ 2 ≤ x

/-- `noʷ` (23)–(24): empty. -/
def no : CardRel := fun x _ ↦ x = 0

/-- `everyʷ` (25)–(26): the whole extension. -/
def every : CardRel := fun x p ↦ x = p

/-- At least `θ`: `many_aʷ` (30), and `a_few_aʷ` (34) at the threshold of `few_aʷ`. -/
def atLeast (θ : ℕ) : CardRel := fun x _ ↦ θ ≤ x

/-- At most `θ`: `few_aʷ` (32). -/
def atMost (θ : ℕ) : CardRel := fun x _ ↦ x ≤ θ

/-- At least the proportion `n / d` of a nonempty extension, cross-multiplied: `mostʷ` (29),
`many_pʷ` (31), and `a_few_pʷ` (35) at the threshold of `few_pʷ`. -/
def propAtLeast (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ n * p ≤ d * x

/-- At most the proportion `n / d` of a nonempty extension: `few_pʷ` (33). -/
def propAtMost (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ d * x ≤ n * p

/-- The complement witness sets of `few_a` (81b): all but at most `θ` of the extension. -/
def compAtMost (θ : ℕ) : CardRel := fun x p ↦ p - θ ≤ x

/-- The complement witness sets of `few_p` (82b): at least the proportion `1 - n / d` of a
nonempty extension. -/
def compPropAtMost (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ (d - n) * p ≤ d * x

/-- `exist_plʷ` is closed upwards. -/
theorem monotone_existPl (p : ℕ) : Monotone (existPl · p) := fun _ _ hxy h ↦ h.trans hxy

/-- At least `θ` is closed upwards. -/
theorem monotone_atLeast (θ p : ℕ) : Monotone (atLeast θ · p) := fun _ _ hxy h ↦ h.trans hxy

/-- At most `θ` is closed downwards. -/
theorem antitone_atMost (θ p : ℕ) : Antitone (atMost θ · p) := fun _ _ hxy h ↦ hxy.trans h

/-- At least a proportion is closed upwards. -/
theorem monotone_propAtLeast (n d p : ℕ) : Monotone (propAtLeast n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, h.2.trans (Nat.mul_le_mul_left d hxy)⟩

/-- At most a proportion is closed downwards. -/
theorem antitone_propAtMost (n d p : ℕ) : Antitone (propAtMost n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, (Nat.mul_le_mul_left d hxy).trans h.2⟩

/-- The complement relation (81b) is closed upwards. -/
theorem monotone_compAtMost (θ p : ℕ) : Monotone (compAtMost θ · p) :=
  fun _ _ hxy h ↦ h.trans hxy

/-- The complement relation (82b) is closed upwards. -/
theorem monotone_compPropAtMost (n d p : ℕ) : Monotone (compPropAtMost n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, h.2.trans (Nat.mul_le_mul_left d hxy)⟩

end CardRel

section WitnessType

open scoped Finset

variable [Fintype E] (P : E → Prop) [DecidablePred P] {c : CardRel} {X : Finset E}

/-- The type `qʷ(P)` of witness sets (20)–(35): subsets of the extension `[↓P]` whose
cardinality stands in the relation `c` to the extension's. -/
def WitnessType (c : CardRel) (X : Finset E) : Prop := X ⊆ ({x | P x} : Finset E) ∧ c #X #{x | P x}

variable {P}

open Classical in
/-- Cooper's witness sets are those of [barwise-cooper-1981] (20a): a witness set of `qʷ(P)` is a
B&C witness set, over `P`, of the quantifier comparing `|P ∩ S|` with `|P|` by the relation of
`qʷ`. -/
theorem witnessType_iff_witness :
    WitnessType P c X ↔ Witness (fun S ↦ c (count fun x ↦ P x ∧ S x) (count P)) P (· ∈ X) := by
  have hsub : X ⊆ ({x | P x} : Finset E) ↔ ∀ x, x ∈ X → P x := by simp [Finset.subset_iff]
  have hcard (h : X ⊆ ({x | P x} : Finset E)) : count (fun x ↦ P x ∧ x ∈ X) = #X := by
    simp only [count, countOn]
    congr 1
    ext a
    simpa using fun ha ↦ (Finset.mem_filter.1 (h ha)).2
  refine ⟨fun ⟨h, hc⟩ ↦ ⟨hsub.1 h, ?_⟩, fun ⟨h, hc⟩ ↦ ⟨hsub.2 h, ?_⟩⟩
  · beta_reduce
    convert hc using 2
    · convert hcard h
    · rfl
  · beta_reduce at hc
    convert hc using 2
    · convert (hcard (hsub.2 h)).symm
    · rfl

/-- The witness sets of `everyʷ(P)` are the B&C witness sets of `every P`. -/
theorem everyW_iff_witness : WitnessType P .every X ↔ Witness (every P) P (· ∈ X) := by
  simp only [WitnessType, CardRel.every, Witness, every]
  exact ⟨fun ⟨h, hc⟩ ↦ ⟨fun a ha ↦ (Finset.mem_filter.1 (h ha)).2, fun a ha ↦
      Finset.eq_of_subset_of_card_le h hc.ge ▸ Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩⟩,
    fun ⟨h, hP⟩ ↦
      have hX : X = ({x | P x} : Finset E) := Finset.ext fun a ↦ by simpa using ⟨h a, hP a⟩
      ⟨hX.le, congrArg Finset.card hX⟩⟩

/-- The witness set of `noʷ(P)` is the B&C witness set of `no P`. -/
theorem noW_iff_witness : WitnessType P .no X ↔ Witness (no P) P (· ∈ X) := by
  simp only [WitnessType, CardRel.no, Witness, no, Finset.card_eq_zero]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨by simp [h], by simp [h]⟩,
    fun ⟨h, hn⟩ ↦ ⟨by simpa [Finset.subset_iff] using h,
      Finset.eq_empty_of_forall_notMem fun a ha ↦ hn a (h a ha) ha⟩⟩

/-- Cooper's singleton witness sets for `exist` (21) are the minimal B&C witness sets of
`some P`. -/
theorem existW_iff_minimal_witness [DecidableEq E] :
    WitnessType P .exist X ↔ Minimal (fun Y : Finset E ↦ Witness (GQ.some P) P (· ∈ Y)) X := by
  simp only [WitnessType, CardRel.exist, Witness, GQ.some, minimal_iff_forall_lt,
    Finset.card_eq_one]
  constructor
  · rintro ⟨hs, a, rfl⟩
    have hPa : P a := (Finset.mem_filter.1 (hs (Finset.mem_singleton_self a))).2
    refine ⟨⟨fun x hx ↦ Finset.mem_singleton.1 hx ▸ hPa, a, hPa, Finset.mem_singleton_self a⟩,
      fun Y hY ⟨_, b, _, hb⟩ ↦ ?_⟩
    rw [Finset.ssubset_singleton_iff.1 hY] at hb
    exact Finset.notMem_empty b hb
  · rintro ⟨⟨hs, a, hPa, haX⟩, hmin⟩
    refine ⟨fun x hx ↦ Finset.mem_filter.2 ⟨Finset.mem_univ x, hs x hx⟩, a, ?_⟩
    refine (eq_of_le_of_not_lt (Finset.singleton_subset_iff.2 haX) fun hlt ↦ hmin hlt
      ⟨fun x hx ↦ Finset.mem_singleton.1 hx ▸ hPa, a, hPa, Finset.mem_singleton_self a⟩).symm

/-- The complement in `[↓P]` of a witness set of `few_aʷ(P)` is a complement witness set
(81b). -/
theorem WitnessType.compAtMost_sdiff [DecidableEq E] {θ : ℕ} (h : WitnessType P (.atMost θ) X) :
    WitnessType P (.compAtMost θ) (({x | P x} : Finset E) \ X) :=
  ⟨Finset.sdiff_subset, by
    have := h.2
    simp only [CardRel.compAtMost, CardRel.atMost] at this ⊢
    rw [Finset.card_sdiff_of_subset h.1]
    omega⟩

end WitnessType

/-! ### Witness sets and probabilities (§7.3) -/

/-- The frequentist conditional probability (36) of one extension given another, `0` when
the condition is unwitnessed. -/
def condProb [DecidableEq E] (A B : Finset E) : ℚ := ((A ∩ B).card : ℚ) / B.card

/-- (51)–(52): for a witness set `X` of objects with the property, the probability of `𝔗(X)`
given `𝔗(P)` is the proportion `|X| / |[↓P]|`. -/
theorem condProb_of_subset [DecidableEq E] {X P : Finset E} (h : X ⊆ P) :
    condProb X P = (X.card : ℚ) / P.card := by
  rw [condProb, Finset.inter_eq_left.2 h]

open scoped Finset in
/-- (50): the probabilistic witness condition for *most* is the cardinal one (29). -/
theorem witnessType_propAtLeast_iff [Fintype E] [DecidableEq E] {P : E → Prop}
    [DecidablePred P] {n d : ℕ} (hd : 0 < d) {X : Finset E} (hX : X ⊆ ({x | P x} : Finset E))
    (hP : 0 < #{x | P x}) :
    WitnessType P (.propAtLeast n d) X ↔ (n : ℚ) / d ≤ condProb X {x | P x} := by
  rw [condProb_of_subset hX, div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast hP),
    mul_comm _ (d : ℚ)]
  exact ⟨fun h ↦ by exact_mod_cast h.2.2, fun h ↦ ⟨hX, hP, by exact_mod_cast h⟩⟩

/-- An experience base (37): the judgements `[sit = a, type = T]` an agent remembers. -/
abbrev ExperienceBase (E Ty : Type) := Finset (E × Ty)

section ExperienceBase

variable {Ty : Type} [DecidableEq E] [DecidableEq Ty] (𝔍 : ExperienceBase E Ty)

/-- The extension of a type with respect to the experience base (38). -/
def ExperienceBase.extension (T : Ty) : Finset E := (𝔍.filter (·.2 = T)).image Prod.fst

/-- The estimate `p_𝔍(T₁ ‖ T₂)` (39) of the probability (36) from the experience base. -/
def ExperienceBase.estimate (T₁ T₂ : Ty) : ℚ :=
  condProb (𝔍.extension T₁) (𝔍.extension T₂)

end ExperienceBase

/-! ### Witness conditions for quantificational ptypes (§7.4)

The general witness conditions (59) correspond to the two procedures of
[barwise-cooper-1981] for monotone quantifiers: for an increasing quantifier (59a), a witness
set of `qʷ(P)` and a function from its members into the scope; for a decreasing one (59b), a
witness set and a function into it from the objects with both properties. The restrictor
enters only through the witness-set type. Each is witnessed exactly when the relation of `qʷ`
holds of `|P ∩ Q|` and `|P|`, provided the relation is closed upwards, respectively
downwards, in `|X|`; `every` is not, and has its own truth condition. -/

section WitnessCondition

open scoped Finset

variable [Fintype E] {P : E → Prop} [DecidablePred P] {c : CardRel} {Q Q' : Ppty E}

variable (P c Q) in
/-- The general witness condition for monotone increasing quantifiers (59a). -/
structure GeneralWCIncr where
  /-- The witness set. -/
  X : Finset E
  /-- Its being of the type `qʷ(P)`. -/
  witness : WitnessType P c X
  /-- The scope for each of its members. -/
  f : ∀ a ∈ X, Q a

variable (P c Q) in
/-- The general witness condition for monotone decreasing quantifiers (59b). -/
structure GeneralWCDecr where
  /-- The witness set. -/
  X : Finset E
  /-- Its being of the type `qʷ(P)`. -/
  witness : WitnessType P c X
  /-- The membership in it of each object with both properties. -/
  f : ∀ a, P a → Nonempty (Q a) → a ∈ X

variable (P c Q) in
/-- A witness set of `qʷ(P)` whose members each preclude the scope, the negated type (69) read
as a function into `Empty`: the particular witness conditions for `no` over `everyʷ(P)` (70)
and for `few` over its complement witness sets (85)–(86). -/
abbrev ParticularWCNeg : Type := GeneralWCIncr P c fun a ↦ Q a → Empty

/-- Increasing in the scope: a witness for a scope is one for any larger scope. -/
def GeneralWCIncr.mapScope (g : ∀ a, Q a → Q' a) (w : GeneralWCIncr P c Q) :
    GeneralWCIncr P c Q' :=
  ⟨w.X, w.witness, fun a ha ↦ g a (w.f a ha)⟩

/-- Decreasing in the scope: a witness for a scope is one for any smaller scope. -/
def GeneralWCDecr.comapScope (g : ∀ a, Q' a → Q a) (w : GeneralWCDecr P c Q) :
    GeneralWCDecr P c Q' :=
  ⟨w.X, w.witness, fun a hP ⟨q⟩ ↦ w.f a hP ⟨g a q⟩⟩

open Classical in
/-- Under (59a) the witness set consists of objects with both properties. -/
theorem GeneralWCIncr.X_subset (w : GeneralWCIncr P c Q) :
    w.X ⊆ ({x | P x ∧ Nonempty (Q x)} : Finset E) :=
  fun a ha ↦ Finset.mem_filter.2
    ⟨Finset.mem_univ a, (Finset.mem_filter.1 (w.witness.1 ha)).2, ⟨w.f a ha⟩⟩

open Classical in
/-- Under a condition with negated scope the witness set consists of objects with the first
property and not the second. -/
theorem ParticularWCNeg.X_subset (w : ParticularWCNeg P c Q) :
    w.X ⊆ ({x | P x ∧ IsEmpty (Q x)} : Finset E) :=
  fun a ha ↦ Finset.mem_filter.2
    ⟨Finset.mem_univ a, (Finset.mem_filter.1 (w.witness.1 ha)).2, ⟨fun q ↦ (w.f a ha q).elim⟩⟩

/-- Under (59b) the witness set lies within the first property. -/
theorem GeneralWCDecr.X_subset (w : GeneralWCDecr P c Q) : w.X ⊆ ({x | P x} : Finset E) :=
  w.witness.1

open Classical in
/-- Under (59b) the witness set contains every object with both properties. -/
theorem GeneralWCDecr.subset_X (w : GeneralWCDecr P c Q) :
    ({x | P x ∧ Nonempty (Q x)} : Finset E) ⊆ w.X :=
  fun a ha ↦ (Finset.mem_filter.1 ha).2.elim (w.f a)

open Classical in
/-- The truth condition of (59a) for a relation closed upwards in `|X|`. -/
theorem nonempty_generalWCIncr_iff (hc : ∀ p, Monotone (c · p)) :
    Nonempty (GeneralWCIncr P c Q) ↔ c #{x | P x ∧ Nonempty (Q x)} #{x | P x} :=
  ⟨fun ⟨w⟩ ↦ hc _ (Finset.card_le_card w.X_subset) w.witness.2,
    fun h ↦ ⟨⟨{x | P x ∧ Nonempty (Q x)},
      ⟨Finset.monotone_filter_right _ fun _ _ h ↦ h.1, h⟩,
      fun _ ha ↦ (Finset.mem_filter.1 ha).2.2.some⟩⟩⟩

open Classical in
/-- The truth condition of (59b) for a relation closed downwards in `|X|`. -/
theorem nonempty_generalWCDecr_iff (hc : ∀ p, Antitone (c · p)) :
    Nonempty (GeneralWCDecr P c Q) ↔ c #{x | P x ∧ Nonempty (Q x)} #{x | P x} :=
  ⟨fun ⟨w⟩ ↦ hc _ (Finset.card_le_card w.subset_X) w.witness.2,
    fun h ↦ ⟨⟨{x | P x ∧ Nonempty (Q x)},
      ⟨Finset.monotone_filter_right _ fun _ _ h ↦ h.1, h⟩,
      fun a hP hQ ↦ Finset.mem_filter.2 ⟨Finset.mem_univ a, hP, hQ⟩⟩⟩⟩

/-- The truth condition of (72): `everyʷ` is not closed upwards, but a witness set within
`[↓P]` of its cardinality is all of it. -/
theorem nonempty_generalWCIncr_every_iff :
    Nonempty (GeneralWCIncr P .every Q) ↔ ∀ a, P a → Nonempty (Q a) :=
  ⟨fun ⟨w⟩ a ha ↦ ⟨w.f a (Finset.eq_of_subset_of_card_le w.witness.1 w.witness.2.ge ▸
      Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩)⟩,
    fun h ↦ ⟨⟨{x | P x}, ⟨subset_rfl, rfl⟩,
      fun a ha ↦ (h a (Finset.mem_filter.1 ha).2).some⟩⟩⟩

/-- The truth condition of (60): a singleton set of an object with `P` all of whose members
have `Q` exists just in case an object has both, (62). -/
theorem nonempty_generalWCIncr_exist_iff [DecidableEq E] :
    Nonempty (GeneralWCIncr P .exist Q) ↔ ∃ a, P a ∧ Nonempty (Q a) :=
  ⟨fun ⟨w⟩ ↦
      have ⟨a, ha⟩ := Finset.card_eq_one.1 w.witness.2
      have haX : a ∈ w.X := ha ▸ Finset.mem_singleton_self a
      ⟨a, (Finset.mem_filter.1 (w.witness.1 haX)).2, ⟨w.f a haX⟩⟩,
    fun ⟨a, hPa, ⟨q⟩⟩ ↦ ⟨⟨{a},
      ⟨Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨Finset.mem_univ a, hPa⟩),
        Finset.card_singleton a⟩,
      fun _ hb ↦ (Finset.mem_singleton.1 hb).symm ▸ q⟩⟩⟩

open Classical in
/-- `many_a` (77) and `a_few_a` (89) are the counting quantifier *at least `θ`*. -/
theorem nonempty_generalWCIncr_atLeast_iff {θ : ℕ} :
    Nonempty (GeneralWCIncr P (.atLeast θ) Q) ↔ atLeast θ P fun a ↦ Nonempty (Q a) :=
  (nonempty_generalWCIncr_iff (CardRel.monotone_atLeast θ)).trans <| by
    simp only [CardRel.atLeast, atLeast, count, countOn, ge_iff_le]

open Classical in
/-- `few_a` (79) is *at most `θ`*. -/
theorem nonempty_generalWCDecr_atMost_iff {θ : ℕ} :
    Nonempty (GeneralWCDecr P (.atMost θ) Q) ↔ atMost θ P fun a ↦ Nonempty (Q a) :=
  (nonempty_generalWCDecr_iff (CardRel.antitone_atMost θ)).trans <| by
    simp only [CardRel.atMost, atMost, count, countOn]

open Classical in
/-- `most` (74), `many_p` (78) and `a_few_p` (90) are the proportional threshold quantifier
over a nonempty restrictor. -/
theorem nonempty_generalWCIncr_propAtLeast_iff {n d : ℕ} :
    Nonempty (GeneralWCIncr P (.propAtLeast n d) Q) ↔
      0 < count P ∧ thresholdOn Finset.univ P (fun a ↦ Nonempty (Q a)) n d :=
  nonempty_generalWCIncr_iff (CardRel.monotone_propAtLeast n d)

open Classical in
/-- With the threshold `few` and `a few` share (34), `few_a` and `a_few_a` both hold just in
case exactly `θ` objects have both properties. -/
theorem few_and_aFew_iff {θ : ℕ} :
    Nonempty (GeneralWCDecr P (.atMost θ) Q) ∧ Nonempty (GeneralWCIncr P (.atLeast θ) Q) ↔
      #{x | P x ∧ Nonempty (Q x)} = θ := by
  rw [nonempty_generalWCDecr_iff (CardRel.antitone_atMost θ),
    nonempty_generalWCIncr_iff (CardRel.monotone_atLeast θ)]
  exact le_antisymm_iff.symm

open Classical in
/-- The objects with `P` split into those with `Q` and those precluding it. -/
private theorem card_add_card_neg (P : E → Prop) [DecidablePred P] (Q : Ppty E) :
    #{x | P x ∧ Nonempty (Q x)} + #{x | P x ∧ Nonempty (Q x → Empty)} = #{x | P x} := by
  have h' : #{x | P x ∧ Nonempty (Q x → Empty)} =
      countOn Finset.univ fun x ↦ P x ∧ ¬ Nonempty (Q x) :=
    congrArg Finset.card <| Finset.filter_congr fun _ _ ↦ and_congr_right fun _ ↦
      ⟨fun ⟨g⟩ ⟨q⟩ ↦ (g q).elim, fun h ↦ ⟨fun q ↦ (h ⟨q⟩).elim⟩⟩
  rw [h']
  exact (countOn_decompose Finset.univ P fun a ↦ Nonempty (Q a)).symm

/-- The particular condition for `few_a` (85) is witnessed iff the general one (79) is: its
complement witness set (81) leaves at most `θ` objects with `P` that may have `Q`. -/
theorem nonempty_particularWCNeg_compAtMost_iff {θ : ℕ} :
    Nonempty (ParticularWCNeg P (.compAtMost θ) Q) ↔ Nonempty (GeneralWCDecr P (.atMost θ) Q) := by
  rw [nonempty_generalWCIncr_iff (CardRel.monotone_compAtMost θ),
    nonempty_generalWCDecr_iff (CardRel.antitone_atMost θ)]
  have := card_add_card_neg P Q
  simp only [CardRel.compAtMost, CardRel.atMost]
  omega

/-- The particular condition for `few_p` (86) is witnessed iff the general one (80) is. -/
theorem nonempty_particularWCNeg_compPropAtMost_iff {n d : ℕ} :
    Nonempty (ParticularWCNeg P (.compPropAtMost n d) Q) ↔
      Nonempty (GeneralWCDecr P (.propAtMost n d) Q) := by
  classical
  rw [nonempty_generalWCIncr_iff (CardRel.monotone_compPropAtMost n d),
    nonempty_generalWCDecr_iff (CardRel.antitone_propAtMost n d)]
  have hkm := card_add_card_neg P Q
  simp only [CardRel.compPropAtMost, CardRel.propAtMost]
  refine and_congr_right fun _ ↦ ?_
  generalize #{x | P x ∧ Nonempty (Q x)} = k at *
  generalize #{x | P x ∧ Nonempty (Q x → Empty)} = m at *
  generalize #{x | P x} = p at *
  subst hkm
  rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add]
  omega

/-- The set-based `no`, the witness set of every object with `P` each precluding `Q`, is
witnessed iff the particular condition (70) is. -/
theorem nonempty_particularWCNeg_every_iff :
    Nonempty (ParticularWCNeg P .every Q) ↔ Nonempty (ParticularWCNo (fun a ↦ PLift (P a)) Q) :=
  nonempty_generalWCIncr_every_iff.trans
    ⟨fun h ↦ ⟨⟨fun a p ↦ (h a p.down).some⟩⟩, fun ⟨w⟩ a p ↦ ⟨w.f a ⟨p⟩⟩⟩

/-- The particular condition for `exist` (63) gives the general one (60), with the singleton
of its individual. -/
def ParticularWCExist.toGeneralWCIncr [DecidableEq E] {R : Ppty E} (w : ParticularWCExist R Q)
    (h : ∀ a, R a → P a) : GeneralWCIncr P .exist Q :=
  ⟨{w.x}, ⟨Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h _ w.pWit⟩),
    Finset.card_singleton _⟩, fun _ ha ↦ (Finset.mem_singleton.1 ha).symm ▸ w.qWit⟩

/-- The particular condition for `no` (70) gives the general one (67), with the empty witness
set. -/
def ParticularWCNo.toGeneralWCDecr {R : Ppty E} (w : ParticularWCNo R Q) (h : ∀ a, P a → R a) :
    GeneralWCDecr P .no Q :=
  ⟨∅, ⟨Finset.empty_subset _, Finset.card_empty⟩, fun a hP ⟨q⟩ ↦ (w.f a (h a hP) q).elim⟩

end WitnessCondition

/-! ### Anaphora sets (§7.4.1)

Which anaphora sets a quantified noun phrase makes available follows from the paths a witness
for its content provides: the content's `restr` field is the property's extension, MAXSET;
the individual of the particular condition for `exist` and the witness set of (59a) are
objects with both properties (`GeneralWCIncr.X_subset`), REFSET; and the witness set of a
condition with negated scope, the particular conditions for `no` and `few`, is objects with
the first property and not the second (`ParticularWCNeg.X_subset`), COMPSET. The witness set
of (59b) lies within the first property and contains every object with both
(`GeneralWCDecr.X_subset`, `GeneralWCDecr.subset_X`); Cooper takes it too to predict REFSET.
The labels REFSET, MAXSET and COMPSET are Moxey and Sanford's [moxey-sanford-1987], as Cooper
attributes them (p. 313). -/

/-- Anaphora-set kinds reachable from a quantified noun phrase. -/
inductive AnaphoraRef where
  /-- REFSET: the witness individual or set ("A dog barked. It heard an intruder.", (103d)). -/
  | refset
  /-- MAXSET: the full extension ("A dog barked. They do when they notice an intruder.",
  (103a)). -/
  | maxset
  /-- COMPSET: the complement witness set ("Few dogs barked. They did not hear the
  intruder.", (113d)). -/
  | compset
  deriving DecidableEq, Repr

/-- The witness conditions of §7.4 by the paths their witnesses provide. -/
inductive WitnessCondition where
  /-- (59a): a witness set and a function from it into the scope. -/
  | generalIncr
  /-- (59b): a witness set and a function into it from the objects with both properties. -/
  | generalDecr
  /-- (63): an individual with both properties. -/
  | particularExist
  /-- (70): the set of all objects with the first property, each precluding the scope. -/
  | particularNo
  /-- (85)–(86): a complement witness set, each member precluding the scope. -/
  | particularFewComp
  deriving DecidableEq, Repr

/-- The anaphora set a condition's witness provides beyond the content's `restr` field. -/
def WitnessCondition.anaphora : WitnessCondition → AnaphoraRef
  | .generalIncr | .generalDecr | .particularExist => .refset
  | .particularNo | .particularFewComp => .compset

/-- The English fragment's quantifier names. -/
inductive QuantName where
  | exist | existPl | no | every | most | many | few | aFew
  deriving DecidableEq, Repr

/-- The witness conditions §7.4 uses for each quantifier relation: the particular ones for
`exist` (63) and `no` (70), the general one elsewhere, and for `few` the general (79)–(80)
and the particular (85)–(86) as alternatives. -/
def QuantName.conditions : QuantName → List WitnessCondition
  | .exist => [.particularExist]
  | .existPl | .every | .most | .many | .aFew => [.generalIncr]
  | .no => [.particularNo]
  | .few => [.generalDecr, .particularFewComp]

/-- The anaphora sets a quantified noun phrase makes available: MAXSET from the content's
`restr` field, and the set of each of its witness conditions. -/
def anaphoraAvailable (q : QuantName) : List AnaphoraRef :=
  .maxset :: q.conditions.map WitnessCondition.anaphora

/-! ### The dogs fragment

With `dog'` and `bark'` the properties (61a–b), a witness for `exist(dog', bark')` under the
particular condition (63) is a dog that barks, whose `x`-field is what *it* picks up in
*A dog is barking. It is right outside my window* (64); under the particular condition for
`no` (70), *No dog barked. They were all busy gnawing on a bone* (71) has *they* pick up the
witness set of every dog, complement set anaphora; and under the general condition for
`most` (74), *they* in (75) picks up the witness set of most dogs. The properties are
decidable predicates lifted to types, as the set-based conditions require. -/

namespace Dogs

/-- The individuals. -/
inductive Ind
  | fido | rex | spot | luna
  deriving DecidableEq, Repr, Fintype

/-- Fido, Rex and Spot are dogs. -/
def IsDog (x : Ind) : Prop := x ≠ .luna

instance : DecidablePred IsDog := fun _ ↦ by unfold IsDog; infer_instance

/-- Fido and Spot bark. -/
def Bark (x : Ind) : Prop := x = .fido ∨ x = .spot

instance : DecidablePred Bark := fun _ ↦ by unfold Bark; infer_instance

/-- The property `dog'` (61a). -/
def dog : Ppty Ind := fun x ↦ PLift (IsDog x)

/-- The property `bark'` (61b). -/
def bark : Ppty Ind := fun x ↦ PLift (Bark x)

/-- *A dog barks* (63): Fido. -/
def aDogBarks : SemIndefArt dog bark := ⟨.fido, ⟨nofun⟩, ⟨.inl rfl⟩⟩

/-- *No dog barks* is false: Fido is a dog that barks. -/
theorem noDogBarks_isEmpty : IsEmpty (SemNo dog bark) :=
  ⟨fun ⟨f⟩ ↦ (f .fido ⟨nofun⟩ ⟨.inl rfl⟩).elim⟩

/-- *No dog barks* with the witness set of every dog, whose members *they* picks up in (71), is
false as well. -/
theorem noDogBarksSet_isEmpty : IsEmpty (ParticularWCNeg IsDog .every bark) :=
  ⟨fun w ↦ (nonempty_particularWCNeg_every_iff.1 ⟨w⟩).elim noDogBarks_isEmpty.false⟩

/-- *Most dogs bark* (74): the witness set of Fido and Spot, two of the three dogs, each
barking, which *they* picks up in (75). The threshold `3 / 5` lies in the range
`.5 < θ_most(P) < 1` of the book's appendix type list. -/
def mostDogsBark : GeneralWCIncr IsDog (.propAtLeast 3 5) bark :=
  ⟨{.fido, .spot}, ⟨by decide, by simp only [CardRel.propAtLeast]; decide⟩,
    fun a ha ↦ ⟨by revert a; decide⟩⟩

/-- (50): the same witness set by its probability, two thirds of the dogs. -/
theorem mostDogsBark_condProb : (3 : ℚ) / 5 ≤ condProb mostDogsBark.X {x | IsDog x} :=
  (witnessType_propAtLeast_iff (by decide) mostDogsBark.witness.1 (by decide)).1
    mostDogsBark.witness

/-- *Few dogs barked. They didn't hear the intruder* (87), under the particular condition for
`few_p` (86) with `θ_fewp = 2 / 3`: the complement witness set of Rex, who does not bark. -/
def fewDogsBark : ParticularWCNeg IsDog (.compPropAtMost 2 3) bark :=
  ⟨{.rex}, ⟨by decide, by simp only [CardRel.compPropAtMost]; decide⟩,
    fun a ha ⟨h⟩ ↦ absurd h (Finset.mem_singleton.1 ha ▸ by decide)⟩

/-- The same content under the general condition (80): at most two thirds of the dogs bark. -/
theorem fewDogsBark_general : Nonempty (GeneralWCDecr IsDog (.propAtMost 2 3) bark) :=
  nonempty_particularWCNeg_compPropAtMost_iff.1 ⟨fewDogsBark⟩

/-- The types judged. -/
inductive Ty
  | dog | bark
  deriving DecidableEq, Repr

/-- An experience base of three dogs, two of which were judged to bark. -/
def experience : ExperienceBase Ind Ty :=
  {(.fido, .dog), (.rex, .dog), (.spot, .dog), (.fido, .bark), (.spot, .bark)}

/-- The estimate `p_𝔍(bark ‖ dog)` is two thirds. -/
theorem bark_given_dog : experience.estimate .bark .dog = 2 / 3 := rfl

end Dogs

/-! ## Type-based underspecification (Ch. 8)

The content of an utterance is raised to a type of contents, the readings being the closure
of the compositional content under the operations of this section. Storage puts a
parametric quantifier into the context's store, leaving in its place the content of a label's
value (17), and retrieval quantifies it back in over the content as a property of that
value (19). Anaphoric combination identifies a pronoun's label with an antecedent's (28)
unless the pronoun is marked local, the marking cleared at the sentence boundary (77);
reflexives are marked (83), bound by reflexivisation (84) and required to be bound at the
verb phrase (85)–(88). Donkey anaphora goes through localisation (49), which folds the
context into the property's domain so that the indefinite's witness in the restrictor can be
aligned with the pronoun (51)–(52); `𝔓` then gives the weak reading (55)–(59) and `𝔓∀` the
strong one (60)–(66), quantifying over farmers and not farmer–donkey pairs. -/

/-! ### Parametric contents and their context types (§8.2–8.3) -/

/-- A context type (§4.3, (16); §8.3, (82)): the labels a content requires the context to
assign to stored quantifiers, `𝔮`, and to pronouns, `𝔰`, and among the latter those marked
local, `𝔩`, and reflexive, `𝔯`. -/
structure CntxtType where
  /-- The labels of stored quantifiers, `𝔮`. -/
  stored : Finset ℕ
  /-- The labels of pronouns, `𝔰`. -/
  pronouns : Finset ℕ
  /-- The labels of pronouns marked local, `𝔩`. -/
  locals : Finset ℕ
  /-- The labels of reflexives, `𝔯`. -/
  reflexives : Finset ℕ
  deriving DecidableEq

namespace CntxtType

/-- The merge of two context types. -/
instance : Max CntxtType :=
  ⟨fun a b ↦ ⟨a.stored ∪ b.stored, a.pronouns ∪ b.pronouns, a.locals ∪ b.locals,
    a.reflexives ∪ b.reflexives⟩⟩

/-- The context type requiring nothing. -/
instance : Bot CntxtType := ⟨⟨∅, ∅, ∅, ∅⟩⟩

/-- `T ⊖ xᵢ` (18): the label removed from every field. -/
def erase (T : CntxtType) (i : ℕ) : CntxtType :=
  ⟨T.stored.erase i, T.pronouns.erase i, T.locals.erase i, T.reflexives.erase i⟩

end CntxtType

/-- A parametric content (14) over the contexts of Ch. 8, assignments of individuals to
labels: its background context type and its foreground, a content for each assignment. -/
structure Content (E : Type) (C : Type*) where
  /-- The background: the context type the content requires. -/
  bg : CntxtType
  /-- The foreground: the content under each assignment. -/
  fg : (ℕ → E) → C

namespace Content

variable {C D : Type*}

/-- Application `α @ β` of a functor content to an argument, the backgrounds merged. -/
def app (α : Content E (C → D)) (β : Content E C) : Content E D :=
  ⟨α.bg ⊔ β.bg, fun g ↦ α.fg g (β.fg g)⟩

/-- The content given a value for a label, the context specification `c[𝔰.xᵢ = a]` behind
retrieval (19), reflexivisation (84) and the alignment of a pronoun with its antecedent
(42)–(44). -/
def given (α : Content E C) (i : ℕ) (a : E) : Content E C :=
  ⟨α.bg.erase i, fun g ↦ α.fg (Function.update g i a)⟩

/-- Storage (17): a stored quantifier leaves in its place the content of its label's value,
required of the store and of the pronoun assignment. -/
def store (i : ℕ) : Content E (Quant E) := ⟨⟨{i}, {i}, ∅, ∅⟩, fun g ↦ SemPropName (g i)⟩

/-- A pronoun (75): the content of its label's value, marked local. -/
def pronoun (i : ℕ) : Content E (Quant E) := ⟨⟨∅, {i}, {i}, ∅⟩, fun g ↦ SemPropName (g i)⟩

/-- A reflexive (83): the content of its label's value, marked reflexive. -/
def reflexive (i : ℕ) : Content E (Quant E) := ⟨⟨∅, {i}, ∅, {i}⟩, fun g ↦ SemPropName (g i)⟩

/-- Retrieval (19): the stored quantifier takes scope over the content as a property of the
label's value, the label discharged. -/
def retrieve (𝒬 : Content E (Quant E)) (i : ℕ) (α : Content E Type) : Content E Type :=
  ⟨𝒬.bg ⊔ α.bg.erase i, fun g ↦ 𝒬.fg g fun a ↦ (α.given i a).fg g⟩

/-- The relabelling `[α]𝔰.xⱼ ⇝ 𝔰.xᵢ`: the content reads the label `j` as `i`, and the
background drops `j`. -/
def relabel (α : Content E C) (j i : ℕ) : Content E C :=
  ⟨α.bg.erase j, fun g ↦ α.fg (Function.update g j (g i))⟩

/-- Anaphoric combination `α @ᵢ,ⱼ β` (28), (76) is defined when the functor requires the
label `i` and the argument requires `j` as a pronoun that is neither a stored quantifier's
nor marked local. -/
def AnaphoricDefined (α : Content E (C → D)) (i j : ℕ) (β : Content E C) : Prop :=
  i ∈ α.bg.pronouns ∧ j ∈ β.bg.pronouns ∧ j ∉ β.bg.stored ∧ j ∉ β.bg.locals

instance (α : Content E (C → D)) (i j : ℕ) (β : Content E C) :
    Decidable (α.AnaphoricDefined i j β) := by
  unfold AnaphoricDefined; infer_instance

/-- Anaphoric combination `α @ᵢ,ⱼ β` (28): the application with `j` relabelled to `i`. -/
def anaphoricApp (α : Content E (C → D)) (i j : ℕ) (β : Content E C) : Content E D :=
  (α.app β).relabel j i

/-- The boundary operation `B` (77): the local marking is cleared at the sentence. -/
def boundary (α : Content E C) : Content E C := ⟨{ α.bg with locals := ∅ }, α.fg⟩

/-- Reflexivisation `ℜ` (84): the reflexive `i` is bound to the property's argument, its
label discharged and all reflexive marking cleared. -/
def reflexivize (P : Content E (Ppty E)) (i : ℕ) : Content E (Ppty E) :=
  ⟨{ P.bg.erase i with reflexives := ∅ }, fun g x ↦ (P.given i x).fg g x⟩

/-- Principle A (85): a content with a reflexive still marked is excluded at the verb
phrase (88). -/
def IsAnaphorFree (α : Content E C) : Prop := α.bg.reflexives = ∅

instance (α : Content E C) : Decidable α.IsAnaphorFree := by
  unfold IsAnaphorFree; infer_instance

end Content

/-! #### *Every boy hugged a dog* (§8.1, (1))

Two boys each hugging a different dog: the reading (1a) with the quantifiers in surface
order is witnessed, and the reading (1b), the object quantifier stored and retrieved over
the sentence, is not. -/

namespace Hugging

/-- The individuals. -/
inductive Ind
  | tom | bill | fido | rex
  deriving DecidableEq

/-- Tom and Bill are boys. -/
def Boy : Ppty Ind
  | .tom | .bill => PUnit
  | _ => Empty

/-- Fido and Rex are dogs. -/
def Dog : Ppty Ind
  | .fido | .rex => PUnit
  | _ => Empty

/-- Tom hugs Fido, Bill hugs Rex. -/
def Hug : Ind → Ind → Type
  | .tom, .fido | .bill, .rex => PUnit
  | _, _ => Empty

/-- *every boy*, requiring nothing of the context. -/
def everyBoy : Content Ind (Quant Ind) := ⟨⊥, fun _ ↦ SemUniversal Boy⟩

/-- *a dog*, requiring nothing of the context. -/
def aDog : Content Ind (Quant Ind) := ⟨⊥, fun _ ↦ SemIndefArt Dog⟩

/-- *hugged*, a transitive verb over its object quantifier (Ch. 6, (63)). -/
def hugged : Content Ind (Quant Ind → Ppty Ind) := ⟨⊥, fun _ Q x ↦ Q (Hug x)⟩

/-- (1a): the quantifiers in surface order. -/
def surface : Content Ind Type := everyBoy.app (hugged.app aDog)

/-- (1b): the object quantifier stored (17) and retrieved (19) over the sentence. -/
def inverse : Content Ind Type := aDog.retrieve 0 (everyBoy.app (hugged.app (Content.store 0)))

/-- Neither reading depends on the context. -/
theorem surface_bg : surface.bg = ⊥ := rfl

/-- Retrieval discharges what storage required. -/
theorem inverse_bg : inverse.bg = ⊥ := rfl

/-- (1a) is witnessed: every boy is such that there is a dog he hugged. -/
def surfaceWitness (g : ℕ → Ind) : surface.fg g
  | .tom, _ => ⟨.fido, ⟨⟩, ⟨⟩⟩
  | .bill, _ => ⟨.rex, ⟨⟩, ⟨⟩⟩
  | .fido, h => nomatch h
  | .rex, h => nomatch h

/-- (1b) is not: there is no dog every boy hugged. -/
theorem inverse_isEmpty (g : ℕ → Ind) : IsEmpty (inverse.fg g) :=
  ⟨fun | ⟨.fido, _, h⟩ => nomatch h .bill ⟨⟩ | ⟨.rex, _, h⟩ => nomatch h .tom ⟨⟩
       | ⟨.tom, h, _⟩ => nomatch h | ⟨.bill, h, _⟩ => nomatch h⟩

end Hugging

/-! ### Localisation and donkey anaphora (§8.3) -/

/-- Localisation `ℒ` (49): the context a parametric property requires is folded into the
property's domain under the label `𝔠`, giving a restricted property. -/
def localize (P : PPpty E) : Restricted E := ⟨fun _ ↦ P.bg, fun x c ↦ P.fg c x⟩

/-! #### *No dog which chases a cat catches it* (46a)

The scope is the localised *catches it* restricted by the restrictor and aligned so that the
caught cat is the chased one (50)–(51); under the particular condition for `no` the sentence
(55) says that every dog which chases a cat fails to be a dog which chases a cat and catches
it. -/

namespace Chasing

/-- The individuals. -/
inductive Ind
  | dog₁ | dog₂ | cat₁ | cat₂
  deriving DecidableEq

/-- The dogs. -/
def Dog : Ppty Ind
  | .dog₁ | .dog₂ => PUnit
  | _ => Empty

/-- The cats. -/
def Cat : Ppty Ind
  | .cat₁ | .cat₂ => PUnit
  | _ => Empty

/-- Each dog chases one cat. -/
def Chase : Ind → Ind → Type
  | .dog₁, .cat₁ | .dog₂, .cat₂ => PUnit
  | _, _ => Empty

/-- *catches it* (47): the pronoun's referent supplied by the context. -/
def catchesIt (Catch : Ind → Ind → Type) : PPpty Ind := ⟨Ind, fun y x ↦ Catch x y⟩

/-- *dog which chases a cat*, the restrictor, as the domain of (50): a dog with a cat it
chases. -/
def DogChasesACat : Ppty Ind := fun x ↦ Dog x × ((c : Ind) × Cat c × Chase x c)

/-- The scope (51): *catches it* localised, restricted by the restrictor and aligned so that
`it` is the chased cat. -/
def scope (Catch : Ind → Ind → Type) : Restricted Ind :=
  ((localize (catchesIt Catch)).restrictBy DogChasesACat).align DogChasesACat
    fun _ r ↦ (r, r.2.1)

/-- (55): `no(restr, scope)` with the scope purified. -/
def Sentence (Catch : Ind → Ind → Type) : Type := SemNo DogChasesACat (Purify (scope Catch))

/-- True when no dog catches anything. -/
def noCatching : Sentence (fun _ _ ↦ Empty) := ⟨fun _ _ ⟨_, h⟩ ↦ h⟩

/-- False when every dog catches the cat it chases. -/
theorem sentence_isEmpty : IsEmpty (Sentence Chase) :=
  ⟨fun ⟨f⟩ ↦ (f .dog₁ ⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩).elim⟩

end Chasing

/-! #### *Every farmer who owns a donkey likes it* (58)–(66)

The localised *likes it* restricted by *farmer who owns a donkey* and aligned (65) is the
property of being a farmer who owns a donkey and likes that donkey; its purification `𝔓`
gives the weak reading, some donkey she owns, and `𝔓∀` (66) the strong one, every donkey
she owns, the readings of [kanazawa-1994]. A farmer who owns two donkeys and likes one
separates them. -/

namespace Donkeys

/-- The individuals. -/
inductive Ind
  | farmer₁ | farmer₂ | donkey₁ | donkey₂
  deriving DecidableEq

/-- The farmers. -/
def Farmer : Ppty Ind
  | .farmer₁ | .farmer₂ => PUnit
  | _ => Empty

/-- The donkeys. -/
def Donkey : Ppty Ind
  | .donkey₁ | .donkey₂ => PUnit
  | _ => Empty

/-- The first farmer owns both donkeys, the second the second. -/
def Own : Ind → Ind → Type
  | .farmer₁, .donkey₁ | .farmer₁, .donkey₂ | .farmer₂, .donkey₂ => PUnit
  | _, _ => Empty

/-- Each farmer likes one donkey. -/
def Like : Ind → Ind → Type
  | .farmer₁, .donkey₁ | .farmer₂, .donkey₂ => PUnit
  | _, _ => Empty

/-- *farmer who owns a donkey*. -/
def FarmerOwnsADonkey : Ppty Ind := fun x ↦ Farmer x × ((d : Ind) × Donkey d × Own x d)

/-- *likes it* (61), localised (62)–(63), restricted (64) and aligned (65). -/
def likesIt : Restricted Ind :=
  ((localize ⟨Ind, fun y x ↦ Like x y⟩).restrictBy FarmerOwnsADonkey).align FarmerOwnsADonkey
    fun _ r ↦ (r, r.2.1)

/-- The weak reading (59): every farmer who owns a donkey likes some donkey she owns. -/
def weak : SemUniversal FarmerOwnsADonkey (Purify likesIt)
  | .farmer₁, _ => ⟨⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .farmer₂, _ => ⟨⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .donkey₁, ⟨h, _⟩ => nomatch h
  | .donkey₂, ⟨h, _⟩ => nomatch h

/-- The strong reading (60), (66) fails: the first farmer does not like the second donkey. -/
theorem strong_isEmpty : IsEmpty (SemUniversal FarmerOwnsADonkey (PurifyUniv likesIt)) :=
  ⟨fun f ↦ nomatch f .farmer₁ ⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩⟩

end Donkeys

/-! ### Pronouns, locality and reflexives (30)–(36), (67)–(88)

With the subject stored, its label is available for anaphoric combination with the pronoun
of *thinks she failed*, whose local marking the embedded sentence's boundary has cleared;
retrieval then quantifies over the property of being a girl who thinks she failed, (36c).
In *Sam likes him* the pronoun is still marked local when the subject combines, so the
combination is undefined, Principle B; *likes himself* reflexivised is `like(x, x)`, its
marking cleared for the verb phrase's filter, which excludes the reflexive left unbound,
Principle A. -/

namespace Binding

/-- The individuals. -/
inductive Ind
  | sam | kim | ann
  deriving DecidableEq

/-- Ann is the girl. -/
def Girl : Ppty Ind
  | .ann => PUnit
  | _ => Empty

/-- Nobody failed. -/
inductive Fail : Ind → Type

/-- Sam likes himself. -/
inductive Like : Ind → Ind → Type
  | mk : Like .sam .sam

/-- `think(x, T)`: a thought with the type's witness. -/
structure Think (x : Ind) (T : Type) where
  thought : T

/-- *Sam* (70), requiring nothing of the context. -/
def sam : Content Ind (Quant Ind) := ⟨⊥, fun _ ↦ SemPropName .sam⟩

/-- *no girl* (33). -/
def noGirl : Content Ind (Quant Ind) := ⟨⊥, fun _ ↦ SemNo Girl⟩

/-- *failed*. -/
def failed : Content Ind (Ppty Ind) := ⟨⊥, fun _ ↦ Fail⟩

/-- *thinks*, over a ptype of thinking. -/
def thinks : Content Ind (Type → Ppty Ind) := ⟨⊥, fun _ T x ↦ Think x T⟩

/-- *likes*, a transitive verb over its object quantifier (Ch. 6, (63)). -/
def likes : Content Ind (Quant Ind → Ppty Ind) := ⟨⊥, fun _ Q x ↦ Q (Like x)⟩

/-- *thinks she failed* (31): *she failed* a sentence, its pronoun no longer local past the
boundary. -/
def thinksSheFailed : Content Ind (Ppty Ind) :=
  thinks.app (Content.boundary ((Content.pronoun 1).app failed))

/-- The stored subject (34) combines anaphorically with the pronoun, (35). -/
theorem anaphoricDefined_thinksSheFailed :
    (Content.store 0).AnaphoricDefined 0 1 thinksSheFailed := by
  decide

/-- Without the boundary of the embedded sentence the pronoun would still be local. -/
theorem not_anaphoricDefined_of_no_boundary :
    ¬ (Content.store 0).AnaphoricDefined 0 1 (thinks.app ((Content.pronoun 1).app failed)) := by
  decide

/-- *No girl thinks she failed* (36): the stored *no girl* retrieved over the anaphoric
combination is `no(girl', λx. think(x, fail(x)))`. -/
theorem noGirlThinksSheFailed (g : ℕ → Ind) :
    (noGirl.retrieve 0 ((Content.store 0).anaphoricApp 0 1 thinksSheFailed)).fg g =
      SemNo Girl (fun x ↦ Think x (Fail x)) :=
  rfl

/-- *likes him* (69), the pronoun marked local. -/
def likesHim : Content Ind (Ppty Ind) := likes.app (Content.pronoun 1)

/-- (72)–(73): *him* cannot be related to the stored *Sam* (71) within the clause,
Principle B. -/
theorem not_anaphoricDefined_likesHim : ¬ (Content.store 0).AnaphoricDefined 0 1 likesHim := by
  decide

/-- *likes himself* reflexivised (84). -/
def likesHimself : Content Ind (Ppty Ind) := (likes.app (Content.reflexive 1)).reflexivize 1

/-- (68c): the reflexivised property is `like(x, x)`. -/
theorem likesHimself_fg (g : ℕ → Ind) (x : Ind) : likesHimself.fg g x = Like x x := rfl

/-- Reflexivisation clears the marking for the verb phrase's filter (88). -/
theorem isAnaphorFree_likesHimself : likesHimself.IsAnaphorFree := by decide

/-- The filter excludes the reflexive left unbound. -/
theorem not_isAnaphorFree_likesReflexive : ¬ (likes.app (Content.reflexive 1)).IsAnaphorFree := by
  decide

/-- *Sam likes himself* (73), the stored *Sam* retrieved, is witnessed by Sam's liking
himself. -/
def samLikesHimself (g : ℕ → Ind) : (sam.retrieve 0 ((Content.store 0).app likesHimself)).fg g :=
  Like.mk

end Binding

/-! #### *A man walked. He whistled.* (37)–(44)

The pronoun's label is identified with the man of the previous utterance's witness (42) and
the dependency on the label replaced by one on the man (43)–(44). -/

namespace Whistling

/-- The individuals. -/
inductive Ind
  | john | mary
  deriving DecidableEq

/-- John is a man. -/
def Man : Ppty Ind
  | .john => PUnit
  | .mary => Empty

/-- John walks. -/
def Walk : Ppty Ind
  | .john => PUnit
  | .mary => Empty

/-- John whistles. -/
def Whistle : Ppty Ind
  | .john => PUnit
  | .mary => Empty

/-- The content of *a man walked* under the particular condition for `exist` (38). -/
def AManWalked : Type := SemIndefArt Man Walk

/-- John walked. -/
def aManWalked : AManWalked := ⟨.john, ⟨⟩, ⟨⟩⟩

/-- *he whistled* (39): the pronoun's label required of the context. -/
def heWhistled : Content Ind Type :=
  Content.boundary ((Content.pronoun 0).app ⟨⊥, fun _ ↦ Whistle⟩)

/-- (42)–(44): given the previous utterance's witness, the pronoun's label is no longer
required and the content is that the man whistled. -/
theorem heWhistled_given (w : AManWalked) (g : ℕ → Ind) :
    (heWhistled.given 0 w.x).bg = ⊥ ∧ (heWhistled.given 0 w.x).fg g = Whistle w.x :=
  ⟨rfl, rfl⟩

/-- The man of the previous utterance whistled. -/
def heWhistledWitness (g : ℕ → Ind) : (heWhistled.given 0 aManWalked.x).fg g := ⟨⟩

end Whistling

/-! ### The book's examples

A selection of the English examples of Chs. 3, 6, 7 and 8 are the rows of
`Data/Examples/Cooper2023.json`. The rows with a `quantifier` feature are the
discourse-anaphora examples of §7.4, §7.4.1 and §8.3, each reading named by the anaphora
set the pronoun picks up. -/

/-- The quantifier relation a row's determiner names. -/
def quantNames : List (String × QuantName) :=
  [("a", .exist), ("some", .existPl), ("no", .no), ("every", .every), ("most", .most),
    ("many", .many), ("few", .few), ("a few", .aFew)]

/-- The anaphora set a reading names. -/
def anaphoraRefs : List (String × AnaphoraRef) :=
  [("refset", .refset), ("maxset", .maxset), ("compset", .compset)]

/-- A reading of a pronoun with a quantified antecedent is acceptable exactly when a witness
for the content provides a path to its anaphora set. -/
theorem anaphora_rows : ∀ row ∈ Examples.all, ∀ v ∈ row.feature? "quantifier",
    ∃ q ∈ quantNames.lookup v, ∀ r ∈ row.readings,
      ∃ ref ∈ anaphoraRefs.lookup r.1, (r.2 = .acceptable ↔ ref ∈ anaphoraAvailable q) := by
  decide

end Cooper2023
