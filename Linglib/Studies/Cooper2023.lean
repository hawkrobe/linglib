import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Quantification.Witness
import Linglib.Data.Examples.Cooper2023

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
* The indefinite article and *no* are the particular witness conditions of
  `Semantics/Quantification/Witness.lean`, and the dogs fragment uses its set-based
  conditions over decidable predicates; modal type systems and Breitholtz's topoi stay
  here, having no second consumer.
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
* Purification is determiner-independent, so both donkey readings are predicted for every
  determiner; the experimental record of [denic-sudo-2022] on non-monotonic determiners and
  the question-based selection of [champollion-bumford-henderson-2019] are the tests to
  state.

## References

* [R. Cooper, *From Perception to Communication* (2023)][cooper-2023]
* [J. Barwise, R. Cooper, *Generalized Quantifiers and Natural Language*
  (1981)][barwise-cooper-1981]
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

namespace Cooper2023

open Quantification

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
def SemPropName (a : E) : Quant E := λ P => P a

/-- `SemIndefArt` (37): a restrictor property to the existential quantifier over it, whose
witness under the particular condition of Ch. 7 (63) is an individual with the restrictor
and the scope. -/
def SemIndefArt (restr : Ppty E) : Quant E := ParticularWC_Exist restr

/-- (55): `exist(P, Q)` is witnessed iff the property extensions of `P` and `Q` overlap. -/
theorem nonempty_semIndefArt_iff (restr scope : Ppty E) :
    Nonempty (SemIndefArt restr scope) ↔ ∃ a, Nonempty (restr a) ∧ Nonempty (scope a) :=
  nonempty_particularWC_exist_iff restr scope

/-- `SemBe` (78), Montague's copula: the property of being the quantifier's witness. -/
def SemBe (Q : Quant E) : Ppty E := λ x => Q λ y => PLift (x = y)

/-- The universal quantifier as a function from the restrictor's witnesses to the scope's,
the function witness of §7.2.4 after [ranta-1994], which, as Cooper notes at (27), yields no
witness set for plural anaphora; the set-based condition (72) is `GeneralWC_Incr` with
`IsEveryW`. -/
def SemUniversal (restr scope : Ppty E) : Type := (x : E) → restr x → scope x

/-- `no(P, Q)` under its particular witness condition (Ch. 7, (70)): every witness of the
restrictor precludes the scope. -/
def SemNo (restr scope : Ppty E) : Type := ParticularWC_No restr scope

/-- (92): *a is a P*, the copula over the indefinite article, is witnessed iff `P(a)` is, so
the compositional content and the construction-based content of (86)–(87) are distinct but
equivalent types. -/
theorem nonempty_semBe_semIndefArt_iff (P : Ppty E) (a : E) :
    Nonempty (SemBe (SemIndefArt P) a) ↔ Nonempty (P a) :=
  ⟨λ ⟨⟨_, h, ⟨rfl⟩⟩⟩ => ⟨h⟩, λ ⟨h⟩ => ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

/-- (94c): *a P is a*, the quantifiers in the other order, is witnessed iff `P(a)` is as
well; only the construction expresses `P(a)` itself, and (89) *A conductor is Dudamel* is
odd. -/
theorem nonempty_semIndefArt_semBe_semPropName_iff (P : Ppty E) (a : E) :
    Nonempty (SemIndefArt P (SemBe (SemPropName a))) ↔ Nonempty (P a) :=
  ⟨λ ⟨⟨_, h, ⟨rfl⟩⟩⟩ => ⟨h⟩, λ ⟨h⟩ => ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

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
  ⟨λ | ⟨.dudamel, _, ⟨h⟩⟩ => nomatch h | ⟨.beethoven, h, _⟩ => nomatch h⟩

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
theorem equivI_of_equivR (h : ms.EquivR T₁ T₂) : ms.EquivI T₁ T₂ := λ p _ _ => h p

theorem subtypeI_of_subtypeR (h : ms.SubtypeR T₁ T₂) : ms.SubtypeI T₁ T₂ := λ p _ _ => h p

theorem necI_of_necR {T : Ty} (h : ms.NecR T) : ms.NecI T := λ p _ => h p

theorem possI_of_possR {T : Ty} (h : ms.PossR T) : ms.PossI T := h.imp λ _ hp _ => hp

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
  ⟨h.sit, h.sub, hne.map λ w => (w, h.incl w)⟩

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
def deontic : Topos := ⟨OnPlate, λ r => Eat r.y r.x⟩

/-- The bouletic topos τ₂ (28b). -/
def bouletic : Topos := ⟨Loves, λ r => Eat r.y r.x⟩

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
  | true => ⟨λ _ => True, λ | .rain, .a => True | .snow, .b => True | _, _ => False⟩
  | false => ⟨λ _ => True, λ | .rain, .a => True | _, _ => False⟩

/-- As `system`, but snow does not occur in the second possibility. -/
def restricted : ModalSystem Bool Ty Obj
  | true => ⟨λ _ => True, λ | .rain, .a => True | .snow, .b => True | _, _ => False⟩
  | false => ⟨(· = .rain), λ | .rain, .a => True | _, _ => False⟩

theorem necR_rain : system.NecR .rain := λ | true => ⟨.a, trivial⟩ | false => ⟨.a, trivial⟩

theorem possR_snow : system.PossR .snow := ⟨true, .b, trivial⟩

theorem not_necR_snow : ¬ system.NecR .snow := λ h => nomatch h false

theorem restricted_necI_snow : restricted.NecI .snow
  | true, _ => ⟨.b, trivial⟩
  | false, h => nomatch h

theorem restricted_not_necR_snow : ¬ restricted.NecR .snow := λ h => nomatch h false

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
def Purify (P : Restricted E) : Ppty E := λ x => (c : P.restr x) × P.body x c

/-- Universal purification `𝔓∀(P)` (13): the body under every way of meeting the
restriction. -/
def PurifyUniv (P : Restricted E) : Ppty E := λ x => (c : P.restr x) → P.body x c

/-- Alignment of paths in the domain (Ch. 8, (51)–(52)): a manifest field identifying two
paths is a further restriction of the domain, through which the body is read. -/
def Restricted.align (P : Restricted E) (R : E → Type) (f : ∀ x, R x → P.restr x) :
    Restricted E :=
  ⟨R, λ x c => P.body x (f x c)⟩

/-- Property restriction `P|ℱ` (Ch. 5, (98)): the domain narrowed by a property, the
alignment along the projection. -/
def Restricted.restrictBy (P : Restricted E) (R : Ppty E) : Restricted E :=
  P.align (λ x => R x × P.restr x) λ _ => Prod.snd

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
  exact ⟨λ ⟨c, hc⟩ c' => (u.uniq c).trans (u.uniq c').symm ▸ hc, λ hall => ⟨u.default, hall _⟩⟩

/-! ### Witness sets and probabilities (§7.3) -/

/-- The frequentist conditional probability (36) of one extension given another, `0` when
the condition is unwitnessed. -/
def condProb [DecidableEq E] (A B : Finset E) : ℚ := ((A ∩ B).card : ℚ) / B.card

/-- (51)–(52): for a witness set `X` of objects with the property, the probability of `𝔗(X)`
given `𝔗(P)` is the proportion `|X| / |[↓P]|`. -/
theorem condProb_of_subset [DecidableEq E] {X P : Finset E} (h : X ⊆ P) :
    condProb X P = (X.card : ℚ) / P.card := by
  rw [condProb, Finset.inter_eq_left.2 h]

/-- (50): the probabilistic witness condition for *most* is the cardinal one (29). -/
theorem isMostW_iff [Fintype E] [DecidableEq E] {P : E → Prop} [DecidablePred P]
    {θ_num θ_denom : ℕ} (hθ : 0 < θ_denom) {X : Finset E} (hX : WitnessSet P X)
    (hP : 0 < (fullExtFinset P).card) :
    IsMostW P θ_num θ_denom X ↔ (θ_num : ℚ) / θ_denom ≤ condProb X (fullExtFinset P) := by
  have hsub : X ⊆ fullExtFinset P := λ a ha =>
    Finset.mem_filter.2 ⟨Finset.mem_univ a, hX.subset a ha⟩
  rw [condProb_of_subset hsub, div_le_div_iff₀ (by exact_mod_cast hθ) (by exact_mod_cast hP)]
  exact ⟨λ h => by exact_mod_cast h.proportion, λ h => ⟨hX, hP, by exact_mod_cast h⟩⟩

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

/-! ### Witness conditions and anaphora (§7.4)

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

instance : DecidablePred IsDog := λ _ => by unfold IsDog; infer_instance

/-- Fido and Spot bark. -/
def Bark (x : Ind) : Prop := x = .fido ∨ x = .spot

instance : DecidablePred Bark := λ _ => by unfold Bark; infer_instance

/-- The property `dog'` (61a). -/
def dog : Ppty Ind := λ x => PLift (IsDog x)

/-- The property `bark'` (61b). -/
def bark : Ppty Ind := λ x => PLift (Bark x)

/-- *A dog barks* (63): Fido. -/
def aDogBarks : SemIndefArt dog bark := ⟨.fido, ⟨nofun⟩, ⟨.inl rfl⟩⟩

/-- *No dog barks* is false: Fido is a dog that barks. -/
theorem noDogBarks_isEmpty : IsEmpty (SemNo dog bark) :=
  ⟨λ ⟨f⟩ => (f .fido ⟨nofun⟩ ⟨.inl rfl⟩).elim⟩

/-- *Most dogs bark* (74): the witness set of Fido and Spot, more than half of the dogs, each
barking, which *they* picks up in (75). -/
def mostDogsBark : GeneralWC_Incr dog bark (IsMostW IsDog 1 2) :=
  ⟨{.fido, .spot}, ⟨⟨by decide⟩, by decide, by decide⟩, λ a ha => ⟨by revert a; decide⟩⟩

/-- (50): the same witness set by its probability, two thirds of the dogs. -/
theorem mostDogsBark_condProb :
    (1 : ℚ) / 2 ≤ condProb mostDogsBark.X (fullExtFinset IsDog) :=
  (isMostW_iff (by decide) mostDogsBark.witnessOK.toWitnessSet (by decide)).1
    mostDogsBark.witnessOK

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
  ⟨λ a b => ⟨a.stored ∪ b.stored, a.pronouns ∪ b.pronouns, a.locals ∪ b.locals,
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
  ⟨α.bg ⊔ β.bg, λ g => α.fg g (β.fg g)⟩

/-- The content given a value for a label, the context specification `c[𝔰.xᵢ = a]` behind
retrieval (19), reflexivisation (84) and the alignment of a pronoun with its antecedent
(42)–(44). -/
def given (α : Content E C) (i : ℕ) (a : E) : Content E C :=
  ⟨α.bg.erase i, λ g => α.fg (Function.update g i a)⟩

/-- Storage (17): a stored quantifier leaves in its place the content of its label's value,
required of the store and of the pronoun assignment. -/
def store (i : ℕ) : Content E (Quant E) := ⟨⟨{i}, {i}, ∅, ∅⟩, λ g => SemPropName (g i)⟩

/-- A pronoun (75): the content of its label's value, marked local. -/
def pronoun (i : ℕ) : Content E (Quant E) := ⟨⟨∅, {i}, {i}, ∅⟩, λ g => SemPropName (g i)⟩

/-- A reflexive (83): the content of its label's value, marked reflexive. -/
def reflexive (i : ℕ) : Content E (Quant E) := ⟨⟨∅, {i}, ∅, {i}⟩, λ g => SemPropName (g i)⟩

/-- Retrieval (19): the stored quantifier takes scope over the content as a property of the
label's value, the label discharged. -/
def retrieve (𝒬 : Content E (Quant E)) (i : ℕ) (α : Content E Type) : Content E Type :=
  ⟨𝒬.bg ⊔ α.bg.erase i, λ g => 𝒬.fg g λ a => (α.given i a).fg g⟩

/-- The relabelling `[α]𝔰.xⱼ ⇝ 𝔰.xᵢ`: the content reads the label `j` as `i`, and the
background drops `j`. -/
def relabel (α : Content E C) (j i : ℕ) : Content E C :=
  ⟨α.bg.erase j, λ g => α.fg (Function.update g j (g i))⟩

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
  ⟨{ P.bg.erase i with reflexives := ∅ }, λ g x => (P.given i x).fg g x⟩

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
def everyBoy : Content Ind (Quant Ind) := ⟨⊥, λ _ => SemUniversal Boy⟩

/-- *a dog*, requiring nothing of the context. -/
def aDog : Content Ind (Quant Ind) := ⟨⊥, λ _ => SemIndefArt Dog⟩

/-- *hugged*, a transitive verb over its object quantifier (Ch. 6, (63)). -/
def hugged : Content Ind (Quant Ind → Ppty Ind) := ⟨⊥, λ _ Q x => Q (Hug x)⟩

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
  ⟨λ | ⟨.fido, _, h⟩ => nomatch h .bill ⟨⟩ | ⟨.rex, _, h⟩ => nomatch h .tom ⟨⟩
     | ⟨.tom, h, _⟩ => nomatch h | ⟨.bill, h, _⟩ => nomatch h⟩

end Hugging

/-! ### Localisation and donkey anaphora (§8.3) -/

/-- Localisation `ℒ` (49): the context a parametric property requires is folded into the
property's domain under the label `𝔠`, giving a restricted property. -/
def localize (P : PPpty E) : Restricted E := ⟨λ _ => P.bg, λ x c => P.fg c x⟩

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
def catchesIt (Catch : Ind → Ind → Type) : PPpty Ind := ⟨Ind, λ y x => Catch x y⟩

/-- *dog which chases a cat*, the restrictor, as the domain of (50): a dog with a cat it
chases. -/
def DogChasesACat : Ppty Ind := λ x => Dog x × ((c : Ind) × Cat c × Chase x c)

/-- The scope (51): *catches it* localised, restricted by the restrictor and aligned so that
`it` is the chased cat. -/
def scope (Catch : Ind → Ind → Type) : Restricted Ind :=
  ((localize (catchesIt Catch)).restrictBy DogChasesACat).align DogChasesACat
    λ _ r => (r, r.2.1)

/-- (55): `no(restr, scope)` with the scope purified. -/
def Sentence (Catch : Ind → Ind → Type) : Type := SemNo DogChasesACat (Purify (scope Catch))

/-- True when no dog catches anything. -/
def noCatching : Sentence (λ _ _ => Empty) := ⟨λ _ _ ⟨_, h⟩ => h⟩

/-- False when every dog catches the cat it chases. -/
theorem sentence_isEmpty : IsEmpty (Sentence Chase) :=
  ⟨λ ⟨f⟩ => (f .dog₁ ⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩).elim⟩

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
def FarmerOwnsADonkey : Ppty Ind := λ x => Farmer x × ((d : Ind) × Donkey d × Own x d)

/-- *likes it* (61), localised (62)–(63), restricted (64) and aligned (65). -/
def likesIt : Restricted Ind :=
  ((localize ⟨Ind, λ y x => Like x y⟩).restrictBy FarmerOwnsADonkey).align FarmerOwnsADonkey
    λ _ r => (r, r.2.1)

/-- The weak reading (59): every farmer who owns a donkey likes some donkey she owns. -/
def weak : SemUniversal FarmerOwnsADonkey (Purify likesIt)
  | .farmer₁, _ => ⟨⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .farmer₂, _ => ⟨⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .donkey₁, ⟨h, _⟩ => nomatch h
  | .donkey₂, ⟨h, _⟩ => nomatch h

/-- The strong reading (60), (66) fails: the first farmer does not like the second donkey. -/
theorem strong_isEmpty : IsEmpty (SemUniversal FarmerOwnsADonkey (PurifyUniv likesIt)) :=
  ⟨λ f => nomatch f .farmer₁ ⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩⟩

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
def sam : Content Ind (Quant Ind) := ⟨⊥, λ _ => SemPropName .sam⟩

/-- *no girl* (33). -/
def noGirl : Content Ind (Quant Ind) := ⟨⊥, λ _ => SemNo Girl⟩

/-- *failed*. -/
def failed : Content Ind (Ppty Ind) := ⟨⊥, λ _ => Fail⟩

/-- *thinks*, over a ptype of thinking. -/
def thinks : Content Ind (Type → Ppty Ind) := ⟨⊥, λ _ T x => Think x T⟩

/-- *likes*, a transitive verb over its object quantifier (Ch. 6, (63)). -/
def likes : Content Ind (Quant Ind → Ppty Ind) := ⟨⊥, λ _ Q x => Q (Like x)⟩

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
      SemNo Girl (λ x => Think x (Fail x)) :=
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
  Content.boundary ((Content.pronoun 0).app ⟨⊥, λ _ => Whistle⟩)

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
