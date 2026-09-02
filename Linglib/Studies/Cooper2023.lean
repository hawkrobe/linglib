import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Rat.Defs
import Linglib.Logic.Assignment
import Linglib.Semantics.Quantification.Witness
import Linglib.Logic.Modal.Extensional

/-!
# [cooper-2023] — From Perception to Communication

Cooper's theory of types with records (TTR) has Lean's own type theory as its metatheory:
the judgement `a : T` is the ambient typing, a type is *true* when inhabited (§1.5), a
record type is a structure, structural subtyping (§1.4.3.5, (53)) is the projection of a
structure with more fields onto one with fewer, and the intensionality of types — distinct
types with the same witnesses (§1.3) — is the ambient theory's as well. A property is
Cooper's `([x:Ind] → RecType)` with the record collapsed to its individual, and a ptype
`p(a)` a Lean type of situations, so `SemCommonNoun` (30) is the identity and unnamed.

The file follows the book's chapters. From §3.4 and §4: the contents of proper names (33),
the indefinite article (37) and the copula (78), the witness condition for `exist` (55), the
construction-based *is a* (85)–(94), and parametric content (§4.3, (14)). From Ch. 6: modal
type systems with their restrictive and inclusive notions (1)–(2), necessity and possibility
relative to a background type and a topos (17)–(24) with the two readings of *Mary should
eat her broccoli* (25)–(31), and intensionality by matching types against an agent's
long-term memory, religious beliefs and desires, with points of view (39)–(92). From Ch. 7:
restricted properties and their purification (7)–(13), the witness type `𝔗(P)` (17), the
frequentist probability of a witness set (36)–(52), and the witness conditions and anaphora
of §7.4. From Ch. 8: quantifier storage (11)–(19), the content type of a doubly quantified
sentence as the join of its readings (8), localisation (49) with the weak and strong donkey
readings (55)–(66), anaphoric combination under the locality of Principle B (74)–(77) and
the reflexive marking of Principle A (82)–(88), and cross-sentential anaphora (37)–(44).
-/

namespace Cooper2023

variable {E : Type}

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
def semPropName (a : E) : Quant E := λ P => P a

/-- The witness of `exist(restr, scope)` under the particular witness condition of Ch. 7
(63): an individual with the restrictor and the scope. -/
structure ExistWitness (E : Type) (restr scope : Ppty E) where
  x : E
  restrWit : restr x
  scopeWit : scope x

/-- `SemIndefArt` (37): a restrictor property to the existential quantifier over it. -/
def semIndefArt (restr : Ppty E) : Quant E := λ scope => ExistWitness E restr scope

/-- (55): `exist(P, Q)` is witnessed iff the property extensions of `P` and `Q` overlap. -/
theorem semIndefArt_nonempty_iff (restr scope : Ppty E) :
    Nonempty (semIndefArt restr scope) ↔ ∃ a, Nonempty (restr a) ∧ Nonempty (scope a) :=
  ⟨λ ⟨w⟩ => ⟨w.x, ⟨w.restrWit⟩, ⟨w.scopeWit⟩⟩, λ ⟨a, ⟨r⟩, ⟨s⟩⟩ => ⟨⟨a, r, s⟩⟩⟩

/-- `SemBe` (78), Montague's copula: the property of being the quantifier's witness. -/
def semBe (Q : Quant E) : Ppty E := λ x => Q λ y => PLift (x = y)

/-- The universal quantifier as a function from the restrictor's witnesses to the scope's,
the function witness of `every(P, Q)` in Ch. 7 §7.2.4 and (72). -/
def semUniversal (restr scope : Ppty E) : Type := (x : E) → restr x → scope x

/-- `no(P, Q)` under its particular witness condition (Ch. 7, (70)): every witness of the
restrictor precludes the scope. -/
def semNo (restr scope : Ppty E) : Type := (x : E) → restr x → scope x → Empty

/-- A monotone increasing quantifier. -/
def Quant.IsMonIncr (Q : Quant E) : Prop :=
  ∀ P P' : Ppty E, (∀ x, P x → P' x) → Nonempty (Q P) → Nonempty (Q P')

/-- A parametric content (§4.3, (14)): a background type, the context it requires, and a
foreground function from contexts of that type to contents. -/
structure Parametric (Content : Type*) where
  Bg : Type
  fg : Bg → Content

/-- A parametric property. -/
abbrev PPpty (E : Type) := Parametric (Ppty E)

/-! #### The Dudamel fragment

*Dudamel is a conductor* has the compositional content (82c), the existential quantifier of
`SemIndefArt` under the copula, and the construction-based content `CnstrIsA` (86)–(87),
the predicate applied to the individual (92a); the two are truth-conditionally equivalent
but distinct types, a distinction Montague's system cannot draw. -/

namespace Dudamel

inductive Ind
  | dudamel | beethoven
  deriving DecidableEq, Repr

/-- The ptype `conductor(x)`: Dudamel conducts. -/
inductive Conductor : Ind → Type
  | mk : Conductor .dudamel

/-- *is a conductor* (81c). -/
abbrev isAConductor : Ppty Ind := semBe (semIndefArt Conductor)

/-- *Dudamel is a conductor* (82c). -/
abbrev dudamelIsAConductor : Type := semPropName .dudamel isAConductor

/-- *Dudamel is a conductor* is true. -/
def dudamelIsAConductorWitness : dudamelIsAConductor := ⟨.dudamel, .mk, PLift.up rfl⟩

/-- *Beethoven is a conductor* is false. -/
instance : IsEmpty (semPropName .beethoven isAConductor) :=
  ⟨λ | ⟨.dudamel, _, ⟨h⟩⟩ => nomatch h | ⟨.beethoven, h, _⟩ => nomatch h⟩

/-- The construction-based content of *NP is a CN* (86)–(87), the predicate of the noun
applied to the individual, (92a). -/
abbrev cnstrIsA (pred : Ind → Type) (a : Ind) : Type := pred a

/-- (92a) and (92b) are truth-conditionally equivalent: distinct types, one with a witness
iff the other has. -/
theorem cnstrIsA_nonempty_iff (pred : Ind → Type) (a : Ind) :
    Nonempty (cnstrIsA pred a) ↔ Nonempty (semPropName a (semBe (semIndefArt pred))) :=
  ⟨λ ⟨h⟩ => ⟨⟨a, h, PLift.up rfl⟩⟩, λ ⟨⟨_, h, ⟨rfl⟩⟩⟩ => ⟨h⟩⟩

/-- *A conductor is Dudamel* (94c): the quantifiers in the other order. -/
abbrev aConductorIsDudamel : Type := semIndefArt Conductor (semBe (semPropName .dudamel))

/-- (94c) and (92b) are truth-conditionally equivalent as well; the construction content
(92a) is expressible only by *Dudamel is a conductor*. -/
theorem aConductorIsDudamel_nonempty_iff :
    Nonempty aConductorIsDudamel ↔ Nonempty dudamelIsAConductor :=
  ⟨λ ⟨⟨_, h, ⟨rfl⟩⟩⟩ => ⟨⟨.dudamel, h, PLift.up rfl⟩⟩,
    λ ⟨⟨_, h, ⟨rfl⟩⟩⟩ => ⟨⟨.dudamel, h, PLift.up rfl⟩⟩⟩

end Dudamel

/-! ## Modality and intensionality without possible worlds (Ch. 6)

A modal type system (§1.4.3.5, (54); §6.3) is a family of possibilities, type systems sharing
their types but differing in which objects witness them; equivalence, subtyping, necessity
and possibility are defined over the family, restrictively — over all possibilities, (1) — or
inclusively — over those in which the types occur, (2) — and the restrictive notions entail
the inclusive ones. Natural-language necessity and possibility are relativised in Kratzer's
manner ([kratzer-1977], [kratzer-1981]) to a background type and a topos, a dependent type
from situations to types ([breitholtz-2020]) taking over the work of the accessibility
relation, (20)–(24). Intensionality replaces sets of worlds by types (§6.5): `believe(a, T)`
holds when the type of `a`'s long-term memory matches `T` modulo relabelling (39)–(41),
postulated subtyping carries belief across (45)–(50), and a point of view — an alternative
type on shared labels, merged asymmetrically with the attitude type — matches instead
(55)–(58), which also serves *worship* (75), (81) and *want* (89)–(92). With record types as
structures a relabelling is absorbed into the function witnessing a subtyping, and
compatibility and the topos conditions are read in the ambient possibility. -/

/-! ### Modal type systems (§6.3) -/

/-- A possibility: which types occur in it and which objects witness them. -/
structure Possibility (Ty Obj : Type) where
  occurs : Ty → Prop
  witnesses : Ty → Obj → Prop

/-- A modal system of types (§1.4.3.5, (54)): a family of possibilities over shared types. -/
structure ModalSystem (Ty Obj : Type) where
  Poss : Type
  poss : Poss → Possibility Ty Obj

namespace ModalSystem

variable {Ty Obj : Type} (ms : ModalSystem Ty Obj) (T T₁ T₂ : Ty)

/-- The extension of `T` in the possibility `p`, (1a). -/
def ext (p : ms.Poss) (T : Ty) : Obj → Prop := (ms.poss p).witnesses T

/-- `T` occurs in the type system of the possibility `p`. -/
def Occurs (p : ms.Poss) (T : Ty) : Prop := (ms.poss p).occurs T

/-- Restrictive equivalence (1a): the same extension in every possibility. -/
def EquivR : Prop := ∀ p, ms.ext p T₁ = ms.ext p T₂

/-- Restrictive subtyping (1b). -/
def SubtypeR : Prop := ∀ p a, ms.ext p T₁ a → ms.ext p T₂ a

/-- Restrictive necessity (1c): witnessed in every possibility. -/
def NecR : Prop := ∀ p, ∃ a, ms.ext p T a

/-- Restrictive possibility (1d): witnessed in some possibility. -/
def PossR : Prop := ∃ p a, ms.ext p T a

/-- Inclusive equivalence (2a): the same extension wherever both types occur. -/
def EquivI : Prop := ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ms.ext p T₁ = ms.ext p T₂

/-- Inclusive subtyping (2b). -/
def SubtypeI : Prop := ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ∀ a, ms.ext p T₁ a → ms.ext p T₂ a

/-- Inclusive necessity (2c): witnessed wherever the type occurs. -/
def NecI : Prop := ∀ p, ms.Occurs p T → ∃ a, ms.ext p T a

/-- Inclusive possibility (2d). -/
def PossI : Prop := ∃ p, ms.Occurs p T → ∃ a, ms.ext p T a

/-- The restrictive notions entail the inclusive ones (§6.3). -/
theorem EquivI_of_EquivR (h : ms.EquivR T₁ T₂) : ms.EquivI T₁ T₂ := λ p _ _ => h p

theorem SubtypeI_of_SubtypeR (h : ms.SubtypeR T₁ T₂) : ms.SubtypeI T₁ T₂ := λ p _ _ => h p

theorem NecI_of_NecR (h : ms.NecR T) : ms.NecI T := λ p _ => h p

theorem PossI_of_PossR (h : ms.PossR T) : ms.PossI T :=
  let ⟨p, hp⟩ := h; ⟨p, λ _ => hp⟩

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
  sit : B
  sub : B → τ.Bg
  incl : τ.fg (sub sit) → T

/-- A witness of `poss(T, B, τ)` (24): as `Nec`, with the returned type compatible with `T`. -/
structure Poss (T B : Type) (τ : Topos) where
  sit : B
  sub : B → τ.Bg
  compat : Compatible (τ.fg (sub sit)) T

/-- Necessity yields possibility when the topos returns an inhabited type. -/
def Nec.toPoss {T B : Type} {τ : Topos} (h : Nec T B τ) (hne : Nonempty (τ.fg (h.sub h.sit))) :
    Poss T B τ :=
  ⟨h.sit, h.sub, ⟨(hne.some, h.incl hne.some)⟩⟩

/-! #### *Mary should eat her broccoli* (25)–(31)

The base situation (26) has the broccoli on Mary's plate and Mary loving it; the deontic
topos (28a) sends a situation of a child with food on her plate to her eating it, the bouletic
topos (28b) a situation of a child loving some food to her eating it, and
`nec([e:eat(m,b)], T_broc, τ)` is witnessed by either, (29)–(30). -/

namespace Broccoli

inductive Ind
  | broccoli | mary | plate
  deriving DecidableEq, Repr

/-- Broccoli is food, (27). -/
def IsFood (x : Ind) : Prop := x = .broccoli

/-- The base situation type (26), its manifest fields fixing the broccoli, Mary and the plate. -/
structure Base where
  x : Ind
  c₁ : x = .broccoli
  y : Ind
  c₂ : y = .mary
  z : Ind
  c₃ : z = .plate
  e₁ : y = .mary ∧ z = .plate
  e₂ : x = .broccoli ∧ z = .plate
  e₃ : y = .mary ∧ x = .broccoli

/-- The background of the deontic topos (28a): a child with food on her plate. -/
structure OnPlate where
  x : Ind
  c₁ : IsFood x
  y : Ind
  c₂ : y = .mary
  z : Ind
  c₃ : z = .plate
  e₁ : y = .mary ∧ z = .plate
  e₂ : x = .broccoli ∧ z = .plate

/-- The background of the bouletic topos (28b): a child loving some food. -/
structure Loves where
  x : Ind
  c₁ : IsFood x
  y : Ind
  c₂ : y = .mary
  e₃ : y = .mary ∧ x = .broccoli

/-- The ptype `eat(y, x)`. -/
def Eat (y x : Ind) : Type := PLift (y = .mary ∧ x = .broccoli)

/-- The deontic topos τ₁ (28a). -/
def deontic : Topos := ⟨OnPlate, λ r => Eat r.y r.x⟩

/-- The bouletic topos τ₂ (28b). -/
def bouletic : Topos := ⟨Loves, λ r => Eat r.y r.x⟩

/-- The base situation: the broccoli on Mary's plate, which she loves. -/
def base : Base := ⟨.broccoli, rfl, .mary, rfl, .plate, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- (29a): eating the broccoli is necessary under the deontic topos. -/
def necDeontic : Nec (Eat .mary .broccoli) Base deontic where
  sit := base
  sub b := ⟨b.x, b.c₁, b.y, b.c₂, b.z, b.c₃, b.e₁, b.e₂⟩
  incl _ := ⟨⟨rfl, rfl⟩⟩

/-- (29b): and under the bouletic topos. -/
def necBouletic : Nec (Eat .mary .broccoli) Base bouletic where
  sit := base
  sub b := ⟨b.x, b.c₁, b.y, b.c₂, b.e₃⟩
  incl _ := ⟨⟨rfl, rfl⟩⟩

end Broccoli

/-! ### Intensionality (§6.5) -/

/-- Subtyping modulo relabelling (39), `T₁ ⊑⇝ T₂`. -/
def RelabelledSubtype (T₁ T₂ : Type) : Prop := Nonempty (T₁ → T₂)

/-- An agent's total information state (91) — long-term memory, religious beliefs and desires
as types — with the point-of-view relation on types: `pov M T` when `M` is a complete point
of view on `T`, the asymmetric merge of `T` with an alternative type on some of its labels,
(55), (80). -/
structure InfoState (Agent : Type) where
  ltm : Agent → Type
  rbel : Agent → Type
  des : Agent → Type
  pov : Type → Type → Prop

section Attitudes

variable {Agent : Type} (s : InfoState Agent) (a : Agent)

/-- `believe(a, T)` (40): the type of `a`'s long-term memory matches `T`. -/
def believe (T : Type) : Prop := RelabelledSubtype (s.ltm a) T

/-- (41): belief is closed under relabelling. -/
theorem believe_equiv {T T' : Type} (h : believe s a T) (e : T ≃ T') : believe s a T' :=
  ⟨e ∘ h.some⟩

/-- Belief is closed under subtyping, structural or postulated. -/
theorem believe_of_subtype {T₁ T₂ : Type} (h : believe s a T₁) (f : T₁ → T₂) :
    believe s a T₂ :=
  ⟨f ∘ h.some⟩

/-- `believe(a, T)` with a point of view (58): the direct match, or a match of the complete
point of view on a belief. -/
def believePov (T : Type) : Prop :=
  believe s a T ∨ ∃ T₁ M, believe s a T₁ ∧ s.pov M T₁ ∧ RelabelledSubtype M T

/-- `rbelieve(a, T)` (74): the type of `a`'s religious beliefs matches `T`. -/
def rbelieve (T : Type) : Prop := RelabelledSubtype (s.rbel a) T

/-- `want†(a, T)` (92): `a`'s desires, or a complete point of view on them, match `T`. -/
def wantDagger (T : Type) : Prop :=
  RelabelledSubtype (s.des a) T ∨
    ∃ T₁ M, RelabelledSubtype (s.des a) T₁ ∧ s.pov M T₁ ∧ RelabelledSubtype M T

end Attitudes

/-- `worship(a, Q)` (75), (81): some religious belief of `a`, or a complete point of view on
one, matches the quantifier exported over `worship†` — intentionality and specificity without
existence. -/
def worship (s : InfoState E) (dagger : E → E → Type) (a : E) (Q : Quant E) : Prop :=
  (∃ T, rbelieve s a T ∧ RelabelledSubtype T (Q (dagger a))) ∨
    ∃ T₁ M, rbelieve s a T₁ ∧ s.pov M T₁ ∧ RelabelledSubtype M (Q (dagger a))

/-- `want_P(a, P)` (90a): wanting to have a property. -/
def wantP (s : InfoState E) (a : E) (P : Ppty E) : Prop := wantDagger s a (P a)

/-- `want_Q(a, Q)` (90b): wanting a quantifier's worth of things is wanting to have them. -/
def wantQ (s : InfoState E) (have_ : E → E → Type) (a : E) (Q : Quant E) : Prop :=
  wantDagger s a (Q (have_ a))

/-! #### Postulated subtyping: buying and selling, (35), (45)–(47), (50) -/

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
postulate restricts attention to — unlike the structural (50a), `BoyHugsDog.toBoyAndDog`. -/
def SellEvent.toBuyEvent (e : SellEvent E) : BuyEvent E := ⟨e.buyer, e.thing, e.seller⟩

/-- Its converse (47). -/
def BuyEvent.toSellEvent (e : BuyEvent E) : SellEvent E := ⟨e.seller, e.thing, e.buyer⟩

theorem BuyEvent.toSellEvent_toBuyEvent (e : SellEvent E) : e.toBuyEvent.toSellEvent = e := rfl

/-- (45)–(47): whoever believes that Kim bought the book from Sam believes that Sam sold it
to Kim. -/
theorem believe_sell_of_believe_buy {Agent : Type} (s : InfoState Agent) (a : Agent)
    (h : believe s a (BuyEvent E)) : believe s a (SellEvent E) :=
  believe_of_subtype s a h BuyEvent.toSellEvent

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

/-- After learning that they are one body (53): the manifest field, a subtype of (52). -/
structure OneStar (E : Type) (Hesperus Phosphorus Evening Morning : E → Type)
    extends TwoStars E Hesperus Phosphorus Evening Morning where
  same : y = x

/-! #### Intensional transitive verbs, (63)–(66), (87) -/

/-- A transitive verb whose predicate takes a quantifier (64), with the variant `p†` between
individuals. -/
structure TransVerb (E : Type) where
  pred : E → Quant E → Type
  dagger : E → E → Type

/-- (65): an extensional verb's ptype is equivalent to the quantifier exported over `p†`. -/
def TransVerb.IsExtensional (v : TransVerb E) : Prop :=
  ∀ a Q, Nonempty (v.pred a Q ≃ Q (v.dagger a))

/-- (66): a successful search is a finding. -/
structure SuccessfulSeek (E : Type) (seek find : E → Quant E → Type) where
  successful : Type → Type
  find_of_successful : ∀ a Q, successful (seek a Q) → find a Q

/-- (87): booking a monotone increasing quantifier's worth of tables requires tables to be,
without requiring a specific one. -/
def BookRequiresBeing (book : E → Quant E → Type) (be : Ppty E) : Prop :=
  ∀ a Q, Q.IsMonIncr → Nonempty (book a Q) → Nonempty (Q be)

/-! #### Restrictive against inclusive necessity

Two possibilities over the types `rain` and `snow`: snow is witnessed only in the first, so it
is possible but not necessary; and when snow does not occur in the second at all, it is
inclusively but not restrictively necessary — the entailment of §6.3 does not reverse. -/

namespace Weather

inductive Ty
  | rain | snow
  deriving DecidableEq

inductive Obj
  | a | b
  deriving DecidableEq

/-- Both types occur in both possibilities; rain is witnessed in both, snow in the first. -/
def system : ModalSystem Ty Obj where
  Poss := Bool
  poss
    | true => ⟨λ _ => True, λ | .rain, .a => True | .snow, .b => True | _, _ => False⟩
    | false => ⟨λ _ => True, λ | .rain, .a => True | _, _ => False⟩

/-- As `system`, but snow does not occur in the second possibility. -/
def restricted : ModalSystem Ty Obj where
  Poss := Bool
  poss
    | true => ⟨λ _ => True, λ | .rain, .a => True | .snow, .b => True | _, _ => False⟩
    | false => ⟨(· = .rain), λ | .rain, .a => True | _, _ => False⟩

theorem necR_rain : system.NecR .rain := λ | true => ⟨.a, trivial⟩ | false => ⟨.a, trivial⟩

theorem possR_snow : system.PossR .snow := ⟨true, .b, trivial⟩

theorem not_necR_snow : ¬ system.NecR .snow := λ h =>
  let ⟨o, ho⟩ := h false
  by cases o <;> simp [system, ModalSystem.ext] at ho

theorem necI_snow : restricted.NecI .snow
  | true, _ => ⟨.b, trivial⟩
  | false, h => absurd h (by simp [restricted, ModalSystem.Occurs])

theorem not_necR_snow_restricted : ¬ restricted.NecR .snow := λ h =>
  let ⟨o, ho⟩ := h false
  by cases o <;> simp [restricted, ModalSystem.ext] at ho

end Weather

/-! ## Witness-based quantification (Ch. 7)

A property may be restricted by conditions in its domain beyond the required `x`-field,
(7b), and purification lowers the restriction into the body, existentially, `𝔓` (12), or
universally, `𝔓∀` (13); the type `𝔗(P)` of objects with a property (17) is the witness type
of its purification. A witness set for a quantifier relation and a property is a set of
objects with the property meeting a cardinality condition (20)–(35); the cardinality
conditions have frequentist probabilistic forms (36), (41)–(58), estimable from an
agent's experience base of remembered judgements (37)–(40), and for a witness set the
probability is the proportion (51)–(52). The witness conditions for the quantificational
ptypes (59) pair a witness set with a function; the particular conditions for `exist` (63)
and `no` (70) are equivalent types whose witnesses carry what discourse anaphora picks
up. -/

/-- A restricted property (7b): conditions on the individual in the domain, and the body. -/
structure Restricted (E : Type) where
  restr : E → Type
  body : (x : E) → restr x → Type

/-- A property is pure (7a) when its restriction is trivial. -/
def Restricted.IsPure (P : Restricted E) : Prop :=
  ∀ x, Nonempty (P.restr x) ∧ Subsingleton (P.restr x)

/-- Purification `𝔓(P)` (12): the restriction lowered into the body under the local context. -/
def purify (P : Restricted E) : Ppty E := λ x => (c : P.restr x) × P.body x c

/-- Universal purification `𝔓∀(P)` (13): the body under every way of meeting the
restriction. -/
def purifyUniv (P : Restricted E) : Ppty E := λ x => (c : P.restr x) → P.body x c

/-- Property restriction `P|ℱ` (Ch. 5, (98); Ch. 7, (98)): the domain narrowed by a property. -/
def Restricted.restrictBy (P : Restricted E) (R : Ppty E) : Restricted E :=
  ⟨λ x => R x × P.restr x, λ x c => P.body x c.2⟩

/-- Alignment of paths in the domain (Ch. 8, (51)–(52)): a manifest field identifying two
paths is a further restriction of the domain, through which the body is read. -/
def Restricted.align (P : Restricted E) (R : E → Type) (f : ∀ x, R x → P.restr x) :
    Restricted E :=
  ⟨R, λ x c => P.body x (f x c)⟩

/-- `𝔗(P)` (17): the objects with the (purified) property. -/
def WitnessType (P : Ppty E) : Type := {a : E // Nonempty (P a)}

theorem purify_nonempty_iff (P : Restricted E) (x : E) :
    Nonempty (purify P x) ↔ ∃ c : P.restr x, Nonempty (P.body x c) :=
  ⟨λ ⟨c, w⟩ => ⟨c, ⟨w⟩⟩, λ ⟨c, ⟨w⟩⟩ => ⟨⟨c, w⟩⟩⟩

theorem purifyUniv_nonempty_iff (P : Restricted E) (x : E) :
    Nonempty (purifyUniv P x) ↔ ∀ c : P.restr x, Nonempty (P.body x c) :=
  ⟨λ ⟨f⟩ c => ⟨f c⟩, λ h => ⟨λ c => (h c).some⟩⟩

/-- For a pure property the two purifications agree — `𝔓` and `𝔓∀` differ only under a
non-trivial restriction. -/
theorem purify_nonempty_iff_purifyUniv (P : Restricted E) (h : P.IsPure) (x : E) :
    Nonempty (purify P x) ↔ Nonempty (purifyUniv P x) := by
  rw [purify_nonempty_iff, purifyUniv_nonempty_iff]
  obtain ⟨⟨c₀⟩, hs⟩ := h x
  exact ⟨λ ⟨c, hc⟩ c' => hs.allEq c c' ▸ hc, λ hall => ⟨c₀, hall c₀⟩⟩

/-! ### Witness sets and probabilities (§7.3) -/

/-- An experience base (37): the judgements `[sit = a, type = T]` an agent remembers. -/
structure ExperienceBase (E Ty : Type) where
  judgements : Finset (E × Ty)

section ExperienceBase

variable {Ty : Type} [DecidableEq E] [DecidableEq Ty] (𝔍 : ExperienceBase E Ty)

/-- The extension of a type with respect to the experience base (38). -/
def ExperienceBase.ext (T : Ty) : Finset E := (𝔍.judgements.filter (·.2 = T)).image Prod.fst

/-- The frequentist estimate `p_𝔍(T₁ ‖ T₂)` (39), and `0` when `T₂` is unwitnessed (36). -/
def ExperienceBase.condProb (T₁ T₂ : Ty) : ℚ :=
  ((𝔍.ext T₁ ∩ 𝔍.ext T₂).card : ℚ) / (𝔍.ext T₂).card

end ExperienceBase

/-- (51)–(52): for a witness set `X` of objects with the property, the frequentist
probability of `𝔗(X)` given `𝔗(P)` is the proportion `|X| / |[↓P]|`. -/
theorem condProb_witnessSet [DecidableEq E] (X P : Finset E) (h : X ⊆ P) :
    ((X ∩ P).card : ℚ) / P.card = (X.card : ℚ) / P.card := by
  rw [Finset.inter_eq_left.2 h]

/-! ### Witness conditions and anaphora (§7.4)

With `dog'` and `bark'` the properties (61a–b), a witness for `exist(dog', bark')` under the
particular condition (63) is a dog that barks, whose `x`-field is what *it* picks up in
*A dog is barking. It is right outside my window* (64); under the particular condition for
`no` (70), *No dog barked. They were all busy gnawing on a bone* (71) has *they* pick up the
witness set of every dog — complement set anaphora — and *few* allows the complement set
(87) where *a few* does not (92). -/

namespace Dogs

open Quantification

inductive Ind
  | fido | rex | spot | luna
  deriving DecidableEq, Repr

/-- Fido, Rex and Spot are dogs. -/
def IsDog : Ind → Prop
  | .luna => False
  | _ => True

/-- Fido and Spot bark. -/
def Barks : Ind → Prop
  | .fido | .spot => True
  | _ => False

/-- *A dog barks* (63): Fido. -/
def aDogBarks : ParticularWC_Exist (λ x : Ind => PLift (IsDog x)) (λ x => PLift (Barks x)) :=
  ⟨.fido, ⟨trivial⟩, ⟨trivial⟩⟩

/-- *No dog barks* is false: Fido is a dog that barks. -/
theorem not_noDogBarks :
    ¬ ParticularWC_No (λ x : Ind => PLift (IsDog x)) (λ x => PLift (Barks x)) :=
  λ ⟨f⟩ => (f .fido ⟨trivial⟩).false ⟨trivial⟩

/-- The complement set is available from *no* (71) and *few* (87) but not *a few* (92). -/
theorem compset : AnaphoraRef.compset ∈ anaphoraAvailable .no ∧
    AnaphoraRef.compset ∈ anaphoraAvailable .few ∧
    AnaphoraRef.compset ∉ anaphoraAvailable .aFew := by
  decide

inductive Ty
  | dog | bark
  deriving DecidableEq, Repr

/-- An experience base of three dogs, two of which were judged to bark. -/
def experience : ExperienceBase Ind Ty :=
  ⟨{(.fido, .dog), (.rex, .dog), (.spot, .dog), (.fido, .bark), (.spot, .bark)}⟩

/-- The estimate `p_𝔍(bark ‖ dog)` is two thirds. -/
theorem bark_given_dog : experience.condProb .bark .dog = 2 / 3 := by
  have h₁ : (experience.ext .bark ∩ experience.ext .dog).card = 2 := by decide
  have h₂ : (experience.ext .dog).card = 3 := by decide
  simp [ExperienceBase.condProb, h₁, h₂]

end Dogs

/-- Property conjunction `P₁ & P₂` (153), the content of a noun modified by a relative clause
(151). -/
def pptyConj (P₁ P₂ : Ppty E) : Ppty E := λ x => P₁ x × P₂ x

/-! ## Type-based underspecification (Ch. 8)

The content of an utterance is raised to a type of contents. Storage puts a parametric
quantifier into the context's quantifier store, leaving a pronoun-like content in its place
(17), and retrieval quantifies it back in over the property purified from the rest (19); for
a doubly quantified sentence the closure yields the two readings, and the content type is the
join of their singleton types (8). Anaphora is added to the closure at combination: `@ᵢ,ⱼ`
identifies a pronoun's path with an antecedent's (28), permitted only when the pronoun is
not marked local, (74)–(76), the boundary operation `B` clearing the marking at the
sentence (77); reflexives are marked in `𝔯` (83), bound by reflexivisation `ℜ` (84) and
required to be bound by the filter `𝔄` at the verb phrase (85)–(88). Donkey anaphora goes
through localisation `ℒ` (49), which folds the context into the property's domain, so that
the indefinite's witness in the restrictor can be aligned with the pronoun (51)–(52): with
`𝔓` the scope gives the weak reading (55)–(59), with `𝔓∀` the strong one (60)–(66), the
quantification being over farmers and not farmer–donkey pairs. -/

/-! ### Quantifier storage (§8.2) -/

/-- A quantifier store (11): the parametric quantifiers awaiting scope, most recent first. -/
structure QStore (E : Type) where
  stored : List (Quant E)

/-- A content is plugged when it requires nothing in the store (16). -/
def QStore.IsPlugged (q : QStore E) : Prop := q.stored = []

/-- Storage (17): a quantifier into the store. -/
def QStore.store (q : QStore E) (Q : Quant E) : QStore E := ⟨Q :: q.stored⟩

/-- Retrieval (19): the most recently stored quantifier out of the store. -/
def QStore.retrieve (q : QStore E) : Option (Quant E × QStore E) :=
  match q.stored with
  | [] => none
  | Q :: rest => some (Q, ⟨rest⟩)

@[simp] theorem QStore.retrieve_store (q : QStore E) (Q : Quant E) :
    (q.store Q).retrieve = some (Q, q) := rfl

theorem QStore.retrieve_eq_none_iff (q : QStore E) : q.retrieve = none ↔ q.IsPlugged := by
  cases q with | mk l => cases l <;> simp [QStore.retrieve, QStore.IsPlugged]

/-- The context (82): the quantifier store, the assignments to pronouns `𝔰`, local pronouns
`𝔩`, reflexives `𝔯`, wh-phrases `𝔴` and gaps `𝔤`, and the propositional context `𝔠`. -/
structure Cntxt (E : Type) where
  𝔮 : QStore E
  𝔰 : PartialAssign ℕ E
  𝔩 : PartialAssign ℕ E
  𝔯 : PartialAssign ℕ E
  𝔴 : PartialAssign ℕ E
  𝔤 : PartialAssign ℕ E
  𝔠 : Type

/-- A doubly quantified sentence: the relation and the subject and object quantifiers. -/
structure TwoQuantScope (E : Type) where
  rel : E → E → Type
  q₁ : Quant E
  q₂ : Quant E

/-- The reading with the subject quantifier outermost. -/
def TwoQuantScope.surface (s : TwoQuantScope E) : Type := s.q₁ λ x => s.q₂ λ y => s.rel x y

/-- The reading with the object quantifier retrieved outermost, (4b). -/
def TwoQuantScope.inverse (s : TwoQuantScope E) : Type := s.q₂ λ y => s.q₁ λ x => s.rel x y

/-- The content type (8)–(9): the join of the singleton types of the two contents the closure
under storage and retrieval yields, whose witnesses are the readings. -/
def TwoQuantScope.contentType (s : TwoQuantScope E) : Type := s.surface ⊕ s.inverse

/-! #### *Every boy hugged a dog* (1)

Two boys each hugging a different dog: the reading (1a) is witnessed, (1b) is not. -/

namespace Hugging

inductive Ind
  | tom | bill | fido | rex
  deriving DecidableEq

def IsBoy : Ppty Ind
  | .tom | .bill => PUnit
  | _ => Empty

def IsDog : Ppty Ind
  | .fido | .rex => PUnit
  | _ => Empty

/-- Tom hugs Fido, Bill hugs Rex. -/
def Hug : Ind → Ind → Type
  | .tom, .fido | .bill, .rex => PUnit
  | _, _ => Empty

def sentence : TwoQuantScope Ind := ⟨Hug, semUniversal IsBoy, semIndefArt IsDog⟩

/-- (1a): every boy is such that there is a dog he hugged. -/
def surfaceWitness : sentence.surface
  | .tom, _ => ⟨.fido, ⟨⟩, ⟨⟩⟩
  | .bill, _ => ⟨.rex, ⟨⟩, ⟨⟩⟩
  | .fido, h => nomatch h
  | .rex, h => nomatch h

/-- (1b): there is no dog every boy hugged. -/
theorem inverse_isEmpty : IsEmpty sentence.inverse :=
  ⟨λ ⟨d, _, hall⟩ => by cases d with
    | fido => exact nomatch hall .bill ⟨⟩
    | rex => exact nomatch hall .tom ⟨⟩
    | tom => exact nomatch (show Empty from ‹IsDog .tom›)
    | bill => exact nomatch (show Empty from ‹IsDog .bill›)⟩

/-- The content type has exactly the surface reading as witness. -/
theorem contentType_nonempty : Nonempty sentence.contentType ∧ IsEmpty sentence.inverse :=
  ⟨⟨.inl surfaceWitness⟩, inverse_isEmpty⟩

end Hugging

/-! ### Localisation and donkey anaphora (§8.3) -/

/-- Localisation `ℒ` (49): the context a parametric property requires is folded into the
property's domain under the label `𝔠`, giving a restricted property. -/
def localize (P : PPpty E) : Restricted E := ⟨λ _ => P.Bg, λ x c => P.fg c x⟩

/-- `𝔓(ℒ(P))` is witnessed iff the property is under some context. -/
theorem purify_localize_nonempty_iff (P : PPpty E) (x : E) :
    Nonempty (purify (localize P) x) ↔ ∃ c : P.Bg, Nonempty (P.fg c x) :=
  purify_nonempty_iff _ x

/-! #### *No dog which chases a cat catches it* (46a)

The scope is the localised *catches it* restricted by the restrictor and aligned so that the
caught cat is the chased one (50)–(51); under the particular condition for `no` the sentence
(55) says that every dog which chases a cat fails to be a dog which chases a cat and catches
it. -/

namespace Chasing

inductive Ind
  | dog₁ | dog₂ | cat₁ | cat₂
  deriving DecidableEq

def IsDog : Ppty Ind
  | .dog₁ | .dog₂ => PUnit
  | _ => Empty

def IsCat : Ppty Ind
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
def dogChasesACat : Ppty Ind := λ x => IsDog x × ((c : Ind) × IsCat c × Chase x c)

/-- The scope (51): *catches it* localised, restricted by the restrictor and aligned so that
`it` is the chased cat. -/
def scope (Catch : Ind → Ind → Type) : Restricted Ind :=
  ((localize (catchesIt Catch)).restrictBy dogChasesACat).align dogChasesACat
    λ _ r => (r, r.2.1)

/-- (55): `no(restr, scope)` with the scope purified. -/
def sentence (Catch : Ind → Ind → Type) : Type := semNo dogChasesACat (purify (scope Catch))

/-- True when no dog catches anything. -/
def noCatching : sentence (λ _ _ => Empty) := λ _ _ ⟨_, h⟩ => h

/-- False when every dog catches the cat it chases. -/
theorem sentence_isEmpty : IsEmpty (sentence Chase) :=
  ⟨λ f => (f .dog₁ ⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩).elim⟩

end Chasing

/-! #### *Every farmer who owns a donkey likes it* (58)–(66)

The localised *likes it* restricted by *farmer who owns a donkey* and aligned (65) is the
property of being a farmer who owns a donkey and likes that donkey; its purification `𝔓`
gives the weak reading — some donkey she owns — and `𝔓∀` (66) the strong one — every
donkey she owns. A farmer who owns two donkeys and likes one separates them. -/

namespace Donkeys

inductive Ind
  | farmer₁ | farmer₂ | donkey₁ | donkey₂
  deriving DecidableEq

def IsFarmer : Ppty Ind
  | .farmer₁ | .farmer₂ => PUnit
  | _ => Empty

def IsDonkey : Ppty Ind
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
def farmerOwnsADonkey : Ppty Ind := λ x => IsFarmer x × ((d : Ind) × IsDonkey d × Own x d)

/-- *likes it* (61), localised (62)–(63), restricted (64) and aligned (65). -/
def likesIt : Restricted Ind :=
  ((localize ⟨Ind, λ y x => Like x y⟩).restrictBy farmerOwnsADonkey).align farmerOwnsADonkey
    λ _ r => (r, r.2.1)

/-- The weak reading (59): every farmer who owns a donkey likes some donkey she owns. -/
def weak : semUniversal farmerOwnsADonkey (purify likesIt)
  | .farmer₁, _ => ⟨⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .farmer₂, _ => ⟨⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .donkey₁, ⟨h, _⟩ => nomatch h
  | .donkey₂, ⟨h, _⟩ => nomatch h

/-- The strong reading (60), (66) fails: the first farmer does not like the second donkey. -/
theorem strong_isEmpty : IsEmpty (semUniversal farmerOwnsADonkey (purifyUniv likesIt)) :=
  ⟨λ f => nomatch f .farmer₁ ⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩⟩

end Donkeys

/-! ### Pronouns, locality and reflexives (67)–(88) -/

/-- Anaphoric combination `@ᵢ,ⱼ` (28), (76): the pronoun `xⱼ` takes the antecedent `xᵢ`'s
value, permitted only when `xⱼ` is not marked local — Principle B. -/
def anaphoricCombine (i j : ℕ) (P : Cntxt E → Type) : Cntxt E → Type :=
  λ c => PLift (c.𝔩 j = none) × P { c with 𝔰 := (λ k => if k = j then c.𝔰 i else c.𝔰 k) }

/-- The boundary operation `B` (77): the locality marking is dropped at the sentence, so
that *Sam thinks that she is lucky* can relate *she* to *Sam*. -/
def boundary (P : Cntxt E → Type) : Cntxt E → Type := λ c => P { c with 𝔩 := PartialAssign.empty }

/-- A pronoun marked local blocks anaphoric combination within its clause: *Sam likes him*
cannot be *Sam likes himself*, (67), (73)–(76). -/
theorem anaphoricCombine_isEmpty_of_local (i j : ℕ) (P : Cntxt E → Type) (c : Cntxt E)
    (h : c.𝔩 j ≠ none) : IsEmpty (anaphoricCombine i j P c) :=
  ⟨λ ⟨⟨hj⟩, _⟩ => h hj⟩

/-- Past the boundary the pronoun is no longer local, and combination is possible. -/
theorem boundary_anaphoricCombine_nonempty_iff (i j : ℕ) (P : Cntxt E → Type) (c : Cntxt E) :
    Nonempty (boundary (anaphoricCombine i j P) c) ↔
      Nonempty (P { c with 𝔩 := PartialAssign.empty,
                           𝔰 := (λ k => if k = j then c.𝔰 i else c.𝔰 k) }) :=
  ⟨λ ⟨_, p⟩ => ⟨p⟩, λ ⟨p⟩ => ⟨⟨rfl⟩, p⟩⟩

/-- Reflexivisation `ℜ` (84): the reflexive `xᵢ` is bound to the subject and its marking in
`𝔯` removed. -/
def reflexivize (i : ℕ) (P : Cntxt E → Ppty E) : Cntxt E → Ppty E :=
  λ c x => P { c with 𝔯 := PartialAssign.empty, 𝔰 := PartialAssign.update c.𝔰 i x } x

/-- The filter `𝔄` (85): contents with a free reflexive are excluded — Principle A, imposed
at the verb phrase (88). -/
def anaphorFree (P : Cntxt E → Type) : Cntxt E → Type :=
  λ c => PLift (∀ i, c.𝔯 i = none) × P c

/-- A reflexive left unbound is excluded. -/
theorem anaphorFree_isEmpty_of_marked (P : Cntxt E → Type) (c : Cntxt E) (i : ℕ)
    (h : c.𝔯 i ≠ none) : IsEmpty (anaphorFree P c) :=
  ⟨λ ⟨⟨hall⟩, _⟩ => h (hall i)⟩

/-- *likes him* (69): the object's referent from the context's `𝔰.x₀`. -/
def likesObject (Like : E → E → Type) : Cntxt E → Ppty E :=
  λ c x => (y : E) × PLift (c.𝔰 0 = some y) × Like x y

/-- *Sam likes himself* by `ℜ` is `like(Sam, Sam)` (68c), (73). -/
theorem reflexivize_nonempty_iff (Like : E → E → Type) (c : Cntxt E) (x : E) :
    Nonempty (reflexivize 0 (likesObject Like) c x) ↔ Nonempty (Like x x) :=
  ⟨λ ⟨_, ⟨h⟩, l⟩ => ⟨by simpa [PartialAssign.update] using (Option.some_inj.1 h ▸ l)⟩,
    λ ⟨l⟩ => ⟨⟨x, ⟨by simp [PartialAssign.update]⟩, l⟩⟩⟩

/-- Reflexivisation clears the reflexive marking, so `𝔄` admits the result. -/
theorem anaphorFree_reflexivize_nonempty_iff (i : ℕ) (P : Cntxt E → Ppty E) (c : Cntxt E)
    (x : E) (h : ∀ k, c.𝔯 k = none) :
    Nonempty (anaphorFree (λ c' => reflexivize i P c' x) c) ↔
      Nonempty (reflexivize i P c x) :=
  ⟨λ ⟨_, p⟩ => ⟨p⟩, λ ⟨p⟩ => ⟨⟨h⟩, p⟩⟩

/-! ### Cross-sentential anaphora (37)–(44)

*A man walked. He whistled.* The content of the previous utterance is merged into the
current context under `𝔭` (41), the pronoun's `𝔰.x₀` is identified with the man `𝔭.e.x` (42),
and the dependency on `𝔰.x₀` is replaced by one on `𝔭.e.x` (43)–(44). -/

/-- A context with the previous utterance's content under `𝔭`. -/
structure Discourse (E : Type) (Prev : Type) where
  𝔭 : Prev
  𝔰 : PartialAssign ℕ E

namespace Whistling

inductive Ind
  | john | mary
  deriving DecidableEq

def IsMan : Ppty Ind
  | .john => PUnit
  | .mary => Empty

def Walk : Ppty Ind
  | .john => PUnit
  | .mary => Empty

def Whistle : Ppty Ind
  | .john => PUnit
  | .mary => Empty

/-- The content of *a man walked* under the particular condition for `exist` (38). -/
abbrev AManWalked : Type := ExistWitness Ind IsMan Walk

def aManWalked : AManWalked := ⟨.john, ⟨⟩, ⟨⟩⟩

/-- *He whistled* with the pronoun resolved to the man of the previous utterance (44). -/
def heWhistled (d : Discourse Ind AManWalked) : Type := Whistle d.𝔭.x

def heWhistledWitness : heWhistled ⟨aManWalked, PartialAssign.empty⟩ := ⟨⟩

end Whistling

end Cooper2023
