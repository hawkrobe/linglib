import Linglib.Syntax.WordGrammar.Inheritance.Choice
import Linglib.Syntax.WordGrammar.Inheritance.Default
import Linglib.Syntax.WordGrammar.Inheritance.Order
import Mathlib.Logic.Relation

/-!
# Hudson (2010): An Introduction to Word Grammar

This file formalizes the worked examples of Part I of [hudson-2010] on the inheritance-network
substrate of `WordGrammar.Inheritance`. Default inheritance is the book's engine: an exemplar
inherits every property of the concepts above it in the isA taxonomy except those overridden
lower down, so a penguin exemplar inherits *lays eggs* from *bird* but *doesn't fly* from
*penguin* (Figure 2.8, `e2_flight`), and a diesel car exemplar runs on diesel rather than the
default petrol (Figure 3.18, `e_fuel`). Multiple inheritance can leave a conflict with no
resolution, the Nixon diamond of Figure 2.7; the substrate's search resolves it by the order
of the isA links (`nixon_war`, `nixon_war_swapped`), and only Nixon's own choice, a copy of
*accepts war* at his node, settles it independently of order (`nixon_resolved`). Choice sets
prevent such conflicts from arising (`choiceSet_sex`).

Relational concepts are defined in terms of existing ones: *parent* merges *mother* and
*father*, *grandmother* is the mother of a parent, and *ancestor* is the recursive closure of
*parent* (Section 3.2.7, `ancestor`). The definition of *grandmother* is a relational
`Triangle`, one node's two relations converging on a third, and the same triangle is the
syntactic pattern of raising: an auxiliary's subject is also its valent's subject
(Figure 7.6). Closing the asserted subjects under the triangle along the valent chain
(`raise`) makes *he* the subject of every verb in *He keeps seeming to have forgotten to go*
(Figure 7.12, `he_subject_of_go`).

## Implementation notes

* Properties are `prop` links to value nodes, so that two values of one relation compete as
  Section 3.5.3 requires; the sample networks are stated directly rather than drawn from a
  fragment.
* The kinship system of Figure 8.16 is built from `mother` and `father` on an arbitrary type
  of people, with sex as predicates; the compositions are mathlib's `Relation.Comp` and
  `Relation.TransGen`.

## References

* [hudson-2010]
-/

namespace Hudson2010

open WordGrammar.Inheritance

/-! ### Default inheritance -/

/-- The taxonomy of Figure 2.8: birds, the typical sparrow, the exceptional penguin, an
exemplar of each, and the property values. -/
inductive Bird where
  | bird
  | sparrow
  | penguin
  | e1
  | e2
  | flies
  | doesntFly
  | laysEggs
  deriving DecidableEq, Repr

/-- The relations of Figure 2.8: how a bird moves and how it reproduces. -/
inductive BirdRel where
  | flight
  | reproduction
  deriving DecidableEq, Repr

def birdNet : Network Bird BirdRel where
  links :=
    [ ⟨.prop, .bird, .laysEggs, some .reproduction⟩
    , ⟨.prop, .bird, .flies, some .flight⟩
    , ⟨.isA, .sparrow, .bird, none⟩
    , ⟨.isA, .penguin, .bird, none⟩
    , ⟨.prop, .penguin, .doesntFly, some .flight⟩
    , ⟨.isA, .e1, .sparrow, none⟩
    , ⟨.isA, .e2, .penguin, none⟩ ]

theorem e2_IsA_bird : IsA birdNet .e2 .bird := by decide

theorem sparrow_not_IsA_penguin : ¬ IsA birdNet .sparrow .penguin := by decide

/-- A sparrow exemplar inherits the defaults of *bird*. -/
theorem e1_flight : inherited birdNet .e1 .flight = [.flies] := by decide

/-- A penguin exemplar inherits *doesn't fly*, the lower of the competing properties
(Section 2.5.3). -/
theorem e2_flight : inherited birdNet .e2 .flight = [.doesntFly] := by decide

/-- The override leaves the other defaults intact. -/
theorem e2_reproduction : inherited birdNet .e2 .reproduction = [.laysEggs] := by decide

/-- Figure 3.18: petrol is the default car fuel and diesel the exception. -/
inductive Car where
  | car
  | dieselCar
  | e
  | e'
  | petrol
  | diesel
  deriving DecidableEq, Repr

inductive CarRel where
  | fuel
  deriving DecidableEq, Repr

def carNet : Network Car CarRel where
  links :=
    [ ⟨.prop, .car, .petrol, some .fuel⟩
    , ⟨.isA, .dieselCar, .car, none⟩
    , ⟨.prop, .dieselCar, .diesel, some .fuel⟩
    , ⟨.isA, .e, .dieselCar, none⟩
    , ⟨.isA, .e', .car, none⟩ ]

/-- The diesel car exemplar inherits the link to *diesel* before it reaches *petrol*. -/
theorem e_fuel : inherited carNet .e .fuel = [.diesel] := by decide

theorem e'_fuel : inherited carNet .e' .fuel = [.petrol] := by decide

/-! ### The Nixon diamond and choice sets -/

/-- Figure 2.7: Nixon is both a Republican and a Quaker, and the two disagree about war. -/
inductive Person where
  | person
  | republican
  | quaker
  | nixon
  | acceptsWar
  | rejectsWar
  deriving DecidableEq, Repr

inductive PersonRel where
  | war
  deriving DecidableEq, Repr

def nixonNet : Network Person PersonRel where
  links :=
    [ ⟨.isA, .republican, .person, none⟩
    , ⟨.isA, .quaker, .person, none⟩
    , ⟨.prop, .republican, .acceptsWar, some .war⟩
    , ⟨.prop, .quaker, .rejectsWar, some .war⟩
    , ⟨.isA, .nixon, .republican, none⟩
    , ⟨.isA, .nixon, .quaker, none⟩ ]

/-- The same diamond with Nixon's two isA links in the other order. -/
def nixonNetSwapped : Network Person PersonRel where
  links :=
    [ ⟨.isA, .republican, .person, none⟩
    , ⟨.isA, .quaker, .person, none⟩
    , ⟨.prop, .republican, .acceptsWar, some .war⟩
    , ⟨.prop, .quaker, .rejectsWar, some .war⟩
    , ⟨.isA, .nixon, .quaker, none⟩
    , ⟨.isA, .nixon, .republican, none⟩ ]

theorem nixon_IsA_republican : IsA nixonNet .nixon .republican := by decide

theorem nixon_IsA_quaker : IsA nixonNet .nixon .quaker := by decide

/-- The book leaves the diamond without a recognized resolution; the substrate's search
returns whichever parent's value it meets first, so the answer turns on the order of the
links. -/
theorem nixon_war : inherited nixonNet .nixon .war = [.acceptsWar] := by decide

theorem nixon_war_swapped : inherited nixonNetSwapped .nixon .war = [.rejectsWar] := by decide

/-- Nixon's resolution (Section 2.4.2): a copy of *accepts war* at his own node wins by the
Best Fit Principle whatever the order of the links. -/
def nixonResolved : Network Person PersonRel where
  links := ⟨.prop, .nixon, .acceptsWar, some .war⟩ :: nixonNetSwapped.links

theorem nixon_resolved : inherited nixonResolved .nixon .war = [.acceptsWar] :=
  bestFit_local _ _ _ (by decide)

/-- Figure 3.8: sex is a choice between *male* and *female*, which prevents a person from
inheriting both. -/
inductive Sex where
  | sex
  | male
  | female
  deriving DecidableEq, Repr

def sexNet : Network Sex Empty where
  links := [⟨.or, .male, .sex, none⟩, ⟨.or, .female, .sex, none⟩]

theorem choiceSet_sex : choiceSet sexNet .sex = [.male, .female] := by decide

/-! ### Relational concepts -/

section Kinship

variable {α : Type*} (mother father : α → α → Prop) (male female : α → Prop)

/-- Figure 8.16 (a): a person's parent is either their mother or their father. -/
def parent (x p : α) : Prop := mother x p ∨ father x p

/-- Figure 8.16 (b): a person's child is anyone whose parent they are. -/
def child (x c : α) : Prop := parent mother father c x

/-- Figure 3.7: a grandmother is the mother of a parent, a relational triangle. -/
def grandmother : α → α → Prop := Relation.Comp (parent mother father) mother

/-- Figure 3.17: a grandparent is a parent's parent. -/
def grandparent : α → α → Prop := Relation.Comp (parent mother father) (parent mother father)

/-- Figure 3.17: a great-grandparent is a grandparent's parent, and the Recycling Principle
of Section 3.5.2 builds it on *grandparent* rather than as the parent of a parent of a
parent, to which it is nonetheless equal. -/
theorem comp_grandparent_parent :
    Relation.Comp (grandparent mother father) (parent mother father) =
      Relation.Comp (parent mother father)
        (Relation.Comp (parent mother father) (parent mother father)) :=
  Relation.comp_assoc

/-- Section 3.2.7: a person's ancestor is either their parent or an ancestor of their
parent, the recursive definition. -/
def ancestor : α → α → Prop := Relation.TransGen (parent mother father)

theorem ancestor_iff (x a : α) :
    ancestor mother father x a ↔
      parent mother father x a ∨ ∃ p, parent mother father x p ∧ ancestor mother father p a := by
  constructor
  · intro h
    obtain ⟨p, hxp, hpa⟩ := Relation.TransGen.head'_iff.1 h
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hpa with rfl | hpa
    · exact Or.inl hxp
    · exact Or.inr ⟨p, hxp, hpa⟩
  · rintro (h | ⟨p, hxp, hpa⟩)
    · exact Relation.TransGen.single h
    · exact Relation.TransGen.head hxp hpa

/-- A grandparent is an ancestor. -/
theorem ancestor_of_grandparent {x g : α} (h : grandparent mother father x g) :
    ancestor mother father x g :=
  let ⟨_, hxp, hpg⟩ := h
  Relation.TransGen.head hxp (Relation.TransGen.single hpg)

/-- Figure 8.16 (c): brothers and sisters are the sons and daughters of a parent. -/
def brother (x b : α) : Prop := Relation.Comp (parent mother father) (child mother father) x b ∧
  male b ∧ x ≠ b

def sister (x s : α) : Prop := Relation.Comp (parent mother father) (child mother father) x s ∧
  female s ∧ x ≠ s

/-- Figure 8.16 (d): uncles and aunts are the brothers and sisters of a parent. -/
def uncle : α → α → Prop := Relation.Comp (parent mother father) (brother mother father male)

def aunt : α → α → Prop := Relation.Comp (parent mother father) (sister mother father female)

/-- A parent's brother is an uncle, though not conversely once Figure 8.16 (e) extends the
relation to the husbands of aunts. -/
theorem uncle_of_parent_brother {x p u : α} (hp : parent mother father x p)
    (hb : brother mother father male p u) : uncle mother father male x u :=
  ⟨p, hp, hb⟩

end Kinship

/-! ### Triangles in kinship and in syntax -/

section Triangle

variable {α : Type*}

/-- The triangle of Figure 7.6: a node's `r₁` value and `r₂` value stand in `r₃`. -/
def Triangle (r₁ r₂ r₃ : α → α → Prop) : Prop := ∀ x y z, r₁ x y → r₂ x z → r₃ y z

/-- In kinship: a person's mother is their child's grandmother. -/
theorem triangle_grandmother (mother father : α → α → Prop) :
    Triangle (child mother father) mother (grandmother mother father) :=
  λ x _ _ hc hm => ⟨x, hc, hm⟩

variable (valent subj : α → α → Prop)

/-- Raising, the syntactic triangle: a word's subject is also its valent's subject. -/
def Raising : Prop := Triangle valent subj subj

/-- The subjects derived from the asserted ones by closing under the triangle along the
valent chain. -/
def raise (v s : α) : Prop := ∃ h, subj h s ∧ Relation.ReflTransGen valent h v

theorem subj_le_raise : ∀ x s, subj x s → raise valent subj x s :=
  λ x _ h => ⟨x, h, Relation.ReflTransGen.refl⟩

/-- The derived subjects satisfy the triangle. -/
theorem raising_raise : Raising valent (raise valent subj) :=
  λ _ _ _ hv ⟨h, hs, hchain⟩ => ⟨h, hs, hchain.tail hv⟩

/-- Any subject relation containing the asserted subjects and closed under the triangle
contains the derived subjects: `raise` is the least closure. -/
theorem raise_le_of_raising {S : α → α → Prop} (hS : Raising valent S)
    (hsubj : ∀ x s, subj x s → S x s) : ∀ v s, raise valent subj v s → S v s := by
  rintro v s ⟨h, hs, hchain⟩
  induction hchain with
  | refl => exact hsubj _ _ hs
  | tail _ hv ih => exact hS _ _ _ hv ih

/-- Section 7.2.6: the subject is shared down a chain of valents, however long, the
recursion of Figure 7.12. -/
theorem raise_of_transGen {h v s : α} (hs : subj h s) (hchain : Relation.TransGen valent h v) :
    raise valent subj v s :=
  ⟨h, hs, hchain.to_reflTransGen⟩

end Triangle

/-! ### Figure 7.12 -/

/-- The words of *He keeps seeming to have forgotten to go*. -/
inductive W where
  | he
  | keeps
  | seeming
  | to₁
  | have
  | forgotten
  | to₂
  | go
  deriving DecidableEq, Repr

/-- The valent chain of Figure 7.12, each verb's valent the next. -/
def valent : W → W → Prop
  | .keeps, .seeming | .seeming, .to₁ | .to₁, .have | .have, .forgotten
  | .forgotten, .to₂ | .to₂, .go => True
  | _, _ => False

/-- The one asserted subject: *he* is the subject of *keeps*. -/
def asserted : W → W → Prop
  | .keeps, .he => True
  | _, _ => False

/-- *He* is the subject of *go*, six triangles down the chain. -/
theorem he_subject_of_go : raise valent asserted .go .he := by
  refine ⟨.keeps, trivial, ?_⟩
  exact (((((Relation.ReflTransGen.refl.tail (c := W.seeming) trivial).tail (c := W.to₁)
    trivial).tail (c := W.have) trivial).tail (c := W.forgotten) trivial).tail (c := W.to₂)
    trivial).tail (c := W.go) trivial

end Hudson2010
