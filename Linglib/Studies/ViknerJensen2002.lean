import Linglib.Semantics.Possession.Quantifier
import Linglib.Studies.Pustejovsky1995
import Linglib.Data.Examples.ViknerJensen2002

/-!
# Vikner & Jensen (2002): A Semantic Analysis of the English Genitive

This file formalizes [vikner-jensen-2002], on which the prenominal genitive has one syntactic
type: the genitive phrase *a girl's* takes a relational noun and returns a generalized
quantifier, and a sortal head noun such as *car* is coerced into a relation by a
meaning-shifting operator that reads the relation off the qualia structure of its lexical
entry, after [pustejovsky-1995]. The genitive clitic (16) carries an implicit definite that
scopes under the possessor quantifier, so that *each girl's teacher* says that each girl has
exactly one teacher; a definite article composed outside the possessor would take wide scope,
and the two scopings part exactly when the possessor is quantified. The clitic is
[peters-westerstahl-2006]'s possessive quantifier over a whole possessor NP with the Russellian
definite as its possessee quantifier, the possessee class folded into the relation by the
coercion (`clitic`).

The operators Co, Ag and Te (23), (30), (47) are one shift over the constitutive, agentive and
telic qualia, [barker-2011]'s relationalizer applied to the quale's relation (`Sense.shift`),
and Ctr and Prag (33), (36) are the same relationalizer over the control and the contextual
relation. The lexical interpretations of a genitive, `Possession.RelationType`, are the
relational nouns the rules (55e), (55f) build from a sense (`Sense.genitive`); a selectional
restriction on a relation, such as animacy of a controller, empties a reading rather than
blocking it. *Favourite* (43) maps a relation to the relation of being preferred among the
relata (`favourite`), keeps the head's relation, is unique under an asymmetric preference, and
on a sortal noun reaches only the telic quale, so that *Mary's movie* has two lexical
interpretations where *Mary's favourite movie* has one and *Anne's favourite sky* has none.

## Implementation notes

Qualia are stored with the related entity first, `q y x` reading *x has y as its whole, agent
or user*, the passive orientation of footnote 17, so that every shift is the relationalizer;
nothing here turns on the orientation. Selectional restrictions are meaning postulates on the
relations, as the paper leaves them out of its derivations. A noun with both a relational and a
sortal use, *teacher*, is two senses. Postnominal and predicative genitives, the sort
hierarchy, and the `HeadPred` revision of the shifts for N-bars with complements (53) are not
formalized.

## References

* [vikner-jensen-2002]
* [pustejovsky-1995]
* [barker-1995], [barker-2011]
* [partee-1997]
* [peters-westerstahl-2006]
-/

namespace ViknerJensen2002

open Possession Quantification

variable {E S : Type*}

/-! ### The genitive clitic -/

/-- The genitive clitic (16) applied to a possessor NP and a relational noun, at a situation: the
possessive quantifier over the whole NP with the Russellian definite as possessee quantifier,
the possessee class already inside the relation. -/
def clitic (Q : Quantifier E) (R : E → E → S → Prop) (s : S) : Quantifier E :=
  PossNP Q the_sem (λ u x => R u x s) (λ _ => True)

/-- The clitic is the paper's (16): the possessor quantifier over the property of having a unique
relatum that is `P`, the definite scoping under the possessor. -/
theorem clitic_apply (Q : Quantifier E) (R : E → E → S → Prop) (s : S) (P : E → Prop) :
    clitic Q R s P ↔ Q (λ u => ∃ x, (∀ y, R u y s ↔ y = x) ∧ P x) := by
  simp only [clitic, PossNP, dom, the_sem, true_and]
  refine iff_of_eq (congrArg Q (funext λ a => propext (and_iff_right_of_imp ?_)))
  rintro ⟨x, hx, -⟩
  exact ⟨x, (hx x).2 rfl⟩

/-- Over a coerced sortal noun the clitic is the possessive quantifier with the sortal as the
possessee class and the free relation as the possession relation. -/
theorem clitic_pi (Q : Quantifier E) (W : E → S → Prop) (R : E → E → S → Prop) (s : S) :
    clitic Q (π W R) s = PossNP Q the_sem (λ u x => R u x s) (λ x => W x s) := by
  funext P
  simp only [clitic, PossNP, dom, the_sem, π, true_and]

/-- The implicit definite: an individual's genitive entails a unique relatum. -/
theorem existsUnique_of_clitic_individual {a : E} {R : E → E → S → Prop} {s : S}
    {P : E → Prop} (h : clitic (individual a) R s P) : ∃! y, R a y s := by
  obtain ⟨x, hx, -⟩ := (clitic_apply _ _ _ _).1 h
  exact ⟨x, (hx x).2 rfl, λ y hy => (hx y).1 hy⟩

/-- A relation the possessor bears to nothing, as when a selectional restriction of the relation
excludes it, gives an empty genitive: *the car's cake* on the control reading. -/
theorem not_clitic_individual {a : E} {R : E → E → S → Prop} {s : S} (h : ∀ x, ¬ R a x s)
    (P : E → Prop) : ¬ clitic (individual a) R s P := by
  rw [clitic_apply]
  rintro ⟨x, hx, -⟩
  exact h x ((hx x).2 rfl)

/-! ### The scope of the definite (§3.2.2) -/

/-- The Montagovian definite (13) composed outside the genitive phrase: the definite takes wide
scope over the possessor quantifier. -/
def wideDefinite (Q : Quantifier E) (R : E → E → S → Prop) (s : S) : Quantifier E :=
  the_sem (λ y => Q (λ u => R u y s))

/-- For an individual possessor the two scopings agree. -/
theorem clitic_individual (a : E) (R : E → E → S → Prop) (s : S) :
    clitic (individual a) R s = wideDefinite (individual a) R s := by
  funext P
  exact propext ((clitic_apply _ _ _ _).trans Iff.rfl)

/-- For a quantified possessor they part: with two girls with different teachers, *each girl's
teacher* is true on the clitic and false on the wide definite, (11b). -/
theorem exists_clitic_ne_wideDefinite :
    ∃ (Q : Quantifier (Fin 4)) (R : Fin 4 → Fin 4 → Unit → Prop) (P : Fin 4 → Prop),
      clitic Q R () P ∧ ¬ wideDefinite Q R () P :=
  ⟨every_sem (· < 2), λ u y _ => u = 0 ∧ y = 2 ∨ u = 1 ∧ y = 3, λ _ => True,
    by rw [clitic_apply]; unfold every_sem; decide,
    by simp only [wideDefinite, the_sem, every_sem]; decide⟩

/-! ### Senses and meaning shifts (§3.2.1, §3.2.3) -/

/-- The argument structure of a sense (9): a sortal predicate, or a relation with the relatum
first, `sister' y x` reading *x is a sister of y*. -/
inductive ArgStructure (E S : Type*)
  | sortal (W : E → S → Prop)
  | relational (R : E → E → S → Prop)

/-- A word sense: its argument structure and its qualia, each a relation with the related entity
first, the whole of the constitutive quale (22), the agent of the agentive quale and the user of
the telic quale (9). -/
structure Sense (E S : Type*) where
  arg : ArgStructure E S
  quale : Pustejovsky1995.QualeRole → Option (E → E → S → Prop)

namespace Sense

variable (σ : Sense E S)

/-- The sortal predicate of a sortal sense. -/
def sortal : Option (E → S → Prop) :=
  match σ.arg with
  | .sortal W => some W
  | .relational _ => none

/-- The inherent relation of a relational sense. -/
def inherent : Option (E → E → S → Prop) :=
  match σ.arg with
  | .sortal _ => none
  | .relational R => some R

/-- The meaning shift over a quale: the relationalizer opens a slot on the sortal predicate with
the quale's relation. Co (23), Ag (30) and Te (47) are the shifts over the constitutive, agentive
and telic qualia. -/
def shift (r : Pustejovsky1995.QualeRole) : Option (E → E → S → Prop) :=
  σ.sortal.bind λ W => (σ.quale r).map (π W)

/-- The shift over a relation not from the entry: Ctr (33) over the control relation, Prag (36)
over contextual relatedness. -/
def shiftWith (R : E → E → S → Prop) : Option (E → E → S → Prop) :=
  σ.sortal.map (π · R)

/-- The relational noun a genitive phrase takes from a sense for each relation type, the rules
(55e) and (55f) with the control relation `ctrl`; the pragmatic reading `shiftWith relatedTo` is
available besides. -/
def genitive (ctrl : E → E → S → Prop) : RelationType → Option (E → E → S → Prop)
  | .inherent => σ.inherent
  | .partWhole => σ.shift .constitutive
  | .agentive => σ.shift .agentive
  | .control => σ.shiftWith ctrl

/-- The lexical interpretations of a genitive over the sense (Table 2). -/
def lexical (ctrl : E → E → S → Prop) : Set RelationType :=
  {t | σ.genitive ctrl t ≠ none}

end Sense

/-- Column 2 of Table 2 as a consequence: the controller must be animate, so an inanimate
possessor's control reading is empty, *the car's cake*. -/
theorem not_clitic_control {ctrl : E → E → S → Prop} {animate : E → S → Prop}
    (hctrl : ∀ y x s, ctrl y x s → animate y s) {a : E} {s : S} (ha : ¬ animate a s)
    (W : E → S → Prop) (P : E → Prop) : ¬ clitic (individual a) (π W ctrl) s P :=
  not_clitic_individual (λ _ h => ha (hctrl _ _ _ h.2)) P

/-! ### *Favourite* (§4) -/

/-- *Favourite* (43) over a relation: `x` is the relatum `y` prefers among all its relata, where
`prefer T T' y s` reads *y prefers the state of affairs `T'` to `T`*. -/
def favourite (prefer : (S → Prop) → (S → Prop) → E → S → Prop) (R : E → E → S → Prop) :
    E → E → S → Prop :=
  λ y x s => R y x s ∧ ∀ z, R y z s ∧ z ≠ x → prefer (R y z) (R y x) y s

variable {prefer : (S → Prop) → (S → Prop) → E → S → Prop}

/-- A favourite relatum is a relatum: *Anne's favourite sister* is a sister of Anne's. -/
theorem favourite_rel {R : E → E → S → Prop} {y x : E} {s : S} (h : favourite prefer R y x s) :
    R y x s :=
  h.1

/-- Under an asymmetric preference the favourite is unique (footnote 21). -/
theorem favourite_subsingleton {R : E → E → S → Prop} {y : E} {s : S}
    (h : ∀ T T', prefer T T' y s → ¬ prefer T' T y s) :
    {x | favourite prefer R y x s}.Subsingleton :=
  λ x hx x' hx' => by_contra λ hne => h _ _ (hx.2 x' ⟨hx'.1, Ne.symm hne⟩) (hx'.2 x ⟨hx.1, hne⟩)

/-- The relational noun *favourite* builds from a sense, (55d) with (55e) and (55f): the inherent
relation of a relational sense, the telic shift of a sortal one. -/
def Sense.favourite (σ : Sense E S) (prefer : (S → Prop) → (S → Prop) → E → S → Prop) :
    Option (E → E → S → Prop) :=
  (σ.inherent <|> σ.shift .telic).map (ViknerJensen2002.favourite prefer)

/-! ### Predictions (§3.3, §4) -/

section Predictions

variable (ctrl : E → E → S → Prop)

/-- *sister*: relational (9). -/
def sister (sister' : E → E → S → Prop) : Sense E S := ⟨.relational sister', λ _ => none⟩

/-- *movie*, like *poem* and *car* in (9): a sortal artifact with an agentive and a telic quale. -/
def movie (movie' : E → S → Prop) (make watch : E → E → S → Prop) : Sense E S :=
  ⟨.sortal movie', λ r => match r with
    | .agentive => some make
    | .telic => some watch
    | _ => none⟩

/-- *sky*: sortal with no telic quale (§4). -/
def sky (sky' : E → S → Prop) : Sense E S := ⟨.sortal sky', λ _ => none⟩

variable (sister' : E → E → S → Prop) (movie' sky' : E → S → Prop) (make watch : E → E → S → Prop)

/-- *Anne's sister* and *Anne's favourite sister* express the same relation. -/
theorem sister_genitive_inherent : (sister sister').genitive ctrl .inherent = some sister' := rfl

theorem sister_favourite :
    (sister sister').favourite prefer = some (favourite prefer sister') := rfl

/-- *Mary's movie* has two lexical interpretations, the movie Mary made and the movie Mary
controls. -/
theorem movie_lexical : (movie movie' make watch).lexical ctrl = {.agentive, .control} := by
  ext t
  cases t <;> simp [Sense.lexical, Sense.genitive, Sense.shift, Sense.shiftWith, Sense.sortal,
    Sense.inherent, movie]

/-- *Mary's favourite movie* has one, the movie Mary prefers to watch, different from both. -/
theorem movie_favourite :
    (movie movie' make watch).favourite prefer = some (favourite prefer (π movie' watch)) := rfl

/-- *Anne's favourite sky* has no lexical interpretation, only pragmatic ones, since *sky* has no
telic quale. -/
theorem sky_favourite : (sky sky').favourite prefer = none := rfl

/-- The pragmatic reading of *Anne's favourite sky* is available all the same. -/
theorem sky_pragmatic (relatedTo : E → E → S → Prop) :
    (sky sky').shiftWith relatedTo = some (π sky' relatedTo) := rfl

end Predictions

end ViknerJensen2002
