import Linglib.Semantics.Genericity.NominalMappingParameter
import Mathlib.Data.Set.Card
import Mathlib.Order.SupClosed

/-!
# Krifka (2003): Bare NPs: Kind-referring, Indefinites, Both, or Neither?

This file formalizes [krifka-2003]'s account of bare noun phrases as properties that locally
triggered type shifts coerce to indefinite or to kind-referring interpretations: in the terms
of the title, neither kind-referring nor indefinites, but shiftable to both. The account keeps
the type-shift framework of [chierchia-1998], with its blocking by overt determiners, and
drops the derived kind predication rule and the restriction of kind formation to cumulative
properties. Count nouns are relations between numbers and individuals, extensive measure
functions in the number argument (`CountNoun`), so a singular count noun is not of the type
of an argument, which is why *dog* cannot be bare; number words and the semantic plural
saturate the number argument, the plural without a condition that the number exceed one,
since *Do you have dogs?* is answered by *Yes, one*. The existential type shift resolves the
mismatch between a nominal and a verbal predicate where it arises, so a bare plural takes
narrow scope under negation even when moved over it (`Den.movedNeutral`), whereas a
determiner phrase binds an entity variable and scopes wide; *two dogs* scopes wide only as a
determiner phrase. Kind reference is the down operator, the greatest element of a property's
extension (`down`), which exists for finite, nonempty, cumulative extensions but is not
confined to them.

## Implementation notes

* Composition is stated on extensions at a world. The composition rule (51) is `Den.app`:
  functional application whichever way is well formed, and otherwise the existential shift of
  a predicate meeting a verbal predicate. Movement over negation binds a type-neutral
  variable, which substitutes the moved denotation at its trace, or an entity variable, which
  abstracts over the trace; a property has no rule for meeting the abstract, which is the
  paper's requirement that the trace of a bare noun phrase be untyped.
* Count nouns that count atoms (`ofAtoms`) witness the measure laws and yield the
  quantization of numeral phrases and the cumulativity of the semantic plural.
* The topic condition on kind reference, the choice-function reading of *some*, and the
  singular definite generics of the paper's last section are not formalized.

## References

* [krifka-2003]
* [chierchia-1998] — the type-shift framework, blocking, and derived kind predication
* [partee-1987] — the type shifts ∃, ι and BE
* [krifka-1989] — count nouns as measure functions
-/

namespace Krifka2003

open Semantics.Kinds.NMP Mereology

variable {World Atom : Type*}

/-! ### Count nouns as measure relations -/

/-- A count noun (52a): at each world, the individuals that consist of `n` instances. -/
abbrev CountNoun (World Atom : Type*) := World → ℕ → Set (Individual Atom)

/-- Count nouns are extensive measure functions in their number argument (53): the count of
an individual is unique, and the counts of non-overlapping individuals add. -/
def IsExtensiveMeasure (den : CountNoun World Atom) : Prop :=
  (∀ w n m x, x ∈ den w n → x ∈ den w m → n = m) ∧
  (∀ w n m x y, x ∈ den w n → y ∈ den w m → Disjoint x y → x ∪ y ∈ den w (n + m))

/-- A number word fills the number argument (54). -/
def withNumber (n : ℕ) (den : CountNoun World Atom) : Property World Atom := λ w => den w n

/-- The semantic plural (59b) binds the number argument existentially, with no condition that
the number exceed one. -/
def pluralize (den : CountNoun World Atom) : Property World Atom :=
  λ w => {x | ∃ n, x ∈ den w n}

/-- *Do you have dogs? Yes, one*: the semantic plural is true of a single instance. -/
theorem mem_pluralize_of_withNumber {den : CountNoun World Atom} {n : ℕ} {w : World}
    {x : Individual Atom} (h : x ∈ withNumber n den w) : x ∈ pluralize den w :=
  ⟨n, h⟩

/-- A count noun that counts atoms: `x` consists of `n` `D`s when it is a finite sum of `n`
atoms of `D`. -/
def ofAtoms (D : World → Set Atom) : CountNoun World Atom :=
  λ w n => {x | x ⊆ D w ∧ x.Finite ∧ x.ncard = n}

theorem isExtensiveMeasure_ofAtoms (D : World → Set Atom) : IsExtensiveMeasure (ofAtoms D) :=
  ⟨λ _ _ _ _ ⟨_, _, h⟩ ⟨_, _, h'⟩ => h.symm.trans h',
    λ _ _ _ _ _ ⟨hx, hfx, hnx⟩ ⟨hy, hfy, hny⟩ hd =>
      ⟨Set.union_subset hx hy, hfx.union hfy, by rw [Set.ncard_union_eq hd hfx hfy, hnx, hny]⟩⟩

/-- Numeral phrases are quantized: a proper part of `n` dogs is not `n` dogs. -/
theorem qua_withNumber_ofAtoms (D : World → Set Atom) (n : ℕ) (w : World) :
    QUA (· ∈ withNumber n (ofAtoms D) w) :=
  qua_of_forall λ _ _ ⟨_, hf, hn⟩ hlt ⟨_, _, hn'⟩ =>
    (Set.ncard_lt_ncard hlt hf).ne (hn'.trans hn.symm)

/-- The semantic plural of an atom-counting noun is cumulative. -/
theorem cum_pluralize_ofAtoms (D : World → Set Atom) (w : World) :
    CUM (· ∈ pluralize (ofAtoms D) w) :=
  λ _ ⟨_, hx, hfx, _⟩ _ ⟨_, hy, hfy, _⟩ => ⟨_, Set.union_subset hx hy, hfx.union hfy, rfl⟩

/-! ### Kind reference -/

/-- The down operator (77): the greatest element of the property's extension, where there is
one. It is not confined to cumulative properties. -/
def down (P : Property World Atom) (w : World) (k : Individual Atom) : Prop :=
  IsGreatest (P w) k

/-- A finite, nonempty, cumulative extension has a greatest element, the sum of its members. -/
theorem exists_down_of_cum {P : Property World Atom} {w : World} (hfin : (P w).Finite)
    (hne : (P w).Nonempty) (hcum : CUM (· ∈ P w)) : ∃ k, down P w k :=
  have ht : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.2 hne
  ⟨hfin.toFinset.sup' ht id, hcum.finsetSup'_mem ht λ _ hx => hfin.mem_toFinset.1 hx,
    λ _ hx => Finset.le_sup' id (hfin.mem_toFinset.2 hx)⟩

/-- The down operator applies to a singular count noun where there is a single instance: in a
world with exactly one dog, `∩[one dog]` is that dog. -/
theorem down_withNumber_one {D : World → Set Atom} {w : World} {a : Atom} (h : D w = {a}) :
    down (withNumber 1 (ofAtoms D)) w {a} :=
  ⟨⟨h ▸ subset_rfl, Set.finite_singleton a, Set.ncard_singleton a⟩, λ _ ⟨hx, _, _⟩ => h ▸ hx⟩

/-! ### Composition and narrow scope -/

/-- The extensions that composition manipulates (51): entities, predicates, verbal predicates,
quantifiers and truth values. -/
inductive Den (E : Type*)
  | ent (x : E)
  | pred (P : E → Prop)
  | vp (V : E → Prop)
  | quant (Q : (E → Prop) → Prop)
  | tv (p : Prop)

namespace Den

variable {E : Type*}

/-- Partee's existential shift (30a). -/
def existsShift (P : E → Prop) : (E → Prop) → Prop := λ Q => ∃ x, P x ∧ Q x

/-- The composition rule (51): functional application whichever way is well formed, and
otherwise the existential shift of a predicate meeting a verbal predicate. -/
def app : Den E → Den E → Option (Den E)
  | pred P, ent x | ent x, pred P | vp P, ent x | ent x, vp P => some (tv (P x))
  | quant Q, vp V | vp V, quant Q | quant Q, pred V | pred V, quant Q => some (tv (Q V))
  | pred P, vp V | vp V, pred P => some (tv (existsShift P V))
  | _, _ => none

/-- Negation. -/
def neg : Den E → Option (Den E)
  | tv p => some (tv (¬ p))
  | _ => none

/-- Movement over negation binding a type-neutral variable (70): the moved denotation is
substituted at its trace, where it meets the verbal predicate. -/
def movedNeutral (d : Den E) (V : E → Prop) : Option (Den E) := (d.app (vp V)).bind neg

/-- Movement over negation binding an entity variable (71): the moved denotation applies to
the abstract over the trace. -/
def movedEntity (d : Den E) (V : E → Prop) : Option (Den E) := d.app (pred λ x => ¬ V x)

/-- *Dogs are barking* (69): a bare noun phrase meets the verbal predicate by the existential
shift. -/
theorem app_pred_vp (P V : E → Prop) : (pred P).app (vp V) = some (tv (∃ x, P x ∧ V x)) := rfl

/-- *Dogs aren't barking* (70): moved over negation, a bare noun phrase still scopes below it,
since the shift applies at the trace. -/
theorem movedNeutral_pred (P V : E → Prop) :
    movedNeutral (pred P) V = some (tv (¬ ∃ x, P x ∧ V x)) := rfl

/-- A property cannot bind an entity variable: there is no wide-scope derivation for a bare
noun phrase. -/
theorem movedEntity_pred (P V : E → Prop) : movedEntity (pred P) V = none := rfl

/-- *A dog isn't barking* with a quantifier variable (71.c.ii): negation scopes over the
quantifier. -/
theorem movedNeutral_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedNeutral (quant Q) V = some (tv (¬ Q V)) := rfl

/-- *A dog isn't barking* with an entity variable (71.c.i): the quantifier scopes over
negation. -/
theorem movedEntity_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedEntity (quant Q) V = some (tv (Q λ x => ¬ V x)) := rfl

end Den

/-- A bare plural at a world: the property the semantic plural yields. -/
def bare (den : CountNoun World Atom) (w : World) : Den (Individual Atom) :=
  .pred (· ∈ pluralize den w)

/-- A determiner phrase with a number word ((67), (72)): the indefinite article is the number
word *one* as a determiner, with existential force. -/
def indefinite (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Individual Atom) :=
  .quant λ P => ∃ x, x ∈ den w n ∧ P x

/-- A noun phrase with a number word (54): a predicate, so it scopes like a bare plural. -/
def numeral (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Individual Atom) :=
  .pred (· ∈ den w n)

/-- Bare plurals scope below negation whether moved or not, and cannot scope above it. -/
theorem bare_narrow (den : CountNoun World Atom) (w : World) (V : Individual Atom → Prop) :
    (bare den w).movedNeutral V = some (.tv (¬ ∃ x, (∃ n, x ∈ den w n) ∧ V x)) ∧
      (bare den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

/-- *Two dogs aren't barking* (72)–(73): as a determiner phrase, a numeral phrase scopes over
negation; as a noun phrase it does not. -/
theorem indefinite_wide_numeral_narrow (n : ℕ) (den : CountNoun World Atom) (w : World)
    (V : Individual Atom → Prop) :
    (indefinite n den w).movedEntity V = some (.tv (∃ x, x ∈ den w n ∧ ¬ V x)) ∧
      (numeral n den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

end Krifka2003
