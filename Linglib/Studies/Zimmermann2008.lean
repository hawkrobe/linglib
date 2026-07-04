import Linglib.Fragments.Hausa.Determiners
import Linglib.Semantics.Quantification.UnifiedUniversal
import Linglib.Semantics.Quantification.ONEModifiers
import Linglib.Semantics.Quantification.Basic

/-!
# [zimmermann-2008]: Quantification in Hausa

Selected formalization from Zimmermann's handbook chapter in
[matthewson-2008], the first formal-semantic treatment of the
Hausa quantifier system whose textbook description is given in
[newman-2000] and [jaggar-2001]. The two reference grammars
fix the inventory typed in `Hausa`; this file
consumes those entries, states Zimmermann's predicted denotations, and
checks their consequences on a small concrete model.

## Main declarations

* `Hausa.UniversalQuantifier.z2008Denot` —
  the predicted denotation each Hausa universal entry receives under
  Zimmermann 2008's GQ analysis, reframed via the
  [haslinger-etal-2025-nllt] Q_∀ + ONE decomposition.
* `Zimmermann2008.Faasinjee` — a 3-passenger SG-count domain
  instantiating the *kō-wh* restrictor case
  ([jaggar-2001] ex. *faasinjojî-n* p.376).
* `Zimmermann2008.kowWh_buckled_false` — *kō-wh*'s singulative-
  distributive prediction on a model where one passenger falsifies
  the scope.
* `Zimmermann2008.wani_ambiguity_witness` — *wani* under VP-negation
  is ambiguous (Jaggar §9.5.3 p.374, Z2008 §3.2.4 ex. 69); on this
  model the ∃¬ reading is true while the ¬∃ reading is false.

## Implementation notes

`z2008Denot` extends the Fragment's `UniversalQuantifier` namespace
with Zimmermann 2008's analytical bridge to substrate denotations.
The denotation is paper-specific (Z2008 §3.2.5 leaves the choice open
between GQ, indeterminate-pronoun, and choice-function); housing it on
the Fragment type via the Studies file follows the project pattern of
paper-specific methods on consensus typological entries. The
denotation for `kowWh` is `everyPresup` (Q_∀ + ONE_∅); for `duk` it is
bare `QForall` on a CUM lattice, but no concrete CUM-lattice model is
exhibited here (see Todo).

## References

* [newman-2000] §17.5, §20, §21 — Hausa reference grammar.
* [jaggar-2001] §9.5 — Hausa universal quantifiers.

## Todo

* CUM-lattice concrete model for *DUK* (Jaggar §9.5.4).
* *kō-wh* under VP-negation yielding negative-existential readings
  (Jaggar §9.5.3 p.374): *bàn gayà wà kōwā ba* 'I told no one'.
* Free-choice *kō-wh* in modal/intensional contexts (Z2008 §3.2.3).
* The Chadic typology of class-B universals (Z2008 §3.4).
-/

open Quantification.UnifiedUniversal
open Quantification.ONEModifiers

namespace Hausa.UniversalQuantifier

/-- [zimmermann-2008]'s predicted denotation for each Hausa
universal entry, reframed via the [haslinger-etal-2025-nllt]
Q_∀ + ONE decomposition. *kō-wh* receives Q_∀ + ONE_∅ (atom-by-atom
distributivity, Jaggar §9.5.1); *DUK* receives bare Q_∀ on a CUM
restrictor (collective single-set scope, Jaggar §9.5.4). -/
def z2008Denot {α : Type*} [PartialOrder α] :
    UniversalQuantifier → (α → Prop) → (α → Prop) → Prop
  | .kowWh => everyPresup
  | .duk   => QForall

end Hausa.UniversalQuantifier

namespace Zimmermann2008

open Hausa
open Quantification (some_sem)

/-! ### A 3-passenger SG-count Hausa domain

Three passengers (*faasinjojî* [jaggar-2001] §9.5.4 p.376) —
*Audù*, *Bàlki*, *Càdi* — board a plane; *Audù* and *Bàlki* buckle
their seatbelts, *Càdi* does not. The minimal SG-count atomic domain
on which *UniversalQuantifier.kowWh*'s atom-by-atom predication and
*Indefinite.wani*'s scope ambiguity under negation are observable. -/

/-- *faasinjèe* 'passenger'; *faasinjojî* PL.
[jaggar-2001] §9.5.4 p.376. -/
inductive Faasinjee where | audu | balki | cadi
  deriving DecidableEq, Repr

/-- Flat order: every passenger is an atom; distinct passengers do
not overlap. -/
instance : PartialOrder Faasinjee where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  le_antisymm _ _ h _ := h

/-- The flat `Faasinjee` order is an `IsAtomicDomain`; its atom/disjoint facts now
derive from the shared `Mereology` machinery rather than bespoke proofs. -/
instance : Mereology.IsAtomicDomain Faasinjee :=
  Mereology.isAtomicDomain_of_le_iff_eq (fun _ _ => Iff.rfl)

/-- *yā daurà wàndà* 'buckled their seatbelt'. -/
def Daura : Faasinjee → Prop
  | .audu => True
  | .balki => True
  | .cadi => False

instance : DecidablePred Daura := fun x => match x with
  | .audu => isTrue trivial
  | .balki => isTrue trivial
  | .cadi => isFalse id

/-! ### Mereological structure -/

theorem atom_of_faasinjee (x : Faasinjee) : Mereology.Atom x :=
  Mereology.IsAtomicDomain.all_atoms x

theorem faasinjee_disjoint (x y : Faasinjee) (h : Mereology.Overlap x y) :
    x = y := Mereology.IsAtomicDomain.eq_of_overlap h

/-- `ONE_empty` holds of the universal *faasinjèe* predicate. This is
the presupposition Z2008's *kō-wh* analysis (via Q_∀ + ONE_∅) places
on its SG-count restrictor. -/
theorem faasinjee_ONE_empty : ONE_empty (fun _ : Faasinjee => True) where
  has_two := ⟨.audu, .balki, trivial, trivial, by decide⟩
  pairwise_disjoint := fun x y _ _ h => faasinjee_disjoint x y h

/-! ### *UniversalQuantifier.kowWh* distributivity (Jaggar §9.5.1, Z2008 §4.2.1) -/

/-- *kōwānè faasinjèe yā daurà wàndà* 'every passenger buckled their
seatbelt' is false on this model: the *kowWh*-entry's denotation forces
atom-by-atom predication (Jaggar p.370), and *Càdi* falsifies the
scope. -/
theorem kowWh_daura_false :
    ¬ UniversalQuantifier.kowWh.z2008Denot (fun _ : Faasinjee => True) Daura := by
  intro ⟨_, hAll⟩
  exact (every_distributes faasinjee_ONE_empty).mp hAll .cadi trivial

/-! ### *Indefinite.wani* scope ambiguity under negation
(Jaggar §9.5.3, Z2008 §3.2.4 ex. 69)

The marked indefinite *wani faasinjèe bài daurà wàndà ba* '*wani*
passenger didn't buckle their seatbelt' is ambiguous between the
¬∃ reading ('no passenger buckled', preferred) and the ∃¬ reading
('some passenger didn't buckle'). On the 3-passenger model the
readings have *different truth values*: the ∃¬ reading is true
(*Càdi* witnesses), the ¬∃ reading is false (*Audù* and *Bàlki* did
buckle). Both readings are linguistically available; their truth
values diverge on this scenario. -/

/-- The wide-scope (∃¬) reading: ∃x. Faasinjèe(x) ∧ ¬Daura(x).
Witnessed by *Càdi*. -/
theorem wani_wide_scope :
    some_sem (fun _ : Faasinjee => True) (¬ Daura ·) :=
  ⟨.cadi, trivial, id⟩

/-- The narrow-scope (¬∃) reading: ¬∃x. Faasinjèe(x) ∧ Daura(x).
False on this model — *Audù* witnesses the negated existential. -/
theorem wani_narrow_scope_false :
    ¬ ¬ ∃ x : Faasinjee, Daura x := by
  intro h; exact h ⟨.audu, trivial⟩

/-- *Indefinite.wani* scope ambiguity, witnessed on a single model:
the ∃¬ reading is true and the ¬∃ reading is false simultaneously.
The empirical content of Z2008's ex. 69. -/
theorem wani_ambiguity_witness :
    some_sem (fun _ : Faasinjee => True) (¬ Daura ·) ∧
      ¬ ¬ ∃ x : Faasinjee, Daura x :=
  ⟨wani_wide_scope, wani_narrow_scope_false⟩

end Zimmermann2008
