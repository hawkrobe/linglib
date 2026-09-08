import Linglib.Semantics.Modification.Classification
import Linglib.Semantics.Modification.Coercion
import Linglib.Studies.Partee2010

/-!
# Del Pinal (2015): Dual Content Semantics, privative adjectives, and dynamic compositionality

This file formalizes the dual-content semantics of [delpinal-2015] for privative adjectives.
A common noun's meaning is a tuple of its extension-determining E-structure and a
C-structure of four qualia after [pustejovsky-1995], (7) and (8), and a privative adjective
is a lexicalized semantic restructuring operator whose components each take the noun's full
meaning, so that the functional application of [heim-kratzer-1998] becomes the pointwise rule
FA_DC of §3. The entry for *fake*, (16), says that a fake N is not an N, does not have N's
origin and was made to look like an N, keeps N's constitutive and formal qualia, negates its
telic and records the making as its agentive; *counterfeit*, (11), is made to look and to
function like an N, *artificial*, (12), only to function like one, and *typical*, (13), is an
N with every quale of its C-structure. The C-structure does work that the E-structure alone
cannot: a typical fake gun looks like a gun and cannot shoot, (18), where a fake gun, (10),
may be badly made or fire; a fake need not function and an artificial heart need not look
like a heart; and with an intersective modifier as a restructuring operator, (20), *fake*
applied to *plastic* before *gun* yields a real gun made of fake plastic, while applied to
*plastic gun* it denies the compound. Against the shifting-heads account of [partee-2010],
§5, the E-structure of *fake* is privative in the sense of [kamp-1975], so the non-vacuity
principle can license no coercion of the head, and none is needed: the literal
interpretation already has a positive and a negative extension.

## Implementation notes

The paper's making events, `∃e[making(e) ∧ goal(e, P(x))]`, are a primitive `made P` on
properties, so no event substrate is assumed and nothing about it, such as monotonicity in
the goal, is. A quale a term has no value for is the trivial property, footnote 10, which is
why the intersective operator conjoins every quale where (20) leaves *plastic*'s empty telic
to the noun. The paper gives full entries only for *fake* and *plastic*; *counterfeit*,
*artificial* and *typical* are stated on E-structure alone, as in (11) to (13).

## TODO

Section 3 also attributes to the bracketing [fake [plastic gun]] a reading on which a fake
plastic gun is a real gun made of plastic. Under (16) applied to (21) that reading is not
derivable, since the E-structure denies the compound *plastic gun*; the reading the text
derives from [[fake plastic] gun] is (`fake_intersective_extension_le`).

## References

* [delpinal-2015]
* [pustejovsky-1995]
* [heim-kratzer-1998]
* [partee-2010]
* [kamp-1975]
-/

namespace DelPinal2015

open Modification Modifier

variable {W E : Type*}

/-! ### Dual content and FA_DC -/

/-- A dual-content meaning, the tuple `⟨E, Q_C, Q_F, Q_T, Q_A⟩` of §3: the E-structure and
the constitutive, formal, telic and agentive qualia; a quale the term has no value for is
the trivial property. -/
structure DualContent (W E : Type*) where
  extension : Property W E
  constitutive : Property W E
  formal : Property W E
  telic : Property W E
  agentive : Property W E

/-- A semantic restructuring operator, the entry of a modifier: each component takes the
full meaning of the modified noun. -/
structure Restructuring (W E : Type*) where
  extension : DualContent W E → Property W E
  constitutive : DualContent W E → Property W E
  formal : DualContent W E → Property W E
  telic : DualContent W E → Property W E
  agentive : DualContent W E → Property W E

/-- FA_DC, §3: the modifier's E-structure applied to the noun's meaning, and each quale of the
modifier applied to the noun's meaning. -/
def Restructuring.apply (A : Restructuring W E) (N : DualContent W E) : DualContent W E :=
  ⟨A.extension N, A.constitutive N, A.formal N, A.telic N, A.agentive N⟩

/-- The classical modifier meaning an operator projects: the E-structure of its output over a
lexicon assigning each property a dual content. -/
def Restructuring.toModifier (A : Restructuring W E) (lex : Property W E → DualContent W E) :
    Modifier (Property W E) :=
  λ P => (A.apply (lex P)).extension

/-- The intersective operator a noun's dual content type-shifts to, (20): each component
conjoined with the noun's. -/
def DualContent.intersective (P : DualContent W E) : Restructuring W E where
  extension N := λ w x => P.extension w x ∧ N.extension w x
  constitutive N := λ w x => P.constitutive w x ∧ N.constitutive w x
  formal N := λ w x => P.formal w x ∧ N.formal w x
  telic N := λ w x => P.telic w x ∧ N.telic w x
  agentive N := λ w x => P.agentive w x ∧ N.agentive w x

/-! ### The entries -/

section Entries

/-! `made P` is made with the goal that `P` hold, the paper's `∃e[making(e) ∧ goal(e, P(x))]`. -/

variable (made : Property W E → Property W E)

/-- *fake*, (16): a fake N is not an N, does not have N's origin, and was made to look like an
N; it keeps N's constitutive and formal qualia, negates the telic, and has the making as its
agentive. -/
def fake : Restructuring W E where
  extension N := λ w x => ¬ N.extension w x ∧ ¬ N.agentive w x ∧ made N.formal w x
  constitutive N := N.constitutive
  formal N := N.formal
  telic N := λ w x => ¬ N.telic w x
  agentive N := made N.formal

/-- The E-structure of *counterfeit*, (11): made to look and to function like an N. -/
def counterfeitE (N : DualContent W E) : Property W E :=
  λ w x => ¬ N.extension w x ∧ ¬ N.agentive w x ∧ made (λ w x => N.formal w x ∧ N.telic w x) w x

/-- The E-structure of *artificial*, (12): made to function like an N, with no commitment to
looking like one. -/
def artificialE (N : DualContent W E) : Property W E :=
  λ w x => ¬ N.extension w x ∧ ¬ N.agentive w x ∧ made N.telic w x

end Entries

/-- The E-structure of *typical*, (13): an N with every quale of its C-structure. -/
def typicalE (N : DualContent W E) : Property W E :=
  λ w x => N.extension w x ∧ N.constitutive w x ∧ N.formal w x ∧ N.telic w x ∧ N.agentive w x

/-- *typical* is subsective. -/
theorem typicalE_le (N : DualContent W E) (w : W) (x : E) (h : typicalE N w x) :
    N.extension w x :=
  h.1

/-! ### What C-structure adds -/

section Contrasts

variable (made : Property W E → Property W E)

/-- (18): a typical fake N looks like an N and cannot serve N's function, read off the
C-structure that (16) gives *fake N*. -/
theorem typical_fake_formal_not_telic (N : DualContent W E) (w : W) (x : E)
    (h : typicalE ((fake made).apply N) w x) : N.formal w x ∧ ¬ N.telic w x :=
  ⟨h.2.2.1, h.2.2.2.1⟩

/-- A fake N alone, (10), settles neither: a badly made fake need not look like an N, and a
malfunctioning one may still serve its function. -/
theorem fake_not_formal_not_telic :
    ∃ (W E : Type) (made : Property W E → Property W E) (N : DualContent W E) (w : W) (x : E),
      ((fake made).apply N).extension w x ∧ ¬ N.formal w x ∧ N.telic w x :=
  ⟨Unit, Bool, λ _ _ _ => True,
    ⟨λ _ x => x = true, λ _ _ => True, λ _ x => x = true, λ _ _ => True, λ _ _ => False⟩,
    (), false, by simp [Restructuring.apply, fake], by simp, trivial⟩

/-- A fake need not be made to function like an N, which a counterfeit is, (11). -/
theorem fake_not_made_telic :
    ∃ (W E : Type) (made : Property W E → Property W E) (N : DualContent W E) (w : W) (x : E),
      ((fake made).apply N).extension w x ∧ ¬ made (λ w x => N.formal w x ∧ N.telic w x) w x :=
  ⟨Unit, Bool, id,
    ⟨λ _ x => x = true, λ _ _ => True, λ _ _ => True, λ _ _ => False, λ _ _ => False⟩,
    (), false, by simp [Restructuring.apply, fake], by simp⟩

/-- An artificial heart need not be made to look like a heart, (12), where fakes and
counterfeits are. -/
theorem artificial_not_made_formal :
    ∃ (W E : Type) (made : Property W E → Property W E) (N : DualContent W E) (w : W) (x : E),
      artificialE made N w x ∧ ¬ made N.formal w x :=
  ⟨Unit, Bool, id,
    ⟨λ _ x => x = true, λ _ _ => True, λ _ x => x = true, λ _ _ => True, λ _ _ => False⟩,
    (), false, by simp [artificialE], by simp⟩

/-! ### Bracketing, §3 -/

/-- [[fake plastic] gun]: a real gun, made of fake plastic. -/
theorem fake_intersective_extension_le (P N : DualContent W E) (w : W) (x : E)
    (h : (((fake made).apply P).intersective.apply N).extension w x) :
    N.extension w x ∧ ¬ P.extension w x :=
  ⟨h.2, h.1.1⟩

/-- [fake [plastic gun]]: not a plastic gun. -/
theorem fake_apply_intersective_not (P N : DualContent W E) (w : W) (x : E)
    (h : ((fake made).apply (P.intersective.apply N)).extension w x) :
    ¬ (P.extension w x ∧ N.extension w x) :=
  h.1

/-! ### Against shifting heads, §5 -/

/-- On E-structure *fake* is privative in the sense of [kamp-1975], over any lexicon whose
E-structures are the properties themselves. -/
theorem fake_toModifier_isPrivative (lex : Property W E → DualContent W E)
    (hlex : ∀ P, (lex P).extension = P) : isPrivative ((fake made).toModifier lex) :=
  isPrivative_iff.2 λ P _ _ h => (hlex P ▸ h.1 :)

/-- So the non-vacuity principle licenses no coercion of the head, [partee-2010]'s
obstruction. -/
theorem fake_no_licensedCoercion (lex : Property W E → DualContent W E)
    (hlex : ∀ P, (lex P).extension = P) (P : Property W E) (w : W) :
    IsEmpty (LicensedCoercion P ((fake made).toModifier lex) w) :=
  Partee2010.isPrivative_no_LicensedCoercion (fake_toModifier_isPrivative made lex hlex) P w

end Contrasts

/-- And none is needed: the literal interpretation of *fake N* has a positive and a negative
extension, so its default interpretation involves no violation of non-vacuity. -/
theorem fake_isNonVacuous :
    ∃ (W E : Type) (made : Property W E → Property W E) (N : DualContent W E) (w : W),
      isNonVacuous ((fake made).apply N).extension w (λ _ => True) :=
  ⟨Unit, Bool, λ _ _ _ => True,
    ⟨λ _ x => x = true, λ _ _ => True, λ _ _ => True, λ _ _ => True, λ _ _ => False⟩, (),
    ⟨false, trivial, by simp [Restructuring.apply, fake]⟩,
    ⟨true, trivial, by simp [Restructuring.apply, fake]⟩⟩

end DelPinal2015
