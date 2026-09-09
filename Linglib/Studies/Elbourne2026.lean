import Linglib.Data.Examples.Elbourne2026
import Linglib.Semantics.Modification.Classification
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset

/-!
# Elbourne (2026): Adjectives without syntactic categories

This file formalizes [elbourne-2026]'s ⟨et,et⟩ theory of adjectives: an adjective denotes a
function from noun denotations to noun denotations, the type of [parsons-1970] and
[lewis-1970], so that its attributive combination with a noun is Functional Application, no rule
of Predicate Modification ([heim-kratzer-1998]) is needed, and every adjective has a single
semantic type, as the programme of replacing syntactic categories by semantic types
([elbourne-2024]) requires. The predicative use is handled by a copula that applies the adjective
to the trivial noun and quantifies over a time in the tense relation, so *Fido was cute* says
that Fido was cute at some earlier time; the indefinite article has a second meaning that turns
a noun into something of the adjective's type, which serves *Fido is a dog*. Intersective
adjectives are meet with a fixed property, the class of [kamp-1975] and [kamp-partee-1995], and
the ⟨e,t⟩ theory's Predicate Modification imposes exactly this semantics, so it cannot express
merely subsective or non-subsective adjectives ([beesley-1982]), whereas *former* has an
⟨et,et⟩ meaning under which a former judge is not a judge now. Adjectives that never stand alone
in predicative position, such as *former*, bear a compulsory selector feature that the copula
cannot select for; the Russian short-form adjectives of [morzycki-2015], which are predicative
only, lack the feature, and the long forms carry it optionally. The relational adjective
*local* carries a bound index rather than an internal argument, keeping it within the type;
[mcnally-boleda-2004]'s contrast between *young alleged murderer* and *alleged young murderer*
is a matter of scope within the type; and a gradable adjective with a degree argument returns to
the type under the positive morpheme of [cresswell-1976], the reply to [kennedy-2012] and to
[bolinger-1967]'s ordering effects being that differences between classes of adjectives need not
be differences of type.

## Implementation notes

* The carrier is the substrate's `Modifier (Property I E)`, `Property I E := I → E → Prop` with
  times first, where the article's `⟨e,it⟩` takes the entity first; conjuncts are likewise
  reordered. An intersective adjective is `Modifier.intersective Q`, meet with the property `Q`,
  and the article's second meaning of the indefinite article (32) is that same function, so
  *a dog* is `Modifier.intersective dog`.
* The syntax of §2 is represented only by the optional/compulsory distinction among selector
  features of (8), on which the attributive/predicative distribution rests; Predicate
  Abstraction and traces are Lean binders, and the meanings composed in §2.3 and §3.5 are
  stated with the article's truth conditions. The thematic relations and culmination function of
  (8) are the fields of `Frame`.
* The examples are `Data.Examples.Elbourne2026`.

## References

* [elbourne-2026]
* [elbourne-2024]
* [heim-kratzer-1998]
* [kamp-1975]
* [kamp-partee-1995]
* [parsons-1970]
* [lewis-1970]
* [montague-1973]
* [beesley-1982]
* [morzycki-2015]
* [mcnally-boleda-2004]
* [kennedy-2012]
* [bolinger-1967]
* [cresswell-1976]
-/

namespace Elbourne2026

open Modification Data.Examples Elbourne2026.Examples

section Theory

variable {I E : Type*}

/-! ### Attributive position (§3.1) -/

/-- (24)–(26): Functional Application of the intersective entry for *cute*,
`λf⟨e,it⟩.λx.λt.f(x)(t) & cute(x)(t)`, to *donkey* gives `λx.λt.donkey(x)(t) & cute(x)(t)`. At
each time this is the meet of the two extensions, `Modifier.intersective` at `e ⇒ t`, which is
Predicate Modification; so the ⟨e,t⟩ theory's rule is unnecessary for adjective–noun
combination. -/
theorem intersective_apply_time (Q N : Property I E) (t : I) :
    Modifier.intersective Q N t = Modifier.intersective (Q t) (N t) :=
  rfl

/-! ### Predicative position (§3.2) -/

/-- The copula BE (8): `λR⟨i,it⟩.λG⟨eit,eit⟩.λx.λt.∃t'(R(t')(t) & G(λy.λt''.⊤)(x)(t'))`. The
adjective is applied to the trivial noun, and the tense relation `R` locates the time. -/
def copula (R : I → I → Prop) (G : Modifier (Property I E)) : Property I E :=
  λ t x => ∃ t', R t' t ∧ G ⊤ t' x

/-- An intersective adjective under the copula holds of the subject at a time in the tense
relation, since the trivial noun drops out of the meet. -/
theorem copula_intersective (R : I → I → Prop) (Q : Property I E) :
    copula R (Modifier.intersective Q) = λ t x => ∃ t', R t' t ∧ Q t' x := by
  funext t x
  simp only [copula, Modifier.intersective, inf_top_eq]

/-- (28)–(30), *Fido was cute*: `λt.∃t'(<(t')(t) & cute(o)(t'))`. -/
theorem fido_was_cute [LT I] (cute : Property I E) (o : E) (t : I) :
    copula (· < ·) (Modifier.intersective cute) t o ↔ ∃ t' < t, cute t' o := by
  rw [copula_intersective]

/-- (31)–(33), *Fido is a dog*: the indefinite article's second meaning (32),
`λf⟨e,it⟩.λg⟨e,it⟩.λx.λt.g(x)(t) & f(x)(t)`, is `Modifier.intersective`, so *a dog* has the shape
of an adjective meaning and the copula can take it. -/
theorem fido_is_a_dog (R : I → I → Prop) (dog : Property I E) (o : E) (t : I) :
    copula R (Modifier.intersective dog) t o ↔ ∃ t', R t' t ∧ dog t' o := by
  rw [copula_intersective]

/-! ### Non-subsective adjectives (§3.3–3.4) -/

/-- *former*, (44) and (60): `λf⟨e,it⟩.λx.λt.∃t'(<(t')(t) & f(x)(t') & ¬f(x)(t))`, with both the
positive and the negative condition asserted. -/
def former [LT I] : Modifier (Property I E) :=
  λ N t x => (∃ t' < t, N t' x) ∧ ¬ N t x

/-- (45)–(46), *John was a former judge*:
`λt.∃t'(<(t')(t) & ∃t''(<(t'')(t') & judge(j)(t'') & ¬judge(j)(t')))`. -/
theorem john_was_a_former_judge [LT I] (judge : Property I E) (j : E) (t : I) :
    copula (· < ·) (Modifier.intersective (former judge)) t j ↔
      ∃ t' < t, (∃ t'' < t', judge t'' j) ∧ ¬ judge t' j := by
  rw [copula_intersective]
  exact Iff.rfl

/-- A former N at `t` is not an N at `t` (§3.4): *former* is privative in [kamp-1975]'s sense. -/
theorem former_isPrivative [LT I] : Modifier.isPrivative (former : Modifier (Property I E)) :=
  isPrivative_iff.mpr λ _ _ _ h => h.2

/-- Given two ordered times, *former* has a non-empty extension, so it is not subsective. -/
theorem former_not_isSubsective [Preorder I] {t' t : I} (h : t' < t) [Nonempty E] :
    ¬ Modifier.isSubsective (former : Modifier (Property I E)) :=
  not_isSubsective_of_isPrivative former_isPrivative
    ⟨λ s _ => s = t', t, Classical.arbitrary E, ⟨t', h, rfl⟩, h.ne'⟩

/-- Predicate Modification imposes intersective semantics
(`Modifier.intersective_isIntersective`), so the ⟨e,t⟩ theory cannot express *former*: no
property combined with the noun by the rule gives its meaning, and a non-subsective adjective must
be a function from noun meanings to noun meanings (§3.3–3.4). -/
theorem intersective_ne_former [Preorder I] {t' t : I} (h : t' < t) [Nonempty E]
    (Q : Property I E) : Modifier.intersective Q ≠ former :=
  λ e => former_not_isSubsective h
    (e ▸ Modifier.intersective_isIntersective Q : Modifier.isIntersective former).isSubsective

/-! ### Relational adjectives (§3.5) -/

/-- *localᵢ*, (54): `λf⟨e,it⟩.λx.λt.f(x)(t) & local(x)(σ(i))(t)`. The relatum `z` is the value of
the index under the assignment, so the adjective stays within the type rather than taking an
internal argument. -/
def localTo (near : I → E → E → Prop) (z : E) : Modifier (Property I E) :=
  Modifier.intersective λ t x => near t x z

/-- The non-logical constants of the fragment (8): the thematic relations and the culmination
function on events. -/
structure Frame (I E S : Type*) where
  /-- `Agent(e)(x)`. -/
  agent : S → E → Prop
  /-- `Theme(e)(x)`. -/
  theme : S → E → Prop
  /-- `CUL(e)`, the last time at which the event obtains. -/
  cul : S → I

variable {S : Type*}

/-- *every* (8): `λf⟨e,it⟩.λg⟨e,it⟩.λt.∀x(f(x)(t) → g(x)(t))`. -/
def every (f g : Property I E) (t : I) : Prop := ∀ x, f t x → g t x

/-- *some* and the quantificational *a* (8): `λf⟨e,it⟩.λg⟨e,it⟩.λt.∃x(f(x)(t) & g(x)(t))`. -/
def indefinite (f g : Property I E) (t : I) : Prop := ∃ x, f t x ∧ g t x

/-- *everyone* (56a): `λf⟨e,it⟩.λt.∀x(person(x)(t) → f(x)(t))`. -/
def everyone (person g : Property I E) (t : I) : Prop := ∀ x, person t x → g t x

/-- A transitive verb, (8) *inspect* and (56d) *enter*:
`λR⟨i,it⟩.λx.λe.λt.P(e) & Theme(e)(x) & R(CUL(e))(t)`. -/
def Frame.transitive (F : Frame I E S) (P : S → Prop) (R : I → I → Prop) (x : E) (e : S)
    (t : I) : Prop :=
  P e ∧ F.theme e x ∧ R (F.cul e) t

/-- Little v (8), (56f): `λF⟨s,it⟩.λx.λt.∃e(F(e)(t) & Agent(e)(x))`. -/
def Frame.littleV (F : Frame I E S) (G : S → I → Prop) : Property I E :=
  λ t x => ∃ e, G e t ∧ F.agent e x

/-- (14) with the object raised lowest, (20)–(21): the inverse scope of *Every woman inspected
some donkey*. -/
theorem inverse_scope [LT I] (F : Frame I E S) (woman donkey : Property I E)
    (inspection : S → Prop) (t : I) :
    indefinite donkey
        (λ t x => every woman (F.littleV (F.transitive inspection (· < ·) x)) t) t ↔
      ∃ x, donkey t x ∧ ∀ y, woman t y →
        ∃ e, inspection e ∧ F.theme e x ∧ F.cul e < t ∧ F.agent e y := by
  simp only [indefinite, every, Frame.littleV, Frame.transitive, and_assoc]

/-- (22)–(23): the surface scope, with the subject raised above the object. -/
theorem surface_scope [LT I] (F : Frame I E S) (woman donkey : Property I E)
    (inspection : S → Prop) (t : I) :
    every woman
        (λ t y => indefinite donkey
          (λ t x => F.littleV (F.transitive inspection (· < ·) x) t y) t) t ↔
      ∀ y, woman t y → ∃ x, donkey t x ∧
        ∃ e, inspection e ∧ F.theme e x ∧ F.cul e < t ∧ F.agent e y := by
  simp only [indefinite, every, Frame.littleV, Frame.transitive, and_assoc]

/-- (55)–(58), *Everyone entered a local bar*: the raised *everyone* binds the index on *local*,
`λt.∀x(person(x)(t) → ∃y(bar(y)(t) & local(y)(x)(t) & ∃e(entering(e) & Theme(e)(y) &
<(CUL(e))(t) & Agent(e)(x))))`. -/
theorem everyone_entered_a_local_bar [LT I] (F : Frame I E S) (person bar : Property I E)
    (near : I → E → E → Prop) (entering : S → Prop) (t : I) :
    everyone person
        (λ t x => indefinite (localTo near x bar)
          (λ t y => F.littleV (F.transitive entering (· < ·) y) t x) t) t ↔
      ∀ x, person t x → ∃ y, near t y x ∧ bar t y ∧
        ∃ e, entering e ∧ F.theme e y ∧ F.cul e < t ∧ F.agent e x := by
  simp only [everyone, indefinite, localTo, intersective_apply, Frame.littleV, Frame.transitive,
    and_assoc]

end Theory

/-! ### Selector features and the two positions (§2.1.4, §3.2, §4.2) -/

/-- The selector features (1): `E_L` and `E_R` trigger External Merge (4) with a constituent to
the left or to the right. -/
inductive Selector
  | eL
  | eR
  deriving DecidableEq

/-- The syntactic features of a lexical entry (8): the compulsory ones and, in angle brackets, the
optional ones. -/
structure Features where
  /-- Features every use of the entry carries. -/
  compulsory : Finset Selector
  /-- Features an entry may enter the derivation with or without. -/
  optional : Finset Selector
  deriving DecidableEq

namespace Features

/-- The feature bundles an entry can enter a derivation with: the compulsory features together
with any choice of the optional ones. -/
def bundles (f : Features) : Finset (Finset Selector) :=
  f.optional.powerset.image (f.compulsory ∪ ·)

/-- An entry takes a noun to its right by External Merge (4a) when one of its bundles carries
`E_R`. -/
def TakesNoun (f : Features) : Prop := ∃ b ∈ f.bundles, Selector.eR ∈ b

/-- Argument Interpretability (6): the constituent selected for by a selector feature, as the
adjective is by the copula's `E_R`, must contain no uninterpretable feature; an entry is
selectable when one of its bundles is empty. -/
def Selectable (f : Features) : Prop := ∅ ∈ f.bundles

instance (f : Features) : Decidable f.TakesNoun :=
  inferInstanceAs (Decidable (∃ b ∈ f.bundles, _))

instance (f : Features) : Decidable f.Selectable :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- An entry is selectable exactly when all its features are optional. -/
theorem selectable_iff (f : Features) : f.Selectable ↔ f.compulsory = ∅ := by
  simp only [Selectable, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, _, h⟩
    exact (Finset.union_eq_empty.mp h).1
  · intro h
    exact ⟨∅, Finset.empty_subset _, by rw [h, Finset.empty_union]⟩

/-- An entry takes a noun exactly when `E_R` is among its features. -/
theorem takesNoun_iff (f : Features) : f.TakesNoun ↔ Selector.eR ∈ f.compulsory ∪ f.optional := by
  simp only [TakesNoun, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, ⟨_, ha, rfl⟩, h⟩
    exact Finset.union_subset_union_right ha h
  · intro h
    exact ⟨_, ⟨f.optional, Finset.Subset.refl _, rfl⟩, h⟩

/-- *cute* (8): an optional `E_R`, so it takes a noun in attributive position and, without the
feature, is selected by the copula. -/
def cute : Features := ⟨∅, {Selector.eR}⟩

/-- *former* and *mere* (§3.2): a compulsory `E_R`, so never alone in predicative position, which
accounts for (42) and, together with the types, for (36). -/
def former : Features := ⟨{Selector.eR}, ∅⟩

/-- Russian short-form adjectives (§4.2): no selector features, so they cannot take nouns but are
selectable by the copula. -/
def shortForm : Features := ⟨∅, ∅⟩

/-- Russian long-form adjectives (§4.2): optional `E_R` or `E_L`, so both positions. -/
def longForm : Features := ⟨∅, {Selector.eR, Selector.eL}⟩

end Features

/-- The two positions of an adjective. -/
inductive Position
  | attributive
  | predicative
  deriving DecidableEq

/-- What licenses an adjective in each position: External Merge with a noun needs `E_R`, and
selection by the copula needs an empty bundle. -/
def Features.Licensed (f : Features) : Position → Prop
  | .attributive => f.TakesNoun
  | .predicative => f.Selectable

instance (f : Features) : ∀ p, Decidable (f.Licensed p)
  | .attributive => inferInstanceAs (Decidable f.TakesNoun)
  | .predicative => inferInstanceAs (Decidable f.Selectable)

/-- The entries as named in the rows. -/
def entryTable : List (String × Features) :=
  [("cute", .cute), ("former", .former), ("long form", .longForm), ("short form", .shortForm)]

/-- The positions as named in the rows. -/
def positionTable : List (String × Position) :=
  [("attributive", .attributive), ("predicative", .predicative)]

/-- The rows whose acceptability the features decide: *cute* and *former* in predicative
position, (28), (36) and (42), and the Russian forms in both positions, (64)–(65). -/
theorem rows_licensed :
    ∀ e ∈ [ex_28, ex_36, ex_42, ex_64_long, ex_64_short, ex_65a, ex_65b],
      ∀ f, e.parse? "entry" entryTable = some f →
        ∀ p, e.parse? "position" positionTable = some p →
          (e.judgment = .acceptable ↔ f.Licensed p) := by
  decide

/-! ### Replies to criticisms (§4) -/

section Replies

variable {I E : Type*}

/-- (92a), *young alleged murderer*: an intersective adjective scoping over any modifier commits
the speaker to its property. -/
theorem intersective_outer (Y N : Property I E) (M : Modifier (Property I E)) (t : I) (x : E)
    (h : Modifier.intersective Y (M N) t x) : Y t x :=
  h.1

/-- (92b), *alleged young murderer*: under a non-subsective modifier there is no such commitment,
so the contrast is one of scope within the type, not of type; *former* witnesses. -/
theorem exists_inner_not_committed :
    ∃ (Y N : Property Bool Unit) (t : Bool) (x : Unit),
      former (Modifier.intersective Y N) t x ∧ ¬ Y t x :=
  ⟨λ s _ => s = false, ⊤, true, (),
    ⟨⟨false, by decide, rfl, trivial⟩, λ h => absurd h.1 (by decide)⟩, by decide⟩

variable {D : Type*}

/-- (100): a gradable adjective with a degree argument, `λd.λf⟨e,it⟩.λx.λt.f(x)(t) & tall(x)(t)(d)`,
of type ⟨d,eiteit⟩. -/
def gradable (P : I → E → D → Prop) (d : D) : Modifier (Property I E) :=
  Modifier.intersective λ t x => P t x d

/-- The positive morpheme of [cresswell-1976] in the form (104),
`λG⟨d,et⟩.λx.∃d(d > standard(G) & G(d)(x))`, transposed to ⟨d,eiteit⟩ as §4.6 proposes. -/
def pos [LT D] (standard : (D → Modifier (Property I E)) → D) (G : D → Modifier (Property I E)) :
    Modifier (Property I E) :=
  λ N t x => ∃ d, standard G < d ∧ G d N t x

/-- A gradable adjective in the positive degree is an intersective adjective of type ⟨eit,eit⟩:
with the positive morpheme, gradable and non-gradable adjectives share the type (§4.6). -/
theorem pos_gradable [LT D] (standard : (D → Modifier (Property I E)) → D)
    (P : I → E → D → Prop) :
    pos standard (gradable P) =
      Modifier.intersective λ t x => ∃ d, standard (gradable P) < d ∧ P t x d := by
  funext N t x
  simp only [pos, gradable, intersective_apply]
  exact propext ⟨λ ⟨d, hd, h, hN⟩ => ⟨⟨d, hd, h⟩, hN⟩, λ ⟨⟨d, hd, h⟩, hN⟩ => ⟨d, hd, h, hN⟩⟩

end Replies

end Elbourne2026
