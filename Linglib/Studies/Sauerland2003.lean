import Linglib.Semantics.Plurality.Algebra
import Linglib.Semantics.Presupposition.PhiFeatures
import Linglib.Semantics.Presupposition.MaximizePresupposition

/-!
# Sauerland (2003): a new semantics for number

[sauerland-2003] locates the interpreted number feature in a φ-head above DP and
interprets agreement features as presuppositions: `[Sg]` is the identity function
presupposing an atom (his entry admits an atom or a mass; `PhiFeatures.sgSem` keeps the
atomic case), `[Pl]` the identity with no presupposition (`plSem`), and [heim-1991]'s
Maximize Presupposition selects the most specific feature whose presupposition holds. The
coordination *Kai and Lina* is the first argument: each conjunct is an atom but their sum
is not, so the φ-head above the coordination can only carry `[Pl]` (`coordination_plural`),
while at an atom Maximize Presupposition blocks `[Pl]` (`mp_selects_sg`, over the constraint
`phiMP`). The two domains are nested (`sg_domain_ssubset_pl`), an instance of his
Feature-Subset Principle, and the competition is presuppositional rather than scalar
(`sg_pl_competition`).

*Every* decomposes into a definite `DER`, taking the maximal element of a cumulative
restrictor (`der_unique`; his cover-based `*` is `Plurality.Cover.algClosure_of_finCover`),
and `JE`, a universal over the atomic parts of a group individual that projects its scope's
presupposition universally (`JE`), whose assertion is [link-1987]'s distributivity operator
(`je_assertion_eq_D`, `je_assertion_eq_forall`). The indefinite projects existentially
(`aSem`), so *every boy invited his sister* requires every boy to have a sister while *a boy
invited his sister* requires one (`projection_asymmetry`), and the weak plural makes *Lina
didn't harvest tomatoes* entail *Lina didn't harvest a tomato*
(`negated_pl_entails_negated_sg`). The same mechanism runs Czech gender agreement on
coordinations — masculine vacuous, feminine presupposing non-masculinity, neuter
presupposing genderlessness (`czech_gender`) — and predicts that polite address recruits
the unmarked values, plural and third person (`politeness_unmarked`).

## References

* [sauerland-2003]
* [heim-1991], [link-1987]
-/

namespace Sauerland2003

open Mereology (Atom AlgClosure cum_maximal_unique algClosure_cum not_atom_sup_of_ne)
open Plurality.Algebra (D)
open Features (ContainmentPair ContainmentPairLike)
open Presupposition
open Constraints OptimalityTheory
open Presupposition.PhiFeatures
open Presupposition.MaximizePresupposition

variable {E : Type*}

/-! ### Number features and Maximize Presupposition -/

section Number

variable [SemilatticeSup E] {a b : E}

/-- The φ-head above a coordination of two distinct atoms cannot carry `[Sg]`. -/
theorem coordination_plural (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    ¬ (sgSem E).defined (a ⊔ b) :=
  not_atom_sup_of_ne ha hb hne

/-- The Feature-Subset Principle for number: the domain of `[Sg]` is a proper subset of the
domain of `[Pl]`. -/
theorem sg_domain_ssubset_pl (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    {x | (sgSem E).defined x} ⊂ {x | (plSem E).defined x} :=
  ⟨fun _ _ => trivial, fun h => not_atom_sup_of_ne ha hb hne (@h (a ⊔ b) trivial)⟩

/-- `DER` is well defined on a cumulative restrictor: `*R` has at most one maximal element. -/
theorem der_unique {R : E → Prop} {m₁ m₂ : E} (h₁ : Maximal (AlgClosure R) m₁)
    (h₂ : Maximal (AlgClosure R) m₂) : m₁ = m₂ :=
  cum_maximal_unique algClosure_cum h₁ h₂

end Number

/-- Maximize Presupposition selects `[Sg]` when both features are candidates: with `phiMP`
top-ranked, every optimal cell has maximal presuppositional strength. -/
theorem mp_selects_sg (rest : List (Constraint ContainmentPair)) :
    ∀ c ∈ (Tableau.ofRanking [ContainmentPair.maximal, .minimal] (phiMP :: rest)
      (List.cons_ne_nil _ _)).optimal,
      presupStrength c = ContainmentPair.maximal.specLevel :=
  phi_mp_selects_maximal _ rest (List.cons_ne_nil _ _) (by decide) (.head _)

/-- The competition between `[Sg]` and `[Pl]` is presuppositional, not scalar: identical
assertions, ordered presuppositions. -/
theorem sg_pl_competition [PartialOrder E] (x : E) :
    ((sgSem E).assertion x ↔ (plSem E).assertion x) ∧
      presupStrength .minimal < presupStrength .maximal :=
  ⟨Iff.rfl, by decide⟩

/-! ### *Every* as `JE ∘ DER`, and the indefinite -/

/-- The indefinite: the scope's presupposition projects existentially. -/
def aSem (R S : E → Prop) (domS : E → Prop := fun _ => True) : PartialProp E where
  presup _ := ∃ x, R x ∧ domS x
  assertion _ := ∃ x, R x ∧ S x

section Every

variable [PartialOrder E]

/-- `JE`, the quantificational part of *every*: over the atomic parts of a group individual
`X`, presupposing the scope predicate is defined at each and asserting it holds at each. -/
def JE (X : E) (P : E → Prop) (domP : E → Prop := fun _ => True) : PartialProp E where
  presup _ := ∀ a, Atom a → a ≤ X → domP a
  assertion _ := ∀ a, Atom a → a ≤ X → P a

/-- When the atoms below `maxR` are exactly the `R`-elements, `JE` asserts the ordinary
universal. -/
theorem je_assertion_eq_forall {R Q : E → Prop} {maxR : E} (hR : ∀ x, R x ↔ Atom x ∧ x ≤ maxR)
    (w : E) : (JE maxR Q).assertion w ↔ ∀ x, R x → Q x :=
  ⟨fun h x hx => h x ((hR x).1 hx).1 ((hR x).1 hx).2, fun h a ha hle => h a ((hR a).2 ⟨ha, hle⟩)⟩

/-- Presupposition projection: `JE` projects universally, the indefinite existentially. With
a restrictor atom `a₂ ≤ boys` outside the scope's domain and some `R`-individual inside it,
*a boy invited his sister* is defined and *every boy invited his sister* is not. -/
theorem projection_asymmetry {boys a₁ a₂ : E} {R domP : E → Prop} (ha₂ : Atom a₂)
    (h₂ : a₂ ≤ boys) (hR₁ : R a₁) (hdom₁ : domP a₁) (hdom₂ : ¬ domP a₂) :
    (aSem R (fun _ => True) domP).defined boys ∧ ¬ (JE boys (fun _ => True) domP).defined boys :=
  ⟨⟨a₁, hR₁, hdom₁⟩, fun h => hdom₂ (h a₂ ha₂ h₂)⟩

/-- The weak plural: *Lina didn't harvest tomatoes* entails *Lina didn't harvest a tomato*,
the singular indefinite restricting the plural's assertion to atoms. -/
theorem negated_pl_entails_negated_sg {starR harvest : E → Prop} {w : E}
    (h : ¬ (aSem starR harvest).assertion w) :
    ¬ (aSem (fun x => Atom x ∧ starR x) harvest).assertion w :=
  fun ⟨e, ⟨_, hR⟩, hH⟩ => h ⟨e, hR, hH⟩

end Every

/-- The assertion of `JE` is [link-1987]'s distributivity operator. -/
theorem je_assertion_eq_D [SemilatticeSup E] (X : E) (P : E → Prop) (w : E) :
    (JE X P).assertion w ↔ D P X :=
  ⟨fun h y hle hAtom => h y hAtom hle, fun h a hAtom hle => h a hle hAtom⟩

/-! ### Gender agreement in Czech coordinations -/

/-- The sex or animacy of a referent. -/
inductive ReferentGender where
  | male
  | female
  | inanimate
  deriving DecidableEq, Repr

/-- Feminine agreement presupposes that no conjunct of the coordination is male. -/
abbrev nonMasculine (s : Finset ReferentGender) : Prop := ∀ r ∈ s, r ≠ .male

/-- Neuter agreement presupposes that every conjunct is genderless. -/
abbrev genderless (s : Finset ReferentGender) : Prop := ∀ r ∈ s, r = .inanimate

/-- Sauerland's Czech coordinations, as sums of their conjuncts: *Jan a Věra* excludes
feminine, *Matka a její dítě* takes feminine but not neuter, and *Otec a jeho dítě* takes
only the vacuous masculine. -/
theorem czech_gender :
    ¬ (femSem nonMasculine).defined {.male, .female} ∧
      (femSem nonMasculine).defined {.female, .inanimate} ∧
      ¬ (neutSem genderless).defined {.female, .inanimate} ∧
      ¬ (femSem nonMasculine).defined {.male, .inanimate} ∧
      (mascSem (E := Finset ReferentGender)).defined {.male, .inanimate} := by
  unfold PartialProp.defined femSem neutSem mascSem
  decide

/-! ### Politeness -/

/-- Polite address recruits the semantically unmarked values, plural and third person, whose
vacuous presuppositions hold of any addressee (German *Sie*). -/
theorem politeness_unmarked :
    isSemanticUnmarked (ContainmentPairLike.toPair Number.pluralF) = true ∧
      isSemanticUnmarked (ContainmentPairLike.toPair Person.thirdF) = true :=
  ⟨rfl, rfl⟩

end Sauerland2003
