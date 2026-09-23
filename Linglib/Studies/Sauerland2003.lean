module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.MaximizePresupposition

/-!
# Sauerland (2003): a new semantics for number

[sauerland-2003] locates the interpreted number feature in a φ-head above DP and
interprets agreement features as presuppositions: `[Sg]` is the identity function
presupposing an atom (his entry admits an atom or a mass; `Number.dom` keeps the atomic
case), `[Pl]` the identity with no presupposition, and [heim-1991]'s
Maximize Presupposition selects the most specific feature whose presupposition holds. The
coordination *Kai and Lina* is the first argument: each conjunct is an atom but their sum
is not, so the φ-head above the coordination can only carry `[Pl]` (`coordination_plural`),
while at an atom Maximize Presupposition blocks `[Pl]` (`mp_selects_sg`, over the constraint
`phiMP`). The two domains are nested (`sg_domain_ssubset_pl`), an instance of his
Feature-Subset Principle, and since the features are domain restrictions the competition is
presuppositional rather than scalar.

*Every* decomposes into a definite `DER`, taking the maximal element of a cumulative
restrictor (`der_unique`; his cover-based `*` is `Mereology.algClosure_iff_exists_sup'`),
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

@[expose] public section

namespace Sauerland2003

open Mereology (Atom AlgClosure cum_maximal_unique algClosure_cum not_atom_sup_of_ne)
open Plurality.Algebra (D)
open Agreement
open Presupposition Constraints OptimalityTheory Presupposition.MaximizePresupposition

variable {E : Type*}

/-! ### Number features and Maximize Presupposition -/

section Number

variable [SemilatticeSup E] {a b : E}

/-- The φ-head above a coordination of two distinct atoms cannot carry `[Sg]`. -/
theorem coordination_plural (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    a ⊔ b ∉ Number.dom (E := E) (some .singular) :=
  (Number.mem_dom_singular _).not.2 (not_atom_sup_of_ne ha hb hne)

/-- The Feature-Subset Principle for number: the domain of `[Sg]` is a proper subset of the
domain of `[Pl]`. -/
theorem sg_domain_ssubset_pl (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    Number.dom (E := E) (some .singular) ⊂ Number.dom (some .plural) := by
  rw [Number.dom_plural]
  exact ⟨Set.subset_univ _, fun h ↦ coordination_plural ha hb hne (h (Set.mem_univ _))⟩

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
      c.specLevel = ContainmentPair.maximal.specLevel :=
  phi_mp_selects_maximal _ rest (List.cons_ne_nil _ _) (.head _)

/-! ### *Every* as `JE ∘ DER`, and the indefinite -/

/-- The indefinite: the scope's presupposition projects existentially. -/
def aSem (R S : E → Prop) (domS : E → Prop := fun _ ↦ True) : PartialProp E where
  presup _ := ∃ x, R x ∧ domS x
  assertion _ := ∃ x, R x ∧ S x

section Every

variable [PartialOrder E]

/-- `JE`, the quantificational part of *every*: over the atomic parts of a group individual
`X`, presupposing the scope predicate is defined at each and asserting it holds at each. -/
def JE (X : E) (P : E → Prop) (domP : E → Prop := fun _ ↦ True) : PartialProp E where
  presup _ := ∀ a, Atom a → a ≤ X → domP a
  assertion _ := ∀ a, Atom a → a ≤ X → P a

/-- When the atoms below `maxR` are exactly the `R`-elements, `JE` asserts the ordinary
universal. -/
theorem je_assertion_eq_forall {R Q : E → Prop} {maxR : E} (hR : ∀ x, R x ↔ Atom x ∧ x ≤ maxR)
    (w : E) : (JE maxR Q).assertion w ↔ ∀ x, R x → Q x :=
  ⟨fun h x hx ↦ h x ((hR x).1 hx).1 ((hR x).1 hx).2, fun h a ha hle ↦ h a ((hR a).2 ⟨ha, hle⟩)⟩

/-- Presupposition projection: `JE` projects universally, the indefinite existentially. With
a restrictor atom `a₂ ≤ boys` outside the scope's domain and some `R`-individual inside it,
*a boy invited his sister* is defined and *every boy invited his sister* is not. -/
theorem projection_asymmetry {boys a₁ a₂ : E} {R domP : E → Prop} (ha₂ : Atom a₂)
    (h₂ : a₂ ≤ boys) (hR₁ : R a₁) (hdom₁ : domP a₁) (hdom₂ : ¬ domP a₂) :
    (aSem R (fun _ ↦ True) domP).defined boys ∧ ¬ (JE boys (fun _ ↦ True) domP).defined boys :=
  ⟨⟨a₁, hR₁, hdom₁⟩, fun h ↦ hdom₂ (h a₂ ha₂ h₂)⟩

/-- The weak plural: *Lina didn't harvest tomatoes* entails *Lina didn't harvest a tomato*,
the singular indefinite restricting the plural's assertion to atoms. -/
theorem negated_pl_entails_negated_sg {starR harvest : E → Prop} {w : E}
    (h : ¬ (aSem starR harvest).assertion w) :
    ¬ (aSem (fun x ↦ Atom x ∧ starR x) harvest).assertion w :=
  fun ⟨e, ⟨_, hR⟩, hH⟩ ↦ h ⟨e, hR, hH⟩

end Every

/-- The assertion of `JE` is [link-1987]'s distributivity operator. -/
theorem je_assertion_eq_D [SemilatticeSup E] (X : E) (P : E → Prop) (w : E) :
    (JE X P).assertion w ↔ D P X :=
  ⟨fun h y hle hAtom ↦ h y hAtom hle, fun h a hAtom hle ↦ h a hle hAtom⟩

/-! ### Gender agreement in Czech coordinations -/

/-- A conjunct of one of Sauerland's Czech coordinations: a man, a woman or a child. -/
inductive Conjunct where
  | man
  | woman
  | child
  deriving DecidableEq, Repr

/-- A coordination is gendered masculine when a conjunct is a man, and feminine when a conjunct is
a woman and none is a man; a coordination of children is gendered neither way. -/
instance gendered : Gendered (Finset Conjunct) where
  masculine := {s | ∃ r ∈ s, r = .man}
  feminine := {s | (∃ r ∈ s, r = .woman) ∧ ∀ r ∈ s, r ≠ .man}
  disjoint := Set.disjoint_left.mpr fun _ ⟨r, hr, hm⟩ ⟨_, hno⟩ ↦ hno r hr hm

/-- *Jan a Věra*, *Matka a její dítě* and *Otec a jeho dítě*, as the sums of their conjuncts. -/
def janVera : Finset Conjunct := {.man, .woman}
def matkaDite : Finset Conjunct := {.woman, .child}
def otecDite : Finset Conjunct := {.man, .child}

/-- Sauerland's Czech coordinations: *Jan a Věra* excludes feminine, *Matka a její dítě* takes
feminine but not neuter, and *Otec a jeho dítě* takes only the vacuous masculine. -/
theorem czech_gender :
    janVera ∉ Gender.dom (some .feminine) ∧
      matkaDite ∈ Gender.dom (some .feminine) ∧
      matkaDite ∉ Gender.dom (some .neuter) ∧
      otecDite ∉ Gender.dom (some .feminine) ∧
      otecDite ∈ Gender.dom (some .masculine) := by
  simp only [Gender.mem_dom_feminine, Gender.mem_dom_neuter, Gender.dom_masculine, Set.mem_univ,
    and_true, Gendered.masculine, Gendered.feminine, Set.mem_ofPred_eq]
  decide

/-! ### Politeness -/

/-- Polite address recruits the semantically unmarked values, plural and third person, whose
vacuous presuppositions hold of any addressee (German *Sie*). -/
theorem politeness_unmarked {W P T : Type*} [PartialOrder E] (c : Reference.Context W E P T) :
    Number.dom (E := E) (some .plural) = Set.univ ∧ Person.dom c (some .third) = Set.univ :=
  ⟨rfl, rfl⟩

end Sauerland2003
