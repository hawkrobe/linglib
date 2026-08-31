import Linglib.Semantics.Questions.Singleton
import Linglib.Semantics.Questions.Hamblin
import Linglib.Fragments.HindiUrdu.Particles

/-!
# Bhatt and Dayal 2020: the polar question particle kya:

This file formalizes Bhatt and Dayal's analysis of Hindi-Urdu polar *kya:*. The particle is
not a clause-typing Q-morpheme of the Japanese *-ka* kind: it occurs in polar and
alternative questions but not in constituent questions, and it embeds under rogative
predicates and modified responsives but not under plain responsives — the quasi-subordinated
configuration, which the authors place in a projection above CP, ForceP, that only some
predicates select. Semantically *kya:* is the identity on its sister question, defined only
when that question's alternative set is a singleton; a polar question denotes the singleton
of its nucleus proposition, a constituent question a plural set. An alternative question is
the disjunction of two polar questions and so has two alternatives; *kya:* is licensed in it
by applying inside a disjunct, and fails when it scopes over the disjunction — which is why
clause-final *kya:*, whose sister is the whole clause, is excluded there.

## Main definitions

* `altQ`: the alternative question *p or q* as the disjunction of two singleton polar
  questions.
* `selectsForceP`: the embedding contexts whose selecting predicate takes a ForceP
  complement.

## Main results

* `kya_polar`, `kya_not_wh`: the presupposition holds of a polar question and fails on a
  constituent question with two answer cells.
* `altQ_not_singleton`, `kya_in_disjunct`: *kya:* over an alternative question fails, while
  *kya:* inside a disjunct leaves the alternative question intact.
* `kya_licensed_iff_selectsForceP`, `kya_clause_types`: the fragment's embedding and
  clause-type distributions are ForceP selection and singleton-satisfiability.

## References

* [bhatt-dayal-2020]
* [dayal-grimshaw-2009]: quasi-subordination.
* [roelofsen-farkas-2015]: the highlighted proposition of a polar question.
* [xu-2012], [xu-2017]: the Mandarin *nandao* analysis the account draws on.
-/

namespace BhattDayal2020

open Question HindiUrdu.Particles Clause

variable {W : Type*}

/-! ### The singleton presupposition -/

/-- A polar question denotes the singleton of its nucleus proposition (22b), so *kya:* is
defined on it and returns it (23). -/
theorem kya_polar (p : Set W) : IsSingleton (ofSet p) :=
  isSingleton_ofSet p

/-- A constituent question with two distinct answer cells is not a singleton (22a), so
*kya:* is undefined on it (4). -/
theorem kya_not_wh {E : Type*} {D : Set E} {P : E → Set W}
    (hD : D.Nonempty) (hne : ∀ e ∈ D, (P e).Nonempty)
    (hA : IsAntichain (· ⊆ ·) (P '' D))
    {e₁ e₂ : E} (h₁ : e₁ ∈ D) (h₂ : e₂ ∈ D) (hPne : P e₁ ≠ P e₂) :
    ¬ IsSingleton (which D P) := by
  refine not_isSingleton_of_two_alternatives _ ?_ ?_ hPne <;>
    rw [alt_which_of_antichain hD hne hA]
  exacts [⟨e₁, h₁, rfl⟩, ⟨e₂, h₂, rfl⟩]

/-- The two-cell Hamblin polar question fails the presupposition as well; the paper's polar
question is the one-cell `ofSet p`. -/
theorem kya_not_two_cell {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬ IsSingleton (polar (W := W) p) :=
  not_isSingleton_polar_of_nontrivial hne hnu

/-! ### Alternative questions -/

/-- The alternative question *p or q*: the disjunction of the two polar questions ((44),
(52)). -/
def altQ (p q : Set W) : Question W := ofSet p ⊔ ofSet q

theorem mem_alt_altQ_left {p q : Set W} (h : ¬ p ⊆ q) : p ∈ alt (altQ p q) :=
  mem_alt_sup_of_alt_left (by simp) fun _ hr hpr => absurd (hpr.trans hr) h

theorem mem_alt_altQ_right {p q : Set W} (h : ¬ q ⊆ p) : q ∈ alt (altQ p q) :=
  mem_alt_sup_of_alt_right (by simp) fun _ hr hqr => absurd (hqr.trans hr) h

/-- An alternative question has two alternatives, so *kya:* scoping over it fails the
presupposition ((43), (51)) — the exclusion of clause-final *kya:* on *p or q* (48b). -/
theorem altQ_not_singleton {p q : Set W} (hpq : ¬ p ⊆ q) (hqp : ¬ q ⊆ p) :
    ¬ IsSingleton (altQ p q) :=
  not_isSingleton_of_two_alternatives _ (mem_alt_altQ_left hpq) (mem_alt_altQ_right hqp)
    fun h => hpq h.le

/-- *kya:* applied inside a disjunct meets its presupposition on `{p}` and returns it, and
the disjunction of the two polar questions is the alternative question ((44), (47), (52)). -/
theorem kya_in_disjunct (p q : Set W) :
    (SingletonQuestion.ofSet p).issue ⊔ ofSet q = altQ p q :=
  rfl

/-- Disjunction inside a polar question keeps a singleton: the yes/no reading of *p or q*
(45). -/
theorem kya_polar_disjunction (p q : Set W) : IsSingleton (ofSet (p ∪ q)) :=
  isSingleton_ofSet _

/-! ### Distribution -/

/-- The embedding contexts whose selecting predicate takes a ForceP complement (21): the
matrix clause and quasi-subordination, not ordinary subordination. -/
def selectsForceP (e : EmbeddingContext) : Prop :=
  e = .matrix ∨ e = .quasiSubordinated

instance (e : EmbeddingContext) : Decidable (selectsForceP e) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Over the contexts the paper records, *kya:* is licensed exactly where ForceP is selected
((8), (9), (21)). -/
theorem kya_licensed_iff_selectsForceP :
    ∀ e, e ≠ EmbeddingContext.quotation → (kya.LicensedInEmbed e ↔ selectsForceP e) := by
  decide

/-- *kya:* is licensed in exactly the clause types whose denotation can be a singleton: polar
and alternative questions, not constituent questions ((4), (5)). -/
theorem kya_clause_types :
    ∀ c, kya.LicensedIn c ↔ c = Particle.ClauseType.polar ∨ c = .alternative := by
  decide

end BhattDayal2020
