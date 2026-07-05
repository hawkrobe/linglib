import Linglib.Semantics.Questions.Singleton
import Linglib.Semantics.Questions.Hamblin
import Linglib.Fragments.HindiUrdu.Particles

/-!
# Bhatt & Dayal (2020): the polar question particle *kya:*
[bhatt-dayal-2020]

Hindi-Urdu polar *kya:* is a **polar question particle** (PQP) — a class
distinct from clause-typing Q-morphemes like Japanese *ka*: it occurs only in
polar questions (not in wh-questions), sits in a projection above CP the
paper labels ForceP, and embeds only in the quasi-subordinated configuration
of [dayal-grimshaw-2009] (complements of rogatives), not in ordinary
subordination. Semantically kya: presupposes that its sister question has a
**singleton** alternative set (eq. 23) and is otherwise the identity; a polar
question denotes the singleton `{p}` (eq. 22b). The same singleton
restriction models the (bias-introducing) Mandarin particle *nandao* in
[xu-2012] (cross-linguistic picture in [xu-2017]), which the paper draws on.
-/

namespace BhattDayal2020

open Question (IsSingleton SingletonQuestion declarative polar which
  isSingleton_declarative not_isSingleton_polar_of_nontrivial
  not_isSingleton_of_two_alternatives alt_which_of_antichain)
open HindiUrdu.Particles (kya)

variable {W : Type*}

/-! ### The singleton-alternative presupposition (eq. 23)

`⟦kya:⟧ = λQ⟨st⟩t : ∃p ∈ Q[∀q[q ∈ Q → q = p]].Q` — defined only when the
sister question `Q` has a singleton alternative set, and then the identity
on `Q`. The presupposition is `Question.IsSingleton`; the felicitous sister
is the subtype `SingletonQuestion W`. In the paper a polar question denotes
a singleton (eq. 22b: ⟦did John leave⟧ = {John left}) — the substrate's
one-cell `declarative p`, not its two-cell Hamblin `polar`. -/

/-- Felicitous case: a polar question in the paper's sense is a singleton. -/
theorem kya_felicitous_singleton_polar (p : Set W) :
    IsSingleton (declarative (W := W) p) :=
  isSingleton_declarative p

/-- Defined case: on a felicitous sister, kya: is the identity. -/
theorem kya_interp (p : Set W) :
    (SingletonQuestion.ofDeclarative (W := W) p).issue = declarative p :=
  SingletonQuestion.ofDeclarative_issue p

/-- The headline restriction (ex. 4): a wh-question with two distinct answer
cells is non-singleton, so kya: rejects it. -/
theorem kya_infelicitous_wh {E : Type*} {D : Set E} {P : E → Set W}
    (hD : D.Nonempty) (hne : ∀ e ∈ D, (P e).Nonempty)
    (hA : IsAntichain (· ⊆ ·) (P '' D))
    {e₁ e₂ : E} (h₁ : e₁ ∈ D) (h₂ : e₂ ∈ D) (hPne : P e₁ ≠ P e₂) :
    ¬ IsSingleton (which D P) := by
  refine not_isSingleton_of_two_alternatives _ ?_ ?_ hPne <;>
    rw [alt_which_of_antichain hD hne hA]
  exacts [⟨e₁, h₁, rfl⟩, ⟨e₂, h₂, rfl⟩]

/-- A two-cell Hamblin polar likewise fails the presupposition. -/
theorem kya_infelicitous_two_cell_polar {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬ IsSingleton (polar (W := W) p) :=
  not_isSingleton_polar_of_nontrivial hne hnu

/-! ### Embedding: quasi-subordination only

kya: appears in matrix polar questions and in the quasi-subordinated
configuration of [dayal-grimshaw-2009] (complements of rogatives, ex. 9)
but not in ordinary subordination (complements of responsives, ex. 8) —
read off the fragment's embedding facet. -/

theorem kya_embedding_profile :
    kya.LicensedInEmbed .matrix ∧ kya.LicensedInEmbed .quasiSubordinated ∧
      ¬ kya.LicensedInEmbed .subordinated := by
  decide

end BhattDayal2020
