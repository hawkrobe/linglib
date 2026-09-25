module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Composition.Cont
public import Linglib.Semantics.Composition.Combinator
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Type ⟨1⟩ quantifiers

This file is the API of `NP α`, the type ⟨1⟩ quantifier that a noun phrase denotes.
Existential closure `A` turns a property into a quantifier and predicative content `BE` turns
one back. `BE ∘ A` is the identity, and on the monotone quantifiers, which are what
[barwise-cooper-1981] take natural-language determiners to denote, the two form a
`GaloisCoinsertion`. Sending a quantifier through `BE` and back preserves truth conditions
exactly when it is a principal ultrafilter, so a proper name survives the round trip and
*every student* does not. The shifts relating `NP` to the other noun-phrase types are
[partee-1987]'s. The total ones are `individual`, `ident`, `A` and `BE`, with the two faces of
Partee's triangle `BE_individual_eq_ident` and `A_ident_eq_individual` proved here, and the
partial ones, `Reference.THE` and `Reference.lower`, are Russellian iotas.

## References

* [barwise-cooper-1981]
* [partee-1987]
* [barker-2002]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Quantifier.NP

open Quantifier.GQ

variable {E : Type*}

/-! ### The continuation identification

These are `rfl`: the carrier definitionally coincides with the
continuation monad at answer type `Prop`, first exploited for natural
language by [barker-2002] (see `Studies/Barker2002.lean`). -/

/-- The quantifier type is the continuation type, since a quantifier is a computation handed
its own scope. -/
theorem np_eq_cont : NP E = Cont Prop E := rfl

/-- Montague lift is the continuation monad's unit. -/
theorem individual_eq_pure (a : E) : individual a = (pure a : Cont Prop E) := rfl

/-- Montague lift is combinatory logic's type-raising combinator `T`. -/
theorem individual_eq_T (a : E) : individual a = Combinator.T (β := Prop) a := rfl

/-- The sets of a principal ultrafilter intersect to the singleton of its generator. -/
theorem sInter_individual (a : E) : ⋂₀ (individual a : Set (Set E)) = {a} :=
  Set.ext fun _ => ⟨fun h => h {a} rfl, fun h _ hs => h ▸ hs⟩

/-! ### Predicative content and existential closure -/

/-- The predicative content of a quantifier, `BE(Q) = λx. Q(λy. y = x)`. -/
def BE (Q : NP E) : E → Prop :=
  fun x => Q (fun y => y = x)

/-- Existential closure of a property over a domain, `A(P) = λQ. ∃x ∈ domain. P(x) ∧ Q(x)`. -/
def A (domain : List E) (P : E → Prop) : NP E :=
  fun Q => ∃ x ∈ domain, P x ∧ Q x

/-- `BE ∘ individual = ident`, the right face of [partee-1987]'s triangle. -/
theorem BE_individual_eq_ident (j : E) : BE (individual j) = ident j :=
  funext fun _ => propext eq_comm

/-- `A ∘ ident = individual` on the domain, the left face of the triangle. -/
theorem A_ident_eq_individual (domain : List E) (j : E) (hj : j ∈ domain) :
    A domain (ident j) = individual j := by
  funext P
  exact propext ⟨fun ⟨_, _, rfl, hP⟩ => hP, fun hP => ⟨j, hj, rfl, hP⟩⟩

/-! ### `BE` as a bounded-lattice homomorphism -/

/-- `BE(Q₁ ∧ Q₂) = BE(Q₁) ∧ BE(Q₂)` -/
theorem BE_conj (Q₁ Q₂ : NP E) :
    BE (fun P => Q₁ P ∧ Q₂ P) = (fun x => BE Q₁ x ∧ BE Q₂ x) := rfl

/-- `BE(Q₁ ∨ Q₂) = BE(Q₁) ∨ BE(Q₂)` -/
theorem BE_disj (Q₁ Q₂ : NP E) :
    BE (fun P => Q₁ P ∨ Q₂ P) = (fun x => BE Q₁ x ∨ BE Q₂ x) := rfl

/-- `BE(¬Q) = ¬BE(Q)` -/
theorem BE_neg (Q : NP E) :
    BE (fun P => ¬(Q P)) = (fun x => ¬(BE Q x)) := rfl

/-- `BE` preserves meets, joins, `⊤` and `⊥` ([partee-1987]). -/
def beHom (E : Type*) : BoundedLatticeHom (NP E) (E → Prop) where
  toFun := BE
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

/-! ### Truth-conditional transparency of the round trip

A type-shift is truth-conditionally transparent when the shifted meaning
produces the same sentential truth value as the original. For a quantifier `Q`,
the round trip `A(BE(Q))` preserves truth conditions exactly when `Q` is a
principal ultrafilter — when `Q = individual j` for some entity `j`. Proper
names, pronouns and definites shift transparently; `every student` shifts to
`some student`, and a numeral to its lower-bounded reading. Where the round trip
is not transparent, both meanings are live interpretive alternatives. -/

/-- A quantifier is a principal ultrafilter when it is some entity's
    Montagovian individual. -/
def isPrincipalUltrafilter (domain : List E) (Q : NP E) : Prop :=
  ∃ j ∈ domain, Q = individual j

/-- `(∃ x ∈ domain, j = x ∧ P x) ↔ P j` when `j ∈ domain`. -/
private theorem exists_eq_and_iff (domain : List E) (j : E)
    (hj : j ∈ domain) (P : E → Prop) :
    (∃ x ∈ domain, j = x ∧ P x) ↔ P j := by
  constructor
  · rintro ⟨x, _, rfl, hPx⟩; exact hPx
  · intro hPj; exact ⟨j, hj, rfl, hPj⟩

/-- The round trip is the identity on principal ultrafilters:
    `A(BE(individual j))(P) = individual j P`. -/
theorem roundtrip_preserves_principal (domain : List E) (j : E)
    (hj : j ∈ domain) :
    ∀ P : E → Prop, A domain (BE (individual j)) P = individual j P := by
  intro P
  simp only [A, BE, individual]
  exact propext (exists_eq_and_iff domain j hj P)

/-- **`BE ∘ A = id` on properties** ([partee-1987]): existential closure
    followed by predicative content recovers the original property, so `A` is a
    section of `BE`. Partee argues on this basis that `A` (with `some`) is the
    most natural determiner-type functor.

    `BE(A(P))(x) = A(P)(λy. y = x) = ∃z ∈ domain. P(z) ∧ z = x = P(x)`. -/
theorem BE_A_id (domain : List E) (P : E → Prop)
    (hcomplete : ∀ x : E, x ∈ domain) :
    BE (A domain P) = P := by
  funext x; show (∃ z ∈ domain, P z ∧ z = x) = P x
  apply propext; constructor
  · rintro ⟨z, _, hPz, hzx⟩; cases hzx; exact hPz
  · intro hPx; exact ⟨x, hcomplete x, hPx, rfl⟩

def twoDomain : List Bool := [true, false]
def twoEvery : (Bool → Prop) → Prop := fun P => ∀ x ∈ twoDomain, P x

/-- For non-principal quantifiers the round trip changes truth conditions:
    `every(⊤)` is true but `A(BE(every))(⊤)` is not, since `BE(every)` asks
    which entity equals every entity and on a two-element domain none does. -/
theorem roundtrip_changes_nonprincipal :
    twoEvery (fun _ => True) ∧ ¬ A twoDomain (BE twoEvery) (fun _ => True) := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro ⟨x, _, hBE, _⟩
  simp only [BE, twoEvery, twoDomain] at hBE
  have h1 : true = x := hBE true (by simp)
  have h2 : false = x := hBE false (by simp)
  rw [← h1] at h2; exact Bool.noConfusion h2

/-! ### Section and retraction -/

/-- `BE` is a left inverse of `A`. -/
theorem BE_leftInverse_A (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.LeftInverse BE (A domain) :=
  fun P => BE_A_id domain P hcomplete

/-- `BE` is surjective, since every property is the predicative content of some
quantifier. -/
theorem BE_surjective (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.Surjective (@BE E) :=
  (BE_leftInverse_A domain hcomplete).surjective

/-- `A` is injective, since distinct properties yield distinct quantifiers under existential
closure. -/
theorem A_injective (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.Injective (A domain) :=
  (BE_leftInverse_A domain hcomplete).injective

/-! ### Galois coinsertion on monotone quantifiers

On the full Boolean algebra of quantifiers `A ⊣ BE` fails: for non-monotone `Q`
such as `λR. ¬R(a)`, the counit `A(BE(Q)) ≤ Q` does not hold. Restricted to the
upward-closed quantifiers — [barwise-cooper-1981]'s constraint on what natural
language determiners denote — it does hold, because a singleton `{x} ≤ R`
whenever `R(x)`, and monotonicity lifts this to `Q({x}) ≤ Q(R)`. So the
monotonicity constraint is exactly the condition making `A` and `BE` an
adjunction. -/

/-- `A(P)` is always monotone. -/
theorem A_monotone (domain : List E) (P : E → Prop) : Monotone (A domain P) := by
  intro R R' hRR'
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P x ∧ R' x
  exact fun ⟨x, hx, hPx, hRx⟩ ↦ ⟨x, hx, hPx, hRR' x hRx⟩

/-- `A` into the monotone quantifiers `(E → Prop) →o Prop`. -/
def A_up (domain : List E) (P : E → Prop) : (E → Prop) →o Prop :=
  ⟨A domain P, A_monotone domain P⟩

/-- `BE` out of the monotone quantifiers. -/
def BE_up (Q : (E → Prop) →o Prop) : E → Prop := BE Q

/-- `A` is monotone as a map from properties to quantifiers. -/
theorem A_up_mono (domain : List E) : Monotone (A_up domain (E := E)) := by
  intro P P' hPP'; show A domain P ≤ A domain P'; intro R
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P' x ∧ R x
  exact fun ⟨x, hx, hPx, hRx⟩ ↦ ⟨x, hx, hPP' x hPx, hRx⟩

/-- `BE` is monotone on the monotone quantifiers. -/
theorem BE_up_mono : Monotone (BE_up (E := E)) := by
  intro Q Q' hQQ'; show BE Q ≤ BE Q'; intro x
  exact hQQ' (fun y ↦ y = x)

/-- The singleton property `{x}` is below any `R` satisfied by `x`. -/
private lemma singleton_le_of_mem {x : E} {R : E → Prop} (hRx : R x) :
    (fun y => y = x) ≤ R := by
  intro y (h : y = x); rw [h]; exact hRx

/-- The counit inequality `A(BE(Q)) ≤ Q` holds for upward-closed `Q`; it fails for
non-monotone `Q` such as `λR. ¬R(a)`, where `Q({a})` is false but `Q(∅)` is true. -/
theorem A_BE_le_of_mono (domain : List E) (Q : (E → Prop) →o Prop) :
    A_up domain (BE_up Q) ≤ Q := by
  show A domain (BE Q) ≤ (Q : (E → Prop) → Prop)
  intro R; simp only [A, BE]
  intro ⟨x, _, hQx, hRx⟩
  exact Q.monotone (singleton_le_of_mem hRx) hQx

/-- `A` and `BE` form a `GaloisCoinsertion` on the monotone quantifiers, since `BE ∘ A` is the
identity on properties and `A(BE(Q)) ≤ Q` for monotone `Q`. -/
def galoisCoinsertion (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisCoinsertion (A_up domain (E := E)) BE_up :=
  GaloisCoinsertion.monotoneIntro
    BE_up_mono
    (A_up_mono domain)
    (A_BE_le_of_mono domain)
    (fun P => BE_A_id domain P hcomplete)

/-- The Galois connection `A(P) ≤ Q ↔ P ≤ BE(Q)` for monotone `Q`. -/
theorem gc_A_BE (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisConnection (A_up domain (E := E)) BE_up :=
  (galoisCoinsertion domain hcomplete).gc

/-- Existential closure over a complete finite domain is ⟦some⟧, since both compute
`λR.λS. ∃x. R(x) ∧ S(x)`. -/
theorem A_eq_some_sem (E : Type*) (domain : List E) (hComplete : ∀ x : E, x ∈ domain) :
    A domain = (some_sem : GQ E) := by
  funext R S
  simp only [A, some_sem]
  exact propext ⟨fun ⟨x, _, hR, hS⟩ ↦ ⟨x, hR, hS⟩, fun ⟨x, hR, hS⟩ ↦ ⟨x, hComplete x, hR, hS⟩⟩

/-! ### The object-position shift

[heim-kratzer-1998] repair the type mismatch of a quantifier in object position in situ by
letting the quantifier take the two-place predicate and the subject, quantifying over the
object, and derive that entry for every determiner from its basic one by a lexical rule. -/

/-- The object-position reading of a quantifier, which takes an object-first two-place
predicate and the subject. -/
def objectShift (Q : NP E) : (E → E → Prop) → E → Prop := fun R x ↦ Q fun y ↦ R y x

@[simp] theorem objectShift_apply (Q : NP E) (R : E → E → Prop) (x : E) :
    objectShift Q R x = Q fun y ↦ R y x := rfl

/-- The object-position reading of a determiner, [heim-kratzer-1998]'s lexical rule deriving
it from the basic entry. -/
def _root_.Quantifier.GQ.objectShift (D : GQ E) : (E → Prop) → (E → E → Prop) → E → Prop :=
  fun P ↦ NP.objectShift (D P)

@[simp] theorem _root_.Quantifier.GQ.objectShift_apply (D : GQ E) (P : E → Prop)
    (R : E → E → Prop) (x : E) : GQ.objectShift D P R x = D P fun y ↦ R y x := rfl

/-! ### Conjunctions and disjunctions of individuals -/

/-- The conjunction of the individuals of `X`, the meet of their lifts. -/
def conjGQ (X : Set E) : NP E := ⨅ x ∈ X, individual x

/-- The disjunction of the individuals of `X`, the join of their lifts. -/
def disjGQ (X : Set E) : NP E := ⨆ x ∈ X, individual x

@[simp] theorem conjGQ_apply (X : Set E) (P : E → Prop) : conjGQ X P ↔ ∀ x ∈ X, P x := by
  simp [conjGQ, iInf_apply, iInf_Prop_eq, individual]

@[simp] theorem disjGQ_apply (X : Set E) (P : E → Prop) : disjGQ X P ↔ ∃ x ∈ X, P x := by
  simp [disjGQ, iSup_apply, iSup_Prop_eq, individual]

/-- The conjunction of the individuals of `X` is *every* restricted to `X`. -/
theorem conjGQ_eq_every_sem (X : Set E) : conjGQ X = every_sem X :=
  funext fun P ↦ propext (conjGQ_apply X P)

/-- The disjunction of the individuals of `X` is *some* restricted to `X`. -/
theorem disjGQ_eq_some_sem (X : Set E) : disjGQ X = some_sem X :=
  funext fun P ↦ propext (disjGQ_apply X P)

end Quantifier.NP
