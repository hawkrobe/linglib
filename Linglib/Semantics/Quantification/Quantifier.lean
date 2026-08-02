import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Counting
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.GaloisConnection.Defs

/-!
# Type ⟨1⟩ quantifiers

The API for `Quantifier α`, the denotation type of a quantified noun phrase.
Existential closure `A` turns a property into a quantifier and predicative
content `BE` turns one back; `BE ∘ A` is the identity, and on the
upward-closed quantifiers that [barwise-cooper-1981] take natural-language
determiners to denote, the two form a `GaloisCoinsertion`. Sending a quantifier through `BE` and back preserves truth
conditions exactly when it is a principal ultrafilter: a proper name survives
the round trip, `every student` does not. `Ty.det` names the determiner type
⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩, and the shifts relating `Quantifier` to the other noun-phrase
types are [partee-1987]'s, in `Semantics.Composition.TypeShifting`.
-/

namespace Quantification

variable {E : Type}

/-! ### Predicative content and existential closure -/

/-- Predicative content of a quantifier: `BE(Q) = λx. Q(λy. y = x)`. -/
def BE (Q : Quantifier E) : E → Prop :=
  fun x => Q (fun y => y = x)

/-- Existential closure: `A(P) = λQ. ∃x ∈ domain. P(x) ∧ Q(x)`. -/
def A (domain : List E) (P : E → Prop) : Quantifier E :=
  fun Q => ∃ x ∈ domain, P x ∧ Q x

/-! ### `BE` as a bounded-lattice homomorphism -/

/-- `BE(Q₁ ∧ Q₂) = BE(Q₁) ∧ BE(Q₂)` -/
theorem BE_conj (Q₁ Q₂ : Quantifier E) :
    BE (fun P => Q₁ P ∧ Q₂ P) = (fun x => BE Q₁ x ∧ BE Q₂ x) := rfl

/-- `BE(Q₁ ∨ Q₂) = BE(Q₁) ∨ BE(Q₂)` -/
theorem BE_disj (Q₁ Q₂ : Quantifier E) :
    BE (fun P => Q₁ P ∨ Q₂ P) = (fun x => BE Q₁ x ∨ BE Q₂ x) := rfl

/-- `BE(¬Q) = ¬BE(Q)` -/
theorem BE_neg (Q : Quantifier E) :
    BE (fun P => ¬(Q P)) = (fun x => ¬(BE Q x)) := rfl

/-- `BE` preserves meets, joins, `⊤` and `⊥` ([partee-1987]). -/
def BE_hom (E : Type) : BoundedLatticeHom (Quantifier E) (E → Prop) where
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
def isPrincipalUltrafilter (domain : List E) (Q : Quantifier E) : Prop :=
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

private def twoDomain : List Bool := [true, false]
private def twoEvery : (Bool → Prop) → Prop := fun P => ∀ x ∈ twoDomain, P x

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

/-- `BE` is surjective: every property is the predicative content of some
    quantifier. -/
theorem BE_surjective (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    Function.Surjective (@BE E) :=
  (BE_leftInverse_A domain hcomplete).surjective

/-- `A` is injective: distinct properties yield distinct quantifiers under
    existential closure — different common nouns mean different things as
    indefinites. -/
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

/-- Upward-closed (monotone) quantifiers: `Q(P)` and `P ≤ P'` imply `Q(P')`. -/
def UpwardGQ (E : Type) := { Q : Quantifier E // Monotone Q }

instance : PartialOrder (UpwardGQ E) := Subtype.partialOrder _

/-- `A(P)` is always upward-closed. -/
theorem A_monotone_gq (domain : List E) (P : E → Prop) :
    Monotone (A domain P) := by
  intro R R' hRR'
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P x ∧ R' x
  exact fun ⟨x, hx, hPx, hRx⟩ => ⟨x, hx, hPx, hRR' x hRx⟩

/-- `A` into the `UpwardGQ` subtype. -/
def A_up (domain : List E) (P : E → Prop) : UpwardGQ E :=
  ⟨A domain P, A_monotone_gq domain P⟩

/-- `BE` out of the `UpwardGQ` subtype. -/
def BE_up (Q : UpwardGQ E) : E → Prop := BE Q.val

/-- `A` is monotone as a map from properties to quantifiers. -/
theorem A_up_mono (domain : List E) : Monotone (A_up domain (E := E)) := by
  intro P P' hPP'; show A domain P ≤ A domain P'; intro R
  show (∃ x ∈ domain, P x ∧ R x) → ∃ x ∈ domain, P' x ∧ R x
  exact fun ⟨x, hx, hPx, hRx⟩ => ⟨x, hx, hPP' x hPx, hRx⟩

/-- `BE` is monotone on `UpwardGQ`. -/
theorem BE_up_mono : Monotone (BE_up (E := E)) := by
  intro Q Q' hQQ'; show BE Q.val ≤ BE Q'.val; intro x
  exact hQQ' (fun y => y = x)

/-- The singleton property `{x}` is below any `R` satisfied by `x`. -/
private lemma singleton_le_of_mem {x : E} {R : E → Prop} (hRx : R x) :
    (fun y => y = x) ≤ R := by
  intro y (h : y = x); rw [h]; exact hRx

/-- **Counit inequality**: `A(BE(Q)) ≤ Q` for upward-closed `Q`. This is what
    fails for non-monotone `Q` such as `λR. ¬R(a)`, where `Q({a})` is false but
    `Q(∅)` is true. -/
theorem A_BE_le_of_mono (domain : List E) (Q : UpwardGQ E) :
    A_up domain (BE_up Q) ≤ Q := by
  show A domain (BE Q.val) ≤ Q.val
  intro R; simp only [A, BE]
  intro ⟨x, _, hQx, hRx⟩
  exact Q.property (singleton_le_of_mem hRx) hQx

/-- `A` and `BE` form a `GaloisCoinsertion` on the upward-closed quantifiers:
    `BE ∘ A = id` on properties, and `A(BE(Q)) ≤ Q` for monotone `Q`. -/
def galoisCoinsertion (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisCoinsertion (A_up domain (E := E)) BE_up :=
  GaloisCoinsertion.monotoneIntro
    BE_up_mono
    (A_up_mono domain)
    (A_BE_le_of_mono domain)
    (fun P => BE_A_id domain P hcomplete)

/-- The Galois connection: `A(P) ≤ Q ↔ P ≤ BE(Q)` for monotone `Q`. -/
theorem gc_A_BE (domain : List E)
    (hcomplete : ∀ x : E, x ∈ domain) :
    GaloisConnection (A_up domain (E := E)) BE_up :=
  (galoisCoinsertion domain hcomplete).gc

namespace Quantifier

open Intensional

/-! ### Semantic-type alias -/

/-- The determiner type ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩. -/
def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- Existential closure over a complete finite domain is ⟦some⟧: both compute
    `λR.λS. ∃x. R(x) ∧ S(x)`. -/
theorem A_eq_some_sem (E : Type) (domain : List E)
    (hComplete : ∀ x : E, x ∈ domain) :
    A domain = (some_sem : GQ E) := by
  funext R S
  simp only [A, some_sem]
  exact propext ⟨fun ⟨x, _, hR, hS⟩ => ⟨x, hR, hS⟩,
                 fun ⟨x, hR, hS⟩ => ⟨x, hComplete x, hR, hS⟩⟩

end Quantifier

end Quantification
