import Linglib.Studies.Veltman1996

/-!
# Kirkpatrick (2023): The Dynamics of Generics

This file formalizes [kirkpatrick-2023]'s dynamic semantics for generics and its account of
generic Sobel sequences: a generic followed by a statement of its exceptions, (1), is felicitous
and judged true, while the reverse order, (2), is infelicitous and sounds contradictory. Static
theories assign each generic a truth value on its own, so the truth of a sequence is a
conjunction invariant under reordering and the contrast is invisible to them, §3
(`static_perm`). The dynamic theory of (24) evaluates a generic against a modal horizon, the set
of salient individuals, which the generic first expands with the normal instances of its
restrictor when none is yet salient (`GenericSentence.update`), and the generic is true when
every salient instance of its restrictor satisfies its scope (`GenericSentence.holds`). In a
Sobel sequence the exceptions are abnormal for the general and so absent from its horizon, while
the reverse order puts them on the horizon first, where the general finds them and no longer
expands: the two orders come apart exactly as the paper predicts (`SobelPair.order_sensitive`),
and a mixed sequence like (12) survives because each generic's restrictor excludes the
individuals the other made salient (`lions_both_orders`). Appendix A's comparison with
[veltman-1996] is checked on his eight worlds: the frame presented by accepted rules is
insensitive to their order, so his theory predicts the reverse sequence consistent
(`veltman_reverse_consistent`).

## Implementation notes

* (24) is taken at a single world: the dispositional orbit is a point, the modal horizon a
  finite set of individuals, and the normality functor of (21) the field `normal` of a
  sentence, with its inclusion in the restrictor as a proof field. The arguments of §5 are
  pointwise in the accessible world and survive the restriction.
* The contextual variable C of (20) is folded into the restrictor, as (26) and (31) do.

## References

* [kirkpatrick-2023]
* [veltman-1996]
* [cohen-1999a]
-/

namespace Kirkpatrick2023

variable {E : Type*} [DecidableEq E]

/-- A generic Gen[φ][ψ], (20), with the normal instances of its restrictor, the value of the
normality functor of (21), which lie within the restrictor. -/
structure GenericSentence (E : Type*) where
  restrictor : E → Prop
  scope : E → Prop
  normal : Finset E
  normal_restrictor : ∀ e ∈ normal, restrictor e
  [decRestrictor : DecidablePred restrictor]
  [decScope : DecidablePred scope]

attribute [instance] GenericSentence.decRestrictor GenericSentence.decScope

namespace GenericSentence

variable (g : GenericSentence E) (σ : Finset E)

/-- The context change potential of (24): a generic presupposes a salient instance of its
restrictor and, failing that, expands the horizon by the normal instances. -/
def update : Finset E := if ∃ e ∈ σ, g.restrictor e then σ else σ ∪ g.normal

/-- The truth conditions of (24): every salient instance of the restrictor on the expanded
horizon satisfies the scope. -/
def holds : Prop := ∀ e ∈ g.update σ, g.restrictor e → g.scope e

instance : Decidable (g.holds σ) := by unfold holds; infer_instance

theorem update_of_exists (h : ∃ e ∈ σ, g.restrictor e) : g.update σ = σ := if_pos h

theorem update_of_forall (h : ∀ e ∈ σ, ¬ g.restrictor e) : g.update σ = σ ∪ g.normal :=
  if_neg λ ⟨e, he, hr⟩ => h e he hr

/-- Expansion is one-way, fn. 24: the horizon never shrinks. -/
theorem subset_update : σ ⊆ g.update σ := by
  unfold update; split_ifs <;> simp

/-- A second assertion of the same generic expands nothing. -/
theorem update_update : g.update (g.update σ) = g.update σ := by
  by_cases h : ∃ e ∈ σ, g.restrictor e
  · rw [update_of_exists g σ h, update_of_exists g σ h]
  · have h' : ∀ e ∈ σ, ¬ g.restrictor e := λ e he hr => h ⟨e, he, hr⟩
    rw [update_of_forall g σ h']
    rcases g.normal.eq_empty_or_nonempty with hn | ⟨e, he⟩
    · rw [hn, Finset.union_empty, update_of_forall g σ h', hn, Finset.union_empty]
    · exact update_of_exists _ _ ⟨e, Finset.mem_union_right _ he, g.normal_restrictor e he⟩

/-- Discourse-initial truth, (23) and (26): against an empty horizon a generic is true iff its
normal instances satisfy its scope. -/
theorem holds_empty : g.holds ∅ ↔ ∀ e ∈ g.normal, g.scope e := by
  rw [holds, update_of_forall g ∅ (by simp), Finset.empty_union]
  exact ⟨λ h e he => h e he (g.normal_restrictor e he), λ h e he _ => h e he⟩

end GenericSentence

/-- A sequence of generics is consistent from a horizon when each is true against the horizon
its predecessors have expanded, §5. -/
def ConsistentFrom : Finset E → List (GenericSentence E) → Prop
  | _, [] => True
  | σ, g :: gs => g.holds σ ∧ ConsistentFrom (g.update σ) gs

instance decidableConsistentFrom :
    ∀ (σ : Finset E) (gs : List (GenericSentence E)), Decidable (ConsistentFrom σ gs)
  | _, [] => isTrue trivial
  | σ, g :: gs =>
    haveI := decidableConsistentFrom (g.update σ) gs
    inferInstanceAs (Decidable (g.holds σ ∧ ConsistentFrom (g.update σ) gs))

/-- Consistency from the empty discourse-initial horizon, §5.1. -/
abbrev Consistent (gs : List (GenericSentence E)) : Prop := ConsistentFrom ∅ gs

/-! ### Static theories, §3 -/

/-- A static semantics assigns each generic a truth value on its own, so a sequence is true
when each member is, whatever the order: the probabilistic truth conditions (18) of
[cohen-1999a], the normality-based ones of (19) and the indexical approach of §3.3 all take
this form. -/
abbrev Static (truth : GenericSentence E → Prop) (gs : List (GenericSentence E)) : Prop :=
  ∀ g ∈ gs, truth g

omit [DecidableEq E] in
/-- §3.4: no static semantics is sensitive to the order of a sequence. -/
theorem static_perm (truth : GenericSentence E → Prop) {gs gs' : List (GenericSentence E)}
    (h : gs.Perm gs') : Static truth gs ↔ Static truth gs' :=
  ⟨λ hs g hg => hs g (h.mem_iff.2 hg), λ hs g hg => hs g (h.mem_iff.1 hg)⟩

/-! ### Generic Sobel sequences, §5 -/

/-- Two generics true on their own, the second of which finds no instance of its restrictor
among the first's normal instances, are consistent in that order: the second expands the
horizon and is evaluated on its own normal instances. -/
theorem consistent_pair {g₁ g₂ : GenericSentence E} (h₁ : g₁.holds ∅) (h₂ : g₂.holds ∅)
    (hdis : ∀ e ∈ g₁.normal, ¬ g₂.restrictor e) : Consistent [g₁, g₂] := by
  refine ⟨h₁, ?_, trivial⟩
  rw [GenericSentence.holds, g₁.update_of_forall ∅ (by simp), Finset.empty_union,
    g₂.update_of_forall _ hdis]
  intro e he hr
  rcases Finset.mem_union.1 he with he | he
  · exact absurd hr (hdis e he)
  · exact g₂.holds_empty.1 h₂ e he

/-- §5.3: two generics true on their own whose restrictors exclude each other's normal
instances are consistent in both orders, each expanding the horizon in turn. -/
theorem consistent_both_orders {g₁ g₂ : GenericSentence E} (h₁ : g₁.holds ∅) (h₂ : g₂.holds ∅)
    (h₁₂ : ∀ e ∈ g₁.normal, ¬ g₂.restrictor e) (h₂₁ : ∀ e ∈ g₂.normal, ¬ g₁.restrictor e) :
    Consistent [g₁, g₂] ∧ Consistent [g₂, g₁] :=
  ⟨consistent_pair h₁ h₂ h₁₂, consistent_pair h₂ h₁ h₂₁⟩

/-- A pair of generics forming a Sobel sequence in the order general, exception, (1): the
exception's restrictor picks out a subkind of the general's, §5.2, its scope contradicts the
general's, and the general's normal instances are not exceptions. -/
structure SobelPair (E : Type*) where
  general : GenericSentence E
  exception : GenericSentence E
  sub : ∀ e, exception.restrictor e → general.restrictor e
  contra : ∀ e, exception.scope e → ¬ general.scope e
  abnormal : ∀ e ∈ general.normal, ¬ exception.restrictor e

namespace SobelPair

variable (p : SobelPair E)

/-- §5.1: a Sobel sequence whose generics are each true on their own is consistent, the
exceptions being absent from the general's horizon. -/
theorem consistent (hg : p.general.holds ∅) (he : p.exception.holds ∅) :
    Consistent [p.general, p.exception] :=
  consistent_pair hg he p.abnormal

/-- §5.2: the reverse order is inconsistent once there is an exception: it is salient when the
general is evaluated, satisfies the general's restrictor, and contradicts its scope. -/
theorem reverse_inconsistent (he : p.exception.holds ∅) (hne : p.exception.normal.Nonempty) :
    ¬ Consistent [p.exception, p.general] := by
  obtain ⟨e, he'⟩ := hne
  have hr : p.general.restrictor e := p.sub e (p.exception.normal_restrictor e he')
  rintro ⟨-, hgen, -⟩
  rw [GenericSentence.holds, p.exception.update_of_forall ∅ (by simp), Finset.empty_union,
    p.general.update_of_exists _ ⟨e, he', hr⟩] at hgen
  exact p.contra e (p.exception.holds_empty.1 he e he') (hgen e he' hr)

/-- The order sensitivity of §5: the same two generics, each true on its own, are consistent
in the Sobel order and inconsistent in the reverse. -/
theorem order_sensitive (hg : p.general.holds ∅) (he : p.exception.holds ∅)
    (hne : p.exception.normal.Nonempty) :
    Consistent [p.general, p.exception] ∧ ¬ Consistent [p.exception, p.general] :=
  ⟨p.consistent hg he, p.reverse_inconsistent he hne⟩

end SobelPair

/-! ### Ravens, (1a) and (2a) -/

/-- Two normally coloured ravens and an albino one. -/
inductive Raven
  | normal₁
  | normal₂
  | albino
  deriving DecidableEq

/-- Black ravens: all but the albino. -/
def Raven.black (x : Raven) : Prop := x ≠ .albino

instance : DecidablePred Raven.black := λ x => inferInstanceAs (Decidable (x ≠ .albino))

/-- *Ravens are black*, (20a): every raven is coloured in some way, and the normal ones are
the normally coloured ones. -/
def ravensAreBlack : GenericSentence Raven :=
  ⟨λ _ => True, Raven.black, {.normal₁, .normal₂}, by decide⟩

/-- *Albino ravens aren't black*. -/
def albinoRavensArentBlack : GenericSentence Raven :=
  ⟨(· = .albino), λ x => ¬ x.black, {.albino}, by decide⟩

/-- Albino ravens are ravens, are not black, and are abnormal as ravens. -/
def ravenPair : SobelPair Raven :=
  ⟨ravensAreBlack, albinoRavensArentBlack, by intro e; cases e <;> decide,
    by intro e; cases e <;> decide, by decide⟩

/-- (25) and (28): *Ravens are black; but albino ravens aren't* is consistent and its reverse
is not, though each generic is true on its own. -/
theorem ravens_order_sensitive :
    Consistent [ravensAreBlack, albinoRavensArentBlack] ∧
      ¬ Consistent [albinoRavensArentBlack, ravensAreBlack] :=
  ravenPair.order_sensitive (by decide) (by decide) ⟨.albino, by decide⟩

/-- A static semantics accepts the reverse order, §3.1. -/
theorem ravens_static : Static (·.holds ∅) [albinoRavensArentBlack, ravensAreBlack] := by
  decide

/-! ### Mixed generics, (12) -/

/-- A male and a female lion. -/
inductive Lion
  | male
  | female
  deriving DecidableEq

/-- *Lions have manes*, (31): the restrictor is lions with some male sexually selected trait,
the normal such lion the male. -/
def lionsHaveManes : GenericSentence Lion := ⟨(· = .male), (· = .male), {.male}, by decide⟩

/-- *Lions give birth to live young*, (32): the restrictor is lions that produce offspring in
some way, the normal such lion the female. -/
def lionsGiveBirth : GenericSentence Lion :=
  ⟨(· = .female), (· = .female), {.female}, by decide⟩

/-- (29): the mixed sequence is consistent in both orders, since each generic's restrictor
excludes the lions the other makes salient. -/
theorem lions_both_orders :
    Consistent [lionsHaveManes, lionsGiveBirth] ∧ Consistent [lionsGiveBirth, lionsHaveManes] :=
  consistent_both_orders (by decide) (by decide) (by decide) (by decide)

/-! ### Appendix A: Veltman (1996) -/

open Veltman1996

/-- σ₁ of Appendix A: the minimal state after `p ⇝ r` then `(p ∧ q) ⇝ ¬r`, with `p` raven,
`q` albino and `r` black on the eight worlds of Table 1. -/
def sobelState : State World := State.init |> rule p r |> rule (p ∩ q) rᶜ

/-- σ₂ of Appendix A: the rules accepted in the reverse order. -/
def reverseState : State World := State.init |> rule (p ∩ q) rᶜ |> rule p r

theorem sobelState_eq : sobelState = ⟨[⟨p ∩ q, rᶜ⟩, ⟨p, r⟩], Finset.univ⟩ := by decide +kernel

theorem reverseState_eq : reverseState = ⟨[⟨p, r⟩, ⟨p ∩ q, rᶜ⟩], Finset.univ⟩ := by
  decide +kernel

/-- Appendix A: neither order crashes and both reach the same frame, since a presented frame
does not depend on the order of its rules, so Veltman's theory predicts the reverse Sobel
sequence consistent. -/
theorem veltman_reverse_consistent :
    sobelState ≠ State.absurd ∧ reverseState ≠ State.absurd ∧
      sobelState.frame = reverseState.frame :=
  ⟨by rw [sobelState_eq]; decide, by rw [reverseState_eq]; decide,
    by rw [sobelState_eq, reverseState_eq]; exact Frame.ofRules_perm (List.Perm.swap _ _ _)⟩

end Kirkpatrick2023
