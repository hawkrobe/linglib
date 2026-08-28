import Linglib.Semantics.Presupposition.Defs
import Linglib.Data.Examples.AnandHacquard2013
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Anand & Hacquard 2013: epistemics and attitudes

Epistemic modals are acceptable in the complements of attitudes of acceptance (*think*, *say*,
*realize*), unacceptable under desideratives and directives, and acceptable under emotive
doxastics (*hope*, *fear*) and dubitatives (*doubt*) with possibility but not necessity force, in
seven-point acceptability surveys of French, Italian, and Spanish. The account combines Yalcin's
information-state semantics, on which an epistemic quantifies over a state `S` anaphoric to the
embedding attitude and presupposes `S ≠ ∅`, with Bolinger's split of attitudes: representational
attitudes pass their doxastic state as `S`; non-representational ones set `S = ∅` and combine
with their complement by Villalta's comparison against the Heimian alternative `¬φ`, so an
embedded epistemic is never defined. Emotive doxastics and dubitatives are hybrids — a doxastic
possibility assertion, a comparison of the complement's verifiers with its falsifiers, and an
uncertainty presupposition demanding both — and the doxastic assertion of an embedded necessity
modal contradicts that presupposition, while an embedded possibility modal contributes nothing
new. Italian *pensare* selects the subjunctive yet licenses epistemics, so subjunctive is an
imperfect correlate.

## Main definitions

* `SProp`: a complement relative to an information state `S`, with `might`, `must`, `ofSet`.
* `Better`: Villalta's lift of an ordering to propositions; `verifiers` the sub-states settled
  on a complement.
* `Licensed`: whether some context makes an embedded epistemic defined and true.

## References

* [anand-hacquard-2013]
* [yalcin-2007] — the information-state parameter and the *imagine* contrast (23)
* [veltman-1996], [hacquard-2006], [hacquard-2010] — anaphoric modal bases
* [bolinger-1968] — representational attitudes
* [villalta-2008] — comparative semantics for subjunctive-selecting attitudes
* [heim-1992] — the alternative set `{φ, ¬φ}`
* [geurts-2005] — the non-triviality presupposition of modals
* [scheffler-2008] — the doxastic component of *hope*
* [falaus-2010] — Romanian *vreun* under *want* and *hope*
* [kratzer-2009] — the filing-cabinet scenario
-/

namespace AnandHacquard2013

open Data.Examples Presupposition

variable {W : Type*}

/-! ### Complements relative to an information state -/

/-- A complement evaluated against an information state `S` — Yalcin's parameter — as a
partial proposition for each `S`. -/
abbrev SProp (W : Type*) := Set W → PartialProp W

/-- An unmodalized complement ignores the information state. -/
def ofSet (p : Set W) : SProp W := fun _ => PartialProp.ofProp (· ∈ p)

/-- Epistemic possibility (37a): presupposes `S ≠ ∅`; true iff `S` contains a `p`-world. -/
def might (p : Set W) : SProp W := fun S => ⟨fun _ => S.Nonempty, fun _ => (S ∩ p).Nonempty⟩

/-- Epistemic necessity (37b): presupposes `S ≠ ∅`; true iff `S ⊆ p`. -/
def must (p : Set W) : SProp W := fun S => ⟨fun _ => S.Nonempty, fun _ => S ⊆ p⟩

/-- Negation of a complement, keeping its presupposition. -/
def neg (φ : SProp W) : SProp W := fun S => ⟨(φ S).presup, fun w => ¬ (φ S).assertion w⟩

/-- Conjunction of complements. -/
def conj (φ ψ : SProp W) : SProp W := fun S =>
  ⟨fun w => (φ S).presup w ∧ (ψ S).presup w, fun w => (φ S).assertion w ∧ (ψ S).assertion w⟩

/-- An *according to X* phrase evaluates its complement at `X`'s own information state (39). -/
def accordingTo (T : Set W) (φ : SProp W) : SProp W := fun _ => φ T

/-- Epistemic modal force. -/
inductive Force
  | possibility
  | necessity
  deriving DecidableEq, Fintype

/-- The epistemic of a given force. -/
def Force.modal : Force → Set W → SProp W
  | .possibility => might
  | .necessity => must

/-! ### Representational and non-representational attitudes -/

/-- A representational attitude (29): the complement holds at every world of the attitude's
domain, which also serves as its information state. -/
def representational (dox : W → Set W) (φ : SProp W) : PartialProp W where
  presup w := ∀ v ∈ dox w, (φ (dox w)).presup v
  assertion w := ∀ v ∈ dox w, (φ (dox w)).assertion v

/-- Vacuous quantification (35): an embedded necessity epistemic claims that the domain is
included in its prejacent. -/
theorem representational_must (dox : W → Set W) (p : Set W) (w : W) :
    (representational dox (must p)).assertion w ↔ dox w ⊆ p :=
  ⟨fun h v hv => h v hv hv, fun h _ _ => h⟩

/-- Yalcin's (23b): *imagine that it is raining but it might not be* is contradictory whenever
the imagination state is nonempty, since the modal quantifies over that very state. -/
theorem imagine_epistemic_contradiction (dox : W → Set W) (p : Set W) {w : W}
    (h : (dox w).Nonempty) :
    ¬ (representational dox (conj (ofSet p) (might pᶜ))).assertion w := by
  intro hc
  obtain ⟨v, hv⟩ := h
  obtain ⟨u, hu, hup⟩ := (hc v hv).2
  exact hup (hc u hu).1

/-- Villalta's lift of a strict ordering to sets (32b): every member of `q` is bettered by some
member of `p`, and some member of `p` is bettered by no member of `q`. Applied to sets of sets
it is the ordering of (52). -/
def Better {α : Type*} (r : α → α → Prop) (p q : Set α) : Prop :=
  (∀ v ∈ q, ∃ u ∈ p, r u v) ∧ ∃ u ∈ p, ∀ v ∈ q, ¬ r v u

theorem Better.mono_left {α : Type*} {r : α → α → Prop} {p p' q : Set α} (h : Better r p q)
    (hp : p ⊆ p') : Better r p' q :=
  ⟨fun v hv => let ⟨u, hu, hr⟩ := h.1 v hv; ⟨u, hp hu, hr⟩,
    let ⟨u, hu, hr⟩ := h.2; ⟨u, hp hu, hr⟩⟩

theorem Better.anti_right {α : Type*} {r : α → α → Prop} {p q q' : Set α} (h : Better r p q)
    (hq : q' ⊆ q) : Better r p q' :=
  ⟨fun v hv => h.1 v (hq hv), let ⟨u, hu, hr⟩ := h.2; ⟨u, hu, fun v hv => hr v (hq hv)⟩⟩

/-- A non-representational attitude (36): the information state is reset to `∅`, and the
complement evaluated there is compared with its negation — Villalta's comparison over the
Heimian alternative set `{φ, ¬φ}`, with `des w` the desirability ordering at `w`. -/
def preferential (des : W → W → W → Prop) (φ : SProp W) : PartialProp W where
  presup w := (φ ∅).presup w
  assertion w := Better (des w) {v | (φ ∅).assertion v} {v | ¬ (φ ∅).assertion v}

/-- (38): an epistemic embedded under a non-representational attitude inherits the empty
information state and fails its non-triviality presupposition. -/
theorem preferential_modal_undefined (des : W → W → W → Prop) (f : Force) (p : Set W)
    (w : W) : ¬ (preferential des (f.modal p)).presup w := by
  cases f <;> exact Set.not_nonempty_empty

/-- The escape hatch (39): an *according to X* phrase makes the embedded epistemic defined
exactly when `X`'s information state is nonempty. -/
theorem preferential_accordingTo_defined (des : W → W → W → Prop) (T : Set W) (f : Force)
    (p : Set W) (w : W) :
    (preferential des (accordingTo T (f.modal p))).presup w ↔ T.Nonempty := by
  cases f <;> exact Iff.rfl

/-! ### Verifiers and falsifiers -/

/-- The nonempty sub-states of `A`. -/
def subStates {α : Type*} (A : Set α) : Set (Set α) := {X | X ⊆ A ∧ X.Nonempty}

/-- The `φ`-verifiers in `S` (50): the nonempty sub-states of `S` on all of whose sub-states
`φ` holds throughout. -/
def verifiers (φ : SProp W) (S : Set W) : Set (Set W) :=
  {X | X ⊆ S ∧ X.Nonempty ∧ ∀ Y ⊆ X, ∀ w ∈ Y, (φ Y).assertion w}

/-- The `φ`-falsifiers in `S`: the `¬φ`-verifiers. -/
def falsifiers (φ : SProp W) (S : Set W) : Set (Set W) := verifiers (neg φ) S

theorem verifiers_eq {φ : SProp W} {q : Set W}
    (h : ∀ X : Set W, (∀ Y ⊆ X, ∀ w ∈ Y, (φ Y).assertion w) ↔ X ⊆ q) (S : Set W) :
    verifiers φ S = subStates (S ∩ q) := by
  ext X; simp only [verifiers, subStates, Set.mem_ofPred_eq, h, Set.subset_inter_iff]; tauto

/-- Figure 3: the verifiers of `p`, `might p`, and `must p` in `S` are all the nonempty
sub-states of `S ∩ p`. -/
theorem verifiers_ofSet (p S : Set W) : verifiers (ofSet p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := ofSet p) (q := p)
    (fun X => ⟨fun h _ hw => h X Set.Subset.rfl _ hw, fun h _ hY _ hw => h (hY hw)⟩) S

theorem verifiers_might (p S : Set W) : verifiers (might p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := might p) (q := p) (fun X => ⟨fun h w hw => by
      obtain ⟨v, hv, hvp⟩ := h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w)
      exact Set.mem_singleton_iff.mp hv ▸ hvp,
    fun h _ hY w hw => ⟨w, hw, h (hY hw)⟩⟩) S

theorem verifiers_must (p S : Set W) : verifiers (must p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := must p) (q := p)
    (fun X => ⟨fun h _ hw => h X Set.Subset.rfl _ hw hw, fun h _ hY _ _ => hY.trans h⟩) S

/-- Figure 3: the falsifiers of `p`, `might p`, and `must p` in `S` are all the nonempty
sub-states of `S ∩ pᶜ`. -/
theorem falsifiers_ofSet (p S : Set W) : falsifiers (ofSet p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (ofSet p)) (q := pᶜ)
    (fun X => ⟨fun h _ hw => h X Set.Subset.rfl _ hw, fun h _ hY _ hw => h (hY hw)⟩) S

theorem falsifiers_might (p S : Set W) : falsifiers (might p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (might p)) (q := pᶜ) (fun _ => ⟨fun h w hw hp =>
      h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w) ⟨w, Set.mem_singleton w, hp⟩,
    fun h _ hY _ _ ⟨_, hvY, hvp⟩ => h (hY hvY) hvp⟩) S

theorem falsifiers_must (p S : Set W) : falsifiers (must p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (must p)) (q := pᶜ) (fun _ => ⟨fun h w hw hp =>
      h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w)
        (Set.singleton_subset_iff.mpr hp),
    fun h _ hY _ hw hYp => h (hY hw) (hYp hw)⟩) S

/-- Footnote 19: comparing two families of nonempty sub-states under the lifted ordering is
comparing the states themselves, by upward monotonicity of `Better` in its first argument and
downward monotonicity in its second. -/
theorem better_subStates_iff {α : Type*} (r : α → α → Prop) (A B : Set α) :
    Better (Better r) (subStates A) (subStates B) ↔ Better r A B := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases B.eq_empty_or_nonempty with rfl | hB
    · obtain ⟨P, ⟨hPA, u, hu⟩, -⟩ := h2
      exact ⟨fun v hv => absurd hv (Set.notMem_empty v), u, hPA hu,
        fun v hv => absurd hv (Set.notMem_empty v)⟩
    · obtain ⟨p, ⟨hpA, -⟩, hp⟩ := h1 B ⟨Set.Subset.rfl, hB⟩
      exact hp.mono_left hpA
  · rintro ⟨h1, u, hu, hr⟩
    refine ⟨fun q hq => ⟨A, ⟨Set.Subset.rfl, u, hu⟩, Better.anti_right ⟨h1, u, hu, hr⟩ hq.1⟩,
      {u}, ⟨Set.singleton_subset_iff.mpr hu, Set.singleton_nonempty u⟩, fun q hq hqu => ?_⟩
    obtain ⟨v, hv, hvr⟩ := hqu.1 u (Set.mem_singleton u)
    exact hr v (hq.1 hv) hvr

/-- (51): the preference component of an emotive doxastic compares `S ∩ p` with `S ∩ pᶜ`. -/
theorem prefers_iff {φ : SProp W} {p S : Set W} (r : W → W → Prop)
    (hv : verifiers φ S = subStates (S ∩ p)) (hf : falsifiers φ S = subStates (S ∩ pᶜ)) :
    Better (Better r) (verifiers φ S) (falsifiers φ S) ↔ Better r (S ∩ p) (S ∩ pᶜ) := by
  rw [hv, hf, better_subStates_iff]

/-- The preference component does not see the modal: *hopes p*, *hopes might p*, and
*hopes must p* all prefer the `p`-verifying doxastic alternatives. -/
theorem prefers_modal_iff (r : W → W → Prop) (p S : Set W) (f : Force) :
    Better (Better r) (verifiers (f.modal p) S) (falsifiers (f.modal p) S) ↔
      Better (Better r) (verifiers (ofSet p) S) (falsifiers (ofSet p) S) := by
  cases f <;> simp only [Force.modal, verifiers_might, verifiers_must, falsifiers_might,
    falsifiers_must, verifiers_ofSet, falsifiers_ofSet]

/-! ### Emotive doxastics and dubitatives -/

/-- The uncertainty condition (54): the complement has both verifiers and falsifiers in the
doxastic state. -/
def Uncertain (φ : SProp W) (S : Set W) : Prop :=
  (verifiers φ S).Nonempty ∧ (falsifiers φ S).Nonempty

/-- The doxastic assertion (53): the complement holds at some world of the doxastic state. -/
def Possible (φ : SProp W) (S : Set W) : Prop := ∃ w ∈ S, (φ S).assertion w

/-- `a hopes that φ` (55): presupposes uncertainty; asserts doxastic possibility and that the
verifiers are more desirable than the falsifiers. *fear* has the shape of `doubt` over the
desirability ordering. -/
def hope (des : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) : PartialProp W where
  presup w := Uncertain φ (dox w)
  assertion w :=
    Possible φ (dox w) ∧ Better (Better (des w)) (verifiers φ (dox w)) (falsifiers φ (dox w))

/-- `a doubts that φ` (63): as `hope`, with the falsifiers likelier than the verifiers. -/
def doubt (prob : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) : PartialProp W where
  presup w := Uncertain φ (dox w)
  assertion w :=
    Possible φ (dox w) ∧ Better (Better (prob w)) (falsifiers φ (dox w)) (verifiers φ (dox w))

/-- (58) with *must*: the doxastic assertion of an embedded necessity epistemic puts the whole
state inside `p`, leaving no falsifier — it contradicts the uncertainty presupposition. -/
theorem uncertain_must_not_possible {p S : Set W} (hu : Uncertain (must p) S) :
    ¬ Possible (must p) S := by
  intro hp
  obtain ⟨_, _, hS⟩ := hp
  obtain ⟨_, hf⟩ := hu
  rw [falsifiers_must] at hf
  obtain ⟨X, hX, v, hv⟩ := hf
  exact (hX hv).2 (hS (hX hv).1)

theorem hope_must_not_holds (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W) :
    ¬ PartialProp.holds w (hope des dox (must p)) :=
  fun ⟨hu, hp, _⟩ => uncertain_must_not_possible hu hp

theorem doubt_must_not_holds (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : ¬ PartialProp.holds w (doubt prob dox (must p)) :=
  fun ⟨hu, hp, _⟩ => uncertain_must_not_possible hu hp

/-- (74): a possibility epistemic scoping under negation is a universal claim and fails like
*must*. -/
theorem hope_not_might_not_holds (des : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : ¬ PartialProp.holds w (hope des dox (neg (might p))) := by
  intro h
  obtain ⟨⟨-, X, hXS, ⟨v, hv⟩, hX⟩, hP, -⟩ := h
  obtain ⟨_, _, hS⟩ := hP
  exact hX X Set.Subset.rfl v hv fun ⟨u, hu⟩ => hS ⟨u, hXS hu.1, hu.2⟩

theorem possible_might_iff (p S : Set W) : Possible (might p) S ↔ Possible (ofSet p) S :=
  ⟨fun ⟨_, _, v, hv⟩ => ⟨v, hv.1, hv.2⟩, fun ⟨w, hw, hp⟩ => ⟨w, hw, w, hw, hp⟩⟩

/-- (59) is (57): under an emotive doxastic, *might p* and bare *p* have the same uncertainty
presupposition, doxastic assertion, and preference — modal concord. -/
theorem hope_might (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    hope des dox (might p) = hope des dox (ofSet p) := by
  ext w <;> simp only [hope, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

theorem doubt_might (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    doubt prob dox (might p) = doubt prob dox (ofSet p) := by
  ext w <;> simp only [doubt, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

/-! ### The distribution -/

/-- The attitude classes of Table 3. -/
inductive AttitudeClass
  | doxastic
  | argumentative
  | semifactive
  | desiderative
  | directive
  | emotiveDoxastic
  | dubitative
  deriving DecidableEq, Fintype

/-- The four lexical semantics the paper assigns. -/
inductive Kind
  | acceptance
  | preferenceOriented
  | emotiveDoxastic
  | dubitative
  deriving DecidableEq

/-- Attitudes of acceptance are representational (§3.3), desideratives and directives
preference-oriented (36), and the two hybrid classes get (55) and (63). -/
def AttitudeClass.kind : AttitudeClass → Kind
  | .doxastic | .argumentative | .semifactive => .acceptance
  | .desiderative | .directive => .preferenceOriented
  | .emotiveDoxastic => .emotiveDoxastic
  | .dubitative => .dubitative

/-- The lexical entry of each kind, over the attitude's scale, doxastic state, and
complement. -/
def Kind.entry : Kind → (W → W → W → Prop) → (W → Set W) → SProp W → PartialProp W
  | .acceptance => fun _ dox => representational dox
  | .preferenceOriented => fun r _ => preferential r
  | .emotiveDoxastic => hope
  | .dubitative => doubt

/-- An epistemic of force `f` is licensed under a kind of attitude when some scale, doxastic
state, prejacent, and world make the embedding defined and true. -/
def Licensed (W : Type*) (k : Kind) (f : Force) : Prop :=
  ∃ (r : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W),
    PartialProp.holds w (k.entry r dox (f.modal p))

theorem licensed_acceptance [Nontrivial W] (f : Force) :
    Licensed W .acceptance f := by
  obtain ⟨a, -, -⟩ := exists_pair_ne W
  refine ⟨fun _ _ _ => True, fun _ => Set.univ, Set.univ, a, ?_⟩
  cases f
  · exact ⟨fun _ _ => Set.univ_nonempty, fun _ _ => ⟨a, trivial, trivial⟩⟩
  · exact ⟨fun _ _ => Set.univ_nonempty, fun _ _ => Set.Subset.rfl⟩

theorem not_licensed_preferenceOriented (f : Force) : ¬ Licensed W .preferenceOriented f :=
  fun ⟨r, _, p, w, h, _⟩ => preferential_modal_undefined r f p w h

theorem licensed_emotiveDoxastic_possibility [Nontrivial W] :
    Licensed W .emotiveDoxastic .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u = a ∧ v ≠ a, fun _ => Set.univ, {a}, a, ?_, ⟨a, trivial, a, trivial, rfl⟩,
    ?_⟩
  · show Uncertain (might {a}) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u = a ∧ v ≠ a) (verifiers (might {a}) Set.univ)
      (falsifiers (might {a}) Set.univ)
    rw [prefers_iff _ (verifiers_might _ _) (falsifiers_might _ _), Set.univ_inter,
      Set.univ_inter]
    exact ⟨fun v hv => ⟨a, rfl, rfl, hv⟩, a, rfl, fun v hv h => hv h.1⟩

theorem not_licensed_emotiveDoxastic_necessity : ¬ Licensed W .emotiveDoxastic .necessity :=
  fun ⟨r, dox, p, w, h⟩ => hope_must_not_holds r dox p w h

theorem licensed_dubitative_possibility [Nontrivial W] : Licensed W .dubitative .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u ≠ a ∧ v = a, fun _ => Set.univ, {a}, a, ?_, ⟨a, trivial, a, trivial, rfl⟩,
    ?_⟩
  · show Uncertain (might {a}) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u ≠ a ∧ v = a) (falsifiers (might {a}) Set.univ)
      (verifiers (might {a}) Set.univ)
    rw [falsifiers_might, verifiers_might, better_subStates_iff, Set.univ_inter, Set.univ_inter]
    exact ⟨fun v hv => ⟨b, hab.symm, hab.symm, hv⟩, b, hab.symm, fun v hv h => h.1 hv⟩

theorem not_licensed_dubitative_necessity : ¬ Licensed W .dubitative .necessity :=
  fun ⟨r, dox, p, w, h⟩ => doubt_must_not_holds r dox p w h

/-- Table 3, derived: epistemics are licensed by representational attitudes, by no
preferential attitude, and by the hybrids only with possibility force. -/
theorem licensed_iff [Nontrivial W] (k : Kind) (f : Force) :
    Licensed W k f ↔ k ≠ .preferenceOriented ∧ (k = .acceptance ∨ f = .possibility) := by
  cases k <;> cases f <;>
    simp only [licensed_acceptance, not_licensed_preferenceOriented,
      licensed_emotiveDoxastic_possibility, not_licensed_emotiveDoxastic_necessity,
      licensed_dubitative_possibility, not_licensed_dubitative_necessity] <;> decide

/-! ### The paper's examples -/

/-- The `attitude_class` feature of an example row. -/
def AttitudeClass.ofString? : String → Option AttitudeClass
  | "doxastic" => some .doxastic
  | "argumentative" => some .argumentative
  | "semifactive" => some .semifactive
  | "desiderative" => some .desiderative
  | "directive" => some .directive
  | "emotive_doxastic" => some .emotiveDoxastic
  | "dubitative" => some .dubitative
  | _ => none

/-- The `modal_force` feature of an example row. -/
def Force.ofString? : String → Option Force
  | "possibility" => some .possibility
  | "necessity" => some .necessity
  | _ => none

/-- Every epistemic anchored to its embedding attitude is judged acceptable exactly when
`Licensed` holds for the attitude's kind and the modal's force. -/
theorem rows_track_licensing [Nontrivial W] :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" →
      r.feature? "modal_flavor" = some "epistemic" →
      ∀ c f, (r.feature? "attitude_class").bind AttitudeClass.ofString? = some c →
        (r.feature? "modal_force").bind Force.ofString? = some f →
        (r.judgment = .acceptable ↔ Licensed W c.kind f) := by
  simp only [licensed_iff]; decide +kernel

/-- Every unacceptable attitude-anchored epistemic in the Romance data sits in a subjunctive
complement (§5.1); the converse fails at (18), (20), and (65). -/
theorem unacceptable_rows_subjunctive :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" → r.judgment = .unacceptable →
      r.feature? "mood" = none ∨ r.feature? "mood" = some "subjunctive" := by
  decide +kernel

end AnandHacquard2013
