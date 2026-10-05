module

public import Linglib.Syntax.Minimalist.Geometry
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Person.Basic
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Tactic.DeriveFintype

/-!
# Cyclic Agree over articulated person probes

Person is decomposed into privative segments ordered by entailment: every person bears `π`,
speech-act participants also `participant`, and the innermost segments `speaker` and `addressee`
distinguish first from second person according to a geometry, which fixes which segments a
language uses. A probe is a list of unvalued segments. A probe on v first meets the internal
argument and checks every segment it bears; the segments left over, its residue, probe again from
the next projection of v, where the external argument is the closest goal. The context is direct
when the external argument checks some residue, and inverse otherwise, when the core probe never
Agrees with it and its person goes unlicensed.

## Main definitions

* `Minimalist.CyclicAgree.Segment`: the person segments, with their entailment order.
* `Minimalist.CyclicAgree.PersonGeometry`: the standard, addressee and branching geometries.
* `Minimalist.CyclicAgree.personSpec`: the segments a person bears under a geometry.
* `Minimalist.CyclicAgree.AgreementSystem`: a geometry and an articulated probe, with the residue,
  the direct and inverse contexts, the controller of the agreement slot, and person licensing of
  the external argument.

## Main results

* `Minimalist.CyclicAgree.AgreementSystem.eaLicensed_iff_isDirect`: the core probe licenses the
  external argument exactly in direct contexts.
* `Minimalist.CyclicAgree.AgreementSystem.isDirect_iff_length_lt`: under a chain geometry a
  context is direct iff the external argument matches more of the probe than the internal one.
* `Minimalist.CyclicAgree.AgreementSystem.IsDirect.mono`: a more articulated probe has more direct
  contexts.
* `Minimalist.CyclicAgree.AgreementSystem.flat_isInverse`: a flat probe makes every context
  inverse.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
-/

@[expose] public section

namespace Minimalist.CyclicAgree

/-! ### Person segments and geometries -/

/-- A segment of an articulated person feature. -/
inductive Segment where
  | pi
  | participant
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Segment

/-- A segment entails `π`, and `speaker` and `addressee` entail `participant`. -/
protected def le (a b : Segment) : Prop :=
  a = b ∨ a = .pi ∨ (a = .participant ∧ (b = .speaker ∨ b = .addressee))

instance : DecidableRel Segment.le := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The entailment order on segments, `a ≤ b` when bearing `b` entails bearing `a`. -/
instance : PartialOrder Segment where
  le := Segment.le
  le_refl _ := Or.inl rfl
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Segment := fun a b ↦ inferInstanceAs (Decidable (Segment.le a b))

/-- The segments a segment entails, itself included. -/
def entailments (s : Segment) : Finset Segment := Finset.univ.filter (· ≤ s)

/-- The segments from the outermost to the innermost. -/
def all : List Segment := [.pi, .participant, .speaker, .addressee]

end Segment

/-- The segments a person bears when both innermost segments are used; the inclusive bears both. -/
def universalSpec : Person → List Segment
  | .first | .firstExclusive => [.pi, .participant, .speaker]
  | .firstInclusive => [.pi, .participant, .speaker, .addressee]
  | .second => [.pi, .participant, .addressee]
  | .third => [.pi]

/-- A person geometry fixes which innermost segment distinguishes first from second person. It is
`speaker` under `standard` and `addressee` under `addressee`, and under `branching` both are sister
leaves of `participant` ([harley-ritter-2002]). -/
inductive PersonGeometry where
  | standard
  | addressee
  | branching
  deriving DecidableEq, Repr, Fintype

namespace PersonGeometry

/-- The segments a geometry uses. -/
def nodes : PersonGeometry → Finset Segment
  | .standard => {.pi, .participant, .speaker}
  | .addressee => {.pi, .participant, .addressee}
  | .branching => Finset.univ

/-- The feature geometry a person geometry denotes. -/
def toGeometry (geom : PersonGeometry) : Minimalist.Geometry Segment where
  nodes := geom.nodes
  entailments := Segment.entailments
  mem_entailments_self a := by simp [Segment.entailments]
  entailments_subset_of_mem a b hb c hc := by
    rw [Segment.entailments, Finset.mem_filter] at hb hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.trans hb.2⟩

end PersonGeometry

/-- The segments a person bears under a geometry, from the outermost to the innermost. -/
def personSpec (geom : PersonGeometry) (p : Person) : List Segment :=
  Segment.all.filter fun s ↦ decide (s ∈ universalSpec p ∧ s ∈ geom.nodes)

/-- Every person bears `π` under every geometry. -/
theorem pi_mem_personSpec (geom : PersonGeometry) (p : Person) :
    Segment.pi ∈ personSpec geom p := by
  cases geom <;> cases p <;> decide +kernel

/-- A geometry is a chain when the persons' specifications are linearly ordered by inclusion. -/
def PersonGeometry.IsChain (geom : PersonGeometry) : Prop :=
  _root_.IsChain (fun l m : List Segment ↦ l ⊆ m) (Set.range (personSpec geom))

theorem PersonGeometry.standard_isChain : PersonGeometry.standard.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

theorem PersonGeometry.addressee_isChain : PersonGeometry.addressee.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

theorem PersonGeometry.not_branching_isChain : ¬ PersonGeometry.branching.IsChain := by
  simp only [PersonGeometry.IsChain, _root_.IsChain, Set.Pairwise, Set.forall_mem_range]
  decide +kernel

/-! ### Articulated probes and agreement systems -/

/-- An articulated probe is a list of unvalued segments, from the most general to the most
specific. -/
abbrev _root_.Minimalist.Probe.Articulation := List Segment

/-- The flat probe `[uπ]`. -/
def flatProbe : Probe.Articulation := [.pi]

/-- The partial probe `[uπ, uparticipant]`, which distinguishes participants from third person. -/
def partialProbe : Probe.Articulation := [.pi, .participant]

/-- The full probe of a geometry, every segment the geometry uses. -/
def fullProbe (geom : PersonGeometry) : Probe.Articulation :=
  Segment.all.filter (· ∈ geom.nodes)

/-- A language's agreement system is a person geometry together with an articulated probe. -/
structure AgreementSystem where
  /-- The person geometry. -/
  geometry : PersonGeometry
  /-- The articulated probe. -/
  probe : Probe.Articulation
  deriving DecidableEq, Repr

/-- One of the two arguments of a transitive clause. -/
inductive Argument where
  | ia
  | ea
  deriving DecidableEq, Repr

namespace AgreementSystem

variable (sys : AgreementSystem) (ea ia : Person)

/-- The segments a person bears under the system's geometry. -/
abbrev spec (p : Person) : List Segment := personSpec sys.geometry p

/-- The residue of the probe after Agree with the internal argument, the segments it does not
bear. -/
def residue : Probe.Articulation := sys.probe.filter fun s ↦ decide (s ∉ sys.spec ia)

/-- A context is direct when the external argument bears some segment of the residue. -/
def IsDirect : Prop := ∃ s ∈ sys.residue ia, s ∈ sys.spec ea

/-- A context is inverse when it is not direct. -/
def IsInverse : Prop := ¬ sys.IsDirect ea ia

instance : Decidable (sys.IsDirect ea ia) := List.decidableBEx _ _

instance : Decidable (sys.IsInverse ea ia) := instDecidableNot

theorem isDirect_iff :
    sys.IsDirect ea ia ↔ ∃ s ∈ sys.probe, s ∉ sys.spec ia ∧ s ∈ sys.spec ea := by
  simp only [IsDirect, residue, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨s, ⟨h1, h2⟩, h3⟩ ↦ ⟨s, h1, h2, h3⟩, fun ⟨s, h1, h2, h3⟩ ↦ ⟨s, ⟨h1, h2⟩, h3⟩⟩

/-- The argument controlling the agreement slot, the external argument in a direct context. -/
def controller : Argument := if sys.IsDirect ea ia then .ea else .ia

/-- The person the agreement slot realizes. -/
def value : Person := if sys.IsDirect ea ia then ea else ia

/-- The segments checked on each cycle, by the internal argument and then by the external one
out of the residue. -/
def cycles : Probe.Articulation × Probe.Articulation :=
  (sys.probe.filter (· ∈ sys.spec ia), (sys.residue ia).filter (· ∈ sys.spec ea))

/-- A segment of the probe searches its domain, halting at the closest goal, which bears `π` and
so intervenes for every segment, and Agrees with that goal iff it bears the segment. -/
def segProbe (s : Segment) : Probe Person := .ofInt fun p ↦ decide (s ∈ sys.spec p)

/-- The external argument is licensed by the core probe when some segment of the residue Agrees
with it from the next projection of v, whose domain has the external argument closest and the
internal one below. -/
def EALicensed : Prop := ∃ s ∈ sys.residue ia, (sys.segProbe s).agree [ea, ia] = some ea

instance : Decidable (sys.EALicensed ea ia) := List.decidableBEx _ _

/-- The core probe licenses the external argument exactly in direct contexts. -/
theorem eaLicensed_iff_isDirect : sys.EALicensed ea ia ↔ sys.IsDirect ea ia := by
  simp only [EALicensed, IsDirect, segProbe, Probe.ofInt_agree_eq_some_iff, List.head?_cons,
    true_and, decide_eq_true_eq]

/-- Arguments of the same person make an inverse context. -/
theorem isInverse_self (p : Person) : sys.IsInverse p p := fun h ↦
  let ⟨_, _, hn, hm⟩ := (sys.isDirect_iff p p).1 h
  hn hm

/-- A probe with more segments has more direct contexts. -/
theorem IsDirect.mono {sys' : AgreementSystem} (hg : sys'.geometry = sys.geometry)
    (hp : sys.probe ⊆ sys'.probe) (h : sys.IsDirect ea ia) : sys'.IsDirect ea ia := by
  rw [isDirect_iff] at h ⊢
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hp hs, by simpa [spec, hg] using h⟩

/-- A flat probe leaves no residue, since every internal argument bears `π`, so every context is
inverse. -/
theorem flat_isInverse (geom : PersonGeometry) :
    (⟨geom, flatProbe⟩ : AgreementSystem).IsInverse ea ia := by
  rintro ⟨s, hs, -⟩
  simp [residue, flatProbe, spec, pi_mem_personSpec] at hs

theorem spec_subset_or_subset {geom : PersonGeometry} (h : geom.IsChain) (p q : Person) :
    personSpec geom p ⊆ personSpec geom q ∨ personSpec geom q ⊆ personSpec geom p := by
  by_cases hpq : personSpec geom p = personSpec geom q
  · exact Or.inl (hpq ▸ List.Subset.refl _)
  · exact h (Set.mem_range_self p) (Set.mem_range_self q) hpq

/-- Under a chain geometry a context is direct iff the external argument matches more of the
probe than the internal one does. -/
theorem isDirect_iff_length_lt (h : sys.geometry.IsChain) :
    sys.IsDirect ea ia ↔
      (sys.cycles ea ia).1.length < (sys.probe.filter (· ∈ sys.spec ea)).length := by
  simp only [cycles]
  rcases spec_subset_or_subset h ia ea with hsub | hsub
  · have key : sys.probe.filter (· ∈ sys.spec ia) =
        (sys.probe.filter (· ∈ sys.spec ea)).filter (· ∈ sys.spec ia) := by
      rw [List.filter_filter]
      exact List.filter_congr fun s _ ↦ by
        by_cases hi : s ∈ sys.spec ia
        · simp [hi, hsub hi]
        · simp [hi]
    rw [key, List.length_filter_lt_length_iff_exists, isDirect_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨s, hs, hi, he⟩ ↦ ⟨s, ⟨hs, he⟩, hi⟩, fun ⟨s, ⟨hs, he⟩, hi⟩ ↦ ⟨s, hs, hi, he⟩⟩
  · constructor
    · intro h
      obtain ⟨s, _, hn, hm⟩ := (sys.isDirect_iff ea ia).1 h
      exact absurd (hsub hm) hn
    · intro hlt
      have := List.countP_mono_left (l := sys.probe) (p := fun s ↦ decide (s ∈ sys.spec ea))
        (q := fun s ↦ decide (s ∈ sys.spec ia)) fun s _ h ↦ by simpa using hsub (by simpa using h)
      simp only [List.countP_eq_length_filter] at this
      exact absurd this (not_le.2 hlt)

end AgreementSystem

end Minimalist.CyclicAgree
