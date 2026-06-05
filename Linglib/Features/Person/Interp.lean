import Linglib.Features.Person.Resolve

/-!
# Person — referent semantics for the values
[harbour-2016] [dalrymple-kaplan-2000] [cysouw-2009]

The denotation of a person value as a region of referents: over an
ontology with speaker `i` and addressee `u`, each value constrains which
of the two distinguished roles the referent (a `Finset` of individuals)
includes. `zero` (impersonal) is context-dependent and gets `none` — the
approximatives precedent of `Number.interp`.

The region semantics grounds the rest of the API:

* `interp_resolve` — coordination unions referents, and the regions are
  closed under it: a `p`-referent united with a `q`-referent lies in the
  `resolve p q` region. `Person.resolve_profile`'s profile disjunction is
  the (i, u)-shadow of this fact (`toProfile_sound`).
* `IsSAP` is the region property "forces a speech-act participant"
  (`isSAP_iff_forces`).
* [harbour-2016]'s partition calculus generates exactly these regions —
  the certification theorem lives with the calculus in
  `Studies/Harbour2016.lean` (`quad_cells_are_interp_regions`); the
  marker-set rendering is [dalrymple-kaplan-2000]'s Fula encoding
  (`Studies/DalrympleKaplan2000.lean`, `person_resolve_is_union`).
-/

set_option autoImplicit false

namespace Person

variable {D : Type*} [DecidableEq D]

/-- The region of referents a person value picks out, over an ontology
    with speaker `i` and addressee `u`: `first` includes the speaker
    (addressee open — the tripartition cell), the quadripartition cells
    fix both roles, `zero` is context-dependent (`none`). -/
def interp (i u : D) : Person → Option (Finset D → Prop)
  | .first => some fun s => i ∈ s
  | .firstInclusive => some fun s => i ∈ s ∧ u ∈ s
  | .firstExclusive => some fun s => i ∈ s ∧ u ∉ s
  | .second => some fun s => u ∈ s ∧ i ∉ s
  | .third => some fun s => i ∉ s ∧ u ∉ s
  | .zero => none

/-- The region, with the empty region for `zero`. -/
def region (i u : D) (p : Person) : Finset D → Prop :=
  (interp i u p).getD fun _ => False

instance (i u : D) (p : Person) (s : Finset D) :
    Decidable (region i u p s) :=
  match p with
  | .first => inferInstanceAs (Decidable (i ∈ s))
  | .firstInclusive => inferInstanceAs (Decidable (i ∈ s ∧ u ∈ s))
  | .firstExclusive => inferInstanceAs (Decidable (i ∈ s ∧ u ∉ s))
  | .second => inferInstanceAs (Decidable (u ∈ s ∧ i ∉ s))
  | .third => inferInstanceAs (Decidable (i ∉ s ∧ u ∉ s))
  | .zero => isFalse fun h => h

/-- `interp` is defined exactly off the impersonal. -/
theorem interp_isSome_iff (i u : D) (p : Person) :
    (interp i u p).isSome ↔ p ≠ .zero := by
  cases p <;> simp [interp]

/-- **Resolution is referent union**: the regions are closed under
    coordination — a `p`-referent united with a `q`-referent is a
    `resolve p q`-referent. The resolution table of
    `Features/Person/Resolve.lean` is the shadow of this closure. -/
theorem interp_resolve (i u : D) :
    ∀ p q : Person, p ≠ .zero → q ≠ .zero →
    ∀ s t : Finset D,
      region i u p s → region i u q t →
      region i u (resolve p q) (s ∪ t) := by
  intro p q hp hq s t hs ht
  cases p <;> cases q <;>
    simp_all [region, interp, resolve, Finset.mem_union] <;> tauto

/-- The profile of `Features/Person/Resolve.lean` is the (i, u)-shadow of
    the region: `speaker` records whether the region forces `i ∈ s`, and
    a determinate `addressee` slot records the forced `u`-status. -/
theorem toProfile_speaker (i u : D) :
    ∀ (p : Person) (pr : Profile), p.toProfile = some pr →
    ∀ s : Finset D, region i u p s → (pr.speaker = true ↔ i ∈ s) := by
  intro p pr hpr s hs
  cases p <;> simp only [toProfile, Option.some.injEq, reduceCtorEq] at hpr <;>
    subst hpr <;> simp_all [region, interp]

/-- A determinate addressee slot records the forced `u`-status of the
    region. -/
theorem toProfile_addressee (i u : D) :
    ∀ (p : Person) (pr : Profile) (b : Bool), p.toProfile = some pr →
    pr.addressee = some b →
    ∀ s : Finset D, region i u p s → (u ∈ s ↔ b = true) := by
  intro p pr b hpr hb s hs
  cases p <;> simp only [toProfile, Option.some.injEq, reduceCtorEq] at hpr <;>
    subst hpr <;> simp_all [region, interp]

/-- `IsSAP` is the semantic property "the region forces a speech-act
    participant in the referent": first/second persons do, third does not
    (the empty referent witnesses). -/
theorem isSAP_iff_forces (i u : D) :
    ∀ p : Person, p ≠ .zero →
      (IsSAP p ↔ ∀ s : Finset D, region i u p s → i ∈ s ∨ u ∈ s) := by
  intro p hp
  cases p
  case zero => exact absurd rfl hp
  case first =>
    simp only [IsSAP, region, interp, Option.getD_some, true_iff]
    exact fun _ h => Or.inl h
  case firstInclusive =>
    simp only [IsSAP, region, interp, Option.getD_some, true_iff]
    exact fun _ h => Or.inl h.1
  case firstExclusive =>
    simp only [IsSAP, region, interp, Option.getD_some, true_iff]
    exact fun _ h => Or.inl h.1
  case second =>
    simp only [IsSAP, region, interp, Option.getD_some, true_iff]
    exact fun _ h => Or.inr h.1
  case third =>
    simp only [IsSAP, region, interp, Option.getD_some, false_iff,
      not_forall]
    exact ⟨∅, by simp⟩

omit [DecidableEq D] in
/-- Coarsening widens the region: dropping clusivity loses information,
    never referents. -/
theorem region_coarsen (i u : D) (p : Person) (s : Finset D) :
    region i u p s → region i u p.coarsen s := by
  cases p <;> simp only [region, interp, coarsen, Option.getD_some] <;>
    tauto

end Person
