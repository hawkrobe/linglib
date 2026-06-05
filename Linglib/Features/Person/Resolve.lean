import Linglib.Features.Person.Basic

/-!
# Person — resolution
[corbett-2006] [zwicky-1977] [dalrymple-kaplan-2000]

Resolution in coordination: the person of a coordinate structure from
the persons of its conjuncts (*you and I* → first inclusive). The
canonical table returns the finest analytical value
(`first + second = firstInclusive`); systems without the distinction
coarsen via `resolveIn`, exactly as `Number.resolve`'s canonical dual
coarsens to plural in {sg, pl} systems.

The table is not stipulated: `resolve_profile` derives it from referent
union. A person value constrains which discourse roles the referent
includes (`Profile`: speaker yes/no, addressee yes/no/underdetermined —
the tripartition `first` leaves the addressee slot open), and
coordination unions referents — so resolution is pointwise disjunction
on profiles, [dalrymple-kaplan-2000]'s set-union semantics for person
resolution. The Zwicky hierarchy (1 < 2 < 3, [zwicky-1977]) falls out:
in a tripartition system, resolution is minimum of `hierarchyRank`
(`resolveIn_tripartition_min`).

`zero` (impersonal) does not participate in attested resolution; it is
treated as an identity by convention (documented, not an empirical
claim).
-/

set_option autoImplicit false

namespace Person

/-! ### Canonical resolution -/

/-- Canonical person resolution: the finest analytical value for the
    coordination of two referents. Speaker inclusion dominates;
    coordination with the addressee yields the inclusive. `zero` is an
    identity by convention. -/
def resolve : Person → Person → Person
  | .zero, p => p
  | p, .zero => p
  | .firstInclusive, _ => .firstInclusive
  | _, .firstInclusive => .firstInclusive
  | .first, .second => .firstInclusive
  | .second, .first => .firstInclusive
  | .firstExclusive, .second => .firstInclusive
  | .second, .firstExclusive => .firstInclusive
  | .first, _ => .first
  | _, .first => .first
  | .firstExclusive, _ => .firstExclusive
  | _, .firstExclusive => .firstExclusive
  | .second, _ => .second
  | _, .second => .second
  | .third, .third => .third

theorem resolve_comm : ∀ a b, resolve a b = resolve b a := by decide

theorem resolve_assoc :
    ∀ a b c, resolve (resolve a b) c = resolve a (resolve b c) := by
  decide

@[simp] theorem resolve_zero_left (p : Person) : resolve .zero p = p := by
  cases p <;> rfl

@[simp] theorem resolve_zero_right (p : Person) : resolve p .zero = p := by
  cases p <;> rfl

/-! ### The grounding: resolution is referent union

A person value constrains the discourse roles in the referent. The
profile records speaker inclusion (determinate for every value) and
addressee inclusion (`none` = underdetermined: the tripartition `first`
says nothing about the addressee). Coordination unions referents, so
the resolved profile is the pointwise disjunction — with
`none ∨ false = none`: if one conjunct's addressee status is open, so
is the coordination's. -/

/-- Discourse-role inclusion profile of a (non-impersonal) person
    value. -/
structure Profile where
  /-- The referent includes the speaker. -/
  speaker : Bool
  /-- The referent includes the addressee; `none` = underdetermined. -/
  addressee : Option Bool
  deriving DecidableEq, Repr

/-- The profile of each value; `zero` constrains roles in a
    context-dependent way and has none. -/
def toProfile : Person → Option Profile
  | .first => some ⟨true, none⟩
  | .firstInclusive => some ⟨true, some true⟩
  | .firstExclusive => some ⟨true, some false⟩
  | .second => some ⟨false, some true⟩
  | .third => some ⟨false, some false⟩
  | .zero => none

/-- Profiles of unions: pointwise disjunction (three-valued on the
    addressee slot). -/
def Profile.or (p q : Profile) : Profile :=
  ⟨p.speaker || q.speaker,
    match p.addressee, q.addressee with
    | some true, _ => some true
    | _, some true => some true
    | some false, some false => some false
    | _, _ => none⟩

/-- **The resolution table is referent union** ([dalrymple-kaplan-2000]):
    for referential persons, the profile of the resolved value is the
    disjunction of the conjuncts' profiles. The table is derived, not
    stipulated. -/
theorem resolve_profile :
    ∀ p q : Person, p ≠ .zero → q ≠ .zero →
      (resolve p q).toProfile =
        (p.toProfile.bind fun pp => q.toProfile.map pp.or) := by
  decide

/-- Distinct values have distinct profiles: the referential inventory is
    exactly the profile space reachable from referents. -/
theorem toProfile_injOn :
    ∀ p q : Person, p ≠ .zero → q ≠ .zero →
      p.toProfile = q.toProfile → p = q := by
  decide

/-! ### System-relative resolution -/

/-- Coarsen a value into a system: keep it if present, else collapse
    clusivity. -/
def coarsenTo (sys : List Person) (p : Person) : Person :=
  if p ∈ sys then p
  else if p.coarsen ∈ sys then p.coarsen
  else p

/-- Resolution within a system: canonical resolution, coarsened. -/
def resolveIn (sys : List Person) (a b : Person) : Person :=
  coarsenTo sys (resolve a b)

theorem resolveIn_comm (sys : List Person) (a b : Person) :
    resolveIn sys a b = resolveIn sys b a := by
  simp only [resolveIn, resolve_comm]

/-- Resolution typed by a `Person.System`. -/
def System.resolve (ns : System) (a b : Person) : Person :=
  resolveIn ns.values a b

/-- In a clusivity system: *you and I* resolves to the inclusive. -/
theorem resolve_quadripartition_incl :
    System.quadripartition.resolve .firstExclusive .second =
      .firstInclusive := by decide

/-- In a tripartition system the canonical inclusive coarsens to plain
    first: English *you and I* → *we*. -/
theorem resolve_tripartition_first :
    System.tripartition.resolve .first .second = .first := by decide

/-- **The Zwicky hierarchy as a corollary** ([zwicky-1977]): in a
    tripartition system, resolution is minimum of `hierarchyRank` —
    1 < 2 < 3 is not a primitive but the shadow of referent union. -/
theorem resolveIn_tripartition_min :
    ∀ p q : Person, p ∈ System.tripartition.values →
      q ∈ System.tripartition.values →
      (System.tripartition.resolve p q).hierarchyRank =
        min p.hierarchyRank q.hierarchyRank := by
  decide

end Person
