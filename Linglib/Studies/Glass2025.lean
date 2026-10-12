module

public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Data.Examples.Glass2025

/-!
# Glass (2025): Attested versus unattested contrafactive belief verbs

Glass reframes Holton's contrafactive gap. The factive presupposition of *know* requires its
complement to be Common Ground (`EntailsP`), and a contrafactive can negate that requirement in
two places: with narrow scope, requiring that not-p be Common Ground (`EntailsNot`), or with wide
scope, requiring only that the Common Ground be compatible with not-p (`CompatibleNot`). The
stronger requirement is unattested; the weaker is the postsupposition Glass gives Mandarin yǐwéi
in earlier work (`yiweiDefined`). Table 1, the states of the Common Ground each profile admits,
is derived from the requirements (`Profile.condition_iff`), and the profiles of *know* and
*think* come from the veridicality of their fragment entries' attitudes (`rows_admits`).

## Implementation notes

* Context sets are the substrate's `Set W`; Table 1 depicts the Common Ground after the report is
  accepted, so the profiles' conditions take the updated context, the intersection with the
  report's at-issue content, as their argument.
* The attestation facts, no strong contrafactive and yǐwéi a weak one, are the empirical premise
  of the reframed question (`Profile.Attested`), which Roberts and Özyıldız derive causally.
* Verbs' profiles come from the veridicality of their fragment entries' attitudes except
  yǐwéi's, the paper's own analysis, since the fragment records only that it is non-veridical.

## References

* [glass-2025]
* [glass-2023]
* [holton-2017]
* [roberts-ozyildiz-2025]
* [brasoveanu-2009]
* [stalnaker-1978]
-/

@[expose] public section

namespace Glass2025

open Doxastic Presupposition
open English
open English.Verbs hiding Verb

variable {W : Type*} {c : Set W} {p : W → Prop}

/-! ### Two ways to negate the factive presupposition -/

/-- Condition (10) is that `p` is Common Ground, true throughout the context set. -/
def EntailsP (c : Set W) (p : W → Prop) : Prop := ∀ w ∈ c, p w

/-- Condition (11) is that not-`p` is Common Ground. -/
def EntailsNot (c : Set W) (p : W → Prop) : Prop := ∀ w ∈ c, ¬ p w

/-- Condition (12) is that the Common Ground is compatible with not-`p`. -/
def CompatibleNot (c : Set W) (p : W → Prop) : Prop := ∃ w ∈ c, ¬ p w

/-- (11) is the narrow-scope negation: it is not possible that `p`. -/
theorem entailsNot_iff : EntailsNot c p ↔ ¬ ∃ w ∈ c, p w := by
  simp [EntailsNot]

/-- (12) is the wide-scope negation: `p` is not Common Ground. -/
theorem compatibleNot_iff : CompatibleNot c p ↔ ¬ EntailsP c p := by
  simp [CompatibleNot, EntailsP]

/-- The stronger requirement entails the weaker on a nonempty Common Ground. -/
theorem compatibleNot_of_entailsNot (hc : c.Nonempty) (h : EntailsNot c p) : CompatibleNot c p :=
  let ⟨w, hw⟩ := hc
  ⟨w, hw, h w hw⟩

/-- The weaker requirement does not entail the stronger. -/
theorem not_entailsNot_of_compatibleNot :
    ∃ (c : Set Bool) (p : Bool → Prop), CompatibleNot c p ∧ ¬ EntailsNot c p :=
  ⟨Set.univ, (· = true), ⟨false, Set.mem_univ _, Bool.false_ne_true⟩,
    fun h ↦ h true (Set.mem_univ _) rfl⟩

/-- *know* and *contra* are complementary on a nonempty Common Ground. -/
theorem not_entailsP_and_entailsNot (hc : c.Nonempty) : ¬ (EntailsP c p ∧ EntailsNot c p) :=
  fun ⟨h, h'⟩ ↦ let ⟨w, hw⟩ := hc; h' w hw (h w hw)

/-- A Common Ground on which `p` is unsettled satisfies neither the *know* nor the *contra*
requirement, the gap between them. -/
theorem know_contra_gap :
    ∃ (c : Set Bool) (p : Bool → Prop), ¬ EntailsP c p ∧ ¬ EntailsNot c p :=
  ⟨Set.univ, (· = true), fun h ↦ Bool.false_ne_true (h false (Set.mem_univ _)),
    fun h ↦ h true (Set.mem_univ _) rfl⟩

/-- *know* and yǐwéi are complementary. -/
theorem not_entailsP_and_compatibleNot : ¬ (EntailsP c p ∧ CompatibleNot c p) :=
  fun ⟨h, h'⟩ ↦ compatibleNot_iff.1 h' h

/-- *know* and yǐwéi exhaust the space, since `p` is Common Ground or it is not. -/
theorem know_yiwei_exhaustive : EntailsP c p ∨ CompatibleNot c p :=
  (em _).imp_right compatibleNot_iff.2

/-! ### The factive presupposition in the substrate -/

variable {E : Type*}

/-- A veridical predicate's presupposition is satisfied exactly when its complement is Common
Ground: the factive presupposition (10). -/
theorem admits_toPartialProp_veridical (V : DoxasticPredicate W E)
    (hV : V.veridicality = .veridical) (a : E) :
    (V.toPartialProp a p).Admits c ↔ EntailsP c p := by
  simp only [PartialProp.Admits, DoxasticPredicate.toPartialProp, hV]
  exact Iff.rfl

/-- A non-veridical predicate places no condition on the Common Ground. -/
theorem admits_toPartialProp_nonVeridical (V : DoxasticPredicate W E)
    (hV : V.veridicality = .nonVeridical) (a : E) :
    (V.toPartialProp a p).Admits c := by
  simp only [PartialProp.Admits, DoxasticPredicate.toPartialProp, hV]
  exact fun _ _ ↦ trivial

/-! ### yǐwéi's postsupposition -/

/-- By (14), *x yǐwéi p* updates the Common Ground with `x`'s belief that `p`, and is defined only
if the result is compatible with not-`p`, a postsupposition in the sense of [brasoveanu-2009]. -/
def yiweiDefined (c belief : Set W) (p : W → Prop) : Prop := CompatibleNot (c ∩ belief) p

/-- A speaker with an opinion about `p`, whose Common Ground entails it or its negation, and who
signals that the Common Ground is compatible with not-`p`, holds that not-`p`: why *x yǐwéi p*
usually conveys that `p` is false. -/
theorem entailsNot_of_opinionated (h : EntailsP c p ∨ EntailsNot c p) (hy : CompatibleNot c p) :
    EntailsNot c p :=
  h.resolve_left (compatibleNot_iff.1 hy)

/-! ### Table 1 -/

/-- The projective profiles of belief verbs require `p` (*know*), nothing (*think*),
compatibility with not-`p` (yǐwéi), or not-`p` (the hypothetical *contra*). -/
inductive Profile
  | factive
  | nonfactive
  | weakContrafactive
  | strongContrafactive
  deriving DecidableEq, Repr

/-- The requirement a profile places on the Common Ground after the report is accepted. -/
def Profile.condition : Profile → Set W → (W → Prop) → Prop
  | .factive, c, p => EntailsP c p
  | .nonfactive, _, _ => True
  | .weakContrafactive, c, p => CompatibleNot c p
  | .strongContrafactive, c, p => EntailsNot c p

/-- The states of the Common Ground regarding `p` distinguished in Table 1. -/
inductive State
  | p
  | unsettled
  | notP
  deriving DecidableEq, Repr

open Classical in
/-- The state of a Common Ground regarding `p`. -/
noncomputable def state (c : Set W) (p : W → Prop) : State :=
  if EntailsP c p then .p else if EntailsNot c p then .notP else .unsettled

/-- The states each profile admits, the rows of Table 1. -/
def Profile.Admits : Profile → State → Prop
  | .factive, s => s = .p
  | .nonfactive, _ => True
  | .weakContrafactive, s => s ≠ .p
  | .strongContrafactive, s => s = .notP

instance (pr : Profile) (s : State) : Decidable (pr.Admits s) := by
  cases pr <;> simp only [Profile.Admits] <;> infer_instance

/-- Table 1 as a theorem. On a nonempty Common Ground, a profile's requirement holds exactly when
the profile admits the Common Ground's state. -/
theorem Profile.condition_iff (hc : c.Nonempty) (pr : Profile) :
    pr.condition c p ↔ pr.Admits (state c p) := by
  have := not_entailsP_and_entailsNot (p := p) hc
  cases pr <;> by_cases h₁ : EntailsP c p <;> by_cases h₂ : EntailsNot c p <;>
    simp_all [Profile.condition, Profile.Admits, state, compatibleNot_iff]

/-- Every profile but the strong contrafactive is attested, by *know*, *think* and yǐwéi; this is
the empirical premise of the reframed question. -/
def Profile.Attested : Profile → Prop
  | .strongContrafactive => False
  | _ => True

instance : DecidablePred Profile.Attested
  | .strongContrafactive => isFalse id
  | .factive | .nonfactive | .weakContrafactive => isTrue trivial

/-! ### The verbs -/

/-- The profile an attitude determines through its veridicality; postsuppositions are invisible
to it. -/
def Profile.ofAttitude (a : Attitude) : Profile :=
  match a.veridicality with
  | .veridical => .factive
  | .nonVeridical => .nonfactive

/-- yǐwéi's profile on the paper's analysis, beyond the non-veridicality its fragment entry
records. -/
def yiweiProfile : Profile := .weakContrafactive

theorem know_profile : know.attitude.map Profile.ofAttitude = some .factive := by
  decide

theorem think_profile : think.attitude.map Profile.ofAttitude = some .nonfactive := by
  decide

/-- The fragment's veridicality alone makes yǐwéi nonfactive. -/
theorem yiwei_profile_ofAttitude :
    Mandarin.yiwei.attitude.map Profile.ofAttitude = some .nonfactive := by
  decide

/-- A belief report of the paper records the verb's profile, the state of the Common Ground in
the context described, and the reported judgment. -/
structure Row where
  profile : Profile
  state : State
  judgment : Judgment
  deriving DecidableEq

/-- The rows' verbs *know*, *think* and rènwéi take their profiles from their fragment entries'
attitudes, and yǐwéi from the paper's analysis. -/
def verbProfiles : List (String × Profile) :=
  [("know", (know.attitude.map Profile.ofAttitude).getD .nonfactive),
   ("think", (think.attitude.map Profile.ofAttitude).getD .nonfactive),
   ("renwei", (Mandarin.renwei.attitude.map Profile.ofAttitude).getD .nonfactive),
   ("yiwei", yiweiProfile)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let profile ← ex.parse? "verb" verbProfiles
  let state ← ex.parse? "state" [("p", .p), ("unsettled", .unsettled), ("notP", .notP)]
  pure ⟨profile, state, ex.judgment⟩

/-- The nine reports of (1), (2), (4), (5) and (7). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The reports are judged acceptable exactly in the states their profiles admit. -/
theorem rows_admits : ∀ r ∈ rows, r.judgment = .acceptable ↔ r.profile.Admits r.state := by
  decide

end Glass2025
