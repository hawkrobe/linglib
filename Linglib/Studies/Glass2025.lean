import Linglib.Semantics.Attitudes.Doxastic
import Linglib.Semantics.Presupposition.Context
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Data.Examples.Glass2025

/-!
# Glass (2025): Attested versus unattested contrafactive belief verbs

This file formalizes [glass-2025]'s reframing of [holton-2017]'s contrafactive gap. The factive
presupposition of *know* requires its complement to be Common Ground, true throughout the context
set (`EntailsP`); a contrafactive can negate it in two places, requiring that not-p be Common
Ground (`EntailsNot`) or that the Common Ground be compatible with not-p (`CompatibleNot`), the
narrow and the wide scope of the negation as in neg-raising (`entailsNot_iff`,
`compatibleNot_iff`). The stronger requirement is unattested; the weaker is the postsupposition
of Mandarin yǐwéi in [glass-2023], a definedness condition on the context updated with the belief
report (`yiweiDefined`), from which the report's usual suggestion that the complement is false
follows for a speaker with an opinion about it (`entailsNot_of_opinionated`). Table 1 is derived:
each profile admits a set of states of the Common Ground (`Profile.Admits`,
`Profile.condition_iff`); *know* and the hypothetical *contra* are complementary but leave the
unsettled state to neither (`not_entailsP_and_entailsNot`, `know_contra_gap`), *know* and yǐwéi
complementary and exhaustive (`not_entailsP_and_compatibleNot`, `know_yiwei_exhaustive`). The
fragments' veridicality gives *know* and *think* their profiles, and the factive presupposition of
the substrate's veridical predicates is the requirement that the complement be Common Ground
(`presupSatisfied_toPartialProp_veridical`); the rows check the reported judgments against the
admitted states (`rows_admits`).

## Implementation notes

* Context sets are the substrate's `Set W`; Table 1 depicts the Common Ground after the report is
  accepted, so the profiles' conditions take the updated context, the intersection with the
  report's at-issue content, as their argument.
* The attestation facts, no strong contrafactive and yǐwéi a weak one, are the empirical premise
  of the reframed question (`Profile.Attested`), which [roberts-ozyildiz-2025] derives causally.
* Verbs' profiles come from their fragment entries' veridicality except yǐwéi's, the paper's own
  analysis, since the fragment records only that it is non-veridical.

## References

* [glass-2025]
* [glass-2023]
* [holton-2017]
* [roberts-ozyildiz-2025]
* [brasoveanu-2009]
* [stalnaker-1978]
-/

namespace Glass2025

open Doxastic Presupposition Data.Examples Features
open English.Predicates.Verbal Mandarin.Predicates

variable {W : Type*} {c : Set W} {p : W → Prop}

/-! ### Two ways to negate the factive presupposition -/

/-- (10): `p` is Common Ground, true throughout the context set. -/
def EntailsP (c : Set W) (p : W → Prop) : Prop := ∀ w ∈ c, p w

/-- (11): not-`p` is Common Ground. -/
def EntailsNot (c : Set W) (p : W → Prop) : Prop := ∀ w ∈ c, ¬ p w

/-- (12): the Common Ground is compatible with not-`p`. -/
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
    λ h => h true (Set.mem_univ _) rfl⟩

/-- *know* and *contra* are complementary on a nonempty Common Ground. -/
theorem not_entailsP_and_entailsNot (hc : c.Nonempty) : ¬ (EntailsP c p ∧ EntailsNot c p) :=
  λ ⟨h, h'⟩ => let ⟨w, hw⟩ := hc; h' w hw (h w hw)

/-- The gap between *know* and *contra*: a Common Ground on which `p` is unsettled satisfies
neither requirement. -/
theorem know_contra_gap :
    ∃ (c : Set Bool) (p : Bool → Prop), ¬ EntailsP c p ∧ ¬ EntailsNot c p :=
  ⟨Set.univ, (· = true), λ h => Bool.false_ne_true (h false (Set.mem_univ _)),
    λ h => h true (Set.mem_univ _) rfl⟩

/-- *know* and yǐwéi are complementary. -/
theorem not_entailsP_and_compatibleNot : ¬ (EntailsP c p ∧ CompatibleNot c p) :=
  λ ⟨h, h'⟩ => compatibleNot_iff.1 h' h

/-- *know* and yǐwéi exhaust the space: `p` is Common Ground or it is not. -/
theorem know_yiwei_exhaustive : EntailsP c p ∨ CompatibleNot c p := by
  by_cases h : EntailsP c p
  · exact Or.inl h
  · exact Or.inr (compatibleNot_iff.2 h)

/-! ### The factive presupposition in the substrate -/

variable {E : Type*}

/-- A veridical predicate's presupposition is satisfied exactly when its complement is Common
Ground: the factive presupposition (10). -/
theorem presupSatisfied_toPartialProp_veridical (V : DoxasticPredicate W E)
    (hV : V.veridicality = .veridical) (a : E) (worlds : List W) :
    Context.presupSatisfied c (V.toPartialProp a p worlds) ↔ EntailsP c p := by
  simp only [Context.presupSatisfied, DoxasticPredicate.toPartialProp, hV, VeridicalityHolds,
    Set.subset_def]
  exact Iff.rfl

/-- A non-veridical predicate places no condition on the Common Ground. -/
theorem presupSatisfied_toPartialProp_nonVeridical (V : DoxasticPredicate W E)
    (hV : V.veridicality = .nonVeridical) (a : E) (worlds : List W) :
    Context.presupSatisfied c (V.toPartialProp a p worlds) := by
  simp only [Context.presupSatisfied, DoxasticPredicate.toPartialProp, hV, VeridicalityHolds,
    Set.subset_def]
  exact λ _ _ => trivial

/-! ### yǐwéi's postsupposition -/

/-- (14): *x yǐwéi p* updates the Common Ground with `x`'s belief that `p`, and is defined only if
the result is compatible with not-`p`, a postsupposition in the sense of [brasoveanu-2009]. -/
def yiweiDefined (c belief : Set W) (p : W → Prop) : Prop := CompatibleNot (c ∩ belief) p

/-- A speaker with an opinion about `p`, whose Common Ground entails it or its negation, and who
signals that the Common Ground is compatible with not-`p`, holds that not-`p`: why *x yǐwéi p*
usually conveys that `p` is false. -/
theorem entailsNot_of_opinionated (h : EntailsP c p ∨ EntailsNot c p) (hy : CompatibleNot c p) :
    EntailsNot c p :=
  h.resolve_left (compatibleNot_iff.1 hy)

/-! ### Table 1 -/

/-- The projective profiles of belief verbs: requiring `p` (*know*), nothing (*think*),
compatibility with not-`p` (yǐwéi), and not-`p` (the hypothetical *contra*). -/
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

/-- The states each profile admits: the rows of Table 1. -/
def Profile.Admits : Profile → State → Prop
  | .factive, s => s = .p
  | .nonfactive, _ => True
  | .weakContrafactive, s => s ≠ .p
  | .strongContrafactive, s => s = .notP

instance (pr : Profile) (s : State) : Decidable (pr.Admits s) := by
  cases pr <;> simp only [Profile.Admits] <;> infer_instance

/-- Table 1 as a theorem: on a nonempty Common Ground, a profile's requirement holds exactly when
the profile admits the Common Ground's state. -/
theorem Profile.condition_iff (hc : c.Nonempty) (pr : Profile) :
    pr.condition c p ↔ pr.Admits (state c p) := by
  by_cases h₁ : EntailsP c p
  · have h₂ : ¬ EntailsNot c p := λ h₂ => not_entailsP_and_entailsNot hc ⟨h₁, h₂⟩
    cases pr <;> simp [Profile.condition, Profile.Admits, state, h₁, h₂, compatibleNot_iff]
  · by_cases h₂ : EntailsNot c p
    · cases pr <;> simp [Profile.condition, Profile.Admits, state, h₁, h₂, compatibleNot_iff]
    · cases pr <;> simp [Profile.condition, Profile.Admits, state, h₁, h₂, compatibleNot_iff]

/-- Attestation: every profile but the strong contrafactive is attested, by *know*, *think* and
yǐwéi; this is the empirical premise of the reframed question. -/
def Profile.Attested : Profile → Prop
  | .strongContrafactive => False
  | _ => True

instance : DecidablePred Profile.Attested := λ pr => by
  cases pr <;> simp only [Profile.Attested] <;> infer_instance

/-! ### The verbs -/

/-- The profile a verb's veridicality determines; postsuppositions are invisible to it. -/
def Profile.ofVeridicality : Veridicality → Profile
  | .veridical => .factive
  | .nonVeridical => .nonfactive

/-- yǐwéi's profile on the paper's analysis, beyond the non-veridicality its fragment entry
records. -/
def yiweiProfile : Profile := .weakContrafactive

theorem know_profile : know.toVerb.veridicality.map Profile.ofVeridicality = some .factive := by
  decide

theorem think_profile :
    think.toVerb.veridicality.map Profile.ofVeridicality = some .nonfactive := by
  decide

/-- The fragment's veridicality alone makes yǐwéi nonfactive. -/
theorem yiwei_profile_ofVeridicality :
    yiwei.toVerb.veridicality.map Profile.ofVeridicality = some .nonfactive := by
  decide

/-- A belief report of the paper: the verb's profile, the state of the Common Ground in the
context described, and the reported judgment. -/
structure Row where
  profile : Profile
  state : State
  judgment : Judgment
  deriving DecidableEq

/-- The profiles of the rows' verbs: *know*, *think* and rènwéi from their fragment entries'
veridicality, yǐwéi from the paper's analysis. -/
def verbProfiles : List (String × Profile) :=
  [("know", (know.toVerb.veridicality.map Profile.ofVeridicality).getD .nonfactive),
   ("think", (think.toVerb.veridicality.map Profile.ofVeridicality).getD .nonfactive),
   ("renwei", (renwei.toVerb.veridicality.map Profile.ofVeridicality).getD .nonfactive),
   ("yiwei", yiweiProfile)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let profile ← ex.parse? "verb" verbProfiles
  let state ← ex.parse? "state" [("p", .p), ("unsettled", .unsettled), ("notP", .notP)]
  pure ⟨profile, state, ex.judgment⟩

/-- The nine reports of (1), (2), (4), (5) and (7). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The reports are judged acceptable exactly in the states their profiles admit. -/
theorem rows_admits : ∀ r ∈ rows, r.judgment = .acceptable ↔ r.profile.Admits r.state := by
  decide

end Glass2025
