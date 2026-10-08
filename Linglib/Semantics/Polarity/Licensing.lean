/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Polarity.Item

/-!
# Polarity licensing

A context licenses a polarity item when its licenser carries the strength of negation the item
needs, after Ladusaw, Zwarts and Gajewski; when it is a modal licenser licensing free choice and the
item is a free choice item, after Kadmon and Landman and Chierchia; or when it is a question and the
item a weak negative polarity item, after van Rooy. It anti-licenses an item when its licenser holds
outright the strength that blocks it, after van der Wouden and Szabolcsi. What each context carries
is a theorem about the operators it denotes (`Semantics/Polarity/LicensingContext.lean`), so what it
licenses follows from what it means, and each fragment checks the theory against the contexts its
entries are attested and excluded in.

## Main declarations

* `PolarityItem.LicensingContext.Licenses`, `AntiLicenses`, `Admits`.
* `PolarityItem.LicensingContext.licenses_nobody`, …: what each named context licenses, as a
  condition on the item, and the `Decidable` instances built from these lemmas, so that `decide`
  checks an item against a named context.

## Main results

* `LicensingContext.licenses_iff_carries`: an item needing a strength above weak, and not a free
  choice item, is licensed exactly by the contexts carrying that strength, so an item needing
  anti-morphic strength is licensed by clausal negation and by no other named context.
* `LicensingContext.antiLicenses_negation`: clausal negation blocks every positive polarity item,
  [vanderwouden-1997]'s (169).
* `LicensingContext.antiLicenses_iff_licenses`: a classical context blocks the positive polarity
  items of a class exactly where it licenses the negative polarity items of that class, the mirror
  image of [vanderwouden-1997]'s (181).

## References

* [ladusaw-1979]
* [kadmon-landman-1993]
* [zwarts-1998]
* [vanderwouden-1997]
* [von-fintel-1999]
* [gajewski-2011]
* [szabolcsi-2004]
* [van-rooy-2003-npi]
* [chierchia-2006]
-/

@[expose] public section

namespace PolarityItem.LicensingContext

open NaturalLogic Licenser

variable (c : LicensingContext) (e : PolarityItem)

/-- A context **licenses** an item when its licenser carries the item's licensor, licenses free
choice and the item is a free choice item, or licenses by relevance and the item is a weak negative
polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, c.licenser.Carries r) ∨ (c.licenser.LicensesFreeChoice ∧ e.IsFCI) ∨
    (c.licenser.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds outright the strength that blocks
the item. -/
def AntiLicenses : Prop := ∃ r ∈ e.antiLicensor, c.licenser.Holds r.toSignature

/-- A context **admits** an item when it licenses the item, if the item needs licensing, and does
not anti-license it. -/
def Admits : Prop := (e.IsNPI ∨ e.IsFCI → c.Licenses e) ∧ ¬ c.AntiLicenses e

variable {c e}

theorem admits_iff_licenses (h : e.antiLicensor = none) (he : e.IsNPI ∨ e.IsFCI) :
    c.Admits e ↔ c.Licenses e := by
  simp [Admits, AntiLicenses, h, he]

theorem admits_iff_not_antiLicenses (hn : ¬ e.IsNPI) (hf : ¬ e.IsFCI) :
    c.Admits e ↔ ¬ c.AntiLicenses e := by
  simp [Admits, hn, hf]

/-! ### The profiles of the licensers -/

private theorem licenses_classical {F : OperatorFamily} {s₀ : DEStrength}
    (hc : c.licenser = .classical F) (h : ∀ s, c.licenser.Holds s.toSignature ↔ s ≤ s₀) :
    c.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ s₀ := by
  unfold Licenses
  rw [hc] at h ⊢
  simp only [carries_classical_iff, h, LicensesFreeChoice, LicensesByRelevance, false_and,
    or_false]

private theorem licenses_strawson {F : PresupposingFamily} (hc : c.licenser = .strawson F)
    (hde : c.licenser.IsStrawsonDE) (hn : ¬ c.licenser.Holds .anti) :
    c.Licenses e ↔ e.licensor = some .weak := by
  unfold Licenses
  rw [hc] at hde hn ⊢
  simp only [carries_iff_eq_weak hde hn, LicensesFreeChoice, LicensesByRelevance, false_and,
    or_false]
  simp

private theorem antiLicenses_classical {s₀ : DEStrength}
    (h : ∀ s, c.licenser.Holds s.toSignature ↔ s ≤ s₀) :
    c.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ s₀ := by
  simp only [AntiLicenses, h]

private theorem not_antiLicenses (h : ¬ c.licenser.Holds .anti) : ¬ c.AntiLicenses e :=
  fun ⟨_, _, hr⟩ ↦ not_holds_toSignature h hr

private theorem le_antiMorphic (s : DEStrength) : s ≤ .antiMorphic := by cases s <;> decide

@[simp] theorem licenses_negation : negation.Licenses e ↔ e.IsNPI := by
  rw [licenses_classical (s₀ := .antiMorphic) rfl fun s ↦
    iff_of_true (holds_negation s) (le_antiMorphic s)]
  exact ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩,
    fun h ↦ let ⟨r, hr⟩ := Option.isSome_iff_exists.1 h; ⟨r, hr, le_antiMorphic r⟩⟩

@[simp] theorem antiLicenses_negation_iff : negation.AntiLicenses e ↔ e.IsPPI := by
  rw [antiLicenses_classical (s₀ := .antiMorphic) fun s ↦
    iff_of_true (holds_negation s) (le_antiMorphic s)]
  exact ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩,
    fun h ↦ let ⟨r, hr⟩ := Option.isSome_iff_exists.1 h; ⟨r, hr, le_antiMorphic r⟩⟩

@[simp] theorem licenses_nobody : nobody.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_nobody_iff

@[simp] theorem antiLicenses_nobody :
    nobody.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_nobody_iff

@[simp] theorem licenses_few : few.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_classical rfl fun _ ↦ holds_few_iff

@[simp] theorem antiLicenses_few : few.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_few_iff

@[simp] theorem licenses_atMost : atMost.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_classical rfl fun _ ↦ holds_atMost_iff

@[simp] theorem antiLicenses_atMost : atMost.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_atMost_iff

@[simp] theorem licenses_universalRestrictor :
    universalRestrictor.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_universalRestrictor_iff

@[simp] theorem antiLicenses_universalRestrictor :
    universalRestrictor.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_universalRestrictor_iff

@[simp] theorem licenses_withoutClause :
    withoutClause.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_withoutClause_iff

@[simp] theorem antiLicenses_withoutClause :
    withoutClause.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_withoutClause_iff

@[simp] theorem licenses_beforeClause :
    beforeClause.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_beforeClause_iff

@[simp] theorem antiLicenses_beforeClause :
    beforeClause.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_beforeClause_iff

@[simp] theorem licenses_clausalComparative :
    clausalComparative.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_clausalComparative_iff

@[simp] theorem antiLicenses_clausalComparative :
    clausalComparative.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_clausalComparative_iff

@[simp] theorem licenses_tooTo : tooTo.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_tooTo_iff

@[simp] theorem antiLicenses_tooTo :
    tooTo.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_tooTo_iff

@[simp] theorem licenses_doubtVerb : doubtVerb.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_classical rfl fun _ ↦ holds_doubtVerb_iff

@[simp] theorem antiLicenses_doubtVerb :
    doubtVerb.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_doubtVerb_iff

@[simp] theorem licenses_denyVerb : denyVerb.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl fun _ ↦ holds_denyVerb_iff

@[simp] theorem antiLicenses_denyVerb :
    denyVerb.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_denyVerb_iff

@[simp] theorem licenses_onlyFocus : onlyFocus.Licenses e ↔ e.licensor = some .weak :=
  licenses_strawson rfl isStrawsonDE_onlyFocus not_holds_onlyFocus

@[simp] theorem not_antiLicenses_onlyFocus : ¬ onlyFocus.AntiLicenses e :=
  not_antiLicenses not_holds_onlyFocus

@[simp] theorem licenses_adversative : adversative.Licenses e ↔ e.licensor = some .weak :=
  licenses_strawson rfl isStrawsonDE_adversative not_holds_adversative

@[simp] theorem not_antiLicenses_adversative : ¬ adversative.AntiLicenses e :=
  not_antiLicenses not_holds_adversative

@[simp] theorem licenses_superlative : superlative.Licenses e ↔ e.licensor = some .weak :=
  licenses_strawson rfl isStrawsonDE_superlative not_holds_superlative

@[simp] theorem not_antiLicenses_superlative : ¬ superlative.AntiLicenses e :=
  not_antiLicenses not_holds_superlative

@[simp] theorem licenses_conditionalAntecedent :
    conditionalAntecedent.Licenses e ↔ e.licensor = some .weak :=
  licenses_strawson rfl isStrawsonDE_conditionalAntecedent not_holds_conditionalAntecedent

@[simp] theorem not_antiLicenses_conditionalAntecedent : ¬ conditionalAntecedent.AntiLicenses e :=
  not_antiLicenses not_holds_conditionalAntecedent

@[simp] theorem licenses_sinceTemporal : sinceTemporal.Licenses e ↔ e.licensor = some .weak :=
  licenses_strawson rfl isStrawsonDE_sinceTemporal not_holds_sinceTemporal

@[simp] theorem not_antiLicenses_sinceTemporal : ¬ sinceTemporal.AntiLicenses e :=
  not_antiLicenses not_holds_sinceTemporal

@[simp] theorem licenses_question : question.Licenses e ↔ e.licensor = some .weak := by
  refine ⟨fun h ↦ ?_, fun h ↦ .inr (.inr ⟨Licenser.licensesByRelevance_question, h⟩)⟩
  rcases h with ⟨r, _, hr⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · cases r <;> exact False.elim hr
  · exact False.elim h
  · exact h

@[simp] theorem not_antiLicenses_question : ¬ question.AntiLicenses e :=
  not_antiLicenses id

private theorem licenses_modal {F : ModalFamily} (hc : c.licenser = .modal F)
    (h : c.licenser.LicensesFreeChoice) : c.Licenses e ↔ e.IsFCI := by
  refine ⟨fun hl ↦ ?_, fun hf ↦ .inr (.inl ⟨h, hf⟩)⟩
  rcases hl with ⟨r, _, hr⟩ | ⟨_, hf⟩ | ⟨hq, _⟩
  · rw [hc] at hr
    cases r <;> exact False.elim hr
  · exact hf
  · rw [hc] at hq
    exact False.elim hq

@[simp] theorem licenses_modalPossibility : modalPossibility.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_modalPossibility

@[simp] theorem licenses_modalNecessity : modalNecessity.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_imperative : imperative.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_generic : generic.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_freeRelative : freeRelative.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem not_antiLicenses_modal {F : ModalFamily} (hc : c.licenser = .modal F) :
    ¬ c.AntiLicenses e :=
  not_antiLicenses (by rw [hc]; exact id)

@[simp] theorem not_antiLicenses_modalPossibility : ¬ modalPossibility.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_modalNecessity : ¬ modalNecessity.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_imperative : ¬ imperative.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_generic : ¬ generic.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_freeRelative : ¬ freeRelative.AntiLicenses e :=
  not_antiLicenses_modal rfl

/-! ### Deciding licensing at the named contexts

What a named context licenses and anti-licenses is decided by the item, through the lemmas
above. -/

instance : DecidablePred negation.Licenses := fun _ ↦ decidable_of_iff' _ licenses_negation
instance : DecidablePred nobody.Licenses := fun _ ↦ decidable_of_iff' _ licenses_nobody
instance : DecidablePred few.Licenses := fun _ ↦ decidable_of_iff' _ licenses_few
instance : DecidablePred atMost.Licenses := fun _ ↦ decidable_of_iff' _ licenses_atMost
instance : DecidablePred universalRestrictor.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_universalRestrictor
instance : DecidablePred withoutClause.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_withoutClause
instance : DecidablePred beforeClause.Licenses := fun _ ↦ decidable_of_iff' _ licenses_beforeClause
instance : DecidablePred clausalComparative.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_clausalComparative
instance : DecidablePred tooTo.Licenses := fun _ ↦ decidable_of_iff' _ licenses_tooTo
instance : DecidablePred doubtVerb.Licenses := fun _ ↦ decidable_of_iff' _ licenses_doubtVerb
instance : DecidablePred denyVerb.Licenses := fun _ ↦ decidable_of_iff' _ licenses_denyVerb
instance : DecidablePred onlyFocus.Licenses := fun _ ↦ decidable_of_iff' _ licenses_onlyFocus
instance : DecidablePred adversative.Licenses := fun _ ↦ decidable_of_iff' _ licenses_adversative
instance : DecidablePred superlative.Licenses := fun _ ↦ decidable_of_iff' _ licenses_superlative
instance : DecidablePred conditionalAntecedent.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_conditionalAntecedent
instance : DecidablePred sinceTemporal.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_sinceTemporal
instance : DecidablePred question.Licenses := fun _ ↦ decidable_of_iff' _ licenses_question
instance : DecidablePred modalPossibility.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_modalPossibility
instance : DecidablePred modalNecessity.Licenses :=
  fun _ ↦ decidable_of_iff' _ licenses_modalNecessity
instance : DecidablePred imperative.Licenses := fun _ ↦ decidable_of_iff' _ licenses_imperative
instance : DecidablePred generic.Licenses := fun _ ↦ decidable_of_iff' _ licenses_generic
instance : DecidablePred freeRelative.Licenses := fun _ ↦ decidable_of_iff' _ licenses_freeRelative

instance : DecidablePred negation.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_negation_iff
instance : DecidablePred nobody.AntiLicenses := fun _ ↦ decidable_of_iff' _ antiLicenses_nobody
instance : DecidablePred few.AntiLicenses := fun _ ↦ decidable_of_iff' _ antiLicenses_few
instance : DecidablePred atMost.AntiLicenses := fun _ ↦ decidable_of_iff' _ antiLicenses_atMost
instance : DecidablePred universalRestrictor.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_universalRestrictor
instance : DecidablePred withoutClause.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_withoutClause
instance : DecidablePred beforeClause.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_beforeClause
instance : DecidablePred clausalComparative.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_clausalComparative
instance : DecidablePred tooTo.AntiLicenses := fun _ ↦ decidable_of_iff' _ antiLicenses_tooTo
instance : DecidablePred doubtVerb.AntiLicenses :=
  fun _ ↦ decidable_of_iff' _ antiLicenses_doubtVerb
instance : DecidablePred denyVerb.AntiLicenses := fun _ ↦ decidable_of_iff' _ antiLicenses_denyVerb
instance : DecidablePred onlyFocus.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_onlyFocus
instance : DecidablePred adversative.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_adversative
instance : DecidablePred superlative.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_superlative
instance : DecidablePred conditionalAntecedent.AntiLicenses :=
  fun _ ↦ isFalse not_antiLicenses_conditionalAntecedent
instance : DecidablePred sinceTemporal.AntiLicenses :=
  fun _ ↦ isFalse not_antiLicenses_sinceTemporal
instance : DecidablePred question.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_question
instance : DecidablePred modalPossibility.AntiLicenses :=
  fun _ ↦ isFalse not_antiLicenses_modalPossibility
instance : DecidablePred modalNecessity.AntiLicenses :=
  fun _ ↦ isFalse not_antiLicenses_modalNecessity
instance : DecidablePred imperative.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_imperative
instance : DecidablePred generic.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_generic
instance : DecidablePred freeRelative.AntiLicenses := fun _ ↦ isFalse not_antiLicenses_freeRelative

instance [DecidablePred c.Licenses] [DecidablePred c.AntiLicenses] : DecidablePred c.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### The theory -/

/-- An item needing a strength above weak, and not a free choice item, is licensed exactly by the
contexts whose licenser carries that strength. -/
theorem licenses_iff_carries {r : DEStrength} (he : e.licensor = some r) (hr : r ≠ .weak)
    (hf : ¬ e.IsFCI) : c.Licenses e ↔ c.licenser.Carries r := by
  refine ⟨?_, fun h ↦ .inl ⟨r, he, h⟩⟩
  rintro (⟨s, hs, hc⟩ | ⟨_, hfc⟩ | ⟨_, hw⟩)
  · rw [he, Option.mem_def, Option.some_inj] at hs
    exact hs ▸ hc
  · exact absurd hfc hf
  · rw [he, Option.some_inj] at hw
    exact absurd hw hr

/-- Clausal negation blocks every positive polarity item, since its licenser holds the top of the
chain ([vanderwouden-1997]'s (169)). -/
theorem antiLicenses_negation (h : e.IsPPI) : negation.AntiLicenses e :=
  antiLicenses_negation_iff.mpr h

/-- A classical context blocks the positive polarity items of a class exactly where it licenses
the negative polarity items of that class (the mirror image of [vanderwouden-1997]'s (181)). -/
theorem antiLicenses_iff_licenses {e' : PolarityItem} {F : OperatorFamily}
    (hc : c.licenser = .classical F) (h : e.antiLicensor = e'.licensor) :
    c.AntiLicenses e ↔ c.Licenses e' := by
  unfold AntiLicenses Licenses
  rw [hc, h]
  simp only [carries_classical_iff, LicensesFreeChoice, LicensesByRelevance, false_and, or_false]

/-- A context licensing an item licenses every item with a weaker licensor that is a free choice
item if the first is. -/
theorem Licenses.of_licensor_le {e' : PolarityItem} {r r' : DEStrength} (he : e.licensor = some r)
    (he' : e'.licensor = some r') (hr : r' ≤ r) (hf : e.IsFCI → e'.IsFCI) (hl : c.Licenses e) :
    c.Licenses e' := by
  rcases hl with ⟨s, hs, hc⟩ | ⟨hc, hfc⟩ | ⟨hc, hw⟩
  · rw [he, Option.mem_def, Option.some_inj] at hs
    subst hs
    refine .inl ⟨r', he', ?_⟩
    cases r' with
    | weak =>
      cases r with
      | weak => exact hc
      | antiAdditive | antiMorphic =>
        exact isStrawsonDE_of_holds_anti (Holds.toSignature_of_le (s := .weak) hc (by decide))
    | antiAdditive | antiMorphic =>
      cases r with
      | weak => exact absurd hr (by decide)
      | antiAdditive | antiMorphic => exact Holds.toSignature_of_le hc hr
  · exact .inr (.inl ⟨hc, hf hfc⟩)
  · rw [he, Option.some_inj] at hw
    subst hw
    exact .inr (.inr ⟨hc, by
      rw [he']; congr; cases r' <;> first | rfl | exact absurd hr (by decide)⟩)

end PolarityItem.LicensingContext
