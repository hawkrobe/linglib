module

public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Semantics.Causation.VerbClass
public import Linglib.Semantics.ArgumentStructure.LevinClass
public import Linglib.Semantics.ArgumentStructure.MeaningComponents
public import Linglib.Semantics.Causation.CausalModel.Dependence
public import Linglib.Semantics.Polarity.Basic

/-!
# Implicative Verbs ([nadathur-2023-implicatives])

Causal-prerequisite semantics for implicative verbs. Implicatives
(*manage*, *fail*, *dare*, *bother*, *jaksaa*, *hesitate*, ...) all
share a prerequisite-account schema (Proposal 32):

- (32i)   Presuppose: ∃ prerequisite A(x) causally necessary for P(x)
- (32ii)  Assert: x did A
- (32iii) Presuppose (two-way only): A(x) causally sufficient for P(x)

## Lexical variation

The chief dimension of variation is the type of prerequisite:

- *dare/uskaltaa* → courage
- *bother/viitsiä* → engagement/effort
- *malttaa* → patience
- *hennoa* → hard-heartedness
- *jaksaa* → strength
- *manage/onnistua* → underspecified

## Causal semantics

The presuppositions and the assertion are stated over a causal model (`CausalModel`), relative to
a background observation: sufficiency is Definition 10a with the preamble of Definition 10
(`manageSem`), and necessity is Definition 10b (`CausalModel.CausallyNecessary`).
-/

@[expose] public section

namespace Implicative

open CausalModel

/-! ### Prerequisite Types ([nadathur-2023-implicatives]) -/

/-- Lexically-specified prerequisite types for implicative verbs.

    Specific verbs (*dare*, *bother*) name their prerequisites; bleached
    verbs (*manage*, *onnistua*) leave the prerequisite underspecified. -/
inductive Prerequisite where
  | courage          -- dare, uskaltaa
  | engagement       -- bother, viitsiä
  | patience         -- malttaa
  | hardHeartedness  -- hennoa
  | strength         -- jaksaa
  | fitness          -- mahtua
  | time             -- ehtiä
  | shamelessness    -- kehdata
  | unspecified      -- manage, onnistua
  deriving DecidableEq, Repr

/-- Is the prerequisite lexically specific or underspecified? -/
def Prerequisite.isSpecific : Prerequisite → Bool
  | .unspecified => false
  | _ => true

/-! ### Causal semantics -/

section Semantics

variable {U V : Type*} {α : V → Type*} [DecidableEq V] (M : CausalModel U V α) [M.IsAcyclic]

/-- *manage*-semantics ([nadathur-2023-implicatives] Definition 10a with the preamble of
Definition 10): the prerequisite `p = xP` is causally sufficient for the complement `c = xC`
relative to the background `s`. The background settles neither fact, and the background with the
prerequisite added settles the complement. -/
def manageSem (s : ∀ v, Flat (α v)) (p : V) (xP : α p) (c : V) (xC : α c) : Prop :=
  (¬ M.CausallyEntails s p xP ∧ ¬ M.CausallyEntails s c xC) ∧
    M.CausallyEntails (Function.update s p ↑xP) c xC

/-- *fail*-semantics: the prerequisite is not causally sufficient for the complement.

TODO: this is the denial of the sufficiency presupposition, which is what the Dreyfus
infelicity judgments test, but it is not Proposal 32's semantics for negative implicative
assertions (assert ¬A(x) with both presuppositions intact); the `.negative` case of
`Implicative.toSemantics` inherits the same caveat. -/
abbrev failSem (s : ∀ v, Flat (α v)) (p : V) (xP : α p) (c : V) (xC : α c) : Prop :=
  ¬ manageSem M s p xP c xC

/-- The necessity presupposition says that the prerequisite is causally necessary
([nadathur-2023-implicatives] Definition 10b) for the complement. -/
abbrev necessityPresup (s : ∀ v, Flat (α v)) (p : V) (xP : α p) (c : V) (xC : α c) : Prop :=
  M.CausallyNecessary s p xP c xC

instance [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
    [DecidableRel M.graph.Adj] (s : ∀ v, Flat (α v)) (p : V) (xP : α p) (c : V) (xC : α c) :
    Decidable (manageSem M s p xP c xC) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Semantics

/-! ### Characteristic entailments (Facts B–C) -/

/-! [nadathur-2023-implicatives] (pp. 316–317) takes Facts A–C as the
class-level data any account of implicatives must derive. On the
prerequisite account they fall out of the presupposition + assertion
split of Proposal 32, for an arbitrary causal model whose prerequisite is an exogenous variable
the background leaves open:
- **Fact B, positive half** (`complement_of_positive_assertion`):
  asserting the prerequisite realizes the complement — the sufficiency
  presupposition's entailment clause.
- **Fact B, negative half** (`no_complement_of_negative_assertion`):
  given the necessity presupposition, the negative assertion leaves no
  exogenous settlement realizing the complement.
- **Fact C** (`complement_iff_prerequisite`): in a felicitous two-way
  context the prerequisite is sufficient *and* necessary — an exogenous settlement of the
  background realizes the complement exactly when it realizes the prerequisite.
Fact A (the existence of a potential obstacle, blocking the entailment
from complement to implicative claim) is carried by the presuppositional
preamble itself. -/

section CharacteristicEntailments

variable {U V : Type*} {α : V → Type*} [DecidableEq V] {M : CausalModel U V α} [M.IsAcyclic]
  {s : ∀ v, Flat (α v)} {p : V} {xP : α p} {c : V} {xC : α c}

/-- **Fact B, positive half**: a positive two-way implicative claim
    entails its complement — the background updated with the asserted
    prerequisite causally entails the complement. -/
theorem complement_of_positive_assertion (h : manageSem M s p xP c xC) :
    M.CausallyEntails (Function.update s p ↑xP) c xC := h.2

/-- **Fact B, negative half**: given the necessity presupposition, a
    negative implicative claim (asserting the prerequisite took a value
    other than `xP`) leaves no exogenous settlement realizing the
    complement: by no-alternative, every path to the
    complement runs through the prerequisite value the assertion denies. -/
theorem no_complement_of_negative_assertion {xP' : α p} (hroot : ∀ w, ¬ M.graph.Adj w p)
    (hopen : ∀ x, ¬ M.CausallyEntails s p x) (hne : xP' ≠ xP)
    (hnec : necessityPresup M s p xP c xC) :
    ∀ s', M.IsExogenousSettlement (Function.update s p ↑xP') s' → s' c = ⊥ →
      ¬ M.CausallyEntails s' c xC := by
  intro s' hset hc hent
  have hEntP : M.CausallyEntails s' p xP :=
    hnec.2.2 s' ((isExogenousSettlement_update hroot hopen xP').trans hset) hc hent
  have hp' : s' p = ↑xP' := Flat.coe_le_iff.1 (Function.update_self (β := fun v ↦ Flat (α v))
    p (↑xP') s ▸ hset.1 p)
  rcases causallyEntails_iff.1 hEntP with h | ⟨h, -⟩
  · exact hne (Flat.coe_injective (hp'.symm.trans h))
  · rw [hp'] at h; exact Flat.coe_ne_bot h

/-- **Fact C**: in a felicitous two-way context (both presuppositions in
    force), an exogenous settlement of the background realizes the
    complement exactly when it realizes the prerequisite. The forward
    direction is no-alternative; the converse composes the sufficiency
    clause with the monotonicity of settlement. -/
theorem complement_iff_prerequisite (hroot : ∀ w, ¬ M.graph.Adj w p)
    (hopen : ∀ x, ¬ M.CausallyEntails s p x) (hsuf : manageSem M s p xP c xC)
    (hnec : necessityPresup M s p xP c xC) :
    ∀ s', M.IsExogenousSettlement s s' → s' c = ⊥ →
      (M.CausallyEntails s' c xC ↔ M.CausallyEntails s' p xP) := by
  intro s' hset hc
  refine ⟨hnec.2.2 s' hset hc, fun hEntP ↦ ?_⟩
  have hsp : s p = ⊥ := by
    by_contra h
    obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 h
    exact hopen y (causallyEntails_iff.2 (.inl hy))
  -- the prerequisite is open in the background, so its entailment is an observation
  have hp' : s' p = ↑xP := by
    by_contra h
    have hs'p : s' p = ⊥ := by
      by_contra h'
      obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 h'
      rcases causallyEntails_iff.1 hEntP with h'' | ⟨h'', -⟩
      · exact h h''
      · rw [hy] at h''; exact Flat.coe_ne_bot h''
    exact hopen xP ((causallyEntails_root_iff hroot hsp).2
      ((causallyEntails_root_iff hroot hs'p).1 hEntP))
  -- the settlement also settles the background with the prerequisite added
  have hset' : M.IsExogenousSettlement (Function.update s p ↑xP) s' := by
    refine ⟨fun v ↦ ?_, fun v hv hne ↦ ?_⟩
    · by_cases hvp : v = p
      · subst hvp; rw [Function.update_self, hp']
      · rw [Function.update_of_ne hvp]; exact hset.1 v
    · have hvp : v ≠ p := by rintro rfl; rw [Function.update_self] at hv; exact Flat.coe_ne_bot hv
      rw [Function.update_of_ne hvp] at hv
      obtain ⟨hr, ho⟩ := hset.2 v hv hne
      refine ⟨hr, fun x hx ↦ ho x ((causallyEntails_root_iff hr hv).2 ?_)⟩
      exact (causallyEntails_root_iff hr (by rwa [Function.update_of_ne hvp])).1 hx
  exact hsuf.2.of_isExogenousSettlement hset'

/-- **The two-way entailment profile** — [karttunen-1971]'s defining
    criterion for the *manage* class — follows from the prerequisite
    account: in a context satisfying both presuppositions, the positive
    assertion entails the complement (Fact B, positive) and any negative
    assertion precludes it in every exogenous settlement (Fact B,
    negative). This is the derivation [nadathur-2023-implicatives]
    advertises for Facts A–C at the class level. -/
theorem twoWay_entailment_profile (hroot : ∀ w, ¬ M.graph.Adj w p)
    (hopen : ∀ x, ¬ M.CausallyEntails s p x) (hsuf : manageSem M s p xP c xC)
    (hnec : necessityPresup M s p xP c xC) :
    M.CausallyEntails (Function.update s p ↑xP) c xC ∧
    ∀ xP', xP' ≠ xP → ∀ s', M.IsExogenousSettlement (Function.update s p ↑xP') s' →
      s' c = ⊥ → ¬ M.CausallyEntails s' c xC :=
  ⟨complement_of_positive_assertion hsuf,
   fun _ hne s' h1 h2 ↦ no_complement_of_negative_assertion hroot hopen hne hnec s' h1 h2⟩

end CharacteristicEntailments

/-! ### Directionality -/

/-- Directionality of complement entailment ([nadathur-2023-implicatives]).

    - **oneWay**: complement entailment under only one matrix polarity.
    - **twoWay**: complement entailment under both polarities. -/
inductive Directionality where
  | oneWay
  | twoWay
  deriving DecidableEq, Repr

/-! ### ImplicativeClass -/

/-- The full lexical signature of an implicative verb ([nadathur-2023-implicatives]). -/
structure ImplicativeClass where
  /-- Positive (manage, force) or negative (fail, prevent) polarity -/
  polarity : Polarity
  /-- One-way (ability) or two-way (manage) entailment -/
  directionality : Directionality
  /-- Does aspect govern the actuality inference? -/
  aspectGoverned : Bool
  /-- Lexically-specified prerequisite type (if any) -/
  prerequisite : Option Prerequisite := none
  deriving DecidableEq, Repr

def ImplicativeClass.manage : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

def ImplicativeClass.fail : ImplicativeClass :=
  { polarity := .negative, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

def ImplicativeClass.dare : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .courage }

def ImplicativeClass.bother : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .engagement }

def ImplicativeClass.jaksaa : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := false
    prerequisite := some .strength }

def ImplicativeClass.ability : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.enough : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.too : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.hesitate : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := false }

-- Classification theorems (substrate-independent — about the enum)

theorem manage_fail_polarity :
    ImplicativeClass.manage.directionality = ImplicativeClass.fail.directionality ∧
    ImplicativeClass.manage.aspectGoverned = ImplicativeClass.fail.aspectGoverned ∧
    ImplicativeClass.manage.polarity ≠ ImplicativeClass.fail.polarity := by
  exact ⟨rfl, rfl, by decide⟩

theorem ability_vs_manage :
    ImplicativeClass.ability.aspectGoverned = true ∧
    ImplicativeClass.manage.aspectGoverned = false ∧
    ImplicativeClass.ability.directionality = .oneWay ∧
    ImplicativeClass.manage.directionality = .twoWay := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem enough_too_polarity :
    ImplicativeClass.enough.aspectGoverned = ImplicativeClass.too.aspectGoverned ∧
    ImplicativeClass.enough.directionality = ImplicativeClass.too.directionality ∧
    ImplicativeClass.enough.polarity ≠ ImplicativeClass.too.polarity := by
  exact ⟨rfl, rfl, by decide⟩

theorem dare_vs_manage_prerequisite :
    ImplicativeClass.dare.polarity = ImplicativeClass.manage.polarity ∧
    ImplicativeClass.dare.directionality = ImplicativeClass.manage.directionality ∧
    ImplicativeClass.dare.prerequisite ≠ ImplicativeClass.manage.prerequisite := by
  exact ⟨rfl, rfl, by decide⟩

theorem jaksaa_vs_dare_directionality :
    ImplicativeClass.jaksaa.directionality = .oneWay ∧
    ImplicativeClass.dare.directionality = .twoWay ∧
    ImplicativeClass.jaksaa.prerequisite.isSome = true ∧
    ImplicativeClass.dare.prerequisite.isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem specific_vs_bleached :
    (ImplicativeClass.dare.prerequisite.bind (some ·.isSpecific)) = some true ∧
    (ImplicativeClass.manage.prerequisite.bind (some ·.isSpecific)) = some false := by
  exact ⟨rfl, rfl⟩

end Implicative

/-! ### `Implicative.toSemantics` dispatch -/

namespace Implicative

/-- Map an implicative verb's polarity to its semantics over a causal model. -/
def toSemantics {U V : Type*} {α : V → Type*} [DecidableEq V] (M : CausalModel U V α)
    [M.IsAcyclic] : Polarity → (∀ v, Flat (α v)) → ∀ p : V, α p → ∀ c : V, α c → Prop
  | .positive => Implicative.manageSem M
  | .negative => Implicative.failSem M

end Implicative
