import Linglib.Semantics.Genericity.Subkinds
import Linglib.Fragments.Dutch.Adjectives

/-!
# McNally and de Swart (2011): Inflection and Derivation

This file formalizes the analysis of [mcnally-deswart-2011] of the three ways Dutch refers
to abstract objects such as colours, illustrated with *rood* 'red': the uninflected nominal
*het rood* and the derived *de roodheid* denote kinds, sets of subkinds, while the inflected
*het rode van de aardbeien* denotes a trope, the entity correlate of a relational property
instantiated in one bearer. The uninflected nominal of a root is the subkind of the shade
partition its root determines, so distinct roots denote disjoint kinds, the disjointness
condition of [carlson-1977] (`uninflectedNominal`, `uninflectedNominal_disjoint`); the
derived nominal is defined only for roots with a *-heid* form and then denotes the same
kind (`derivedNominal`, `derivedNominal_eq_uninflected`); the inflectional suffix is not a
category-changing nominalizer but a valence-increasing operator turning the adjective into a
relation between an object and its aspect, which the determiner *het*, the nominalization
operator of [chierchia-1984] when it embeds an adjective phrase, reifies as a trope
(`inflectAdjective`, `inflectedWithHet`). The three forms differ in what the determiner
embeds and in what they denote, and the paper's distributional diagnostics follow from those
two coordinates: adjectival modification and determiners other than *het* need a noun, and
generic use needs a kind, so the inflected form alone fails all three (`Form`,
`inflected_diagnostics`, `fails_iff_inflected`). The paper's three rival analyses of the
inflected form are named for later comparison (`InflectedAnalysis`).

## Implementation notes

The roots and their forms come from the Dutch adjective fragment, and the subkind relation is
the salient equivalence relation of `Semantics/Genericity/Subkinds`; the model is extensional,
so the kind denoted by the derived nominal coincides with the uninflected one. The trope is
the pair of the aspect property and its bearer. The paper's observation that the inflected
construction is rare with concrete adjectives, and its extension to Dutch nominalized
infinitives and Spanish *lo*-nominals, are described in prose.

## TODO

The paper is not on file; the example numbers are transcribed from an earlier version of
this file and are UNVERIFIED.

## References

* [mcnally-deswart-2011]
* [chierchia-1984]
* [carlson-1977]
-/

namespace McNallyDeSwart2011

open Semantics.Kinds.Subkinds Dutch.Adjectives

/-! ### Kinds: the uninflected and derived nominals -/

/-- A shade: an adjective entry of the fragment with an index, so that several shades belong
to one colour. -/
structure Shade where
  root : AdjEntry
  idx : ℕ
  deriving DecidableEq, Repr

/-- The kind-forming relation on shades: sharing a root. -/
def kfShade : Setoid Shade where
  r s₁ s₂ := s₁.root = s₂.root
  iseqv := ⟨λ _ => rfl, Eq.symm, Eq.trans⟩

/-- The canonical shade of a root. -/
def canonicalShade (a : AdjEntry) : Shade := ⟨a, 0⟩

/-- The uninflected nominal *het rood* (19): the set of subkinds, the shades, of the colour. -/
def uninflectedNominal (a : AdjEntry) : Set Shade :=
  subkindOf kfShade (canonicalShade a)

theorem mem_uninflectedNominal (a : AdjEntry) (s : Shade) :
    s ∈ uninflectedNominal a ↔ s.root = a :=
  ⟨Eq.symm, Eq.symm⟩

/-- Distinct roots denote disjoint kinds, the disjointness condition of [carlson-1977]. -/
theorem uninflectedNominal_disjoint {a₁ a₂ : AdjEntry} (h : a₁ ≠ a₂) :
    Disjoint (uninflectedNominal a₁) (uninflectedNominal a₂) :=
  disjointness_condition kfShade (a := canonicalShade a₁) (b := canonicalShade a₂) h

/-- A prepositional modifier (20) restricts the kind by a contextual relation to the
complement's entity. -/
def ppModifier {Entity : Type*} (R : Shade → Entity → Prop) (s : Entity) (P : Set Shade) :
    Set Shade :=
  {x | x ∈ P ∧ R x s}

/-- The derived nominal *de roodheid* (24): defined for the roots with a *-heid* form, and
denoting the kind of the root. -/
def derivedNominal (a : AdjEntry) : Option (Set Shade) :=
  a.nominalHeid.map λ _ => uninflectedNominal a

/-- Where defined, the derived nominal is the uninflected one. -/
theorem derivedNominal_eq_uninflected {a : AdjEntry} (h : a.nominalHeid.isSome) :
    derivedNominal a = some (uninflectedNominal a) := by
  obtain ⟨_, hh⟩ := Option.isSome_iff_exists.1 h
  simp [derivedNominal, hh]

/-- *roze* 'pink' has no *-heid* form, so no derived nominal. -/
theorem derivedNominal_roze : derivedNominal roze = none := by decide

/-! ### The trope: the inflected form -/

/-- The aspect relation a language pairs with each adjectival property: the relation between
a bearer and its aspect of that property. -/
def AspectOf (Entity : Type*) := (Shade → Prop) → Entity → Shade → Prop

/-- The inflectional suffix (25): a valence-increasing operator taking the adjective's property
to the aspect relation. -/
def inflectAdjective {Entity : Type*} (asp : AspectOf Entity) (P : Shade → Prop) :
    Entity → Shade → Prop :=
  asp P

/-- The trope *het rode van de aardbeien* (26): the aspect property saturated by the bearer,
reified by *het* together with its bearer. -/
def inflectedWithHet {Entity : Type*} (asp : AspectOf Entity) (P : Shade → Prop) (s : Entity) :
    (Shade → Prop) × Entity :=
  (inflectAdjective asp P s, s)

/-! ### The three forms and the diagnostics -/

/-- What the determiner embeds. -/
inductive Embedded where
  | noun
  | adjectivePhrase
  deriving DecidableEq, Repr

/-- The kind of abstract object a form denotes. -/
inductive AbstractObject where
  | kind
  | trope
  deriving DecidableEq, Repr

/-- A form of abstract reference: what the determiner embeds and what the whole denotes. -/
structure Form where
  embedded : Embedded
  denotation : AbstractObject
  deriving DecidableEq, Repr

/-- *het rood*: a neuter mass noun denoting a kind. -/
def uninflected : Form := ⟨.noun, .kind⟩

/-- *de roodheid*: a derived noun denoting a kind. -/
def derived : Form := ⟨.noun, .kind⟩

/-- *het rode van X*: an adjective phrase under *het*, denoting a trope. -/
def inflected : Form := ⟨.adjectivePhrase, .trope⟩

/-- Adjectival modification targets a noun (13). -/
def Form.AdmitsAdjectivalModification (f : Form) : Prop := f.embedded = .noun

/-- Determiners other than *het* select a noun; *het* alone carries the nominalization of an
adjective phrase (14). -/
def Form.AdmitsOtherDeterminers (f : Form) : Prop := f.embedded = .noun

/-- Generic use needs a kind (15). -/
def Form.AdmitsGeneric (f : Form) : Prop := f.denotation = .kind

instance : DecidablePred Form.AdmitsAdjectivalModification :=
  λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Form.AdmitsOtherDeterminers := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Form.AdmitsGeneric := λ _ => inferInstanceAs (Decidable (_ = _))

/-- The inflected form fails all three diagnostics, and the two nominal forms pass them. -/
theorem inflected_diagnostics :
    (¬ inflected.AdmitsAdjectivalModification ∧ ¬ inflected.AdmitsOtherDeterminers ∧
      ¬ inflected.AdmitsGeneric) ∧
    ∀ f ∈ [uninflected, derived],
      f.AdmitsAdjectivalModification ∧ f.AdmitsOtherDeterminers ∧ f.AdmitsGeneric := by
  decide

/-- Among the three forms, failing any diagnostic is being the inflected form: the
distributional restrictions are the trope semantics. -/
theorem fails_iff_inflected (f : Form) (hf : f ∈ [uninflected, derived, inflected]) :
    (¬ f.AdmitsAdjectivalModification ∨ ¬ f.AdmitsOtherDeterminers ∨ ¬ f.AdmitsGeneric) ↔
      f = inflected := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> decide

/-- The three analyses of the inflected form the paper weighs (§2.3): a category-changing
nominalization, ellipsis of a noun, and *het* as the nominalization operator over an adjective
phrase, the one adopted. -/
inductive InflectedAnalysis where
  | nominalisation
  | ellipsis
  | hetAsCap
  deriving DecidableEq, Repr

end McNallyDeSwart2011
