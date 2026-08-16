import Linglib.Morphology.Morphotactics.RelevanceHierarchy

/-!
# The Mirror Principle

[baker-1985]'s Mirror Principle: "Morphological derivations must directly reflect
syntactic derivations (and vice versa)" ([baker-1985] (4)). Each
grammatical-function-changing rule — passive, causative, applicative,
reflexive/reciprocal — simultaneously adds an affix to the verb and changes the
grammatical functions of arguments, so affix layering must match the order of rule
application.

[baker-1985] §6 argues the principle should not be stipulated but should follow from
the architecture: where the morphological and syntactic effects of a GF-rule are one
process, mirroring holds by construction. `Derivation` realizes that architecture — a
single list of `DerivationStep`s, with the morphological reading (`affixOrder`) and
the syntactic reading (`ruleOrder`) as its two projections.

## Main definitions

- `GFRuleType`: the GF-changing rules, with `toMorphCategory` mapping them into
  [bybee-1985]'s relevance hierarchy.
- `Derivation`, `ruleOrder`, `affixOrder`: single-process derivations and their
  syntactic and morphological projections.
- `AgreementPattern`, `deriveReference`: agreement position relative to a GF-rule
  morpheme, and the grammatical-function level derivational timing makes visible at
  that position.
- `MorphDomain.InScope`: the principle's scope — concatenative morphology, excluding
  cliticization and nonconcatenative processes ([baker-1985] §5).
-/

namespace Morphology.MirrorPrinciple

open Morphology (MorphCategory)

/-! ### GF-rules -/

/-- Grammatical-function-changing rules: the processes that both add an affix to the
verb and rearrange the grammatical functions of its arguments ([baker-1985] §§2–4). -/
inductive GFRuleType where
  | passive
  | causative
  | applicative
  | reflexReciprocal
  deriving DecidableEq, Repr

/-- Map GF-rules to [bybee-1985]'s morphological categories: passive marks voice;
causative, applicative, and reflexive/reciprocal change valence. -/
def GFRuleType.toMorphCategory : GFRuleType → MorphCategory
  | .passive => .voice
  | .causative => .valence
  | .applicative => .valence
  | .reflexReciprocal => .valence

/-- GF-rule categories are strictly more stem-relevant than subject agreement on
[bybee-1985]'s hierarchy. A relevance-order fact, not a positional universal:
prefixal agreement can sit inside a GF-rule morpheme, as in Chamorro
*na'-fan-otchu* ([baker-1985] (15c)). -/
theorem GFRuleType.toMorphCategory_relevanceLT_agreement (r : GFRuleType) :
    r.toMorphCategory.RelevanceLT (.agreement .subj) := by
  cases r <;> decide

/-! ### Derivations -/

/-- A derivational step bundling a GF-rule with the affix it adds. Because the
morphological and syntactic effects travel together, the Mirror Principle holds by
construction ([baker-1985] §6). -/
structure DerivationStep where
  rule : GFRuleType
  affix : String
  deriving DecidableEq, Repr

/-- Steps ordered first-applied (innermost affix) to last-applied (outermost). -/
abbrev Derivation := List DerivationStep

/-- The syntactic projection of a derivation: its GF-rules in order of application. -/
def ruleOrder (d : Derivation) : List GFRuleType := d.map (·.rule)

/-- The morphological projection of a derivation: its affixes from innermost to
outermost. -/
def affixOrder (d : Derivation) : List String := d.map (·.affix)

/-! ### Agreement and derivational timing -/

/-- Position of an agreement morpheme relative to a GF-rule morpheme: closer to the
verb root (inner) or farther out (outer). -/
inductive AgreementPosition where
  | inner | outer
  deriving DecidableEq, Repr

/-- The level of grammatical functions an agreement morpheme references: semantic
(pre-rule) or surface (post-rule). -/
inductive GFReference where
  | semantic | surface
  deriving DecidableEq, Repr

/-- An agreement morpheme's position relative to a GF-rule morpheme, paired with the
level of grammatical functions it references. -/
structure AgreementPattern where
  position : AgreementPosition
  reference : GFReference
  deriving DecidableEq, Repr

/-- The GF reference derivational timing dictates: an inner agreement morpheme is
added before the GF-rule and sees semantic grammatical functions; an outer one is
added after and sees surface ones. -/
def deriveReference : AgreementPosition → GFReference
  | .inner => .semantic
  | .outer => .surface

/-! ### Scope -/

/-- The kinds of morphology [baker-1985] §5 distinguishes when delimiting the Mirror
Principle's scope. -/
inductive MorphDomain where
  | concatenative | cliticization | nonconcatenative
  deriving DecidableEq, Repr

/-- The Mirror Principle's domain: concatenative (agglutinative) morphology, leaving
cliticization and nonconcatenative morphology outside its scope ([baker-1985] §5). -/
def MorphDomain.InScope (d : MorphDomain) : Prop := d = .concatenative

instance : DecidablePred MorphDomain.InScope :=
  fun d => inferInstanceAs (Decidable (d = .concatenative))

end Morphology.MirrorPrinciple
