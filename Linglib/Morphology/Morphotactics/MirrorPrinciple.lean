import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Morphology.Word.Tree

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
single list of `DerivationStep`s, each a rule with the affix it adds on the side it
attaches — and the word's surface is derived from it by attachment (`surface`):
the affixes of each side read outward from the root in the order the rules applied
(`surface_eq`).

## Main definitions

- `GFRuleType`: the GF-changing rules, with `toMorphCategory` mapping them into
  [bybee-1985]'s relevance hierarchy.
- `Derivation`, `ruleOrder`, `surface`: single-process derivations, their syntactic
  projection, and the surface they derive.
- `AgreementPattern`, `referenceAt`, `deriveReference`: agreement position relative
  to a GF-rule morpheme, the grammatical-function level visible once given rules
  have applied, and the level derivational timing makes visible at that position.
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

/-- A derivational step bundling a GF-rule with the affix it adds and the side on
which it attaches. Because the morphological and syntactic effects travel together,
the Mirror Principle holds by construction ([baker-1985] §6). An infix attaches
after its host, as `Word.Tree.toList` linearizes it. -/
structure DerivationStep where
  rule : GFRuleType
  affix : String
  side : Morph.Side
  deriving DecidableEq, Repr

/-- Steps ordered first-applied (innermost affix) to last-applied (outermost). -/
abbrev Derivation := List DerivationStep

/-- The syntactic projection of a derivation: its GF-rules in order of application. -/
def ruleOrder (d : Derivation) : List GFRuleType := d.map (·.rule)

/-- The word a derivation builds on a root: each affix attached on its side, in
order of application. -/
def toTree (root : String) (d : Derivation) : Word.Tree String :=
  Word.Tree.attachAll root (d.map fun st => (st.side, st.affix))

/-- The surface a derivation derives on a root. -/
def surface (root : String) (d : Derivation) : List String := (toTree root d).toList

/-- **The Mirror Principle** ([baker-1985] (4)): the surface is the prefixes in
reverse order of application, the root, and the suffixes in order of application —
on each side, affix order outward from the root is rule order. -/
theorem surface_eq (root : String) (d : Derivation) :
    surface root d =
      ((d.filter (·.side = .before)).map (·.affix)).reverse ++
        root :: (d.filter (·.side = .after)).map (·.affix) := by
  simp [surface, toTree, Word.Tree.toList_attachAll, List.filter_map, List.map_map,
    Function.comp_def]

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

/-- The grammatical functions visible once the given GF-rules have applied: the
semantic ones before any rule, the surface ones after. -/
def referenceAt (applied : List GFRuleType) : GFReference :=
  if applied.isEmpty then .semantic else .surface

/-- The GF reference derivational timing dictates: an inner agreement morpheme is
added before the GF-rule and sees semantic grammatical functions; an outer one is
added after and sees surface ones. -/
def deriveReference : AgreementPosition → GFReference
  | .inner => .semantic
  | .outer => .surface

/-- Relative to one GF-rule, an inner agreement morpheme attaches with no rule
applied and an outer one after it: `deriveReference` is `referenceAt` at the
rules applied before the morpheme. -/
theorem deriveReference_eq_referenceAt (r : GFRuleType) :
    ∀ pos, deriveReference pos = referenceAt (match pos with | .inner => [] | .outer => [r])
  | .inner => rfl
  | .outer => rfl

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
