import Linglib.Syntax.Minimalist.Verbal.Aspect
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Fragments.Mandarin.Particles
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Fragments.Cantonese.Aspect
import Linglib.Fragments.Cantonese.Particles
import Linglib.Fragments.Cantonese.Predicates
import Linglib.Fragments.Cantonese.ResultativeComplements

/-!
# Liu and Yip (2026): Again, finiteness, and split aspect in Chinese languages

This file formalizes the size-based account of finiteness and of exceptional scope in
[liu-yip-2026]. Verb complements in Mandarin and Cantonese come in three sizes, a finite CP, a
nonfinite TP and a nonfinite vP, and the two aspect projections of the split aspect approach
sit at fixed heights, the outer one at the level of T above vP and the inner one at the level
of v, so every complement contains inner aspect and only a TP or larger contains outer aspect
(`Contains`). An *again*-element or aspectual suffix associates with one of the two
projections, by movement for Mandarin preverbal *you* and by agreement for the suffixes, and
takes exceptional scope across a complement, skipping the matrix predicate or lowering onto it,
exactly when the complement has no projection of its flavour to intervene, so that it
associates with the matrix one (`ExceptionalScope`). The paper's tables follow from that one
definition: outer-associated elements, Mandarin *you*, Cantonese *-faan* and the outer
aspectual suffixes, take exceptional scope across a vP and across nothing larger
(`exceptionalScope_outer_iff`); inner-associated elements, Mandarin *zai*, Cantonese *zoi* and
repetitive *-gwo*, the continuous *-zyu* and the phase complements, never do
(`not_exceptionalScope_inner`), which is the argument that vP is the minimal size of a nonfinite
clause; and transparency is downward closed along the size hierarchy
(`ExceptionalScope.anti`), the implicational complementation hierarchy of
[wurmbrand-lohninger-2023]. Mandarin *you* alone carries the unvalued dynamic feature of
[lin-liu-2009] and must be licensed by an outer aspect head bearing `[+D]`, which the paper's
selectional table for *xiang* 'want', *rang* 'let' and *xiangxin* 'believe' turns into the
embeddability of *you* (`Pred.embedsYou`) and into the blocking of aspect lowering by an embedded
*you* (`not_exceptionalScope_of_licensesDynamic`).

## Main definitions

* `Contains`, `ExceptionalScope` — a complement size contains an aspect projection, and an
  element of that flavour takes exceptional scope across it.
* `Again`, `Again.flavor`, `Again.NeedsDynamic` — the six *again*-elements, the projection each
  associates with, and the dynamic feature of *you*.
* `aspectFlavor`, `phaseComplementFlavor` — the association of the Cantonese aspect suffixes
  and phase complements.
* `Pred.selects`, `Complement.LicensesDynamic`, `CPred.size` — the complements the Mandarin
  and Cantonese predicates select.

## Main results

* `exceptionalScope_outer_iff`, `not_exceptionalScope_inner`, `ExceptionalScope.anti` — the
  scope pattern by size and flavour, and the implicational hierarchy.
* `generalization_I`, `generalization_II`, `correlation_I`, `correlation_II` — the Mandarin
  generalizations as consequences.
* `cantonese_lowering`, `aspect_lowering`, `no_phaseComplement_lowering` — the Cantonese
  pattern for the *again*-elements, the aspect suffixes and the phase complements.
* `embedsYou`, `not_exceptionalScope_of_licensesDynamic` — the licensing of *you* and its
  blocking of aspect lowering.

## Implementation notes

The heights are those of the functional sequence in `Syntax/Minimalist/ExtendedProjection`,
outer aspect at the level of T and inner aspect at the level of v, so containment is a
comparison of levels. Defective intervention [chomsky-2000] is not a relation between heads: an
embedded projection blocks association whatever its features, which is the paper's claim. The
semicomplementizer and Exfoliation, the restitutive reading, the Italian parallel and the
crosstype ambiguity of *dasuan* 'plan' are not represented.

## References

* [liu-yip-2026]
* [wurmbrand-lohninger-2023]
* [lin-liu-2009]
* [chomsky-2000]
-/

namespace LiuYip2026

open Minimalist

/-! ### Clause sizes and the projections they contain -/

/-- Type I, the finite CP. -/
def typeI : ComplementSize := .cP

/-- Type II, the nonfinite TP without aspect restructuring. -/
def typeII : ComplementSize := .tP

/-- Type III, the nonfinite vP with aspect restructuring. -/
def typeIII : ComplementSize := .vP

/-- A complement of size `s` contains the aspect projection of flavour `f`: the outer
projection sits at the level of T and the inner one at the level of v. -/
def Contains (s : ComplementSize) (f : AspFlavor) : Prop := f.defaultFLevel ≤ s.fLevel

instance (s : ComplementSize) (f : AspFlavor) : Decidable (Contains s f) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Every complement from vP up contains inner aspect. -/
theorem contains_inner {s : ComplementSize} (h : ComplementSize.vP ≤ s) : Contains s .inner := h

/-- A complement contains outer aspect exactly when it is at least a TP. -/
theorem contains_outer_iff (s : ComplementSize) : Contains s .outer ↔ ComplementSize.tP ≤ s :=
  Iff.rfl

/-- An element associated with the projection of flavour `f` takes exceptional scope across a
complement of size `s`, skipping the matrix predicate or lowering onto it, when the complement
has no projection of that flavour to intervene, so that the element associates with the matrix
one. -/
def ExceptionalScope (f : AspFlavor) (s : ComplementSize) : Prop := ¬ Contains s f

instance (f : AspFlavor) (s : ComplementSize) : Decidable (ExceptionalScope f s) :=
  inferInstanceAs (Decidable (¬ _))

/-- Transparency is downward closed along the size hierarchy: what crosses a larger complement
crosses a smaller one, the implicational complementation hierarchy. -/
theorem ExceptionalScope.anti {f : AspFlavor} {s s' : ComplementSize} (h : s ≤ s')
    (hs : ExceptionalScope f s') : ExceptionalScope f s :=
  fun hc ↦ hs (le_trans hc (ComplementSize.le_def.mp h))

/-- Outer-associated elements take exceptional scope across a complement smaller than a TP,
the vP, and across nothing larger. -/
theorem exceptionalScope_outer_iff (s : ComplementSize) :
    ExceptionalScope .outer s ↔ s < ComplementSize.tP :=
  Nat.not_le

/-- Inner-associated elements never take exceptional scope: every complement contains inner
aspect, so vP is the minimal size of a nonfinite clause. -/
theorem not_exceptionalScope_inner {s : ComplementSize} (h : ComplementSize.vP ≤ s) :
    ¬ ExceptionalScope .inner s :=
  fun hs ↦ hs (contains_inner h)

/-- Generalization II: exceptional scope crosses a nonfinite vP, not a nonfinite TP nor a
finite CP. -/
theorem generalization_II :
    ExceptionalScope .outer typeIII ∧ ¬ ExceptionalScope .outer typeII ∧
      ¬ ExceptionalScope .outer typeI := by
  decide

/-! ### The *again*-elements and their projections -/

/-- The *again*-type elements of the two languages: Mandarin preverbal *you* and *zai*,
Cantonese preverbal *jau* and *zoi* and postverbal *-faan* and repetitive *-gwo*. -/
inductive Again where
  | you
  | zai
  | jau
  | zoi
  | faan
  | gwo
  deriving DecidableEq, Repr

/-- The Mandarin lexical entry of an element. -/
def Again.mandarin : Again → Option Mandarin.Particles.PresupParticle
  | .you => some Mandarin.Particles.you
  | .zai => some Mandarin.Particles.zai
  | _ => none

/-- The Cantonese lexical entry of an element. -/
def Again.cantonese : Again → Option Cantonese.Particles.PresupParticle
  | .jau => some Cantonese.Particles.jau
  | .zoi => some Cantonese.Particles.zoi
  | .faan => some Cantonese.Particles.faan
  | .gwo => some Cantonese.Particles.gwo
  | _ => none

/-- The projection each element associates with: *you* by movement and *-faan* by agreement
with the outer one, *zai*, *zoi* and repetitive *-gwo* with the inner one; preverbal *jau* is
base-generated where it is pronounced and associates with neither. -/
def Again.flavor : Again → Option AspFlavor
  | .you | .faan => some .outer
  | .zai | .zoi | .gwo => some .inner
  | .jau => none

/-- The element carries the unvalued dynamic feature `[u+D]` that an outer aspect head bearing
`[+D]` must check: *you* alone. -/
def Again.NeedsDynamic (a : Again) : Prop := a = .you

instance : DecidablePred Again.NeedsDynamic := fun a ↦ inferInstanceAs (Decidable (a = .you))

/-- The element takes exceptional scope across some complement. -/
def Again.Skips (a : Again) : Prop :=
  ∃ f ∈ a.flavor, ∃ s ∈ [typeI, typeII, typeIII], ExceptionalScope f s

instance : DecidablePred Again.Skips := fun a ↦ by
  unfold Again.Skips; cases a.flavor <;> simp only [Option.mem_def] <;> infer_instance

/-- An element takes exceptional scope somewhere exactly when it associates with the outer
projection. -/
theorem skips_iff (a : Again) : a.Skips ↔ a.flavor = some .outer := by cases a <;> decide

/-- Generalization I: exceptional scope is found with *you* but not with *zai*. -/
theorem generalization_I : Again.you.Skips ∧ ¬ Again.zai.Skips := by decide

/-- The Cantonese pattern: *-faan* lowers, repetitive *-gwo* does not, and neither preverbal
adverb has exceptional scope. -/
theorem cantonese_lowering :
    Again.faan.Skips ∧ ¬ Again.gwo.Skips ∧ ¬ Again.jau.Skips ∧ ¬ Again.zoi.Skips := by
  decide

/-- Correlation I: a Mandarin *again*-element has exceptional scope iff it cannot surface in
an embedded nonfinite clause without a dynamic aspect, that is, iff it carries `[u+D]`. -/
theorem correlation_I : ∀ a ∈ [Again.you, Again.zai], (a.Skips ↔ a.NeedsDynamic) := by decide

/-- Correlation II: an *again*-element has exceptional scope iff its projection is at least as
high as the aspectual heads, the level of `Asp` in the functional sequence. -/
theorem correlation_II (a : Again) :
    a.Skips ↔ ∃ f ∈ a.flavor, fValue .Asp ≤ f.defaultFLevel := by
  cases a <;> decide

/-! ### Aspect suffixes and phase complements -/

/-- The association of the Cantonese aspect suffixes: the perfective *-zo*, the progressive
*-gan* and the experiential *-gwo* with the outer projection, the continuous *-zyu* with the
inner one. -/
def aspectFlavor (m : Cantonese.Aspect.Marker) : AspFlavor :=
  if m = Cantonese.Aspect.zyu then .inner else .outer

/-- Every phase complement associates with the inner projection. -/
def phaseComplementFlavor (_ : Cantonese.ResultativeComplements.PhaseComplement) : AspFlavor :=
  .inner

/-- Aspect lowering: an outer aspect suffix embedded in a vP is interpreted on the matrix
predicate, and the continuous *-zyu* alone is not. -/
theorem aspect_lowering :
    ∀ m ∈ Cantonese.Aspect.markers,
      (ExceptionalScope (aspectFlavor m) typeIII ↔ m ≠ Cantonese.Aspect.zyu) := by
  decide

/-- No phase complement lowers across any complement. -/
theorem no_phaseComplement_lowering (pc : Cantonese.ResultativeComplements.PhaseComplement)
    {s : ComplementSize} (h : ComplementSize.vP ≤ s) :
    ¬ ExceptionalScope (phaseComplementFlavor pc) s :=
  not_exceptionalScope_inner h

/-! ### Selection and the licensing of *you* -/

/-- A complement as a predicate selects it: a vP, a TP whose outer aspect head has the given
dynamicity, or a CP. -/
inductive Complement where
  | vP
  | tP (d : Aspect.Dynamicity)
  | cP
  deriving DecidableEq, Repr

/-- The size of a complement. -/
def Complement.size : Complement → ComplementSize
  | .vP => .vP
  | .tP _ => .tP
  | .cP => .cP

/-- A complement licenses a `[u+D]` element when it has an outer aspect head bearing `[+D]`: a
dynamic TP, or a CP, whose outer aspect head may be dynamic. -/
def Complement.LicensesDynamic (c : Complement) : Prop := c = .tP .dynamic ∨ c = .cP

instance : DecidablePred Complement.LicensesDynamic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A complement that licenses *you* contains outer aspect, so nothing outer-associated takes
exceptional scope across it: an embedded *you* blocks aspect lowering. -/
theorem not_exceptionalScope_of_licensesDynamic {c : Complement} (h : c.LicensesDynamic) :
    ¬ ExceptionalScope .outer c.size := by
  rcases h with rfl | rfl <;> decide

/-- The three Mandarin predicates of the selectional table. -/
inductive Pred where
  | xiang
  | rang
  | xiangxin
  deriving DecidableEq, Repr

/-- The lexical entry of a predicate. -/
def Pred.entry : Pred → Mandarin.Predicates.Verb
  | .xiang => Mandarin.Predicates.xiang
  | .rang => Mandarin.Predicates.rang
  | .xiangxin => Mandarin.Predicates.xiangxin

/-- The complements each predicate selects: *xiang* 'want' a vP or a stative TP, *rang* 'let'
a vP or a TP of either dynamicity, *xiangxin* 'believe' a CP. -/
def Pred.selects : Pred → List Complement
  | .xiang => [.vP, .tP .stative]
  | .rang => [.vP, .tP .stative, .tP .dynamic]
  | .xiangxin => [.cP]

/-- *You* can surface in a complement of the predicate iff the predicate selects a complement
licensing `[u+D]`. -/
def Pred.EmbedsYou (p : Pred) : Prop := ∃ c ∈ p.selects, c.LicensesDynamic

instance : DecidablePred Pred.EmbedsYou := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- *You* skips the predicate iff the predicate selects a vP. -/
def Pred.SkipsYou (p : Pred) : Prop := ∃ c ∈ p.selects, ExceptionalScope .outer c.size

instance : DecidablePred Pred.SkipsYou := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The selectional table: *want* embeds no *you* but is skipped, *let* does both, *believe*
embeds *you* and is not skipped. -/
theorem embedsYou :
    (¬ Pred.xiang.EmbedsYou ∧ Pred.xiang.SkipsYou) ∧ (Pred.rang.EmbedsYou ∧ Pred.rang.SkipsYou) ∧
      (Pred.xiangxin.EmbedsYou ∧ ¬ Pred.xiangxin.SkipsYou) := by
  decide

/-- The Cantonese predicates and the size of the complement each selects: the nonfinite
clause-taking *soeng* 'want', *hyun* 'urge', *bik* 'force', *giu* 'ask' and *daasyun* 'intend'
a vP, the finite clause-taking *seon* 'believe', *gong* 'say' and *geidak* 'remember' a CP. -/
inductive CPred where
  | soeng
  | hyun
  | bik
  | giu
  | daasyun
  | seon
  | gong
  | geidak
  deriving DecidableEq, Repr

/-- The lexical entry of a predicate. -/
def CPred.entry : CPred → Cantonese.Predicates.Verb
  | .soeng => Cantonese.Predicates.soeng
  | .hyun => Cantonese.Predicates.hyun
  | .bik => Cantonese.Predicates.bik
  | .giu => Cantonese.Predicates.giu
  | .daasyun => Cantonese.Predicates.daasyun
  | .seon => Cantonese.Predicates.seon
  | .gong => Cantonese.Predicates.gong
  | .geidak => Cantonese.Predicates.geidak

/-- The size of the complement each predicate selects. -/
def CPred.size : CPred → ComplementSize
  | .soeng | .hyun | .bik | .giu | .daasyun => .vP
  | .seon | .gong | .geidak => .cP

/-- The sizes agree with the fragment's frames: a predicate selects a CP iff its citation
frame is a finite clause. -/
theorem CPred.size_eq_cP_iff (p : CPred) :
    p.size = .cP ↔ p.entry.complementType = .finiteClause := by
  cases p <;> decide

/-- Likewise for the Mandarin predicates: *xiangxin* alone selects a CP. -/
theorem Pred.selects_cP_iff (p : Pred) :
    Complement.cP ∈ p.selects ↔ p.entry.complementType = .finiteClause := by
  cases p <;> decide

/-- *-Faan* lowers across the complement of *soeng* 'want' and not across that of *seon*
'believe'. -/
theorem faan_lowering :
    ExceptionalScope .outer CPred.soeng.size ∧ ¬ ExceptionalScope .outer CPred.seon.size := by
  decide

/-! ### The implicational complementation hierarchy -/

/-- The semantic complement classes of the hierarchy, event, situation and proposition, and
the minimal size each maps to. -/
inductive ComplementClass where
  | event
  | situation
  | proposition
  deriving DecidableEq, Repr

/-- The minimal size of each class: vP, TP and CP. -/
def ComplementClass.size : ComplementClass → ComplementSize
  | .event => .vP
  | .situation => .tP
  | .proposition => .cP

/-- A dependency transparent for a class is transparent for every more integrated class. -/
theorem ComplementClass.exceptionalScope_of_le {f : AspFlavor} {c c' : ComplementClass}
    (h : c.size ≤ c'.size) (hs : ExceptionalScope f c'.size) : ExceptionalScope f c.size :=
  hs.anti h

end LiuYip2026
