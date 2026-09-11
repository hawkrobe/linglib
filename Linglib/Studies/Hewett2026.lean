import Linglib.Data.Examples.Hewett2026
import Linglib.Syntax.Minimalist.Agree.Checking
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Hewett (2026): Verbal templates can influence l-selection in Semitic

This file formalizes [hewett-2026]'s generalization that the preposition a Semitic root
lexically selects can vary with the verbal template, and its analysis by joint selection. A
`Datum` records the root, the category, the template where the paper names one, and the
selected preposition of an example, and `Determines` says that the preposition is a function
of a coordinate of the data, `Function.FactorsThrough` on the attested rows. Selection by
the root ([harley-2014]) or by the categorizing head ([merchant-2019]), the structures (12a)
and (12b), predicts that the root and its category determine the preposition; the Tunisian
roots of (13), the Syrian root of (14) and the Hebrew roots of (17) and (18) refute this
(`krh_not_categoryDetermined`), the category-dependent roots of (5) and (6) refute
determination by the root alone, and the roots of (1), (2) and (11) are invariant. Joint
selection (23) indexes a selectional feature by an ordered tuple of category features that
c-commanding heads strip in order, `Minimalist.ActivationIndex`; `selected` runs the
derivations (24) and (25), and the lexical entries read off the data select exactly the
attested preposition once the categorizing head and then the template have activated them
(`selected_eq`).

## Implementation notes

* The prepositions of the four languages are one inductive, each constructor a language's
  item, the Arabic *b-* and *bi-* and *ʕala*, *ʕalej* and *ʕli-* identified; the category of
  a Semitic verb is `V`, of the nominals and adjectives of (1), (2), (5) and (6) `N` and `A`,
  and the templates of (2) and (6) are unnamed in the paper.
* The alternations of (15) and (16) and the roots without nonactive forms of (19) and (20)
  are example rows only; the paper draws from them no claim beyond the template dependence
  the other examples establish.

## TODO

* The locality of joint selection (§4): Activate over spans or within a phase domain.

## References

* [hewett-2026]
* [harley-2014]
* [merchant-2019]
* [merchant-2015]
* [preminger-2014]
-/

namespace Hewett2026

open Minimalist

/-! ### Roots, templates and prepositions -/

/-- The verbal templates of the data: the Arabic Forms I, II, VII and V and the Hebrew
*pi'el*, *pu'al*, *hif'il* and *huf'al*. -/
inductive Template where
  | XaYaZ
  | XaYYaZ
  | nXaYaZ
  | tXaYYaZ
  | XiYeZ
  | XuYaZ
  | hiXYiZ
  | huXYaZ
  deriving DecidableEq, Fintype

/-- The roots of the examples: English √apologi (1) and √prd (5); Syrian Arabic √fxr (2),
√brk (6) and √ħkm (14); Tunisian Arabic √xwf (11), √krh and √dwr (13); Hebrew √tpl (17)
and √ʃpʕ (18). -/
inductive Root where
  | apologi
  | prd
  | fxr
  | brk
  | Hkm
  | xwf
  | krh
  | dwr
  | tpl
  | shps
  deriving DecidableEq, Fintype

/-- The l-selected prepositions: English *for*, *on*, *in* and *of*; Arabic *b-*, *ʕala*,
*min*, *la-* and *fi*; Hebrew *be-* and *al*. -/
inductive Prep where
  | for_
  | on
  | in_
  | of
  | b
  | Eala
  | min
  | la
  | fi
  | be
  | al
  deriving DecidableEq, Fintype

/-- The languages of the data. -/
inductive Lang where
  | english
  | syrianArabic
  | tunisianArabic
  | hebrew
  deriving DecidableEq, Fintype

/-- An example's selection: the root, the category of its realization, the verbal template
when the paper names one, and the l-selected preposition, `none` for a bare object or a
suppressed preposition. -/
structure Datum where
  /-- The root. -/
  root : Root
  /-- The category of the root's realization. -/
  cat : Cat
  /-- The verbal template. -/
  template : Option Template
  /-- The l-selected preposition. -/
  prep : Option Prep
  /-- The language. -/
  lang : Lang
  deriving DecidableEq

/-- The category-independent selection of (1) and (2) and the template-independent selection
of (11). -/
def invariantData : List Datum :=
  [⟨.apologi, .V, none, some .for_, .english⟩, ⟨.apologi, .N, none, some .for_, .english⟩,
   ⟨.apologi, .A, none, some .for_, .english⟩,
   ⟨.fxr, .V, none, some .b, .syrianArabic⟩, ⟨.fxr, .N, none, some .b, .syrianArabic⟩,
   ⟨.fxr, .A, none, some .b, .syrianArabic⟩,
   ⟨.xwf, .V, some .XaYaZ, some .min, .tunisianArabic⟩,
   ⟨.xwf, .V, some .XaYYaZ, some .min, .tunisianArabic⟩]

/-- The category-dependent selection of (5) and (6). -/
def categoryData : List Datum :=
  [⟨.prd, .V, none, some .on, .english⟩, ⟨.prd, .N, none, some .in_, .english⟩,
   ⟨.prd, .A, none, some .of, .english⟩,
   ⟨.brk, .V, none, some .b, .syrianArabic⟩, ⟨.brk, .N, none, some .Eala, .syrianArabic⟩]

/-- The template-dependent selection of (13), (14), (17) and (18). -/
def templateData : List Datum :=
  [⟨.krh, .V, some .XaYaZ, none, .tunisianArabic⟩,
   ⟨.krh, .V, some .XaYYaZ, some .fi, .tunisianArabic⟩,
   ⟨.dwr, .V, some .XaYaZ, some .b, .tunisianArabic⟩,
   ⟨.dwr, .V, some .XaYYaZ, some .Eala, .tunisianArabic⟩,
   ⟨.Hkm, .V, some .XaYaZ, some .Eala, .syrianArabic⟩,
   ⟨.Hkm, .V, some .XaYYaZ, none, .syrianArabic⟩,
   ⟨.tpl, .V, some .XiYeZ, some .be, .hebrew⟩, ⟨.tpl, .V, some .XuYaZ, none, .hebrew⟩,
   ⟨.shps, .V, some .hiXYiZ, some .al, .hebrew⟩, ⟨.shps, .V, some .huXYaZ, none, .hebrew⟩]

/-- All the selection data. -/
def data : List Datum := invariantData ++ categoryData ++ templateData

/-- The rows of a root. -/
def rows (r : Root) : List Datum := data.filter (·.root = r)

/-! ### What determines the preposition -/

/-- The preposition is a function of the coordinate `π` on the rows: `Datum.prep` factors
through `π` there (`Function.FactorsThrough` restricted to the list). -/
def Determines {K : Type*} (π : Datum → K) (rows : List Datum) : Prop :=
  ∀ d ∈ rows, ∀ d' ∈ rows, π d = π d' → d.prep = d'.prep

instance {K : Type*} [DecidableEq K] (π : Datum → K) (rows : List Datum) :
    Decidable (Determines π rows) :=
  inferInstanceAs (Decidable (∀ d ∈ rows, ∀ d' ∈ rows, _ → _))

/-- A coordinate that factors through a finer one determines whatever the coarser does. -/
theorem Determines.of_factorsThrough {K K' : Type*} {π : Datum → K} {π' : Datum → K'}
    (h : Function.FactorsThrough π π') {rows : List Datum} (hπ : Determines π rows) :
    Determines π' rows :=
  λ d hd d' hd' he => hπ d hd d' hd' (h he)

/-- Selection by the root (12a): the root determines the preposition. -/
abbrev RootDetermined (rows : List Datum) : Prop := Determines Datum.root rows

/-- Selection by the categorizing head (12b): the root and its category determine the
preposition, the prediction root-based selection makes as well. -/
abbrev CategoryDetermined (rows : List Datum) : Prop :=
  Determines (λ d => (d.root, d.cat)) rows

/-- Joint selection: the root, its category and the template determine the preposition. -/
abbrev TemplateDetermined (rows : List Datum) : Prop :=
  Determines (λ d => (d.root, d.cat, d.template)) rows

theorem CategoryDetermined.of_rootDetermined {rows : List Datum} (h : RootDetermined rows) :
    CategoryDetermined rows :=
  h.of_factorsThrough λ _ _ he => congrArg Prod.fst he

theorem TemplateDetermined.of_categoryDetermined {rows : List Datum}
    (h : CategoryDetermined rows) : TemplateDetermined rows :=
  h.of_factorsThrough λ _ _ he => Prod.ext (congrArg (·.1) he) (congrArg (·.2.1) he)

/-- √apologi selects *for* in every category (1). -/
theorem apologi_rootDetermined : RootDetermined (rows .apologi) := by decide

/-- √fxr selects *b-* in every category (2). -/
theorem fxr_rootDetermined : RootDetermined (rows .fxr) := by decide

/-- √xwf selects *min* in both templates (11): template-independent l-selection. -/
theorem xwf_rootDetermined : RootDetermined (rows .xwf) := by decide

/-- √prd selects *on*, *in* and *of* by category (5), so the root alone does not determine
the preposition, though the root with its category does. -/
theorem prd_not_rootDetermined : ¬ RootDetermined (rows .prd) := by decide

theorem prd_categoryDetermined : CategoryDetermined (rows .prd) := by decide

/-- √brk selects *b-* as a verb and *ʕala* as a noun (6). -/
theorem brk_not_rootDetermined : ¬ RootDetermined (rows .brk) := by decide

theorem brk_categoryDetermined : CategoryDetermined (rows .brk) := by decide

/-- √krh takes a bare object in XaYaZ and *fi* in XaYYaZ (13a): the root and its category do
not determine the preposition, so selection at or below the categorizer is too early. -/
theorem krh_not_categoryDetermined : ¬ CategoryDetermined (rows .krh) := by decide

/-- √dwr selects *b-* in XaYaZ and *ʕala* in XaYYaZ (13b). -/
theorem dwr_not_categoryDetermined : ¬ CategoryDetermined (rows .dwr) := by decide

/-- √ħkm selects *ʕala* in XaYaZ and no preposition in XaYYaZ (14). -/
theorem Hkm_not_categoryDetermined : ¬ CategoryDetermined (rows .Hkm) := by decide

/-- √tpl selects *be-* in XiYeZ and suppresses it in the passive XuYaZ (17). -/
theorem tpl_not_categoryDetermined : ¬ CategoryDetermined (rows .tpl) := by decide

/-- √ʃpʕ selects *al* in hiXYiZ and suppresses it in the passive huXYaZ (18). -/
theorem shps_not_categoryDetermined : ¬ CategoryDetermined (rows .shps) := by decide

/-- The root, its category and the template together determine the preposition throughout
the data: the fixing point of l-selection. -/
theorem data_templateDetermined : TemplateDetermined data := by decide

/-- The data are not determined below the template. -/
theorem data_not_categoryDetermined : ¬ CategoryDetermined data := by decide

/-! ### Joint selection via Activate (23) -/

/-- An activation key: a category feature, stripped by the categorizing head, or a template,
stripped by the template-defining head. -/
abbrev Key := Cat ⊕ Template

/-- A selectional feature `[SEL: p^C]` (23): the preposition it selects, visible to selection
only once its activation tuple `C` is exhausted. -/
structure SelectionalFeature where
  /-- The selected preposition. -/
  prep : Prep
  /-- The ordered activation tuple. -/
  activation : ActivationIndex Key

namespace SelectionalFeature

/-- The feature `[SEL: p⟨V, t⟩]`: dormant until the categorizing head and then the template
`t` have activated it. -/
def dormant (p : Prep) (t : Template) : SelectionalFeature := ⟨p, ⟨[.inl .V, .inr t]⟩⟩

/-- Activate (23) by a c-commanding head bearing the key. -/
def activate (f : SelectionalFeature) (k : Key) : SelectionalFeature :=
  { f with activation := f.activation.activate k }

/-- Whether the feature is active. -/
def status (f : SelectionalFeature) : FeatureStatus := f.activation.toStatus

variable (p : Prep) (t : Template)

/-- A dormant feature is inactive: a derivational time bomb ([preminger-2014]). -/
theorem dormant_status : (dormant p t).status = .inactive := rfl

/-- The categorizing head alone leaves the template key. -/
theorem activate_V_status : ((dormant p t).activate (.inl .V)).status = .inactive := rfl

/-- The template before the categorizing head strips nothing: only the leftmost key can be
matched. -/
theorem activate_template_first :
    ((dormant p t).activate (.inr t)).activation.remaining = [.inl .V, .inr t] := by
  revert p t; decide

/-- The categorizing head and then the matching template activate the feature. -/
theorem activate_V_template_status :
    (((dormant p t).activate (.inl .V)).activate (.inr t)).status = .active := by
  revert p t; decide

/-- Another template leaves the feature inactive: the features of one root for different
templates are mutually exclusive. -/
theorem activate_V_other_status {t' : Template} (h : t' ≠ t) :
    (((dormant p t).activate (.inl .V)).activate (.inr t')).status = .inactive := by
  revert p t t'; decide

end SelectionalFeature

/-- The lexical entry of a root (§4): one dormant feature per attested template in which it
selects a preposition, `[SEL: {b⟨V, XaYaZ⟩, ʕala⟨V, XaYYaZ⟩}]` for √dwr. -/
def entry (r : Root) : List SelectionalFeature :=
  (rows r).filterMap λ d => d.template.bind λ t => d.prep.map λ p => .dormant p t

/-- The derivations (24) and (25): the categorizing head activates the root's features and
the template-defining head follows. -/
def derive (r : Root) (t : Template) : List SelectionalFeature :=
  (entry r).map λ f => (f.activate (.inl .V)).activate (.inr t)

/-- The prepositions the active features select after the derivation. -/
def selected (r : Root) (t : Template) : List Prep :=
  (derive r t).filterMap λ f => if f.status = .active then some f.prep else none

/-- (24): in XaYaZ the root √dwr's feature for *b-* is activated and the one for *ʕala* is
not. -/
theorem dwr_XaYaZ : selected .dwr .XaYaZ = [.b] := by decide

/-- (25): in XaYYaZ it is the feature for *ʕala* that is activated. -/
theorem dwr_XaYYaZ : selected .dwr .XaYYaZ = [.Eala] := by decide

/-- Joint selection reproduces the data: in every attested root–template pairing the active
features select exactly the attested preposition, and none where none is selected. -/
theorem selected_eq : ∀ d ∈ data, ∀ t, d.template = some t → selected d.root t = d.prep.toList := by
  decide

end Hewett2026
