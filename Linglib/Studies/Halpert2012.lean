import Linglib.Syntax.Minimalist.Phi.Probing

/-!
# Halpert 2012 — Argument Licensing and Agreement in Zulu [halpert-2012]

[halpert-2012] (MIT dissertation): the familiar structural licensers
(T⁰, v⁰, P⁰) are not licensers in Zulu; instead a Licensing head L⁰
above vP licenses the highest element within vP, and the **augment**
vowel on a nominal is itself an intrinsic case licenser. Augmentless
nominals therefore need L⁰: they must be vP-internal, structurally
highest there, and at most one occurs per simplex clause. The
**conjoint/disjoint** alternation on the verb (present tense:
conjoint ∅- vs. disjoint *ya-*) is the morphological spellout of L⁰
itself (her ch. 4): "the disjoint appears when L fails to find a
goal", and "the derivation converges even if a probe fails to find a
goal" — failure-tolerance, adopted by [preminger-2014] Ch. 6 as the
second case study in tolerated failed agreement.

Formalized through `Phi/Probing.lean`: L⁰ is the **indiscriminate**
instance of `probeSearch` (`vis = ⊤`, so bare minimality delivers
`List.head?`; augmented nominals intervene, her Chomsky-2000-style
intervention), and the licensing condition is the off-diagonal
`AllLicensed needs ⊤` with `needs` = augmentless. Contrast Kichean
([preminger-2014] Ch. 4): the diagonal case, π⁰ relativized to
exactly the needy, hence omnivorous and position-insensitive.

Scope: simplex clauses only — the dissertation's second licensing
route (V⁰ together with specifier-taking CAUS/APPL heads, licensing
one additional augmentless nominal; her LP schemas in ch. 3) is not
modeled.
-/

namespace Halpert2012

open Minimalist

/-- A vP-internal nominal: noun class + augment status. Class numbers
    follow the standard Bantu numbering Halpert uses (1 *muntu*
    'person', 5 *qanda* 'egg', ...). -/
structure Nominal where
  nounClass : Nat
  augmented : Bool
  deriving DecidableEq, Repr

/-- Does a nominal need licensing by L⁰? Augmentless nominals do; the
    augment is an intrinsic case licenser, so augmented nominals
    don't (while still intervening for L⁰). -/
def needsL (n : Nominal) : Bool := !n.augmented

/-- L⁰'s goal in a vP: an indiscriminate `probeSearch` — every
    element is visible, so bare minimality delivers the structurally
    highest one. -/
def lGoal (vp : List Nominal) : Option Nominal :=
  probeSearch (fun _ => true) vp

/-- The licensing condition on a simplex vP: every augmentless
    nominal is licensed by L⁰'s single search. -/
def LicensingOk (vp : List Nominal) : Prop :=
  AllLicensed needsL (fun _ => true) vp

instance (vp : List Nominal) : Decidable (LicensingOk vp) :=
  inferInstanceAs (Decidable (AllLicensed needsL (fun _ => true) vp))

/-- L⁰'s probing outcome: valued iff the vP has any overt content. -/
def lOutcome (vp : List Nominal) : ProbeOutcome :=
  searchOutcome (fun _ => true) vp

/-- The conjoint/disjoint marker (present tense) as the spellout of
    L⁰: conjoint ∅- when L⁰ found a goal, disjoint *ya-* when it
    failed. A marked pattern — the overt member realizes FAILED
    valuation ([preminger-2014] Ch. 6 notes the parallel with English
    non-past -Ø vs. *-z*). -/
def lSpellout (vp : List Nominal) : String :=
  match (lOutcome vp).pfRealization with
  | .agreement => "∅-"
  | .elsewhere => "ya-"

/-! ### The conjoint/disjoint distribution -/

/-- Disjoint iff vP is empty: the conjoint requires overt postverbal
    material — L⁰'s indiscriminate search is sensitive even to
    non-arguments, which is the learner's evidence that L⁰ is
    unrelativized ([preminger-2014] Ch. 7's locative-modifier
    point). -/
theorem disjoint_iff_empty (vp : List Nominal) :
    lSpellout vp = "ya-" ↔ vp = [] := by
  cases vp with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons a t =>
    have hne : ("∅-" : String) ≠ "ya-" := by decide
    exact ⟨fun h => absurd h hne, fun h => nomatch h⟩

/-! ### Licensing: highest-only and at-most-one -/

/-- An augmentless nominal is licensed iff it is the structurally
    highest element of its vP — her ch. 3: L "licenses the highest
    element in vP". Instance of `allLicensed_const_true_iff`. -/
theorem licensingOk_iff_highest (vp : List Nominal) :
    LicensingOk vp ↔
      ∀ n ∈ vp, needsL n = true → vp.head? = some n :=
  allLicensed_const_true_iff

/-- At most one augmentless nominal per simplex vP (her transitive
    and intransitive LP schemas): L⁰'s single Agree relation licenses
    at most one goal. -/
theorem at_most_one_augmentless {vp : List Nominal} (h : LicensingOk vp) :
    ∀ n ∈ vp, ∀ m ∈ vp, needsL n = true → needsL m = true → n = m :=
  fun n hn m hm hn' hm' => (h n hn hn').unique (h m hm hm')

/-! ### The negative-existential VS(O) paradigm -/

/-- The augmentless distribution in negative existentials (her ch. 3
    paradigm; reproduced as [preminger-2014] (128)): an augmentless
    nominal is fine alone or above an augmented object; blocked in
    pairs (single Agree relation) and below an augmented subject
    (intervention). Tokens: *muntu* '1person', *qanda* '5egg'. -/
theorem augmentless_distribution :
    -- ✔ VS with augmentless S
    LicensingOk [⟨1, false⟩] ∧
    -- ✔ VSO: augmentless S over augmented O
    LicensingOk [⟨1, false⟩, ⟨5, true⟩] ∧
    -- ✗ VSO: two augmentless nominals
    ¬ LicensingOk [⟨1, false⟩, ⟨5, false⟩] ∧
    -- ✗ VSO: augmentless O below augmented S
    ¬ LicensingOk [⟨1, true⟩, ⟨5, false⟩] := by
  decide

/-! ### Tolerated failed agreement -/

/-- Failure-tolerance, in her own terms ("the derivation converges
    even if a probe fails to find a goal"; "when L fails to find a
    goal, the derivation records this failure in the morphological
    spell-out"): an empty vP leaves L⁰ unvalued, the derivation
    converges under the obligatory-operations model, and PF realizes
    the failure as the overt disjoint *ya-*. With any goal — even a
    licensing-indifferent augmented one — L⁰ is valued and the
    conjoint ∅- surfaces. -/
theorem failed_agree_spells_disjoint :
    lOutcome [] = .unvalued ∧
    derivationConverges .obligatoryNocrash (lOutcome []) = true ∧
    (lOutcome []).pfRealization = .elsewhere ∧
    lSpellout [] = "ya-" ∧
    lOutcome [⟨5, true⟩] = .valued ∧
    lSpellout [⟨5, true⟩] = "∅-" := by
  decide

end Halpert2012
