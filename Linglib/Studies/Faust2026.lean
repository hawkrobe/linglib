import Linglib.Studies.McCarthy1981
import Linglib.Fragments.Hebrew.ConsonantalRoots
import Linglib.Fragments.Amharic.ConsonantalRoots
import Linglib.Features.Gender.Basic
import Linglib.Data.Examples.Faust2026

/-!
# Faust (2026): Intrusion as template satisfaction and the QaTaT–QaTa problem in Semitic

This file formalizes [faust-2026]'s *Misalignment principle — a nonfinal root element must
not be template-final — and the two template-satisfaction strategies it leaves to a root whose
final radical cannot associate to a [+consonantal] C-slot: leaving the slot vacant (Hebrew
[kala], the QaTaT–QaTa problem of (3)–(4)) or filling it with the consonant of the feminine
suffix (Hebrew [tadmit] (10), Amharic [fäʤt-o] (8) and [mäsmat] (13a)). The derivations run
[mccarthy-1981]'s association conventions, as implemented in `Studies/McCarthy1981.lean`,
over the substrate `Morphology.TemplateMatch`: the [+c] specification bars glides and vowels
from a slot, Amharic joins a barred glide to the preceding consonant and merges a barred vowel
with the vocalization ((7), (13)), and an unsatisfied final syllable is truncated (7a). Template
satisfaction by spreading (1) is the candidate *Misalignment rules out for j-final roots
((4), (6a)) and permits for biradicals (√wd, [wäddäd-ä]); intrusion never misaligns because the
intruder is not a radical, and its absence from the hollow verbs (13b–c) follows from the
No-Crossing Constraint on the root-plus-suffix melody. The feminine morph is inherent
inflection on n, so only a nominal base merges with it (11): that gives the distribution of the
intruder across the Amharic paradigms (5) and (12) that [broselow-1984]'s default consonant
left unexplained. The pipeline reproduces the paradigms (3), (5), (12) and the taQTiL nouns
(9) whose roots the squib identifies (`Data/Examples/Faust2026.json`).

## Implementation notes

* A plain C-slot admits a glide (kaluj, klija) but no vowel; a [+c] slot admits consonants
  only. `segClass` classifies the segments of the two fragments accordingly, and `merge`
  states the three mergers the squib names: d + j to ʤ, ä + a to a, ä + i to e.
* The medial gemination of the Amharic PFV is prespecified ({C C} in (7)) and doubled at
  realization; truncation deletes the final VC when the final C-slot is vacant and the
  pattern truncates (Amharic, not Hebrew).
* The intruder's line is checked against `NoCrossing`, the No-Crossing Constraint on the
  consonantal melody of the base merged with the suffix, root elements before the suffix's;
  `isNonCrossing_melodyLinks_iff` interprets it into `Autosegmental.IsNonCrossing`. The
  morph's vowel (√(a)t) does not surface in the forms derived, so the affix carries only t.
* The squib labels (13c) [mähid] while (12e) and its merger /i,ä/ to [e] give [mähed]; the
  rows follow (12e).
* Not derived: the IPFV and JUSS, whose prefixal templates the squib does not draw, and the
  PFV of √sma, where the final radical merges with the suffix vowel outside the template.

## References

* [faust-2026]
* [mccarthy-1981]
* [broselow-1984]
* [greenberg-1950]
* [leslau-1995]
* [lowenstamm-1996]
* [lowenstamm-2014]
* [goldsmith-1976]
-/

namespace Faust2026

open Morphology Data.Examples Autosegmental

variable {α : Type*}

/-! ### *Misalignment -/

/-- *Misalignment (2), (6b): some nonfinal root element is associated to the template-final
slot. -/
def Misaligned (m : TemplateMatch α) : Prop :=
  ∃ a ∈ m.associations,
    a.source = .root ∧ m.root.IsNonfinal a.melodyIndex ∧ m.template.isFinalSlot a.slotIndex

instance (m : TemplateMatch α) : Decidable (Misaligned m) :=
  inferInstanceAs (Decidable (∃ a ∈ m.associations, _))

theorem misaligned_append (m : TemplateMatch α) (l : List Association) :
    Misaligned { m with associations := m.associations ++ l } ↔
      Misaligned m ∨ ∃ a ∈ l, a.source = .root ∧ m.root.IsNonfinal a.melodyIndex ∧
        m.template.isFinalSlot a.slotIndex := by
  simp only [Misaligned, List.mem_append, or_and_right, exists_or]

/-- Lines from the affix tier never misalign the root: the intruder "is not a radical" ((8),
(10)). -/
theorem misaligned_append_affix (m : TemplateMatch α) (l : List Association)
    (h : ∀ a ∈ l, a.source = .affix) :
    Misaligned { m with associations := m.associations ++ l } ↔ Misaligned m := by
  rw [misaligned_append, or_iff_left]
  rintro ⟨a, ha, hr, -⟩
  exact absurd (h a ha) (by rw [hr]; decide)

/-! ### Segments, patterns, and association -/

/-- The classes the [+consonantal] specification of a C-slot separates. -/
inductive SegClass where
  | consonant
  | glide
  | vowel
  deriving DecidableEq, Repr

/-- The glide j and the nonconsonantal radicals a, i of the Amharic hollow roots (12c–e) are
barred from [+c] slots; every other segment is a consonant. -/
def segClass : String → SegClass
  | "j" => .glide
  | "a" | "i" => .vowel
  | _ => .consonant

/-- The mergers of two elements sharing a slot that the squib states: a glide joined to the
preceding consonant palatalizes it ((7), [fäʤʤ-ä]), and a nonconsonantal radical merges with
the vocalization, /a,ä/ yielding [a] and /i,ä/ yielding [e] (13). -/
def merge : String → String → String
  | "d", "j" => "ʤ"
  | "ä", "a" => "a"
  | "ä", "i" => "e"
  | x, _ => x

/-- The category of the base a template builds: gender markers are inherent inflection on n,
so only a nominal base merges with the feminine morph (11). -/
inductive Category where
  | noun
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- A template with its lexical shape: skeleton, category, vocalization and its lines,
segmental material outside the skeleton, and the parameters of the squib's derivations. -/
structure Pattern where
  /-- The skeleton. -/
  template : CVTemplate
  /-- The category of the base. -/
  category : Category
  /-- The vocalization and its association lines. -/
  vocalism : List String := []
  vocLines : List Association := []
  /-- Segmental material preceding and following the skeleton. -/
  pre : List String := []
  post : List String := []
  /-- A slot prespecified as geminate ({C C} in (7)). -/
  geminate : Option Nat := none
  /-- A barred glide joins the consonant on its left (Amharic (7)) rather than floating
  (Hebrew (4)). -/
  joinsGlide : Bool := false
  /-- An unsatisfied final syllable is deleted (7a). -/
  truncates : Bool := false

/-- One-to-one left-to-right association of the root with the C-slots, the final radical
spreading onto leftover slots ([mccarthy-1981]'s conventions, `McCarthy1981.associateLR`), plus
the pattern's vocalization lines. -/
def lines (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  { root := r, vocalism := p.vocalism, template := p.template,
    associations := McCarthy1981.associateLR .root r.arity p.template.cSlots ++ p.vocLines }

/-- `m.Admits a`: the slot's specification admits the segment — a [+c] slot hosts consonants
only ((4), (7), (13)), a plain C-slot anything but a vowel. -/
def Admits (m : TemplateMatch String) (a : Association) : Prop :=
  match m.template.slotAt a.slotIndex, m.segmentAt a with
  | some .Cspec, some x => segClass x = .consonant
  | some .C, some x => segClass x ≠ .vowel
  | _, _ => True

instance (m : TemplateMatch String) (a : Association) : Decidable (Admits m a) := by
  unfold Admits; split <;> infer_instance

/-- The root line on the immediate left of slot `i`. -/
def rootLeft (m : TemplateMatch String) (i : Nat) : Option Association :=
  (m.associations.filter λ a => a.source == .root && decide (a.slotIndex < i)).foldl
    (λ acc a => match acc with
      | none => some a
      | some b => if b.slotIndex < a.slotIndex then some a else some b) none

/-- The V-slots flanking slot `i`. -/
def flankingV (m : TemplateMatch String) (i : Nat) : List Nat :=
  [i - 1, i + 1].filter λ s => m.template.slotAt s = some .V

/-- The vocalization line at slot `s`. -/
def vocAt (m : TemplateMatch String) (s : Nat) : Option Association :=
  m.associations.find? λ a => a.source == .vocalism && a.slotIndex == s

/-- Where a barred root element goes. A glide joins the slot of the consonant on its left,
where the pattern's language does that ((7): Amharic, not Hebrew). A nonconsonantal radical
merges with the vocalization on the V-slots flanking its slot, the vocalization element
spreading to a flanking V-slot it did not occupy: the merger "occupies the two vocalic
positions around the C position" (13b–c). -/
def join (p : Pattern) (m : TemplateMatch String) (a : Association) : TemplateMatch String :=
  match (m.segmentAt a).map segClass with
  | some .glide =>
    if p.joinsGlide then
      match rootLeft m a.slotIndex with
      | some b =>
        { m with associations := m.associations ++ [⟨.root, a.melodyIndex, b.slotIndex⟩] }
      | none => m
    else m
  | some .vowel =>
    let vs := flankingV m a.slotIndex
    match vs.findSome? (vocAt m) with
    | some v =>
      { m with associations := m.associations ++ vs.map (λ s => ⟨.root, a.melodyIndex, s⟩) ++
          (vs.filter λ s => (vocAt m s).isNone).map λ s => ⟨.vocalism, v.melodyIndex, s⟩ }
    | none => m
  | _ => m

/-- Association under the slot specifications: the rejected lines are removed and their
elements joined or merged as the pattern's language allows. -/
def associate (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  let m := lines p r
  (m.associations.filter λ a => ¬ Admits m a).foldl (join p)
    { m with associations := m.associations.filter (Admits m ·) }

/-- Template satisfaction by spreading (1): each vacant C-slot receives the root element on
its immediate left. -/
def spread (m : TemplateMatch String) : TemplateMatch String :=
  { m with associations := m.associations ++ m.unfilledCSlots.filterMap λ s =>
      (rootLeft m s).map λ b => ⟨.root, b.melodyIndex, s⟩ }

/-! ### Intrusion -/

/-- The No-Crossing Constraint ([goldsmith-1976]) on the consonantal melody of a base merged
with a suffix: the suffix follows the root, so its consonant associates to the left of no root
line (13). -/
def NoCrossing (m : TemplateMatch String) : Prop :=
  ∀ a ∈ m.associations, ∀ b ∈ m.associations,
    a.source = .root → b.source = .affix → a.slotIndex ≤ b.slotIndex

instance (m : TemplateMatch String) : Decidable (NoCrossing m) :=
  inferInstanceAs (Decidable (∀ a ∈ m.associations, ∀ b ∈ m.associations, _))

/-- The consonantal melody of a base merged with a suffix, root elements then the suffix's, in
the coordinates of `Autosegmental.IsNonCrossing`. -/
def melodyLinks (m : TemplateMatch String) : Finset (Nat × Nat) :=
  m.links .root ∪ (m.links .affix).image λ p => (p.1 + m.root.arity, p.2)

/-- `NoCrossing` is the cross-tier part of the substrate's non-crossing condition on the merged
melody: the merged melody is non-crossing iff each tier is and no suffix line lies to the left
of a root line. -/
theorem isNonCrossing_melodyLinks_iff (m : TemplateMatch String)
    (hb : ∀ a ∈ m.associations, a.source = .root → a.melodyIndex < m.root.arity) :
    IsNonCrossing (melodyLinks m) ↔
      IsNonCrossing (m.links .root) ∧ IsNonCrossing (m.links .affix) ∧ NoCrossing m := by
  simp only [isNonCrossing_iff, melodyLinks, Finset.mem_union, Finset.mem_image, NoCrossing]
  constructor
  · intro h
    refine ⟨λ p hp q hq hlt => h p (Or.inl hp) q (Or.inl hq) hlt,
      λ p hp q hq hlt => h (p.1 + m.root.arity, p.2) (Or.inr ⟨p, hp, rfl⟩)
        (q.1 + m.root.arity, q.2) (Or.inr ⟨q, hq, rfl⟩) (by simpa using hlt),
      λ a ha b hb' has hbs => ?_⟩
    have hp := (m.mem_links (a.melodyIndex, a.slotIndex) .root).mpr ⟨a, ha, has, rfl, rfl⟩
    have hq := (m.mem_links (b.melodyIndex, b.slotIndex) .affix).mpr ⟨b, hb', hbs, rfl, rfl⟩
    have := hb a ha has
    exact h _ (Or.inl hp) _ (Or.inr ⟨_, hq, rfl⟩) (by simp; omega)
  · rintro ⟨hr, ha, hc⟩ l₁ hl₁ l₂ hl₂ hlt
    rcases hl₁ with hl₁ | ⟨p, hp, rfl⟩ <;> rcases hl₂ with hl₂ | ⟨q, hq, rfl⟩
    · exact hr _ hl₁ _ hl₂ hlt
    · obtain ⟨a, ha', has, h1, h2⟩ := (m.mem_links _ _).mp hl₁
      obtain ⟨b, hb', hbs, h3, h4⟩ := (m.mem_links _ _).mp hq
      simp only at h2 h4 ⊢
      rw [← h2, ← h4]
      exact hc a ha' b hb' has hbs
    · obtain ⟨a, ha', has, h1, -⟩ := (m.mem_links _ _).mp hl₂
      have := hb a ha' has
      simp only at hlt
      omega
    · exact ha p hp q hq (by simpa using hlt)

/-- The feminine morph √(a)t merged with the base, its consonant associated to slot `s`. -/
def intrudeAt (m : TemplateMatch String) (s : Nat) : TemplateMatch String :=
  { m with affix := ["t"], associations := m.associations ++ [⟨.affix, 0, s⟩] }

/-- Intrusion (10b–c): the morph's consonant associates from right to left, to the rightmost
vacant C-slot, provided its line crosses none of the root's; otherwise it floats (13b–c). -/
def intrude (m : TemplateMatch String) : TemplateMatch String :=
  match m.unfilledCSlots.getLast? with
  | some s => if NoCrossing (intrudeAt m s) then intrudeAt m s else { m with affix := ["t"] }
  | none => { m with affix := ["t"] }

theorem misaligned_intrudeAt (m : TemplateMatch String) (s : Nat) :
    Misaligned (intrudeAt m s) ↔ Misaligned m :=
  misaligned_append_affix m [⟨.affix, 0, s⟩] (by simp)

/-- Intrusion is template satisfaction without misalignment: the intruder never misaligns the
root ((8), (10)). -/
theorem misaligned_intrude (m : TemplateMatch String) : Misaligned (intrude m) ↔ Misaligned m := by
  unfold intrude
  split
  · split
    · exact misaligned_intrudeAt m _
    · exact Iff.rfl
  · exact Iff.rfl

/-- The intruder's line never crosses a root line. -/
theorem noCrossing_intrude (m : TemplateMatch String) (h : NoCrossing m) :
    NoCrossing (intrude m) := by
  unfold intrude
  split
  · split
    · assumption
    · exact h
  · exact h

/-- The derivation of a root in a pattern: association under the slot specifications, then,
for a nominal base whose template is unsatisfied, merger of the feminine morph ((10b), (11)). -/
def derive (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  let m := associate p r
  if p.category = .noun ∧ ¬ m.allCSlotsFilled then intrude m else m

/-- Only a nominal base merges with the feminine morph (11): a verbal or adjectival base is
realized as associated. -/
theorem derive_of_category_ne_noun (p : Pattern) (r : ConsonantalRoot String)
    (h : p.category ≠ .noun) : derive p r = associate p r := by
  simp [derive, h]

/-! ### Realization -/

/-- The segments a slot hosts: vocalization first, then root, then affix lines. -/
def hosted (m : TemplateMatch String) (s : Nat) : List String :=
  [AssocSource.vocalism, .root, .affix].flatMap λ src =>
    (m.associations.filter λ a => a.source == src && a.slotIndex == s).filterMap m.segmentAt

/-- The realization of a slot: the hosted segments merged onto the first. -/
def realizeSlot (m : TemplateMatch String) (s : Nat) : Option String :=
  match hosted m s with
  | [] => none
  | x :: xs => some (xs.foldl merge x)

/-- `collapses x l`: the V-slot realized `x` is followed by a vacant C-slot and a V-slot
realized the same. -/
def collapses (x : String) : List (CVSlot × Option String) → Bool
  | (c, none) :: (.V, some y) :: _ => c.IsC && x == y
  | _ => false

/-- The realized slots in order, V-slots around a vacant C-slot with the same realization
surfacing once: "the phonological length of these vowels is not translated to phonetic
length" (13). The flag records that the vowel has already been realized. -/
def collapse : Bool → List (CVSlot × Option String) → List String
  | _, [] => []
  | skip, (_, none) :: tl => collapse skip tl
  | true, (.V, some _) :: tl => collapse false tl
  | _, (s, some x) :: tl => x :: collapse (s == .V && collapses x tl) tl

/-- Truncation (7a): when the pattern truncates and the final C-slot is vacant, the final
syllable — that slot and the V-slot before it — is deleted. -/
def truncate (p : Pattern) (m : TemplateMatch String) : CVTemplate :=
  match m.unfilledCSlots.getLast?, m.template.cSlots.getLast? with
  | some s, some s' =>
    if p.truncates ∧ s = s' then ⟨m.template.slots.take (s - 1)⟩ else m.template
  | _, _ => m.template

/-- The surface segments of a match in a pattern: the realized slots, a filled prespecified
geminate slot counting twice ({C C} in (7)), between the pattern's outer material. -/
def realize (p : Pattern) (m : TemplateMatch String) : List String :=
  p.pre ++ collapse false ((truncate p m).slots.zipIdx.flatMap λ (c, i) =>
    let e := (c, realizeSlot m i)
    if p.geminate = some i ∧ e.2.isSome then [e, e] else [e]) ++ p.post

/-- The surface segments of a root in a pattern. -/
def surface (p : Pattern) (r : ConsonantalRoot String) : List String := realize p (derive p r)

/-- The surface form as characters, for comparison with a transcription. -/
def surfaceChars (p : Pattern) (r : ConsonantalRoot String) : List Char :=
  (surface p r).flatMap String.toList

/-! ### Modern Hebrew: the QaTaT–QaTa problem (3)–(4) and taQTiL (9)–(10) -/

/-- The PST.3MSG template CaCaC[+c] ((3)–(4)), vocalization a,a. -/
def hebrewPst : Pattern :=
  { template := ⟨[.C, .V, .C, .V, .Cspec]⟩, category := .verb, vocalism := ["a"],
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 3⟩] }

/-- The action-noun template QTiLa (3). -/
def hebrewQtila : Pattern :=
  { template := ⟨[.C, .C, .V, .C, .V]⟩, category := .noun, vocalism := ["i", "a"],
    vocLines := [⟨.vocalism, 0, 2⟩, ⟨.vocalism, 1, 4⟩] }

/-- The passive-participle template QaTuL (3). -/
def hebrewQatul : Pattern :=
  { template := ⟨[.C, .V, .C, .V, .C]⟩, category := .adjective, vocalism := ["a", "u"],
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 1, 3⟩] }

/-- The resultative nominal template taQTiL[+c] ((9)–(10)): its fixed ta precedes the
skeleton. -/
def hebrewTaqtil : Pattern :=
  { template := ⟨[.C, .C, .V, .Cspec]⟩, category := .noun, vocalism := ["i"],
    vocLines := [⟨.vocalism, 0, 2⟩], pre := ["ta"] }

/-- (3a–b), (1): √klt fills CaCaC[+c] radical by radical, and the biradical √kl satisfies it by
spreading its final l — QaTaT, never QaQaT — with no misalignment. -/
theorem klt_kl_satisfy :
    (derive hebrewPst Hebrew.klt).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst Hebrew.klt) ∧
    (derive hebrewPst Hebrew.kl).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst Hebrew.kl) ∧
    ⟨.root, 1, 4⟩ ∈ (derive hebrewPst Hebrew.kl).associations := by
  decide

/-- (4), (6): for √klj the [+c] final slot stays vacant; template satisfaction by spreading
would yield [kalal] with the nonfinal l template-final, which *Misalignment rules out. -/
theorem klj_spread_misaligned :
    (derive hebrewPst Hebrew.klj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive hebrewPst Hebrew.klj) ∧
    Misaligned (spread (derive hebrewPst Hebrew.klj)) ∧
    realize hebrewPst (spread (derive hebrewPst Hebrew.klj)) = ["k", "a", "l", "a", "l"] := by
  decide

/-- (3c): the final slots of QTiLa and QaTuL are unspecified, so j associates and surfaces. -/
theorem klj_qtila_qatul :
    (derive hebrewQtila Hebrew.klj).allCSlotsFilled ∧
    (derive hebrewQatul Hebrew.klj).allCSlotsFilled := by
  decide

/-- (10): √dmj leaves the [+c] final slot of taQTiL vacant and spreading would misalign; merged
with the feminine morph, whose t associates from the right, the template is satisfied without
misalignment. -/
theorem dmj_taqtil :
    (associate hebrewTaqtil Hebrew.dmj).unfilledCSlots = [3] ∧
    Misaligned (spread (associate hebrewTaqtil Hebrew.dmj)) ∧
    ⟨.affix, 0, 3⟩ ∈ (derive hebrewTaqtil Hebrew.dmj).associations ∧
    (derive hebrewTaqtil Hebrew.dmj).allCSlotsFilled ∧
    ¬ Misaligned (derive hebrewTaqtil Hebrew.dmj) := by
  decide

/-! ### Amharic: (5), (7)–(8), (12)–(13) -/

/-- The type A PFV.3MSG stem CäCCäC[+c] ((5), (7)): the medial C prespecified geminate, the
final slot [+c], the person suffix -ä outside; a barred glide joins the consonant on its left,
and an unsatisfied final syllable is truncated (7a). -/
def amharicPfv : Pattern :=
  { template := ⟨[.C, .V, .C, .V, .Cspec]⟩, category := .verb, vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 3⟩], post := ["-ä"], geminate := some 2,
    joinsGlide := true, truncates := true }

/-- The GRND stem CäCC[+c] with the subject suffix -o ((5), (8)). -/
def amharicGrnd : Pattern :=
  { template := ⟨[.C, .V, .C, .Cspec]⟩, category := .noun, vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 1⟩], post := ["-o"], joinsGlide := true }

/-- The INF: the prefix mä- and, in Strict CV terms (13), the skeleton CVC[+c]VC[+c] with ä on
the second V-slot. -/
def amharicInf : Pattern :=
  { template := ⟨[.C, .V, .Cspec, .V, .Cspec]⟩, category := .noun, vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 3⟩], pre := ["mä"], joinsGlide := true }

/-- (7): √fdj in the PFV — the barred j joins d at the geminate slot, the final slot stays
vacant, no misalignment; spreading d there would misalign. -/
theorem fdj_pfv :
    ⟨.root, 2, 2⟩ ∈ (derive amharicPfv Amharic.fdj).associations ∧
    (derive amharicPfv Amharic.fdj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive amharicPfv Amharic.fdj) ∧
    Misaligned (spread (derive amharicPfv Amharic.fdj)) := by
  decide

/-- √wd (5b): the biradical satisfies the PFV template by spreading its final d without
misalignment and is OCP-clean; [broselow-1984]'s √wdd is not. -/
theorem wd_pfv :
    (derive amharicPfv Amharic.wd).allCSlotsFilled ∧ ¬ Misaligned (derive amharicPfv Amharic.wd) ∧
    Amharic.wd.IsOCPClean ∧ ¬ (⟨["w", "d", "d"]⟩ : ConsonantalRoot String).IsOCPClean := by
  decide

/-- (8): in the GRND the intruder fills the vacant final slot, satisfying the template without
misalignment. -/
theorem fdj_grnd :
    ⟨.affix, 0, 3⟩ ∈ (derive amharicGrnd Amharic.fdj).associations ∧
    (derive amharicGrnd Amharic.fdj).allCSlotsFilled ∧
    ¬ Misaligned (derive amharicGrnd Amharic.fdj) := by
  decide

/-- (13): all three INF derivations leave a C-slot vacant, but the intruder associates only
in (13a), where the vacancy is final; in (13b–c) its line to the medial vacancy would cross the
final radical's, so it floats, and no representation is misaligned. -/
theorem inf_intrusion :
    (associate amharicInf Amharic.sma).unfilledCSlots = [4] ∧
    (associate amharicInf Amharic.sam).unfilledCSlots = [2] ∧
    (associate amharicInf Amharic.hid).unfilledCSlots = [2] ∧
    ⟨.affix, 0, 4⟩ ∈ (derive amharicInf Amharic.sma).associations ∧
    ¬ NoCrossing (intrudeAt (associate amharicInf Amharic.sam) 2) ∧
    ¬ NoCrossing (intrudeAt (associate amharicInf Amharic.hid) 2) ∧
    (derive amharicInf Amharic.sam).unfilledCSlots = [2] ∧
    (derive amharicInf Amharic.hid).unfilledCSlots = [2] ∧
    ¬ Misaligned (derive amharicInf Amharic.sam) ∧
    ¬ Misaligned (derive amharicInf Amharic.hid) := by
  decide

/-! ### The paradigms (3), (5), (12) and the nouns (9) -/

/-- The languages of the rows. -/
inductive Lang where
  | hebrew
  | amharic
  deriving DecidableEq, Repr

/-- The paradigm cells of (3), (5), (12). -/
inductive Cell where
  | pst3msg
  | actionNoun
  | passPrtc
  | pfv
  | ipfv
  | juss
  | grnd
  | inf
  deriving DecidableEq, Repr

/-- The pattern of a cell, for the cells the squib draws. -/
def Cell.pattern? : Cell → Option Pattern
  | .pst3msg => some hebrewPst
  | .actionNoun => some hebrewQtila
  | .passPrtc => some hebrewQatul
  | .pfv => some amharicPfv
  | .grnd => some amharicGrnd
  | .inf => some amharicInf
  | .ipfv | .juss => none

/-- The cells with a nominal base: the Amharic GRND and INF, whose subjects are marked as
possessors (§4.2), and the Hebrew action noun. -/
def Cell.IsNominal (c : Cell) : Prop := c.pattern?.map Pattern.category = some .noun

instance (c : Cell) : Decidable c.IsNominal := inferInstanceAs (Decidable (_ = _))

/-- A paradigm cell of a root. -/
structure Row where
  lang : Lang
  root : ConsonantalRoot String
  cell : Cell
  form : String
  deriving DecidableEq, Repr

/-- A taQTiL noun (9), with its root where the squib identifies it. -/
structure NounRow where
  form : String
  gender : Gender
  root : Option (ConsonantalRoot String)
  deriving DecidableEq, Repr

def langTable : List (String × Lang) := [("hebr1245", .hebrew), ("amha1245", .amharic)]

def rootTable : List (String × ConsonantalRoot String) :=
  [("klt", Hebrew.klt), ("kl", Hebrew.kl), ("klj", Hebrew.klj), ("dmj", Hebrew.dmj),
   ("glj", Hebrew.glj), ("rmj", Hebrew.rmj), ("skt", Hebrew.skt), ("sbr", Amharic.sbr),
   ("wd", Amharic.wd), ("fdj", Amharic.fdj), ("sma", Amharic.sma), ("sam", Amharic.sam),
   ("hid", Amharic.hid)]

def cellTable : List (String × Cell) :=
  [("pst3msg", .pst3msg), ("actionNoun", .actionNoun), ("passPrtc", .passPrtc), ("pfv", .pfv),
   ("ipfv", .ipfv), ("juss", .juss), ("grnd", .grnd), ("inf", .inf)]

def genderTable : List (String × Gender) := [("masculine", .masculine), ("feminine", .feminine)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let lang ← List.lookup ex.language langTable
  let root ← ex.parse? "root" rootTable
  let cell ← ex.parse? "cell" cellTable
  pure ⟨lang, root, cell, ex.primaryText⟩

def NounRow.ofExample (ex : LinguisticExample) : Option NounRow := do
  let gender ← ex.parse? "gender" genderTable
  pure ⟨ex.primaryText, gender, ex.parse? "root" rootTable⟩

theorem row_ofExample_isSome :
    ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome ∨ (NounRow.ofExample ex).isSome := by
  decide

def rows : List Row := Examples.all.filterMap Row.ofExample

def nounRows : List NounRow := Examples.all.filterMap NounRow.ofExample

/-- The surface form the pipeline derives for a row, where its cell has a pattern. -/
def Row.surface? (r : Row) : Option (List Char) := r.cell.pattern?.map (surfaceChars · r.root)

/-- The pipeline reproduces every cell of (3), (5), (12) that has a pattern, except the PFV
of √sma, where the final radical merges with the suffix vowel. -/
theorem rows_surface :
    ∀ r ∈ rows, r.cell.pattern?.isSome → (r.root, r.cell) ≠ (Amharic.sma, .pfv) →
      r.surface? = some r.form.toList := by
  decide

/-- (3): the final j of √klj surfaces in the action noun and the passive participle and not in
the PST.3MSG. -/
theorem j_surfaces :
    ∀ r ∈ rows, r.lang = .hebrew →
      ('j' ∈ r.form.toList ↔ r.root = Hebrew.klj ∧ r.cell ≠ .pst3msg) := by
  decide

/-- The root's final radical is barred from a [+c] slot: the glide of √klj and √fdj, the vowel
of √sma. -/
def BarredFinal (r : ConsonantalRoot String) : Prop :=
  match r.finalSegment with
  | some x => segClass x ≠ .consonant
  | none => False

instance (r : ConsonantalRoot String) : Decidable (BarredFinal r) := by
  unfold BarredFinal; split <;> infer_instance

/-- Across the Amharic paradigms (5) and (12), a nonradical [t] occurs exactly in the nominal
cells of the roots whose final radical is barred — the distribution [broselow-1984]'s default
consonant leaves unexplained (§2.2) and the suffix analysis derives (§4.2). -/
theorem intruder_distribution :
    ∀ r ∈ rows, r.lang = .amharic →
      ('t' ∈ r.form.toList ∧ "t" ∉ r.root.segments ↔ r.cell.IsNominal ∧ BarredFinal r.root) := by
  decide

/-- (9): a taQTiL noun whose last consonant is not [t] is masculine. -/
theorem masculine_of_not_t_final :
    ∀ r ∈ nounRows, r.form.toList.getLast? ≠ some 't' → r.gender = .masculine := by
  decide

/-- The taQTiL derivation of a noun's root reproduces the noun, and the noun is feminine iff
the derivation merged the feminine morph: [taskit] from t-final √skt is masculine, the nouns
from j-final roots feminine (9b). -/
def NounRow.Derived (r : NounRow) : Prop :=
  match r.root with
  | some ρ =>
    surfaceChars hebrewTaqtil ρ = r.form.toList ∧
      (r.gender = .feminine ↔ (derive hebrewTaqtil ρ).affix ≠ [])
  | none => True

instance (r : NounRow) : Decidable r.Derived := by
  unfold NounRow.Derived; split <;> infer_instance

theorem nounRows_derived : ∀ r ∈ nounRows, r.Derived := by decide

end Faust2026
