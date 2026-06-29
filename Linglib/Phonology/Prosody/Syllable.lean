import Linglib.Phonology.Prosody.Mora

/-!
# Syllables
[hayes-1989] [hyman-1985] [selkirk-1982] [clements-1990]

The syllable (σ) — the level above the mora in the prosodic hierarchy: a headed
**moraic** constituent ([hayes-1989]; [hyman-1985]). A non-moraic `onset` sits over a
moraic spine whose **head is the nucleus** — the sonority peak ([clements-1990]; the
"nucleus = head of σ" reading follows dependency/government phonology).
The nucleus mora is mandatory and structurally **initial** (a σ has ≥1 mora by
construction; there is no head-direction parameter — unlike the foot); `tail` carries
any further nuclear morae (long vowels) and a moraic coda.

The moraic structure is the **carrier** (weight is mora-based and load-bearing, so —
unlike the foot — the tree and onset-rime are secondary). The rival **onset-rime**
theory ([selkirk-1982]) is a re-representation (`toOnsetRime`), proved to agree with the
moraic carrier on weight; the segment string is the `yield`.

## Main definitions

* `Syllable` — a headed moraic σ: `onset`, a nucleus `head` mora, and a `tail` of morae.
* `Syllable.morae` / `nucleusMora` / `nucleusSegments` / `weight` / `moraCount`.
* `Syllable.IsHeavy` / `IsLight` — the weight inventory (sonority/SSP well-formedness is
  a syllabification follow-up).
* `Syllable.ofCV` / `mk'` — smart constructors (a non-empty nucleus is required).
* `Syllable.yield` / `toOnsetRime` — re-representations; `toOnsetRime_weight` is the
  weight-correspondence between the moraic and onset-rime theories.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/`.superheavy`.
-/

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- σ — a headed moraic syllable ([hayes-1989]): a non-moraic `onset`, a nucleus `head`
    mora (the sonority peak; mandatory, so σ has ≥1 mora and the head is initial by
    construction), and a `tail` of further morae (long-vowel morae + a moraic coda). -/
structure Syllable where
  onset : List Segment
  head  : Mora
  tail  : List Mora
  deriving DecidableEq

namespace Syllable

/-- Syllable weight is just the mora count — there is no separate weight type.
    `.light` (1μ), `.heavy` (2μ), `.superheavy` (3μ) name the common values for
    readable weight profiles in metrical and accentual computations. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The moraic spine, nucleus (peak) first. -/
def morae (σ : Syllable) : List Mora := σ.head :: σ.tail

/-- The nucleus — the head mora (the sonority peak). -/
abbrev nucleusMora (σ : Syllable) : Mora := σ.head

/-- The nucleus segment(s). -/
def nucleusSegments (σ : Syllable) : List Segment := σ.head.dominates

/-- The number of morae — the syllable's weight. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The syllable's weight (= its mora count). -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

/-- A heavy syllable: at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A light syllable: exactly one mora. -/
def IsLight (σ : Syllable) : Prop := σ.weight = Weight.light

instance (σ : Syllable) : Decidable σ.IsHeavy := by unfold IsHeavy; infer_instance
instance (σ : Syllable) : Decidable σ.IsLight := by unfold IsLight; infer_instance

/-- Build a syllable from an explicit nucleus mora (+ optional further/coda morae). -/
def mk' (onset : List Segment) (nucleus : Mora) (coda : List Mora := []) : Syllable :=
  ⟨onset, nucleus, coda⟩

/-- Build a syllable from an onset and a non-empty mora spine (nucleus = first mora). -/
def ofMorae (onset : List Segment) (ms : List Mora) (h : ms ≠ [] := by simp) : Syllable :=
  ⟨onset, ms.head h, ms.tail⟩

/-- Build a syllable from a segmental onset–nucleus–coda string. Each nucleus segment
    projects a mora (the first is the nucleus head); a coda segment projects its own
    mora iff Weight-by-Position is active ([hayes-1989]), else it rides the last nucleus
    mora (a non-moraic coda). A non-empty nucleus is required. -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true)
    (hn : nucleus ≠ [] := by simp) : Syllable :=
  match nucleus, hn with
  | [], h => (h rfl).elim
  | n₀ :: ns, _ =>
    if wbp then ⟨onset, Mora.of n₀, ns.map Mora.of ++ coda.map Mora.of⟩
    else match (ns.map Mora.of).reverse with
      | last :: rest => ⟨onset, Mora.of n₀, rest.reverse ++ [last.attach coda]⟩
      | []           => ⟨onset, (Mora.of n₀).attach coda, []⟩

/-- The segment string (yield) of a syllable: onset followed by the moraic melody. -/
def yield (σ : Syllable) : List Segment := σ.onset ++ σ.morae.flatMap (·.dominates)

/-! ### Moraic operations (stranding and re-licensing)

The moraic-syllabification operations of [hayes-1989]: segment deletion strands a μ
(an empty prosodic position), which is then re-licensed by re-association ([ito-1986]'s
Prosodic Licensing) or else erased. This is the mechanism of compensatory lengthening —
"CL" the phenomenon is a *composition* of these operations, documented per-language in
`Studies/Hayes1989`. Mora count is conserved by construction (the μ survives deletion). -/

/-- Delete the segment under mora `i`, leaving the μ **stranded** (it survives,
    dominating nothing) — the engine of compensatory lengthening. -/
def strand (σ : Syllable) (i : Nat) : Syllable :=
  match i with
  | 0     => ⟨σ.onset, Mora.stranded, σ.tail⟩
  | i + 1 => ⟨σ.onset, σ.head, σ.tail.set i Mora.stranded⟩

/-- Delete an onset segment. Onsets are non-moraic, so this strands no μ — the
    onset-deletion asymmetry: it cannot feed compensatory lengthening ([hayes-1989]). -/
def deleteOnset (σ : Syllable) (i : Nat) : Syllable :=
  { σ with onset := σ.onset.eraseIdx i }

/-- The number of stranded (segmentally unaffiliated) morae. -/
def strandedCount (σ : Syllable) : Nat := σ.morae.countP (fun μ => decide μ.IsStranded)

private def relink : List Segment → List Mora → List Mora
  | _,   []      => []
  | mel, μ :: ms =>
    if μ.dominates.isEmpty then ⟨mel⟩ :: relink mel ms
    else μ :: relink μ.dominates ms

private theorem relink_length (mel : List Segment) (ms : List Mora) :
    (relink mel ms).length = ms.length := by
  induction ms generalizing mel with
  | nil => rfl
  | cons μ ms ih => simp only [relink]; split <;> simp [ih]

private theorem relink_ne_nil (mel : List Segment) {ms : List Mora} (h : ms ≠ []) :
    relink mel ms ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, relink_length]
  exact List.length_pos_iff_ne_nil.mpr h

private def rebuild (σ : Syllable) (ms : List Mora) (h : ms ≠ []) : Syllable :=
  ⟨σ.onset, ms.head h, ms.tail⟩

private theorem rebuild_morae (σ : Syllable) (ms : List Mora) (h : ms ≠ []) :
    (rebuild σ ms h).morae = ms := by simp [rebuild, morae]

/-- **Tautosyllabic re-licensing** ([ito-1986]): re-associate σ's stranded morae to the
    nucleus, within σ. Length-preserving on the spine, so weight is conserved. -/
def relicense (σ : Syllable) : Syllable :=
  rebuild σ (relink [] σ.morae) (relink_ne_nil [] (by simp [morae]))

/-- **Heterosyllabic re-licensing** (Parasitic Delinking, [hayes-1989]): a stranded
    nucleus μ delinks — the syllable, now nucleus-less, is deleted (`none`), and its μ
    migrates onto the preceding `host`'s nucleus, lengthening it (the host vowel spans
    two morae). A no-op if the target's nucleus is not stranded. -/
def relicenseLeft (host target : Syllable) : Syllable × Option Syllable :=
  if target.head.IsStranded ∧ target.tail = [] then
    (⟨host.onset, host.head, host.tail ++ [⟨host.head.dominates⟩]⟩, none)
  else (host, some target)

/-! Mora conservation, by construction. -/

theorem strand_moraCount (σ : Syllable) (i : Nat) :
    (strand σ i).moraCount = σ.moraCount := by
  cases i with
  | zero => rfl
  | succ n => simp [strand, moraCount, morae, List.length_set]

theorem deleteOnset_moraCount (σ : Syllable) (i : Nat) :
    (deleteOnset σ i).moraCount = σ.moraCount := rfl

/-- The onset-deletion asymmetry ([hayes-1989]): deleting an onset strands no μ. -/
theorem deleteOnset_strandedCount (σ : Syllable) (i : Nat) :
    (deleteOnset σ i).strandedCount = σ.strandedCount := rfl

theorem relicense_moraCount (σ : Syllable) :
    σ.relicense.moraCount = σ.moraCount := by
  simp only [Syllable.moraCount, relicense, rebuild_morae, relink_length]

/-- Heterosyllabic re-licensing conserves the total mora count across the boundary:
    the migrated μ leaves the (deleted) target and is gained by the host. -/
theorem relicenseLeft_conserves (host target : Syllable)
    (h : target.head.IsStranded) (hmono : target.tail = []) :
    (host.relicenseLeft target).1.moraCount
      + ((host.relicenseLeft target).2.map Syllable.moraCount).getD 0
      = host.moraCount + target.moraCount := by
  unfold relicenseLeft
  rw [if_pos ⟨h, hmono⟩]
  simp [moraCount, morae, hmono, List.length_append]

end Syllable

/-! ### Onset-rime re-representation -/

/-- The onset-rime structure ([selkirk-1982]): a rival theory of σ structure, an onset
    over a rime. Here a re-representation of the canonical moraic `Syllable`. -/
structure OnsetRime where
  onset : List Segment
  rime  : List Mora
  deriving DecidableEq

/-- σ → onset-rime: the rime is the moraic spine ([selkirk-1982]). -/
def Syllable.toOnsetRime (σ : Syllable) : OnsetRime := ⟨σ.onset, σ.morae⟩

/-- **Weight correspondence**: the onset-rime rime's mora count equals σ's weight — the
    moraic and onset-rime theories agree on weight ([selkirk-1982]; [hayes-1989]). -/
theorem Syllable.toOnsetRime_weight (σ : Syllable) :
    σ.toOnsetRime.rime.length = σ.moraCount := rfl

/-! ### Yield -/

/-- A **yield**: the terminal σ-weight string of a prosodic structure — the
    unparsed input, or the leaves of a prosodic `Tree`. Distinct from the prosodic
    word ω (`Prosody.Word`), which is a *headed constituent*: a yield is just the
    weight profile, with no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of fully-moraified syllables — the σ → yield bridge. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- Total mora count (each weight *is* a mora count). -/
def moraCount (y : Yield) : Nat := y.sum

/-- The minimal-word *size* constraint ([mccarthy-prince-1993]): at least
    `minMorae` morae (default 2, the moraic-trochee minimum). The *structural*
    minimal word — that an ω properly contains a foot — is `Word.feet_ne_nil`. -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

end Prosody
