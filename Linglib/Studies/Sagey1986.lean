import Linglib.Phonology.Segmental.Geometry
import Linglib.Phonology.Autosegmental.Sharing
import Linglib.Phonology.Autosegmental.NonCrossing
import Linglib.Phonology.Subregular.LocalRewrite
import Linglib.Core.Order.Interval
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Sagey (1986) [sagey-1986]

The Representation of Features and Relations in Non-Linear Phonology.
PhD dissertation, Massachusetts Institute of Technology.

[sagey-1986] proposes a hierarchical feature geometry organized by
vocal tract articulator, establishing the labial, coronal, dorsal, and
soft palate nodes that are now standard in phonological theory
(`Phonology/Segmental/Geometry.lean`). The geometry predicts which
multiply-articulated (complex) segments are possible in human language
(`Phonology/Segmental/Geometry.lean`).

This study file formalizes Sagey-specific contributions that go beyond
the consensus geometry:

## Formalized contributions

1. **Major/minor articulator distinction** (Ch. 3): in complex segments,
   one articulator is major (determines degree of closure) and one is minor.

2. **Degree of closure as articulator-level property** (Ch. 3): [continuant]
   and [consonantal] describe the root-to-articulator relationship, not the
   segment as a whole. This allows different degrees of closure at
   different articulators within one segment (e.g., clicks).

3. **Soft palate independence** (Ch. 2): nasal assimilation (spreading
   the soft palate node) is structurally simpler than place assimilation
   (spreading the place node), explaining its cross-linguistic frequency.

4. **Empirical arguments**: Nupe labiovelars [k͡p]/[g͡b] as labio-dorsal
   complex segments with dorsal as major articulator.
-/

open Phonology (Segment Feature)
open Phonology.FeatureGeometry (GeomNode)
open Autosegmental (agreeAt)

namespace Autosegmental

/-! ### Interval-overlap semantics for association lines

[sagey-1986] §5.3 derives the ban on crossing association lines from
temporal precedence rather than stipulating it as a well-formedness condition.

The key move is choosing the right temporal relation for association lines.
Simultaneity (identity of time points) is too strong — it predicts that
contour segments and geminates are impossible, since two distinct elements
cannot both be identical to the same time point (§5.2.2). Overlap is the
correct relation: it is reflexive and symmetric but crucially NOT transitive
(`NonemptyInterval.overlaps_not_transitive`), which is what allows the NCC proof to
go through via a contradiction chain (§5.2.2, fn. 6).

The derivation (§5.3, p.294): if timing₁ ≺ timing₂ on the timing tier but
melody₂ ≺ melody₁ on the melody tier, the overlap requirements on valid
associations produce a chain melody₂.finish < melody₁.start ≤ timing₁.finish
< timing₂.start ≤ melody₂.finish — a contradiction. Crossing is therefore
logically impossible for valid associations.

This section formalizes the derivation using `NonemptyInterval` for
temporal intervals and its `precedes`/`overlaps` relations.
-/

section NoCrossing

variable {T : Type*} [LinearOrder T]


/-- A position on an autosegmental tier, occupying a temporal interval. -/
structure TierPosition (T : Type*) [LinearOrder T] where
  interval : NonemptyInterval T

/-- An association between a timing-tier position and a melody-tier position.
    An association line represents temporal overlap: the melody element is
    realized during the timing position's interval. -/
structure Association (T : Type*) [LinearOrder T] where
  timing : TierPosition T
  melody : TierPosition T

/-- Association validity: the timing and melody intervals must overlap.
    This is the phonetic grounding — an association line means the melodic
    content is realized during the timing slot. -/
def validAssociation (a : Association T) : Prop :=
  a.timing.interval.overlaps a.melody.interval

/-- **Simultaneity contradicts contours** ([sagey-1986] §5.2.2):
    if association required temporal identity (simultaneity), contour
    segments — two distinct melody elements F ≠ G associated to the same
    timing position x — would be impossible, since F = x and G = x
    imply F = G by transitivity. This is Sagey's negative argument for
    why association must be overlap, not identity. -/
theorem simultaneity_no_contours {T : Type*} (t m₁ m₂ : T)
    (h₁ : t = m₁) (h₂ : t = m₂) : m₁ = m₂ :=
  h₁.symm.trans h₂

/-- Two associations cross iff their timing positions are ordered one way
    but their melody positions are ordered the other way.
    Crossing(a₁, a₂) ≡ timing₁ ≺ timing₂ ∧ melody₂ ≺ melody₁. -/
def crosses (a₁ a₂ : Association T) : Prop :=
  a₁.timing.interval.precedes a₂.timing.interval ∧
  a₂.melody.interval.precedes a₁.melody.interval

/-- **No-Crossing Constraint** ([sagey-1986] §5.3, [goldsmith-1976]):
    Two valid associations cannot cross.

    If timing₁ ≺ timing₂, then timing₁.finish < timing₂.start.
    Validity requires timing₁ overlaps melody₁ and timing₂ overlaps melody₂.
    If melodies also cross (melody₂ ≺ melody₁), then melody₂.finish < melody₁.start.

    From timing₁ overlaps melody₁: melody₁.start ≤ timing₁.finish.
    From timing₂ overlaps melody₂: timing₂.start ≤ melody₂.finish.

    Chaining: melody₂.finish < melody₁.start ≤ timing₁.finish < timing₂.start ≤ melody₂.finish.
    This gives melody₂.finish < melody₂.finish — a contradiction. -/
theorem no_crossing (a₁ a₂ : Association T)
    (h₁ : validAssociation a₁) (h₂ : validAssociation a₂) :
    ¬ crosses a₁ a₂ := by
  intro ⟨htime, hmelody⟩
  -- Unpack definitions
  simp only [NonemptyInterval.precedes] at htime hmelody
  simp only [validAssociation, NonemptyInterval.overlaps] at h₁ h₂
  obtain ⟨h₁_tm, h₁_mt⟩ := h₁
  obtain ⟨h₂_tm, h₂_mt⟩ := h₂
  -- Chain: melody₂.finish < melody₁.start ≤ timing₁.finish < timing₂.start ≤ melody₂.finish
  have : a₂.melody.interval.snd < a₂.melody.interval.snd :=
    calc a₂.melody.interval.snd
        < a₁.melody.interval.fst := hmelody
      _ ≤ a₁.timing.interval.snd := h₁_mt
      _ < a₂.timing.interval.fst := htime
      _ ≤ a₂.melody.interval.snd := h₂_tm
  exact lt_irrefl _ this

/-- Crossing is also impossible in the symmetric direction: if timing₂ ≺ timing₁
    and melody₁ ≺ melody₂, the same contradiction arises. -/
theorem no_crossing_symm (a₁ a₂ : Association T)
    (h₁ : validAssociation a₁) (h₂ : validAssociation a₂) :
    ¬ crosses a₂ a₁ :=
  no_crossing a₂ a₁ h₂ h₁

/-! ### Set-level No-Crossing Constraint -/

namespace Association

/-- A set of associations satisfies the **No-Crossing Constraint** iff no two
    associations in the set cross. Expressed via mathlib's `Set.Pairwise`. -/
def IsNoCrossing (associations : Set (Association T)) : Prop :=
  associations.Pairwise (fun a₁ a₂ => ¬ crosses a₁ a₂)

/-- **Set-level lift of `no_crossing`**: any set of valid associations
    automatically satisfies the No-Crossing Constraint. -/
theorem IsNoCrossing.of_all_valid {associations : Set (Association T)}
    (hValid : ∀ a ∈ associations, validAssociation a) :
    IsNoCrossing associations :=
  fun a₁ ha₁ a₂ ha₂ _ => no_crossing a₁ a₂ (hValid a₁ ha₁) (hValid a₂ ha₂)

/-- A subset of a no-crossing association set is no-crossing.
    Inherited from `Set.Pairwise.mono`. -/
theorem IsNoCrossing.subset {s t : Set (Association T)} (hst : s ⊆ t)
    (h : IsNoCrossing t) : IsNoCrossing s :=
  Set.Pairwise.mono hst h

end Association

/-! ### Grounding the combinatorial No-Crossing Constraint

[goldsmith-1976]'s index-level NCC (`IsNonCrossing` over `Finset (ℕ × ℕ)` in
`Autosegmental/NonCrossing.lean`) is *stipulated* as the filter on autosegmental
GEN. [sagey-1986] §5.4 argues it should instead be *derived* from the
temporal-overlap semantics of association lines (§5.3). This section makes the
derivation load-bearing: an order-respecting assignment of time intervals to
tier positions turns an index-level crossing into a Sagey `crosses`, which
`no_crossing` rules out. The combinatorial filter is thus the discrete shadow
of the temporal derivation, not an independent axiom. -/

/-- An interval realization of the two tiers: time intervals for lower-tier
    (timing) positions and upper-tier (melody) positions, each respecting tier
    index order as temporal precedence. -/
structure TierRealization (T : Type*) [LinearOrder T] where
  tim : ℕ → NonemptyInterval T
  mel : ℕ → NonemptyInterval T
  tim_mono : ∀ {i j : ℕ}, i < j → (tim i).precedes (tim j)
  mel_mono : ∀ {k l : ℕ}, k < l → (mel k).precedes (mel l)

/-- The association realizing the index link `(k, i)`: upper-tier position `k`
    linked to lower-tier position `i`. -/
def TierRealization.assoc (R : TierRealization T) (k i : ℕ) : Association T :=
  ⟨⟨R.tim i⟩, ⟨R.mel k⟩⟩

/-- **The combinatorial NCC is derived, not stipulated.** If every link in a set
    is realized as a *valid* (temporally overlapping) association under some
    order-respecting interval assignment, the set automatically satisfies
    [goldsmith-1976]'s index-level No-Crossing Constraint. The stipulated GEN
    filter (`IsNonCrossing`) is exactly the discrete shadow of [sagey-1986]'s
    overlap derivation (`no_crossing`): a crossing pair of links would realize
    two associations that cross, which cannot both overlap-validly. -/
theorem isNonCrossing_of_validRealization (R : TierRealization T)
    {links : Finset (ℕ × ℕ)}
    (hValid : ∀ p ∈ links, validAssociation (R.assoc p.1 p.2)) :
    IsNonCrossing links := by
  rw [isNonCrossing_iff]
  intro l₁ hl₁ l₂ hl₂ hlt
  by_contra hgt
  push_neg at hgt
  exact no_crossing (R.assoc l₂.1 l₂.2) (R.assoc l₁.1 l₁.2)
    (hValid l₂ hl₂) (hValid l₁ hl₁) ⟨R.tim_mono hgt, R.mel_mono hlt⟩

/-- Witness that the grounding hypothesis is non-vacuous: over `ℤ`, tier
    position `n` occupies the unit interval `[2n, 2n+1]`, so index order is
    realized as temporal precedence (consecutive positions are disjoint and
    ordered). -/
def TierRealization.canonical : TierRealization ℤ where
  tim n := ⟨⟨2 * (n : ℤ), 2 * (n : ℤ) + 1⟩, by omega⟩
  mel n := ⟨⟨2 * (n : ℤ), 2 * (n : ℤ) + 1⟩, by omega⟩
  tim_mono h := by simp only [NonemptyInterval.precedes]; omega
  mel_mono h := by simp only [NonemptyInterval.precedes]; omega

/-- Under the canonical realization every diagonal link `(n, n)` is valid — a
    position overlaps itself — so the grounding theorem's hypothesis is
    satisfiable (any diagonal link set is `IsNonCrossing` through it), not
    vacuously true. -/
theorem canonical_diagonal_valid (n : ℕ) :
    validAssociation (TierRealization.canonical.assoc n n) := by
  simp only [validAssociation, TierRealization.canonical, TierRealization.assoc,
    NonemptyInterval.overlaps]
  omega

/-! ### Concrete demonstrations -/

/-- Helper: build an interval from start and finish with a proof of validity. -/
private def mkInterval (s f : T) (h : s ≤ f) : NonemptyInterval T := ⟨⟨s, f⟩, h⟩

/-- A geminate consonant: two adjacent timing positions associated to a single
    melodic element. The melodic element's interval spans both timing slots.

    Example: /t/ linked to two C-slots in [atta].

    ```
    C-tier:    C₁    C₂
                \  /
    melody:     t
    ``` -/
def geminate (t1s t1f t2s t2f ms mf : T)
    (h1 : t1s ≤ t1f) (h2 : t2s ≤ t2f) (hm : ms ≤ mf)
    : Association T × Association T :=
  ( ⟨⟨mkInterval t1s t1f h1⟩, ⟨mkInterval ms mf hm⟩⟩,
    ⟨⟨mkInterval t2s t2f h2⟩, ⟨mkInterval ms mf hm⟩⟩ )

/-- A contour tone: one timing position associated to two tonal elements
    sequenced within it. The two tonal elements occupy sub-intervals.

    Example: falling tone HL on a single syllable.

    ```
    timing:     σ
               / \
    tone:     H   L
    ``` -/
def contourTone (ts tf m1s m1f m2s m2f : T)
    (ht : ts ≤ tf) (hm1 : m1s ≤ m1f) (hm2 : m2s ≤ m2f)
    : Association T × Association T :=
  ( ⟨⟨mkInterval ts tf ht⟩, ⟨mkInterval m1s m1f hm1⟩⟩,
    ⟨⟨mkInterval ts tf ht⟩, ⟨mkInterval m2s m2f hm2⟩⟩ )

end NoCrossing

end Autosegmental

namespace Sagey1986

-- ============================================================================
-- § 1: Major/Minor Articulator Distinction (Ch. 3)
-- ============================================================================

/-- When a complex segment's two articulations **differ in degree of closure**,
    one articulator is **major** — it receives the segment's lexical
    degree-of-closure specification — and the other **minor**, its degree of
    closure predictable ([sagey-1986] §3.3, p.217). Majorness is lexically
    marked, not reducible to anterior/posterior order. This distinction is
    Sagey-specific — modern phonology does not uniformly adopt it. -/
structure MajorMinor where
  major : GeomNode
  minor : GeomNode
  major_is_articulator : major.IsArticulator
  minor_is_articulator : minor.IsArticulator
  distinct : major ≠ minor

/-- Margi labiocoronal /ps/: the **coronal** articulation is major, the labial
    minor — even though coronal is the *more posterior* of the two
    ([sagey-1986] §3.4, p.258, where Sagey contrasts it with Kinyarwanda [skw],
    also coronal-major). The point is that majorness cannot be read off
    articulator order; it must be lexically marked.

    Nupe /k͡p/ is deliberately *not* the example here: Sagey shows that in /k͡p/
    **both** labial and dorsal are major — they share a degree of closure (both
    stops) — so it is symmetric, not an asymmetric major/minor segment
    ([sagey-1986] §3.3, p.217). -/
def margi_ps_articulation : MajorMinor where
  major := .coronal
  minor := .labial
  major_is_articulator := by decide
  minor_is_articulator := by decide
  distinct := by decide

-- ============================================================================
-- § 2: Degree of Closure as Articulator-Level Property (Ch. 3)
-- ============================================================================

/-- Sagey's degree of closure: a property of an articulator node, not a
    terminal feature. This is the Sagey-specific treatment; the modern
    geometry encodes closure as [±continuant] at the supralaryngeal node. -/
inductive DegreeOfClosure where
  | stop        -- complete closure
  | fricative   -- narrow constriction
  | approximant -- open constriction
  deriving DecidableEq, Repr

/-- An articulator paired with its degree of closure: degree of closure is a
    property of an articulator node, not the whole segment. In a !Xõ click both
    the coronal (anterior) and dorsal (velar) closures are stops, but only the
    major one — the velar — carries the segment's lexical degree-of-closure
    specification; the anterior closure's is predictable ([sagey-1986] §3.4,
    p.258). -/
structure ArticulatorSpec where
  node : GeomNode
  closure : DegreeOfClosure
  node_is_articulator : node.IsArticulator = true

/-- A click's anterior closure (coronal, full stop). -/
def click_anterior : ArticulatorSpec where
  node := .coronal
  closure := .stop
  node_is_articulator := by decide

/-- A click's posterior closure (dorsal, full stop). -/
def click_posterior : ArticulatorSpec where
  node := .dorsal
  closure := .stop
  node_is_articulator := by decide

-- ============================================================================
-- § 3: Soft Palate Independence (Ch. 2)
-- ============================================================================

/-- Nasal assimilation spreads the soft palate node (1 feature), while
    place assimilation spreads the place node (14 features). The soft
    palate's independence from place explains why nasal assimilation is
    cross-linguistically simpler and more common than place assimilation:
    it involves spreading a smaller constituent. -/
theorem nasal_assimilation_scope :
    GeomNode.softPalate.features.length < GeomNode.place.features.length := by
  decide

/-- Nasality is NOT under the place node — spreading place does not
    spread nasality. This is Sagey's core structural argument for the
    soft palate node as a separate constituent. -/
theorem nasal_not_under_place :
    ¬ Feature.nasal.DominatedBy .place := by decide

/-- Nasality IS under supralaryngeal (via the soft palate node), so
    total assimilation (spreading supralaryngeal) does spread nasality. -/
theorem nasal_under_supralaryngeal :
    Feature.nasal.DominatedBy .supralaryngeal := by decide

-- ============================================================================
-- § 4: Nupe Labiovelars
-- ============================================================================

/-- A Nupe labiovelar stop /k͡p/: specified for both labial and dorsal,
    voiceless, non-continuant. -/
def nupe_kp_segment : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.labial, true), (.dorsal, true)]

/-- The Nupe /k͡p/ is a complex segment (two active place articulators). -/
theorem nupe_kp_is_complex : Segment.IsComplex nupe_kp_segment := by decide

/-- The Nupe /k͡p/ is well-formed: its active articulators (labial, dorsal) are
    distinct — an instance of the by-construction guarantee. -/
theorem nupe_kp_wf : nupe_kp_segment.activeArticulators.Nodup :=
  Segment.activeArticulators_nodup _

/-- A simple /p/ (labial only) is not complex. -/
def simple_p : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.labial, true)]

theorem simple_p_not_complex : ¬ Segment.IsComplex simple_p := by decide

/-- A velar nasal /ŋ/ is NOT complex despite activating both the dorsal
    articulator and the soft palate (velum lowering). The soft palate
    is structurally independent of place, so nasal + place combinations
    are simple segments — this is Sagey's core argument for the soft
    palate node's independence. -/
def velar_nasal : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, true), (.continuant, false),
     (.nasal, true), (.voice, true), (.dorsal, true)]

theorem velar_nasal_not_complex : ¬ Segment.IsComplex velar_nasal := by decide

/-- The velar nasal is well-formed (only one place articulator: dorsal), its
    active articulators trivially distinct. -/
theorem velar_nasal_wf : velar_nasal.activeArticulators.Nodup :=
  Segment.activeArticulators_nodup _

-- ============================================================================
-- § 5: Impossible Complex Segments (Ch. 2)
-- ============================================================================

/-- A coronal-only segment (alveolar /t/, [+cor, +ant]) is NOT complex:
    multiple coronal features fall under the single coronal articulator. This
    formalizes Sagey's key prediction (§2.2): complex segments are possible
    only for combinations of two *different* articulators, so no combination of
    features under a single articulator yields a complex segment. The
    same-articulator bar is exactly why alveolars and alveopalatals — both
    coronal — cannot form a doubly-articulated stop ([sagey-1986] §2.2, p.64). -/
def alveolar_t : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.coronal, true), (.anterior, true)]

theorem alveolar_not_complex : ¬ Segment.IsComplex alveolar_t := by decide

/-- An alveopalatal (postalveolar) is [+cor, −ant, +dist] — still just
    one articulator (coronal), so not complex. An alveolar-alveopalatal
    doubly-articulated stop is therefore impossible: both articulations
    use the coronal articulator ([sagey-1986] §2.2). -/
def alveopalatal : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.coronal, true), (.anterior, false),
     (.distributed, true)]

theorem alveopalatal_not_complex : ¬ Segment.IsComplex alveopalatal := by decide

-- ============================================================================
-- § 6: No-Crossing Constraint (Ch. 5)
-- ============================================================================

/-! ### Temporal derivation of the No-Crossing Constraint

[sagey-1986] Ch. 5 derives the ban on crossing association lines from
temporal precedence. This section demonstrates the derived constraint with
concrete integer-valued time instances. -/

section NoCrossing

open Autosegmental (Association TierPosition
  validAssociation crosses no_crossing)

/-- Helper: build a ℤ interval. -/
private def mkI (s f : ℤ) (h : s ≤ f := by omega) : NonemptyInterval ℤ := ⟨⟨s, f⟩, h⟩

/-- Helper: build an association from four ℤ values. -/
private def mkAssoc (ts tf ms mf : ℤ) (ht : ts ≤ tf := by omega) (hm : ms ≤ mf := by omega)
    : Association ℤ :=
  ⟨⟨⟨⟨ts, tf⟩, ht⟩⟩, ⟨⟨⟨ms, mf⟩, hm⟩⟩⟩

/-- A concrete geminate /t:/ occupying timing slots [0,1] and [2,3],
    with the melodic element spanning [0,3]. -/
def geminate_tt : Association ℤ × Association ℤ :=
  (mkAssoc 0 1 0 3, mkAssoc 2 3 0 3)

/-- Both associations in the geminate are valid (timing overlaps melody). -/
theorem geminate_tt_valid :
    validAssociation geminate_tt.1 ∧ validAssociation geminate_tt.2 := by
  simp only [geminate_tt, mkAssoc, validAssociation, NonemptyInterval.overlaps]
  omega

/-- A concrete falling contour tone: timing [0,4], H tone [0,2], L tone [2,4]. -/
def contour_HL : Association ℤ × Association ℤ :=
  (mkAssoc 0 4 0 2, mkAssoc 0 4 2 4)

/-- Both associations in the contour tone are valid. -/
theorem contour_HL_valid :
    validAssociation contour_HL.1 ∧ validAssociation contour_HL.2 := by
  simp only [contour_HL, mkAssoc, validAssociation, NonemptyInterval.overlaps]
  omega

/-- **Crossing forces invalidity** ([sagey-1986] §5.3):
    a crossing configuration — timing₁ at [0,1] → melody₁ at [4,5],
    timing₂ at [2,3] → melody₂ at [0,1] — has its timing positions
    correctly ordered and melody positions reversed, but the first
    association is invalid because timing [0,1] does not overlap
    melody [4,5]. This demonstrates the mechanism: crossing is
    impossible not because it's stipulated, but because validity
    (temporal overlap) cannot be satisfied for both associations
    simultaneously when they cross. -/
theorem crossing_forces_invalidity :
    let a₁ := mkAssoc 0 1 4 5
    let a₂ := mkAssoc 2 3 0 1
    crosses a₁ a₂ ∧ ¬ validAssociation a₁ := by
  simp only [mkAssoc, crosses, validAssociation,
    NonemptyInterval.precedes, NonemptyInterval.overlaps]
  omega

end NoCrossing

end Sagey1986
