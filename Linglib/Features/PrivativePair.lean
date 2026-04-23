/-!
# Privative Feature Pairs
@cite{harbour-2016}

A neutral abstraction over pairs of privative features with containment:
the inner feature entails the outer feature ([+inner] → [+outer]).

This pattern recurs across the two φ-feature domains established in
@cite{harbour-2016}:

- **Person**: [±author] (inner) ⊂ [±participant] (outer)
- **Number**: [±atomic] (inner) ⊂ [±minimal] (outer)

In each case, the containment constraint rules out one of the four
Boolean combinations, yielding exactly **three** well-formed cells:

| outer | inner | Status         | Person      | Number   |
|-------|-------|----------------|-------------|----------|
|   +   |   +   | most specified | 1st person  | singular |
|   +   |   −   | intermediate   | 2nd person  | dual     |
|   −   |   −   | least specified| 3rd person  | plural   |
|   −   |   +   | **ill-formed** | —           | —        |

@cite{harbour-2016} calls this shared skeleton the **phi kernel**: the
same formal mechanism generates the partition structure of both person
and number.

-/

namespace Features

-- ============================================================================
-- § 1: The Privative Pair
-- ============================================================================

/-- A pair of privative features with a containment relation.

    `inner` entails `outer`: bearing the inner feature requires
    bearing the outer feature. The four Boolean combinations reduce
    to three well-formed cells:

    - `⟨true, true⟩`  — [+outer, +inner] (most specified)
    - `⟨true, false⟩` — [+outer, −inner] (intermediate)
    - `⟨false, false⟩` — [−outer, −inner] (least specified)

    The fourth combination `⟨false, true⟩` ([−outer, +inner])
    violates containment.

    Instances:
    - `Features.Person.Features`: outer = hasParticipant, inner = hasAuthor
    - `Features.Number.Features`: outer = isMinimal, inner = isAtomic -/
structure PrivativePair where
  /-- The entailed (outer) feature. -/
  outer : Bool
  /-- The entailing (inner) feature — implies `outer`. -/
  inner : Bool
  deriving DecidableEq, Repr, Inhabited, BEq

-- ============================================================================
-- § 2: Well-Formedness
-- ============================================================================

/-- Well-formedness: [+inner] → [+outer].
    The inner feature entails the outer feature. -/
def PrivativePair.wellFormed (p : PrivativePair) : Bool :=
  !p.inner || p.outer

-- ============================================================================
-- § 3: Canonical Cells
-- ============================================================================

/-- Most specified cell: [+outer, +inner].
    Person: 1st (speaker). Number: singular (atom). -/
def PrivativePair.maximal : PrivativePair := ⟨true, true⟩

/-- Intermediate cell: [+outer, −inner].
    Person: 2nd (non-speaker participant). Number: dual (minimal non-atom). -/
def PrivativePair.intermediate : PrivativePair := ⟨true, false⟩

/-- Least specified cell: [−outer, −inner].
    Person: 3rd (non-participant). Number: plural (non-minimal non-atom). -/
def PrivativePair.minimal : PrivativePair := ⟨false, false⟩

-- ============================================================================
-- § 4: Cell Verification
-- ============================================================================

@[simp] theorem PrivativePair.maximal_wellFormed : PrivativePair.maximal.wellFormed = true := rfl
@[simp] theorem PrivativePair.intermediate_wellFormed : PrivativePair.intermediate.wellFormed = true := rfl
@[simp] theorem PrivativePair.minimal_wellFormed : PrivativePair.minimal.wellFormed = true := rfl

/-- The unique ill-formed combination. -/
theorem PrivativePair.illFormed_unique :
    (⟨false, true⟩ : PrivativePair).wellFormed = false := rfl

/-- There are exactly 3 well-formed combinations. -/
theorem PrivativePair.exactly_three :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      PrivativePair.wellFormed).length = 3 := by decide

-- ============================================================================
-- § 5: Classification
-- ============================================================================

/-- Every well-formed pair is one of the three canonical cells. -/
theorem PrivativePair.classification (p : PrivativePair)
    (h : p.wellFormed = true) :
    p = .maximal ∨ p = .intermediate ∨ p = .minimal := by
  cases p with | mk o i =>
  simp only [wellFormed, Bool.not_eq_true', Bool.or_eq_true] at h
  cases o <;> cases i <;> simp_all [maximal, intermediate, minimal]

/-- Inner feature entails outer for well-formed pairs. -/
theorem PrivativePair.inner_implies_outer (p : PrivativePair)
    (h : p.wellFormed = true) (hi : p.inner = true) :
    p.outer = true := by
  simp only [wellFormed, Bool.not_eq_true', Bool.or_eq_true] at h
  cases h with
  | inl h => simp [hi] at h
  | inr h => exact h

-- ============================================================================
-- § 6: Specification Level
-- ============================================================================

/-- Specification level: counts the number of positive features.
    Maximal = 2, intermediate = 1, minimal = 0.

    This defines a natural linear order on the three cells:
    more specified means more privative features are present. -/
def PrivativePair.specLevel (p : PrivativePair) : Nat :=
  p.outer.toNat + p.inner.toNat

@[simp] theorem PrivativePair.spec_maximal : PrivativePair.maximal.specLevel = 2 := rfl
@[simp] theorem PrivativePair.spec_intermediate : PrivativePair.intermediate.specLevel = 1 := rfl
@[simp] theorem PrivativePair.spec_minimal : PrivativePair.minimal.specLevel = 0 := rfl

/-- Specification is strictly ordered across cells. -/
theorem PrivativePair.spec_strict_order :
    PrivativePair.maximal.specLevel > PrivativePair.intermediate.specLevel ∧
    PrivativePair.intermediate.specLevel > PrivativePair.minimal.specLevel :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- § 7: Impossibility
-- ============================================================================

/-- **No four-way distinction.** Any partition based on a privative pair
    has at most 3 cells. This is the core impossibility result:
    a single privative pair cannot support a 4-way contrast.

    For person: no language has a 4-way singular person distinction.
    For number: no language has a 4-way base number distinction from
    two features alone. -/
theorem PrivativePair.no_four_way :
    ∀ (a b c d : PrivativePair),
      a.wellFormed → b.wellFormed → c.wellFormed → d.wellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  intro a b c d ha hb hc hd hab hac had hbc hbd hcd
  have := PrivativePair.classification a ha
  have := PrivativePair.classification b hb
  have := PrivativePair.classification c hc
  have := PrivativePair.classification d hd
  -- Each of a, b, c, d is one of 3 values; with 4 distinct items, pigeonhole
  rcases ‹a = _ ∨ _› with rfl | rfl | rfl <;>
    rcases ‹b = _ ∨ _› with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | skip <;>
      rcases ‹c = _ ∨ _› with rfl | rfl | rfl <;>
        first | exact absurd rfl hac | exact absurd rfl hbc | skip <;>
        rcases ‹d = _ ∨ _› with rfl | rfl | rfl <;>
          first | exact absurd rfl had | exact absurd rfl hbd | exact absurd rfl hcd

-- ============================================================================
-- § 8: PhiFeatures Class
-- ============================================================================

/-- Any type that is isomorphic to `PrivativePair`.

    Person.Features and Number.Features instantiate this class,
    inheriting `no_four_way`, `classification`, `specLevel`, etc.
    by construction — no per-domain bridge theorems needed. -/
class PhiFeatures (α : Type) where
  /-- Embed into the canonical privative pair. -/
  toPair : α → PrivativePair
  /-- Recover from the canonical privative pair. -/
  ofPair : PrivativePair → α
  /-- Round-trip: `ofPair ∘ toPair = id`. -/
  roundtrip : ∀ a, ofPair (toPair a) = a

namespace PhiFeatures

variable {α : Type} [inst : PhiFeatures α]

/-- The embedding is injective (follows from `roundtrip`). -/
theorem injective : Function.Injective (@toPair α inst) :=
  fun {a b} h => by
    have := congrArg (@ofPair α inst) h
    rw [roundtrip, roundtrip] at this
    exact this

/-- Well-formedness via the embedding. -/
def wellFormed (a : α) : Bool := (toPair a).wellFormed

/-- No 4-way distinction for any PhiFeatures instance. -/
theorem no_four_way [DecidableEq α] (a b c d : α)
    (ha : wellFormed a = true) (hb : wellFormed b = true)
    (hc : wellFormed c = true) (hd : wellFormed d = true)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False :=
  PrivativePair.no_four_way
    (toPair a) (toPair b) (toPair c) (toPair d)
    ha hb hc hd
    (fun h => hab (injective h)) (fun h => hac (injective h))
    (fun h => had (injective h)) (fun h => hbc (injective h))
    (fun h => hbd (injective h)) (fun h => hcd (injective h))

/-- Specification level via the embedding. -/
def specLevel (a : α) : Nat := (toPair a).specLevel

end PhiFeatures

end Features
