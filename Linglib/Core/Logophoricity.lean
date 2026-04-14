import Mathlib.Order.Nat

/-!
# Logophoric Roles @cite{sells-1987}

@cite{sells-1987} identifies three logophoric roles that govern the licensing
of logophoric pronouns and long-distance reflexives cross-linguistically:

- **Pivot**: the individual whose point of view the event is described from.
  The most general logophoric role. In matrix clauses, the speaker is the
  default pivot; in embedded clauses, the attitude holder whose perspective
  is adopted.
- **Self**: the individual whose mental state (thought, belief, knowledge) is
  reported. An attitude holder. The speaker is a self by definition.
- **Source**: the individual who makes the report — the "one who makes the
  report." The speaker is a source by definition; the addressee is a self
  (forms an attitude toward propositional content) but not a source.

These roles form an implicational hierarchy:
  source → self → pivot

That is, a source is necessarily a self and a pivot; a self is necessarily
a pivot; but a pivot need not be a self or source.

## Connection to Perspectival Phenomena

The same logophoric roles govern:
- Logophoric pronouns (Ewe *yè*): antecedent must be at least a self
- Long-distance reflexives (Japanese *zibun*): antecedent must be a pivot
- Point-of-view verbs (Japanese yar- vs kure-): lexically encode pivot
- The Clitic Logophoric Restriction (CLR): 3P IO clitic interpreted as
  point-of-view center blocks *de se* reading of accusative clitic

The bridge to Minimalist P-Prominence (@cite{pancheva-zubizarreta-2018}) is
in `Phenomena.Agreement.Studies.PanchevaZubizarreta2018`.
-/

namespace Core.Logophoricity

-- ============================================================================
-- § 1: Logophoric Roles
-- ============================================================================

/-- Logophoric roles from @cite{sells-1987}.

    The roles capture different dimensions of perspectival centering:
    who is the narrator (source), who is thinking/believing (self),
    and whose viewpoint structures the description (pivot).

    Ordered by entailment: `pivot ≤ self ≤ source`. Being a source
    entails being a self, which entails being a pivot. -/
inductive LogophoricRole where
  /-- The individual whose point of view the event is described from.
      Most general role. Bottom of the hierarchy. -/
  | pivot
  /-- The individual whose mental state is reported. An attitude holder.
      Entails pivot. -/
  | self
  /-- The individual who makes the report. Entails both self and pivot.
      Top of the hierarchy. -/
  | source
  deriving DecidableEq, Repr

/-- Numeric embedding into ℕ preserving the entailment order. -/
def LogophoricRole.toNat : LogophoricRole → Nat
  | .pivot  => 0
  | .self   => 1
  | .source => 2

instance : LinearOrder LogophoricRole :=
  LinearOrder.lift' LogophoricRole.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [LogophoricRole.toNat])

-- ============================================================================
-- § 2: Implicational Hierarchy
-- ============================================================================

/-- A self entails a pivot. -/
theorem pivot_le_self : LogophoricRole.pivot ≤ .self := by decide

/-- A source entails a self. -/
theorem self_le_source : LogophoricRole.self ≤ .source := by decide

/-- A source entails a pivot (transitivity). -/
theorem pivot_le_source : LogophoricRole.pivot ≤ .source := by decide

/-- The full hierarchy as a conjunction. -/
theorem hierarchy :
    LogophoricRole.pivot < LogophoricRole.self ∧
    LogophoricRole.self < LogophoricRole.source := by decide

/-- Pivot is the bottom of the hierarchy. -/
theorem pivot_le (r : LogophoricRole) : .pivot ≤ r := by
  cases r <;> decide

/-- Source is the top of the hierarchy. -/
theorem le_source (r : LogophoricRole) : r ≤ .source := by
  cases r <;> decide

-- ============================================================================
-- § 3: Point-of-View Principle
-- ============================================================================

/-- The Point-of-View Principle (@cite{pancheva-zubizarreta-2018}, (48)):

    Within a logophoric domain marking point of view, if there are
    attitude holders among the event participants, one of them has to
    be the point-of-view center.

    This principle is a semantic requirement that individual grammars
    can enforce at different points in the derivation. For the PCC,
    the relevant domain is the ApplP. For the CLR, the domain is
    evaluated at the semantics. -/
def pointOfViewPrinciple (hasAttitudeHolder : Bool) (povIsAttitudeHolder : Bool) : Bool :=
  !hasAttitudeHolder || povIsAttitudeHolder

/-- If there is no attitude holder, the principle is trivially satisfied. -/
theorem pov_trivial_no_attitude :
    pointOfViewPrinciple false false = true := rfl

/-- If there is an attitude holder and the POV center IS the attitude
    holder, the principle is satisfied. -/
theorem pov_satisfied :
    pointOfViewPrinciple true true = true := rfl

/-- If there is an attitude holder but the POV center is NOT the
    attitude holder, the principle is violated. -/
theorem pov_violated :
    pointOfViewPrinciple true false = false := rfl

end Core.Logophoricity
