import Linglib.Theories.Syntax.Minimalism.Core.PConstraint

/-!
# Logophoric Roles @cite{sells-1987}
@cite{pancheva-zubizarreta-2018}

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

## Connection to Person Features

@cite{pancheva-zubizarreta-2018} connect logophoric roles to the
interpretable person feature on Appl:

| P-Prominence | Logophoric role | Eligible persons |
|--------------|----------------|-----------------|
| [+proximate] | pivot          | 1P, 2P, 3P proximate |
| [+participant] | self         | 1P, 2P          |
| [+author]    | source         | 1P only         |

This connection is what gives the P-Constraint its semantic content: the
syntactic mechanism of person-feature agreement on Appl *encodes* the
identification of the indirect object as a point-of-view center.

## Connection to Other Perspectival Phenomena

The same logophoric roles govern:
- Logophoric pronouns (Ewe *yè*): antecedent must be at least a self
- Long-distance reflexives (Japanese *zibun*): antecedent must be a pivot
- Point-of-view verbs (Japanese yar- vs kure-): lexically encode pivot
- The Clitic Logophoric Restriction (CLR): 3P IO clitic interpreted as
  point-of-view center blocks *de se* reading of accusative clitic
-/

namespace Core.Logophoricity

open Minimalism.PConstraint (PProminence)

-- ============================================================================
-- § 1: Logophoric Roles
-- ============================================================================

/-- Logophoric roles from @cite{sells-1987}.

    The roles capture different dimensions of perspectival centering:
    who is the narrator (source), who is thinking/believing (self),
    and whose viewpoint structures the description (pivot). -/
inductive LogophoricRole where
  /-- The individual whose point of view the event is described from.
      Most general role. -/
  | pivot
  /-- The individual whose mental state is reported. An attitude holder.
      Entails pivot. -/
  | self
  /-- The individual who makes the report. Entails both self and pivot. -/
  | source
  deriving DecidableEq, Repr

/-- Logophoric roles form an implicational hierarchy.
    Rank: source (2) > self (1) > pivot (0). -/
def LogophoricRole.rank : LogophoricRole → Nat
  | .pivot  => 0
  | .self   => 1
  | .source => 2

/-- A source is also a self. -/
theorem source_entails_self :
    LogophoricRole.source.rank ≥ LogophoricRole.self.rank := by decide

/-- A self is also a pivot. -/
theorem self_entails_pivot :
    LogophoricRole.self.rank ≥ LogophoricRole.pivot.rank := by decide

-- ============================================================================
-- § 2: Bridge to P-Prominence
-- ============================================================================

/-- The P-Prominence setting that corresponds to a logophoric role.

    This is the formal link between the syntactic mechanism of the
    P-Constraint and the semantic content of perspectival centering:
    the interpretable person feature on Appl selects for the logophoric
    role of the indirect object. -/
def LogophoricRole.toProminence : LogophoricRole → PProminence
  | .pivot  => .proximate
  | .self   => .participant
  | .source => .author

/-- The logophoric role corresponding to a P-Prominence setting. -/
def prominenceToRole : PProminence → LogophoricRole
  | .proximate   => .pivot
  | .participant => .self
  | .author      => .source

/-- The bridge is an isomorphism. -/
theorem prominence_role_roundtrip (r : LogophoricRole) :
    prominenceToRole r.toProminence = r := by
  cases r <;> rfl

theorem role_prominence_roundtrip (p : PProminence) :
    (prominenceToRole p).toProminence = p := by
  cases p <;> rfl

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
