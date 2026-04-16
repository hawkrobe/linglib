/-!
# Discourse Segments — DSP Stack
@cite{grosz-sidner-1986} @cite{grosz-joshi-weinstein-1995}

A theory-neutral type for the **discourse segment purpose** (DSP) stack
of @cite{grosz-sidner-1986}. Segments organize a discourse into a tree
of purposes; the DSP stack tracks which segment is currently active
during processing.

Centering theory @cite{grosz-joshi-weinstein-1995} is explicitly *local*
to a single segment: Cf, Cb, and the transition typology only apply to
adjacent utterances within the same segment. Cross-segment transitions
are governed by the segment-structure level instead. This module
provides the minimal scaffolding (the stack and basic push/pop
operations) that downstream Centering and SDRT files can hook into
without committing to a specific account of segment boundaries.

Segment-purpose semantics — what makes a sequence of utterances a
single purpose, how purposes are introduced and terminated — is not
fixed here; this module provides the *bookkeeping* layer.
-/

set_option autoImplicit false

namespace Core.Discourse.Segment

-- ════════════════════════════════════════════════════
-- § Discourse Segments
-- ════════════════════════════════════════════════════

/-- A discourse segment, parameterized by the purpose-content type `P`.
    The `id` distinguishes co-purposed segments (two distinct segments
    can share a purpose-description but be different segments). -/
structure Segment (P : Type) where
  id : Nat
  purpose : P
  deriving Repr

/-- The discourse-segment-purpose stack: most recently pushed segment
    is at the head. The empty stack represents the discourse-initial
    state (before any purpose has been opened). -/
abbrev DSPStack (P : Type) := List (Segment P)

namespace DSPStack
variable {P : Type}

/-- The currently active segment (top of the stack), or `none` if the
    stack is empty. -/
def current (s : DSPStack P) : Option (Segment P) := s.head?

/-- Push a new segment onto the stack — beginning a new sub-purpose. -/
def push (s : DSPStack P) (seg : Segment P) : DSPStack P := seg :: s

/-- Pop the topmost segment — terminating the current purpose and
    returning to the dominating one. Returns the original stack
    unchanged if it was already empty. -/
def pop : DSPStack P → DSPStack P
  | []      => []
  | _ :: xs => xs

/-- Two utterances are **co-segmental** when they are processed under
    the same active segment. Centering operations are restricted to
    co-segmental utterance pairs. -/
def coSegmental [DecidableEq P] (s₁ s₂ : DSPStack P) : Bool :=
  match s₁.head?, s₂.head? with
  | some a, some b => a.id == b.id
  | none, none     => true
  | _, _           => false

end DSPStack

end Core.Discourse.Segment
