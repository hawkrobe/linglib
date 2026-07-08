import Linglib.Syntax.Category.Particle.Basic

/-!
# Particle capabilities

This file defines `Distributed α Ctx`: a carrier `α` with a recorded
three-valued distribution over licensing contexts `Ctx`, the
`Proform`-style capability behind `Particle`'s two facets (instances
for `Clause.Context` and `Clause.Embedding`).

There is deliberately no universal clause carrier: a theory whose
clause representation `C` classifies into these cells obtains
`Distributed Particle C` by pullback along its classifier, keeping the
stored facets finite and decidable.
-/

set_option autoImplicit false

open Clause (Context Embedding)

/-- A carrier `α` with a recorded three-valued distribution over
licensing contexts `Ctx`. `none` = the source records nothing
(distinct from `some .excluded`). -/
class Distributed (α : Type*) (Ctx : Type*) where
  /-- Recorded status of `a` in context `c`, if any. -/
  status? : α → Ctx → Option ParticleStatus

namespace Distributed

variable {α Ctx : Type*} [Distributed α Ctx]

/-- Positively recorded as available (obligatorily or optionally). -/
def LicensedIn (a : α) (c : Ctx) : Prop :=
  match status? a c with
  | some .obligatory | some .optional => True
  | _ => False

instance (a : α) (c : Ctx) : Decidable (LicensedIn a c) := by
  unfold LicensedIn; exact match status? a c with
    | some .obligatory => .isTrue trivial
    | some .optional => .isTrue trivial
    | some .excluded => .isFalse nofun
    | none => .isFalse nofun

end Distributed

instance : Distributed Particle Clause.Context := ⟨Particle.status?⟩

instance : Distributed Particle Clause.Embedding := ⟨Particle.embedStatus?⟩

/-- The capability agrees with the carrier's own clause-axis view. -/
theorem Particle.distributed_clause_eq (p : Particle) (c : Clause.Context) :
    Distributed.status? p c = p.status? c := rfl

/-- The capability agrees with the carrier's own embedding-axis view. -/
theorem Particle.distributed_embed_eq (p : Particle) (c : Clause.Embedding) :
    Distributed.status? p c = p.embedStatus? c := rfl
