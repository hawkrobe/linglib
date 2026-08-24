/-!
# Comparative argument roles

`ArgumentRole`: the S/A/P/R/T comparative concepts for argument coding,
neutral between case and agreement. `ArgumentRole.core` is the
monotransitive core that alignment partitions quantify over;
`IsHighDefault`/`IsLowDefault` classify the roles by their usual
referential prominence (the role-reference association).

## References

* [comrie-1978]
* [haspelmath-2021]
-/

/-- Argument roles spanning monotransitive and ditransitive clauses,
    following [comrie-1978] and [haspelmath-2021] in using S/A/P/R/T
    (not subject/object) to avoid theory-dependent constituency
    assumptions. -/
inductive ArgumentRole where
  /-- S: sole argument of an intransitive verb -/
  | S
  /-- A: the more agent-like argument of a transitive verb -/
  | A
  /-- P: the more patient-like argument of a transitive verb -/
  | P
  /-- R: the recipient-like argument of a ditransitive verb -/
  | R
  /-- T: the theme-like argument of a ditransitive verb -/
  | T
  deriving DecidableEq, Repr

/-- The monotransitive core roles: A, P, and S (omits the ditransitive
    scaffolding roles R/T). The domain over which alignment partitions
    and per-language case/agreement coverage theorems quantify. -/
def ArgumentRole.core : List ArgumentRole := [.A, .P, .S]

/-- The role defaults to high referential prominence (A and R, which are
    usually human, definite, topical) — so differential marking targets its
    *non-prominent* end ([haspelmath-2021]'s (6)). -/
def ArgumentRole.IsHighDefault (r : ArgumentRole) : Prop := r = .A ∨ r = .R

instance (r : ArgumentRole) : Decidable r.IsHighDefault :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The role defaults to low referential prominence (P and T) — so
    differential marking targets its *prominent* end. S is the alignment
    reference point and is neither. -/
def ArgumentRole.IsLowDefault (r : ArgumentRole) : Prop := r = .P ∨ r = .T

instance (r : ArgumentRole) : Decidable r.IsLowDefault :=
  inferInstanceAs (Decidable (_ ∨ _))
