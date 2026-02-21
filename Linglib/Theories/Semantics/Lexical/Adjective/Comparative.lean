import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Degree.Frameworks.Rett

/-!
# DEPRECATED: Comparative Semantics (re-export shim)

Content has moved to:
- `Theories.Semantics.Degree.Comparative` — framework-independent comparative semantics
- `Theories.Semantics.Degree.Frameworks.Rett` — Rett's MAX-based framework

This file re-exports the key definitions under the old namespace for
backward compatibility.
-/

namespace Semantics.Lexical.Adjective.Comparative

-- Re-export key definitions under the old namespace
open Semantics.Degree.Comparative in
abbrev ScaleDirection := Semantics.Degree.Comparative.ScaleDirection

open Semantics.Degree.Comparative in
def comparativeSem {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) (dir : Core.Scale.ScalePolarity) : Prop :=
  Semantics.Degree.Comparative.comparativeSem μ a b dir

open Semantics.Degree.Comparative in
def equativeSem {Entity : Type*} {α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) (dir : Core.Scale.ScalePolarity) : Prop :=
  Semantics.Degree.Comparative.equativeSem μ a b dir

abbrev MannerEffect := Semantics.Degree.Comparative.MannerEffect

def enEvaluativeEffect := Semantics.Degree.Comparative.enEvaluativeEffect

end Semantics.Lexical.Adjective.Comparative
