import Lake

open System Lake DSL

package «lean-matlib-1stproj» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions :=
  #[⟨`pp.unicode.fun, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`maxSynthPendingDepth, Lean.LeanOptionValue.ofNat 3⟩]

require "leanprover-community" / mathlib

@[default_target] lean_lib LeanMatlib1stproj
