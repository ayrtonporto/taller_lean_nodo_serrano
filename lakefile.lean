import Lake
open Lake DSL

package «taller» where
  -- Settings del package

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

@[default_target]
lean_lib «Taller» where
  -- Cualquier archivo .lean en la carpeta Taller/ está incluido
