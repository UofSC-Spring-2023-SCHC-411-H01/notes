import Lake
open Lake DSL

package notes4 

@[default_target]
lean_lib Notes4 where 
  moreLeanArgs := #["-DwarningAsError=true", "-Dpp.unicode.fun=true"] -- pretty-prints `fun a ↦ b`

@[default_target]
lean_exe notes4 {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "main"
