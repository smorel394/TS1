import Lake
open Lake DSL

package «TS1» {
  -- add any package configuration options here
}


require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "560eeb2b8ebd4d98257483aef6ddb81e598fa5b0"


@[default_target]
lean_lib «TS1» {
  -- add any library configuration options here
}
