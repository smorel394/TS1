import Lake
open Lake DSL

package «tS1» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "9ec7de3c06654f18053a390fa05a6db21c36ebd0"


@[default_target]
lean_lib «TS1» {
  -- add any library configuration options here
}
