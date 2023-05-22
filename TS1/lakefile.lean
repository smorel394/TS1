import Lake
open Lake DSL

package «preorder_to_powerset».«lean» {
  -- add package configuration options here
}

lean_lib «PreorderToPowerset».«Lean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «preorder_to_powerset».«lean» {
  root := `Main
}
