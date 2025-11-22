import Lake
open Lake DSL

package echidna_proofs where
  -- add package configuration options here

@[default_target]
lean_lib ECHIDNA where
  -- add library configuration options here
  roots := #[`ECHIDNA]
