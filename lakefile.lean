import Lake
open Lake DSL

package «cryptography» where
  -- add package configuration options here

@[default_target]
lean_lib «Cryptography» where
  buildType := BuildType.release
  moreLeancArgs := #["-O3"]

lean_exe  Cryptography.Hashes.SHA3.test

lean_exe  Cryptography.Hashes.SHA3.perftest where
  buildType := BuildType.release
  moreLeancArgs := #["-O3"]

lean_exe Cryptography.Hashes.SHA3.example
