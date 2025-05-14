/-
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import «Cryptography».Hashes.SHA3.Basic
import «Cryptography».Data.HexString

/-!
Examples on how to invoke the various primitives.
-/

-- Build and run:
-- lake build Cryptography.Hashes.SHA3.example && ./.lake/build/bin/Cryptography-Hashes-SHA3-example


def main :IO UInt32 := do

  let input := "b1caa396771a09a1db9bc20543e988e359d47c2a616417bbca1b62cb02796a888fc6eeff5c0b5c3d5062fcb4256f6ae1782f492c1cf03610b4a1fb7b814c057878e1190b9835425c7a4a0e182ad1f91535ed2a35033a5d8c670e21c575ff43c194a58a82d4a1a44881dd61f9f8161fc6b998860cbe4975780be93b6f87980bad0a99aa2cb7556b478ca35d1f3746c33e2bb7c47af426641cc7bbb3425e2144820345e1d0ea5b7da2c3236a52906acdc3b4d34e474dd714c0c40bf006a3a1d889a632983814bbc4a14fe5f159aa89249e7c738b3b73666bac2a615a83fd21ae0a1ce7352ade7b278b587158fd2fabb217aa1fe31d0bda53272045598015a8ae4d8cec226fefa58daa05500906c4d85e7567"

  let d ← IO.ofExcept $ HexString.parse input
  let h := SHA3_256.hashData d
  IO.println $ HexString.toHexString h

  let a := ByteArray.mk $ Array.replicate 10 1
  let b := ByteArray.mk $ Array.replicate 20 2
  let c := ByteArray.mk $ Array.replicate 30 3
  let state := SHA3_256.mk |> (SHA3_256.update ·  a) |> (SHA3_256.update · b)
  -- one more time for good measure, "later" in the code
  let state := SHA3_256.update state c
  IO.println $ HexString.toHexString $ SHA3_256.final state

  let outLen := 20
  let (_ , res) := SHAKE256.mk |> (SHAKE256.absorb · d) |> (SHAKE256.squeeze · outLen)
  IO.println $ HexString.toHexString res

  let (kstate , _res) := SHAKE256.mk |> (SHAKE256.absorb · d) |> (SHAKE256.squeeze · outLen)
  -- this won't compile, can't re-absorb after squeezing
  -- let r := SHAKE256.absorb kstate d
  -- but one can squeeze more:
  let _ := SHAKE256.squeeze kstate outLen

  let _kstate := SHAKE256.mk |> (SHAKE256.absorb · d)
  -- let (_kstate, res) := SHAKE128.squeeze  _kstate outLen -- won't work, different types (SHAKE128 vs SHAKE256)
  -- IO.println $ HexString.toHexString res

  let _kstate := SHAKE256.mk |> (SHAKE256.absorb · d)
  -- let _kstate := (SHAKE128.absorb _kstate d) -- won't work, different types
  -- let (_kstate, res) := SHAKE128.squeeze _kstate outLen -- won't work, different types
  -- IO.println $ HexString.toHexString res

  -- Transforms an absorbing sponge into a squeezing one (by absorbing any remaining input, and squeezing 0 bytes)
  -- This could be useful before entering a mutating loop of a given SHAKE context
  let mut ctx1 := SHAKE128.mk |> (SHAKE128.absorb · a ) |> (SHAKE128.toSqueezing · )
  let mut s1 := ByteArray.mk $ Array.replicate 10 0
  for _ in [0:3] do
    (ctx1, s1) := SHAKE128.squeeze ctx1 10
    -- (do something with s1 SHAKE output)

  -- Double squeezes in one line, should not be necessary but this is how to do it
  let mut (_ctx2, s2) := SHAKE128.mk |> (SHAKE128.absorb · a ) |> (SHAKE128.squeeze · outLen ) |> (SHAKE128.squeeze ·.1 outLen )
  IO.println $ HexString.toHexString s2

  pure 0
