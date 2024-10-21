/-
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

-- Build and run:
-- lake build Cryptography.Hashes.SHA3.perftest && ./.lake/build/bin/Cryptography-Hashes-SHA3-perftest
--  perf record  -g  --call-graph=dwarf     ./.lake/build/bin/Cryptography-Hashes-SHA3-perftest

import «Cryptography».Hashes.SHA3.Basic
import «Cryptography».Data.HexString


def main : IO Unit := do

--  let input := ""

  let chunkSizes : List Nat := [32, 2^10, 2^20]
  let mbCount := 100
  let dataSize := mbCount * 2^20

  let mut h := SHAKE128.mk

  let mut startTime := 0
  let mut endTime := 0
  let mut elapsed := 0

  for chunkSize in chunkSizes do

    let lsts := (List.range (dataSize / chunkSize)).map λ _ => do
      let r ←  IO.getRandomBytes chunkSize.toUSize
      pure r

    IO.println s!"Go."
    startTime ← IO.monoNanosNow

    for e in lsts do
      h := SHAKE128.absorb h (← e)

    endTime ← IO.monoNanosNow
    elapsed := (endTime - startTime).toFloat / 1000000000

    IO.println s!"chunk size: {chunkSize} chunk count: {lsts.length} elapsed: {elapsed} MB/s: {mbCount.toFloat / elapsed}"


  pure ()
