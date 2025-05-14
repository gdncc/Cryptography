/-
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

-- Build and run:
-- lake build Cryptography.Hashes.SHA3.test && ./.lake/build/bin/Cryptography-Hashes-SHA3-test
-- Currently, the output must be reviewed manually.

import Cryptography.Data.HexString
import Cryptography.Hashes.SHA3.Basic
import Cryptography.Data.CAVS

def testSHA3HashData (input : String) (fn: ByteArray → ByteArray ) (expectedResult : String) := do
  let d ← HexString.parse input
  let result := fn d
  pure $ HexString.toHexString result == expectedResult

def testHashMsg (file : String) (fn: ByteArray → ByteArray )  :=  do
  let cavsfile ←  slurpMsgFile file
  let records := cavsfile.records
  let total := cavsfile.records.size
  let mut pass := 0
  let mut fail := 0
  for r in records do
    match testSHA3HashData (r.msg.take $ r.len / 8 * 2) fn r.md with
      | Except.ok true => pass := pass + 1
      | _ => fail := fail + 1
  pure (total , pass, fail)

def testSHA3Sponge (input : String) (resultLength : Nat) (fn: ByteArray →  Nat → ByteArray ) (expectedResult : String) := do
  let d ← HexString.parse input
  let result := fn d resultLength
  pure $ HexString.toHexString result == expectedResult

def testXOFChunked (f : XOF) (msg : ByteArray ) (outLen : Nat) (chunkSize : Nat) (expectedResult : String) := Id.run do
  let mut state := f.mk |> (f.absorb · msg) |> f.toSqueezing
  let mut output := ByteArray.emptyWithCapacity outLen
  let mut bs := ByteArray.emptyWithCapacity chunkSize
  for _ in [:outLen / chunkSize] do
    ( state, bs ) := f.squeeze state chunkSize
    output := ByteArray.append output bs
  if outLen % chunkSize > 0 then
    let mut bs2 := ByteArray.emptyWithCapacity $ (outLen % chunkSize)
    ( state, bs2 ) := f.squeeze state (outLen % chunkSize)
    output := ByteArray.append output bs2
  pure $ (HexString.toHexString output) == expectedResult

def testSpongeMsgChunkedOutput (file : String) (f : XOF ) (chunkSize : Nat) :=  do
  let cavsfile ←  slurpMsgFile file
  let records := cavsfile.records
  let total := cavsfile.records.size
  let mut pass := 0
  let mut fail := 0
  for r in records do
      let d ←   IO.ofExcept $ HexString.parse (r.msg.take $ r.len / 8 * 2)
      let res := testXOFChunked f d (cavsfile.len / 8)  chunkSize r.md
        if res == true then pass := pass + 1 else fail := fail + 1
   pure (total , pass, fail)

def testSpongeMsg (file : String) (fn: ByteArray → Nat →  ByteArray )  :=  do
  let cavsfile ←  slurpMsgFile file
  let records := cavsfile.records
  let total := cavsfile.records.size
  let mut pass := 0
  let mut fail := 0
  for r in records do
    match testSHA3Sponge (r.msg.take $ r.len / 8 * 2) (cavsfile.len / 8) fn r.md with
      | Except.ok true => pass := pass + 1
      | _ => fail := fail + 1
  pure (total , pass, fail)

def testSpongeVariableOut (file : String) (fn: ByteArray → Nat →  ByteArray )  :=  do
  let cavsfile ←  slurpVariableOutFile file
  let records := cavsfile.records
  let total := cavsfile.records.size
  let mut pass := 0
  let mut fail := 0
  for r in records do
    match testSHA3Sponge (r.msg) (r.outputLen / 8 ) fn r.output with
      | Except.ok true => pass := pass + 1
      | _ => fail :=
        fail + 1
  pure (total , pass, fail)

def testSpongeVariableOutChunkedOutput (file : String) (f: XOF ) (chunkSize : Nat)  :=  do
  let cavsfile ←  slurpVariableOutFile file
  let records := cavsfile.records
  let total := cavsfile.records.size
  let mut pass := 0
  let mut fail := 0
  for r in records do
    let d ←   IO.ofExcept $ HexString.parse r.msg
    let res := testXOFChunked f d  (r.outputLen / 8 )  chunkSize r.output
    if res == true then pass := pass + 1 else fail := fail + 1
  pure (total , pass, fail)

-- https://csrc.nist.gov/csrc/media/projects/cryptographic-algorithm-validation-program/documents/sha3/sha3vs.pdf
def testHashMonteCarlo (file : String) (fn: ByteArray → ByteArray ) := do
  let cavsfile ←  slurpHashMonteFile file
  let records := cavsfile.records
  let last_record := records[records.size - 1]!
  let mut seed ←  IO.ofExcept $ HexString.parse cavsfile.seed
  let mut mds : Array ByteArray := Array.replicate 1001 $ ByteArray.mk #[]
  for _ in [0:100] do
    mds := mds.set! 0 seed
    for j in [1:1001] do
      let msg := mds[j - 1]!
      mds := mds.set! j $ fn msg
    seed := mds[1000]!
  let result :=  HexString.toHexString seed
  pure $ result == last_record.md

-- Encode `ByteArray` of size 2 as big  endian  `UInt16`.
def readUInt16be (bs : ByteArray) : UInt16 :=
  (bs.get! 0).toUInt16 <<< 0x08 |||
  (bs.get! 1).toUInt16

-- https://csrc.nist.gov/csrc/media/projects/cryptographic-algorithm-validation-program/documents/sha3/sha3vs.pdf
def testXofMonteCarlo (file : String) (fn: ByteArray → Nat →  ByteArray) := do
  let cavsfile ←  slurpXofMonteFile file
  let records := cavsfile.records
  let last_record := records[records.size - 1]!
  let mut seed ←  IO.ofExcept $ HexString.parse cavsfile.msg
  let min := cavsfile.minOutputLen / 8
  let max := cavsfile.maxOutputLen / 8
  let mut range := max - min + 1
  let mut outputLen := max
  let mut mds : Array ByteArray := Array.replicate 1001 $ ByteArray.mk #[]
  for _ in [0:100] do
    mds := mds.set! 0 seed
    for j in [1:1001] do
      let mut msg := ByteArray.empty
      let mut mdlen := mds[j - 1]!.size
      if mdlen < 16 then
        mdlen := 16 - mdlen
        msg := (mds[j - 1]!.extract 0 16 ).append ( ByteArray.mk $  Array.replicate mdlen 0)
      else
        msg := mds[j - 1]!.extract 0 16
      let r := fn msg outputLen
      mds := mds.set! j r
      let rightMostOutputBits := readUInt16be $ r.extract (r.size - 2) r.size
      outputLen := min + (rightMostOutputBits % range).toNat
    seed := mds[1000]!

  let result :=  HexString.toHexString seed
  pure $ result == last_record.output

def SHA3_224Files :=
  ["Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_224ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_224LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_224Monte.rsp"]

def SHA3_256Files :=
  ["Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_256ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_256LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_256Monte.rsp"]

def SHA3_384Files :=
  ["Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_384ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_384LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_384Monte.rsp"]

def SHA3_512Files :=
  ["Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_512ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_512LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/sha-3bytetestvectors/SHA3_512Monte.rsp"]

def SHAKE128_Files :=
  ["Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE128ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE128LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE128VariableOut.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE128Monte.rsp"]

def SHAKE256_Files :=
  ["Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE256ShortMsg.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE256LongMsg.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE256VariableOut.rsp",
  "Cryptography/test/Hashes/SHA3/shakebytetestvectors/SHAKE256Monte.rsp"]

def testHashEqUpdateFinal :=
  let a := ByteArray.mk $ Array.replicate 10 1
  let b := ByteArray.mk $ Array.replicate 20 2
  let c := a.append b
  let state := SHA3_256.mk |> (SHA3_256.update ·  a ) |> (SHA3_256.update ·  b )
  (HexString.toHexString $ SHA3_256.hashData c) == (HexString.toHexString  $ SHA3_256.final state)

def main : IO Unit := do

  IO.println s!"testHashEqUpdateFinal() success:  {testHashEqUpdateFinal}"

  for file in (SHA3_224Files.dropLast ) do
    let (t,p,f) ← testHashMsg file SHA3_224.hashData
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHA3_256Files.dropLast ) do
    let (t,p,f) ← testHashMsg file SHA3_256.hashData
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHA3_384Files.dropLast ) do
    let (t,p,f) ← testHashMsg file SHA3_384.hashData
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHA3_512Files.dropLast ) do
    let (t,p,f) ← testHashMsg file SHA3_512.hashData
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHAKE128_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsg file (fun  msg outLen =>
      (SHAKE128.mk |> (SHAKE128.absorb · msg) |> (SHAKE128.squeeze · outLen)).2 )
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHAKE256_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsg file (fun  msg outLen =>
      (SHAKE256.mk |> (SHAKE256.absorb · msg) |> (SHAKE256.squeeze · outLen)).2 )
    IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  for file in (SHAKE128_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsgChunkedOutput file SHAKE128 1
    IO.println s!"{file} (byte per byte) total: {t} pass: {p} fail: {f}"

  for file in (SHAKE256_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsgChunkedOutput file SHAKE256 1
    IO.println s!"{file} (byte per byte) total: {t} pass: {p} fail: {f}"

  for file in (SHAKE128_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsgChunkedOutput file SHAKE128 13
    IO.println s!"{file} (13 bytes chunks) total: {t} pass: {p} fail: {f}"

  for file in (SHAKE256_Files.take 2 ) do
    let (t,p,f) ← testSpongeMsgChunkedOutput file SHAKE256 13
    IO.println s!"{file} (13 bytes chunks) total: {t} pass: {p} fail: {f}"

  let file := SHAKE128_Files[2]!
  let (t,p,f) ← testSpongeVariableOut file (fun  msg outLen =>
      (SHAKE128.mk |> (SHAKE128.absorb · msg) |> (SHAKE128.squeeze · outLen)).2 )
  IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  let file := SHAKE256_Files[2]!
  let (t,p,f) ← testSpongeVariableOut file (fun  msg outLen =>
      (SHAKE256.mk |> (SHAKE256.absorb · msg) |> (SHAKE256.squeeze · outLen)).2 )
  IO.println s!"{file} total: {t} pass: {p} fail: {f}"

  let file := SHAKE128_Files[2]!
  let (t,p,f) ← testSpongeVariableOutChunkedOutput file SHAKE128 1
  IO.println s!"{file} (byte per byte) total: {t} pass: {p} fail: {f}"

  let file := SHAKE256_Files[2]!
  let (t,p,f) ← testSpongeVariableOutChunkedOutput file SHAKE256 1
  IO.println s!"{file} (byte per byte) total: {t} pass: {p} fail: {f}"

  let file := SHAKE128_Files[2]!
  let (t,p,f) ← testSpongeVariableOutChunkedOutput file SHAKE128 13
  IO.println s!"{file} (13 bytes chunks) total: {t} pass: {p} fail: {f}"

  let file := SHAKE256_Files[2]!
  let (t,p,f) ← testSpongeVariableOutChunkedOutput file SHAKE256 13
  IO.println s!"{file} (13 bytes chunks) total: {t} pass: {p} fail: {f}"

  let file := SHA3_224Files[2]!
  let r  ←  testHashMonteCarlo file $ fun d => SHA3_224.hashData d
  IO.println s!"{file} success: {r}"

  let file := SHA3_256Files[2]!
  let r  ←  testHashMonteCarlo file $ fun d => SHA3_256.hashData d
  IO.println s!"{file} success: {r}"

  let file := SHA3_384Files[2]!
  let r  ←  testHashMonteCarlo file $ fun d => SHA3_384.hashData d
  IO.println s!"{file} success: {r}"

  let file := SHA3_512Files[2]!
  let r  ←  testHashMonteCarlo file $ fun d => SHA3_512.hashData d
  IO.println s!"{file} success: {r}"

  let file := SHAKE128_Files[3]!
  let r ← testXofMonteCarlo file (fun  msg outLen =>
      (SHAKE128.mk |> (SHAKE128.absorb · msg) |> (SHAKE128.squeeze · outLen)).2 )
  IO.println s!"{file} success: {r}"

  let file := SHAKE256_Files[3]!
  let r ← testXofMonteCarlo file (fun  msg outLen =>
      (SHAKE256.mk |> (SHAKE256.absorb · msg) |> (SHAKE256.squeeze · outLen)).2 )
  IO.println s!"{file} success: {r}"

  pure ()
