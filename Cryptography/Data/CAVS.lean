/-
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

-- Cryptographic Algorithm Validation Program

structure CAVSMsgRecord where
  len : Nat
  msg : String
  md : String
deriving Inhabited, Repr

structure CAVSMsgFile where
  pathname : String := ""
  comments : Array String := #[]
  len : Nat := 0
  records : Array CAVSMsgRecord := #[]
deriving Inhabited, Repr

private def CAVSMsgFile.mkEmpty : CAVSMsgFile :=
   {}

private partial def commentCore (acc : String) : Parser String := do
  let some c ← peek? | return acc
  if c = '\n' then
    skip
    return  acc
  else
    let c ← any
    commentCore (acc.push c)

private partial def manyComments (acc : Array String) : Parser $ Array String := do
  let some c ← peek? | return acc
  if c = '#' then
    skip
    ws
    let s ← commentCore ""
    manyComments $ acc.push s
  else
    return acc

private def lString : Parser String := pstring "[L = "
private def outputLenString : Parser String := pstring "[Outputlen = "

private partial def bitsLenCore : Parser String := do
   let n ← manyChars digit
   skipString "]"
   return n

private partial def lenCore : Parser String := do
   skipString "Len = "
   let n ← manyChars digit
   ws
   return n

private partial def msgCore : Parser String := do
   skipString "Msg = "
   let n ← manyChars hexDigit
   ws
   return n

private def mDString : Parser String := pstring "MD = "
private def outputString : Parser String := pstring "Output = "

private partial def mdCore : Parser String := do
   let n ← manyChars hexDigit
   ws
   return n

private partial def recordCore : Parser CAVSMsgRecord := do
  let len ← lenCore
  let msg ←  msgCore
  let md ← attempt (mDString <|> outputString <|> fail s!"'MD = ' or 'Output = ' expected") *> mdCore
  ws
  let record :=  {len := len.toNat! , msg:= msg, md := md}
  return record

private partial def manyRecordCore (acc : Array CAVSMsgRecord) : Parser $ Array CAVSMsgRecord := do
  let some _ ← peek? | return acc
  manyRecordCore $ acc.push (← recordCore)

private def msgFileCore : Parser CAVSMsgFile  := do
  let mut f := CAVSMsgFile.mkEmpty
  f := {f  with comments :=  (← manyComments #[] )}
  ws
  let len ← attempt (lString <|> outputLenString <|> fail s!"'[L = ' or '[Outputlen = ' expected") *> bitsLenCore
  f := {f with len := len.toNat!}
  ws
  let records ← manyRecordCore #[]
  f := {f with records := records }
  return f

private def msgFileContent : Parser CAVSMsgFile := do
  ws
  let res ← msgFileCore
  eof
  return res

private def parseMsgFile (s : String) : Except String CAVSMsgFile  :=
  match (msgFileContent s.mkIterator) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

def slurpMsgFile (pathname : String)   := do
  let contents ← IO.FS.readFile pathname
  let f ← IO.ofExcept $ parseMsgFile contents
  return {f with pathname := pathname}

--
structure CAVSVariableOutRecord where
  count : Nat
  outputLen : Nat
  msg : String
  output : String
deriving Inhabited, Repr

structure CAVSVariableOutFile where
  pathname : String := ""
  comments : Array String := #[]
  parameters : Array String := #[]
  records : Array CAVSVariableOutRecord := #[]
deriving Inhabited, Repr

private def cAVSVariableOutFile.mkEmpty : CAVSVariableOutFile :=
   {}

private partial def paramsCore (acc : String) : Parser String := do
  let some c ← peek? | return acc
  if c = '\n' then
    skip
    return  acc
  else
    let c ← any
    paramsCore (acc.push c)

private partial def manyParams (acc : Array String) : Parser $ Array String := do
  let some c ← peek? | return acc
  if c = '[' then
    ws
    let s ← paramsCore ""
    ws
    manyParams $ acc.push s
  else
    return acc

private partial def countCore : Parser String := do
   skipString "COUNT = "
   let n ← manyChars digit
   ws
   return n

private def outputVOLenString : Parser String := pstring "Outputlen = "

private partial def OutputVOLenCore : Parser String := do
   let n ← manyChars digit
   ws
   return n

private partial def variableOutRecordCore : Parser CAVSVariableOutRecord := do
  let count ← countCore
  let len ← outputVOLenString *> OutputVOLenCore
  let msg ←  msgCore
  let md ← outputString *> mdCore
  ws
  let record :=  {count := count.toNat! , outputLen := len.toNat! ,  msg:= msg, output := md}
  return record

private partial def manyVariableOutRecordCore (acc : Array CAVSVariableOutRecord) : Parser $ Array CAVSVariableOutRecord := do
  let some _ ← peek? | return acc
  manyVariableOutRecordCore $ acc.push (← variableOutRecordCore)

private def variableOutFileCore : Parser CAVSVariableOutFile := do
  let mut f := cAVSVariableOutFile.mkEmpty
  f := {f  with comments :=  (← manyComments #[] )}
  ws
  f := {f  with parameters :=  (← manyParams #[] )}
  ws
  let records ← manyVariableOutRecordCore #[]
  f := {f with records := records }
  return f

private def variableOutFileContent : Parser CAVSVariableOutFile := do
  ws
  let res ← variableOutFileCore
  eof
  return res

private def parseVariableOutFile (s : String) : Except String CAVSVariableOutFile  :=
  match (variableOutFileContent s.mkIterator) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

def slurpVariableOutFile (pathname : String)   := do
  let contents ← IO.FS.readFile pathname
  let f ← IO.ofExcept $ parseVariableOutFile contents
  return {f with pathname := pathname}

--

structure CAVSHashMonteRecord where
  count : Nat
  md : String
deriving Inhabited, Repr

structure CAVSHashMonteFile where
  pathname : String := ""
  comments : Array String := #[]
  len : Nat := 0
  seed : String := ""
  records : Array CAVSHashMonteRecord := #[]
deriving Inhabited, Repr

private def cAVSHashMonteFile.mkEmpty : CAVSHashMonteFile :=
  {}

private partial def hashMonteRecordCore : Parser CAVSHashMonteRecord := do
  let count ← countCore
  let md ← mDString *> mdCore
  ws
  let record :=  {count := count.toNat!, md := md }
  return record

private partial def manyHashMonteRecordCore (acc : Array CAVSHashMonteRecord) : Parser $ Array CAVSHashMonteRecord := do
  let some _ ← peek? | return acc
  manyHashMonteRecordCore $ acc.push (← hashMonteRecordCore)

private def seedString : Parser String := pstring "Seed = "

private partial def seedCore : Parser String := do
   let n ← manyChars hexDigit
   ws
   return n

private def hashMonteFileCore : Parser CAVSHashMonteFile := do
  let mut f := cAVSHashMonteFile.mkEmpty
  f := {f  with comments :=  (← manyComments #[] )}
  ws
  let len ← lString *> bitsLenCore
  f := {f with len := len.toNat!}
  ws
  let seed ← seedString *> seedCore
  f := {f with seed := seed }
  ws
  let records ← manyHashMonteRecordCore #[]
  f := {f with records := records }
  return f

private def hashMonteFileContent : Parser CAVSHashMonteFile := do
  ws
  let res ← hashMonteFileCore
  eof
  return res

private def parseHashMonteFile (s : String) : Except String CAVSHashMonteFile  :=
  match (hashMonteFileContent s.mkIterator) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

def slurpHashMonteFile (pathname : String)   := do
  let contents ← IO.FS.readFile pathname
  let f ← IO.ofExcept $ parseHashMonteFile contents
  return {f with pathname := pathname}

--

structure CAVSXofMonteRecord where
  count : Nat
  outputLen : Nat
  output : String
deriving Inhabited, Repr

structure CAVSXofMonteFile where
  pathname : String := ""
  comments : Array String := #[]
  minOutputLen : Nat := 0
  maxOutputLen : Nat := 0
  msg : String := ""
  records : Array CAVSXofMonteRecord := #[]
deriving Inhabited, Repr

private def cAVSXofMonteFile.mkEmpty : CAVSXofMonteFile :=
  {}

private def minOutputLenString : Parser String := pstring "[Minimum Output Length (bits) = "
private def maxOutputLenString : Parser String := pstring "[Maximum Output Length (bits) = "

private partial def xofMonteRecordCore : Parser CAVSXofMonteRecord := do
  let count ← countCore
  let len ← outputVOLenString *> OutputVOLenCore
  let md ← outputString *> mdCore
  ws
  let record :=  {count := count.toNat!, outputLen := len.toNat!,  output := md }
  return record

private partial def manyXofMonteRecordCore (acc : Array CAVSXofMonteRecord) : Parser $ Array CAVSXofMonteRecord := do
  let some _ ← peek? | return acc
  manyXofMonteRecordCore $ acc.push (← xofMonteRecordCore)

private def xofMonteFileCore : Parser CAVSXofMonteFile := do
  let mut f := cAVSXofMonteFile.mkEmpty
  f := {f  with comments :=  (← manyComments #[] )}
  ws
  let len ← minOutputLenString *> bitsLenCore
  f := {f with minOutputLen := len.toNat!}
  ws
  let len ← maxOutputLenString *> bitsLenCore
  f := {f with maxOutputLen := len.toNat!}
  ws
  let msg ← msgCore
  f := {f  with msg := msg}
  ws
  let records ← manyXofMonteRecordCore #[]
  f := {f with records := records }
  return f

private def xofMonteFileContent : Parser CAVSXofMonteFile := do
  ws
  let res ← xofMonteFileCore
  eof
  return res

private def parseXofMonteFile (s : String) : Except String CAVSXofMonteFile  :=
  match (xofMonteFileContent s.mkIterator) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

def slurpXofMonteFile (pathname : String)   := do
  let contents ← IO.FS.readFile pathname
  let f ← IO.ofExcept $ parseXofMonteFile contents
  return {f with pathname := pathname}
