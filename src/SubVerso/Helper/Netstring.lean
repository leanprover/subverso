/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import SubVerso.Compat
public section

namespace SubVerso.Helper

/-!
An implementation of DJB's [netstrings](https://cr.yp.to/proto/netstrings.txt), one of the
officially-recommended transports for JSON-RPC. It's a very lightweight way of length-encoding
messages.
-/

/--
Reads a netstring from a stream, returning its bytes, or `none` if an EOF is the first thing in the stream.

If the stream doesn't contain a valid netstring, or an EOF occurs during the netstring, an exception is thrown.
-/
def readNetstring (stream : IO.FS.Stream) : IO (Option ByteArray) := do
  -- This byte-at-atime reading is a bit silly, but expedient, and unlikely to be the bottleneck
  let mut len : String := ""
  repeat
    let byte ← stream.read 1
    if byte.size = 0 then
      if len == "" then return none -- EOF between messages
      else throw <| .userError s!"Unexpected EOF decoding input after length '{len}'"
    let byte := byte[0]!
    let c := Char.ofNat byte.toNat
    if c.isDigit then len := len.push c
    else if c == ':' then break
    else throw <| .userError s!"Unexpected input character in length '{c}'"
  let some length := len.toNat?
    | throw <| .userError "Failed to decode length {repr len}"
  if length > 99999 then throw <| .userError "Implausible length: {length}"
  let length : USize := .ofNat length
  let mut buf : ByteArray := {}
  while buf.usize < length do
    let payload ← stream.read ((length - buf.usize) + 1)
    if payload.size == 0 then
      throw <| .userError s!"Unexpected EOF reading message after {buf.size} out of {length} bytes"
    buf := buf ++ payload
  let lastChar := Char.ofNat buf[buf.size - 1]!.toNat
  if lastChar == ',' then
    return some (buf.extract 0 (buf.size - 1))
  else
    throw <| .userError s!"Expected trailing comma, got '{lastChar}'"

/--
Writes the provided bytes to the stream as a netstring.
-/
def writeNetstring (stream : IO.FS.Stream) (message : ByteArray) : IO Unit := do
  stream.putStr (s!"{message.size}:")
  stream.write message
  stream.putStr ","
  stream.flush
