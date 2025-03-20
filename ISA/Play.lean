/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

abbrev Err := Except String

-- Getter and Setter for BitVec
def bvGet' (bv : BitVec n) (s e : Nat) : BitVec (e - s) :=
  (bv >>> s).setWidth (e - s)

def bvGet (bv : BitVec n) (s : Nat) : BitVec m :=
  (bv >>> s).setWidth m

def bvSet (bv : BitVec n) (s : Nat) (mid : BitVec m) : BitVec n :=
  let low := bvGet' bv 0 s
  let high := bvGet' bv (s+m) n
  (high ++ mid ++ low).setWidth n

-- "Vectors"
abbrev Vec (n c : Nat) := BitVec (n * c)
namespace Vec
def get (v : Vec n c) (i : Nat) : BitVec n := bvGet v (i*n)
def set (v : Vec n c) (i : Nat) (val : BitVec c) := bvSet v (i*c) val
end Vec

instance : GetElem (Vec n c) Nat (BitVec n) (fun _ _ => True) where
  getElem xs i _ := Vec.get xs i

notation "[" "u8" ";" c "]" => Vec 8 c
notation "[" "u16" ";" c "]" => Vec 16 c
notation "[" "u32" ";" c "]" => Vec 32 c

-- A vector of 3 u8's all initialized to 1 2 and 3
def vec : [u8; 3] := 0x030201
#eval vec[0]
#eval vec[1]
#eval vec[2]
#eval vec[4]

-- Each enumeration is a 8-bit value
abbrev AccumCmd := BitVec 8

namespace AccumCmd
def Idle             : AccumCmd := 0
def Zero             : AccumCmd := 1
def Accumulate       : AccumCmd := 2
def ZeroAccumulate   : AccumCmd := 3
def LoadAccumulate   : AccumCmd := 4
end AccumCmd

-- We could also generate a nice Lean version
inductive AccumCommand where
  | idle
  | zero
  | accumulate
  | zeroAccumulate
  | loadAccumulate

namespace AccumCommand

def ofAccumCmd : AccumCmd -> Err AccumCommand
  | .Idle => return .idle
  | .Zero => return .zero
  | .Accumulate => return .accumulate
  | .ZeroAccumulate => return .zeroAccumulate
  | .LoadAccumulate => return .loadAccumulate
  | d => throw s!"invalid AccumCmd {d}"

def toAccumCmd : AccumCommand -> AccumCmd
  | .idle => .Idle
  | .zero => .Zero
  | .accumulate => .Accumulate
  | .zeroAccumulate => .ZeroAccumulate
  | .loadAccumulate => .LoadAccumulate

end AccumCommand

-- Opcode is also a enumeration (a big one)
abbrev Opcode := BitVec 8

-- Header is a structure with 4 bytes
abbrev Header := BitVec 32
namespace Header
-- first 8-bits is Header
def opcode (h : Header) : Opcode := bvGet h 0
end Header

-- Each instruction is exactly 64-bytes
abbrev Inst := BitVec 512
namespace Inst
-- to make assertion functions work
def unknown : Inst -> Inst := id

-- the header is at the start
def header (i : Inst) : Header := bvGet i 0
end Inst

-- Each instruction format is also 64 bytes
abbrev s3d3_ts := BitVec 512
namespace s3d3_ts
def header (i : s3d3_ts) : Header := bvGet i 0
-- the accum cmd comes after the header
def accumulator_cmd (i : s3d3_ts) : AccumCmd := bvGet i 32
end s3d3_ts

-- For assertion functions
def Inst.s3d3_ts : Inst -> s3d3_ts := id

-- The big payoff
def foo (i : Inst) : Bool :=
  i.unknown.header.opcode = 7

def bar (i : Inst) : Bool :=
  i.s3d3_ts.accumulator_cmd == AccumCmd.Idle
