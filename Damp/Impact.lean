/-
The Impact VM instructions that ledger operations compile to, and their
encoding as field elements in a circuit's public inputs.

The numbering is fixed by the Rust ledger (`FieldRepr` for `Op`); the cases
here were checked against compactc 0.36.1 output. Only instructions whose
encoding has been checked that way are included.

`Op` is generic in the operand type: circuit expressions in the IR, registers
when emitting ZKIR, field elements when evaluating.
-/
import Damp.Zkir

namespace Damp.Impact
open Damp.Zkir (AlignAtom)

/-- How an alignment atom appears in the transcript. -/
def atomCode : AlignAtom → Int
  | .bytes n => n
  | .compress => -1
  | .field => -2

/-- A value with its alignment. `vals` holds the field elements, flat. -/
structure Aligned (α : Type) where
  align : List AlignAtom
  vals : List α
  deriving Repr, Inhabited

/-- A state value written literally into an instruction. Only the forms seen in
    compactc 0.36.1 output: empty maps and Merkle trees, arrays of these. -/
inductive StateLit (α : Type) where
  | null
  | cell (v : Aligned α)
  | emptyMap
  | array (elems : List (StateLit α))
  /-- An empty bounded Merkle tree. compactc 0.36.1 can encode depths up to 15 only. -/
  | emptyMerkleTree (depth : Nat)
  deriving Repr, Inhabited

inductive Op (α : Type) where
  | lt | eq | type | size | and | or | neg | log | root | pop
  | add | sub | member | ckpt
  /-- Pop the top of the stack and require it to equal `result`: a ledger read. -/
  | popeq (cached : Bool) (align : List AlignAtom) (result : List α)
  | addi (imm : α)
  | subi (imm : α)
  /-- Push a cell holding `value`. -/
  | push (storage : Bool) (value : Aligned α)
  /-- Push the null state value (what a set stores against each member). -/
  | pushNull (storage : Bool)
  | rem (cached : Bool)
  | dup (n : Nat)
  | swap (n : Nat)
  | idx (cached pushPath : Bool) (path : List (Aligned α))
  | ins (cached : Bool) (n : Nat)
  /-- Push any state value; `push` and `pushNull` are its two commonest cases. -/
  | pushState (storage : Bool) (value : StateLit α)
  /-- Pop a boolean; if it is true, skip the next `skip` instructions. -/
  | branch (skip : Nat)
  /-- Skip the next `skip` instructions. -/
  | jmp (skip : Nat)
  /-- Concatenate the top two cells (uncached), `n` the maximum encoded size of the result. -/
  | concat (n : Nat)
  /-- `idx` (cached, not pushing the path) along the literal keys `pre`, then
      one more key taken from the top of the stack (popped). A stack key is
      encoded `-1`: `0x60 + |pre|`, the keys of `pre`, `-1`. -/
  | idxStack (pre : List (Aligned α))
  /-- `concat` of the top two cells, cached; `n` the maximum encoded size of the result. -/
  | concatCached (n : Nat)
  deriving Repr, Inhabited

def Aligned.mapM [Monad m] (f : α → m β) (v : Aligned α) : m (Aligned β) :=
  return { align := v.align, vals := ← v.vals.mapM f }

mutual
def StateLit.mapM [Monad m] (f : α → m β) : StateLit α → m (StateLit β)
  | .null => pure .null
  | .cell v => return .cell (← v.mapM f)
  | .emptyMap => pure .emptyMap
  | .array es => return .array (← StateLit.mapMList f es)
  | .emptyMerkleTree d => pure (.emptyMerkleTree d)
def StateLit.mapMList [Monad m] (f : α → m β) : List (StateLit α) → m (List (StateLit β))
  | [] => pure []
  | e :: es => return (← StateLit.mapM f e) :: (← StateLit.mapMList f es)
end

def Op.mapM [Monad m] (f : α → m β) : Op α → m (Op β)
  | .lt => pure .lt | .eq => pure .eq | .type => pure .type | .size => pure .size
  | .and => pure .and | .or => pure .or | .neg => pure .neg | .log => pure .log
  | .root => pure .root | .pop => pure .pop | .add => pure .add | .sub => pure .sub
  | .member => pure .member | .ckpt => pure .ckpt
  | .popeq c a r => return .popeq c a (← r.mapM f)
  | .addi i => return .addi (← f i)
  | .subi i => return .subi (← f i)
  | .push s v => return .push s (← v.mapM f)
  | .pushNull s => pure (.pushNull s)
  | .rem c => pure (.rem c)
  | .dup n => pure (.dup n)
  | .swap n => pure (.swap n)
  | .idx c p path => return .idx c p (← path.mapM (·.mapM f))
  | .ins c n => pure (.ins c n)
  | .pushState s v => return .pushState s (← v.mapM f)
  | .branch n => pure (.branch n)
  | .jmp n => pure (.jmp n)
  | .concat n => pure (.concat n)
  | .idxStack pre => return .idxStack (← pre.mapM (·.mapM f))
  | .concatCached n => pure (.concatCached n)

def Op.map (f : α → β) (op : Op α) : Op β := Id.run (op.mapM (m := Id) fun a => pure (f a))

section Encode
variable {α : Type} (const : Int → α)

def Aligned.encode (v : Aligned α) : List α :=
  const v.align.length :: v.align.map (fun a => const (atomCode a)) ++ v.vals

/- A state value's tag is its kind in the low nibble and a length in the high
   one: null 0, cell 1, map 2 (entry count), array 3 (length), bounded Merkle
   tree 4 (depth). Observed in compactc 0.36.1; it rejects depths above 15. -/
mutual
def StateLit.encode : StateLit α → List α
  | .null => [const 0]
  | .cell v => const 1 :: v.encode const
  | .emptyMap => [const 0x02]
  | .array es => const (16 * es.length + 3) :: StateLit.encodeList es
  | .emptyMerkleTree d => [const (16 * d + 4)]
def StateLit.encodeList : List (StateLit α) → List α
  | [] => []
  | e :: es => StateLit.encode e ++ StateLit.encodeList es
end

/-- The field elements this instruction contributes to the public inputs. -/
def Op.encode : Op α → List α
  | .lt => [const 0x01] | .eq => [const 0x02] | .type => [const 0x03] | .size => [const 0x04]
  | .and => [const 0x06] | .or => [const 0x07] | .neg => [const 0x08] | .log => [const 0x09]
  | .root => [const 0x0a] | .pop => [const 0x0b]
  | .popeq cached align result =>
      const (if cached then 0x0d else 0x0c) :: const align.length
        :: align.map (fun a => const (atomCode a)) ++ result
  | .addi i => [const 0x0e, i]
  | .subi i => [const 0x0f, i]
  | .push storage v => const (if storage then 0x11 else 0x10) :: const 1 :: v.encode const
  | .pushNull storage => [const (if storage then 0x11 else 0x10), const 0]
  | .add => [const 0x14] | .sub => [const 0x15]
  | .member => [const 0x18]
  | .rem cached => [const (if cached then 0x1a else 0x19)]
  | .dup n => [const (0x30 + n)]
  | .swap n => [const (0x40 + n)]
  | .idx cached pushPath path =>
      let base : Int := match cached, pushPath with
        | false, false => 0x50 | true, false => 0x60 | false, true => 0x70 | true, true => 0x80
      const (base + (path.length - 1 : Nat)) :: path.flatMap (·.encode const)
  | .ins cached n => [const ((if cached then 0xa0 else 0x90) + n)]
  | .ckpt => [const 0xff]
  | .pushState storage v => const (if storage then 0x11 else 0x10) :: v.encode const
  | .branch n => [const 0x12, const n]
  | .jmp n => [const 0x13, const n]
  | .concat n => [const 0x16, const n]
  | .idxStack pre => const (0x60 + pre.length) :: pre.flatMap (·.encode const) ++ [const (-1)]
  | .concatCached n => [const 0x17, const n]

end Encode
end Damp.Impact
