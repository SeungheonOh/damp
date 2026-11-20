/-
Range checks that a later persistent hash makes redundant (`--O3`).

A persistent hash reads its inputs under an alignment, and an input that does
not fit the bytes it is read as makes the hash fail: `Bytes<n>` is read as one
element of `8·(n mod 31)` bits (if `n mod 31 ≠ 0`) followed by `n / 31`
elements of 248 bits each (`Damp/Crypto/Prims.lean`, `parseBytesAtom`, after
ZKIR's `Alignment::parse_field_repr`; in the circuit, `persistent_hash`
decomposes each such element into exactly that many bytes, which constrains it
the same way). Compact range checks a `Bytes<32>` witness result, circuit
argument or coin value when it enters the circuit, and then usually hashes it:
the range check is implied by the hash, and costs rows of its own
(`constrain_bits 248` is 62 rows, `bench/costs.py`).

`Circuit.hashRanges` drops

* a `constrain e (.bits n)` with `n < 255`, and
* the range `.bits n` (`n < 255`) of a witness result `v`, when `v` does not
  occur again later in the same witness's results,

when the rest of the body certainly hashes `e` (or `.var v`) as an element of
at most `n` bits before any variable of it is rebound: some later statement
evaluates, whatever happens, a `phash` with `e` in such a position (in a
binding, an assertion, a range check, a guard, or the operands of a ledger
statement that does not read a variable of `e`), and no statement in between
binds a variable of `e`. Every statement in between either fails or leaves `e`
with its value, so a value that the dropped check would have refused makes
the run fail at the hash instead: the run fails exactly when it did.

That a hash fails on an input that does not fit is a property of the hash
functions, not of every `Prims`: the pass is sound for every `p` with
`AlignChecked p` (`Damp/Proofs/Optimize/HashRanges.lean`), which
`Damp.Crypto.prims` is proved to have. So it is an `--O3` pass, sound relative
to Damp's implementation of the persistent hash, as `foldHashes` is.
-/
import Damp.Optimize.Pass

namespace Damp.IR
open Damp.Zkir (AlignAtom)

/-- The elements of `xs` that a persistent hash with alignment `al` reads as
    bytes, each with the number of bits it must fit in. It follows
    `Crypto.binaryRepr` step by step; where the inputs run out or an atom
    cannot be read (`compress`) it stops. -/
def alignSlots {α : Type} : List AlignAtom → List α → List (α × Nat)
  | [], _ => []
  | .compress :: _, _ => []
  | .field :: _, [] => []
  | .field :: al, _ :: xs => alignSlots al xs
  | .bytes n :: al, xs =>
      if xs.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0) then []
      else if n % 31 = 0 then (xs.take (n / 31)).map (·, 248) ++ alignSlots al (xs.drop (n / 31))
      else match xs with
        | [] => []
        | x :: rest =>
            (x, 8 * (n % 31)) :: ((rest.take (n / 31)).map (·, 248) ++ alignSlots al (rest.drop (n / 31)))

mutual
/-- Every expression that some persistent hash inside `e` reads as bytes, with
    its width. Evaluating `e` evaluates every subexpression, so all of them. -/
def Expr.hashSlots : Expr → List (Expr × Nat)
  | .var _ | .const _ | .invalid _ => []
  | .add a b | .mul a b | .lt _ a b | .eq a b => a.hashSlots ++ b.hashSlots
  | .neg a | .disclose a | .divmod _ _ a => a.hashSlots
  | .select c a b => c.hashSlots ++ a.hashSlots ++ b.hashSlots
  | .hash xs => Expr.hashSlotsList xs
  | .phash _ al xs => alignSlots al xs ++ Expr.hashSlotsList xs
def Expr.hashSlotsList : List Expr → List (Expr × Nat)
  | [] => []
  | x :: xs => x.hashSlots ++ Expr.hashSlotsList xs
end

/-- The variables a statement binds. -/
def Stmt.binds : Stmt → List Var
  | .bind v _ _ => [v]
  | .witness _ _ _ outs _ => outs.map (·.1)
  | .ledger _ reads _ => reads
  | _ => []

/-- What a statement certainly hashes, in the environment it starts from:
    the hash slots of everything it evaluates whatever its guard (not the
    arguments of a witness call, which only the executor evaluates, and only
    when the guard holds). The operands of a ledger statement are evaluated
    after its reads are bound, so only slots that mention none of its reads
    count. -/
def Stmt.hashSlots : Stmt → List (Expr × Nat)
  | .bind _ _ e | .assert e _ | .constrain e _ => e.hashSlots
  | .witness g .. => g.hashSlots
  | .ledger g reads ops =>
      g.hashSlots ++ ((ops.flatMap fun op => Expr.hashSlotsList (op.encode Expr.const)).filter
        fun x => x.1.vars.all fun v => !reads.contains v)

/-- `e` is certainly hashed as an element of at most `n` bits, and a check of
    `n` bits can therefore go. -/
def hashImplied (F : List (Expr × Nat)) (e : Expr) (n : Nat) : Bool :=
  decide (n < 255) && F.any fun x => x.1 == e && decide (x.2 ≤ n)

/-- The results of a witness call with the ranges a later hash implies dropped. -/
def weakenOuts (F : List (Expr × Nat)) : List (Var × Option Range) → List (Var × Option Range)
  | [] => []
  | (v, some (.bits n)) :: rest =>
      (if hashImplied F (.var v) n && !(rest.any fun o => o.1 == v) then (v, none) else (v, some (.bits n)))
        :: weakenOuts F rest
  | o :: rest => o :: weakenOuts F rest

/-- The statements with redundant range checks dropped, and what the
    statements certainly hash from their start (before any is dropped). -/
def hashRangesGo : List Stmt → List Stmt × List (Expr × Nat)
  | [] => ([], [])
  | s :: rest =>
      let r := hashRangesGo rest
      let F := s.hashSlots ++ r.2.filter fun x => x.1.vars.all fun v => !s.binds.contains v
      match s with
      | .constrain e (.bits n) => (if hashImplied r.2 e n then r.1 else s :: r.1, F)
      | .witness g name args outs shape => (.witness g name args (weakenOuts r.2 outs) shape :: r.1, F)
      | _ => (s :: r.1, F)

/-- Drop range checks that a later persistent hash implies (`--O3`). -/
def Circuit.hashRanges (c : Circuit) : Circuit :=
  { c with body := (hashRangesGo c.body.toList).1.toArray }

end Damp.IR
