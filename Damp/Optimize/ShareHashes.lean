/-
One hash for the two arms of a conditional (`--O3`).

When a circuit computes a hash of the same shape in both arms of a
conditional, one hash of the selected inputs does: `H (select c a b)`,
componentwise, in place of `select c (H a) (H b)`. A persistent hash is
about 1 900 to 3 700 rows (`bench/costs.py`) and a `select` one, so this pays
whenever the inputs differ in fewer than a thousand places.

Whether it is exact depends on the hash, because evaluation is partial and a
conditional evaluates both arms:

* `select c (hash as) (hash bs)` (the transient hash, which cannot fail) and
  `hash (select c as bs)` evaluate to the same thing, failures included, for
  any hash functions, as long as `as` and `bs` have the same length and differ
  somewhere (where they agree, the input is kept as it is; a place where they
  differ makes the new form evaluate `c` and require it to be 0 or 1, as the
  conditional did).
* `select c (phash as) (phash bs)` fails when the hash of the arm *not* taken
  fails, and `phash (select c as bs)` does not compute that hash. With hash
  functions that refuse an input that does not fit its alignment (Midnight's,
  `Damp.Crypto.prims`), the two agree when the inputs differ only in constants
  that fit the bytes their places are read as: then both arms' hashes fail
  together. So this part is sound only for `Crypto.prims`
  (`Pass.SoundFor Crypto.prims`), and runs at `--O3`.

Compact rarely produces the conditional itself: an `if` writes each arm's
hash into a ledger operation guarded by the arm's condition
(`coracle.start`: `red.write(red_pk(sk))` under `state == no_game`,
`blue.write(blue_pk(sk))` under its negation, the two keys hashes of `sk` with
different constant domain separators). A ledger statement evaluates its
operands whatever its guard, but uses their values only when the guard is 1
(when it is 0 it declares zeros), so in the statement guarded by `c` the
operand `phash as` can be replaced by `phash (select c as bs)`: equal when
`c` is 1, and failing exactly when it did when `c` is 0, by the same argument.
The statement guarded by the negation of `c` gets the same expression in
place of `phash bs`, and the emitter, which shares equal expressions,
computes the hash once. `Circuit.shareGuarded` plans such pairs over the
whole body and then checks each replacement where it is made, against what is
known there (`Defs`, as in `Damp/Optimize/MergeChecks.lean`): that the
statement's guard is `c` (or its negation) and that the inputs differ only in
constants that fit. Ledger operations, their order and their public inputs
are unchanged: only how an operand is computed.

Measured: `coracle.start` 59 149 -> 55 408 rows at `--O3` (one persistent
hash of two `Bytes<32>`, 3 741 rows). The other same-shape pairs in the
benchmark (`coracle.withdraw` and `concede`) differ in inputs computed inside
each arm (a witness, ledger reads), which are not constants; they are left
alone. Proofs: `Damp/Proofs/Optimize/ShareHashes.lean`.
-/
import Damp.Optimize.MergeChecks
import Damp.Optimize.Algebra

namespace Damp.IR
open Damp.Zkir (AlignAtom)

/-- The inputs of one hash for both arms: where `as` and `bs` agree the input
    itself, where they differ `select c a b`. -/
def zipSel (c : Expr) : List Expr → List Expr → List Expr
  | a :: as, b :: bs => (if a == b then a else .select c a b) :: zipSel c as bs
  | _, _ => []

/-- `a` and `b` agree, or are both constants. -/
def agreeOrConst : Expr × Expr → Bool
  | (a, b) => a == b || (match a, b with | .const _, .const _ => true | _, _ => false)

/-- In a byte slot of `w` bits, `a` and `b` agree, or are both constants that fit. -/
def slotOk : (Expr × Expr) × Nat → Bool
  | ((a, b), w) => a == b ||
      (match a, b with
       | .const k, .const k' => decide ((Fr.ofInt k).val < 2 ^ w) && decide ((Fr.ofInt k').val < 2 ^ w)
       | _, _ => false)

/-- A persistent hash of `as` and one of `bs` under the alignment `al` fail
    together: same length, different somewhere, and wherever they differ both
    are constants, fitting the bytes their place is read as. -/
def phashMergeable (al : List AlignAtom) (as bs : List Expr) : Bool :=
  as.length == bs.length && !(Expr.sameList as bs) && (as.zip bs).all agreeOrConst &&
    (alignSlots al (as.zip bs)).all slotOk

/-- How many places two input lists differ in. -/
def diffCount (as bs : List Expr) : Nat := ((as.zip bs).filter fun (a, b) => !(a == b)).length

/-! ## The conditional of two hashes -/

/-- `select c (H as) (H bs)` as `H (select c as bs)`, at the root of `e`. -/
def shareSelRoot : Expr → Expr
  | .select c (.hash as) (.hash bs) =>
      if as.length == bs.length && !(Expr.sameList as bs) && diffCount as bs ≤ 8 then .hash (zipSel c as bs)
      else .select c (.hash as) (.hash bs)
  | .select c (.phash h al as) (.phash h' al' bs) =>
      if h == h' && al == al' && phashMergeable al as bs then .phash h al (zipSel c as bs)
      else .select c (.phash h al as) (.phash h' al' bs)
  | e => e

mutual
/-- `shareSelRoot` everywhere in an expression, bottom up. -/
def Expr.shareSel : Expr → Expr
  | .add a b => .add a.shareSel b.shareSel
  | .mul a b => .mul a.shareSel b.shareSel
  | .neg a => .neg a.shareSel
  | .lt n a b => .lt n a.shareSel b.shareSel
  | .eq a b => .eq a.shareSel b.shareSel
  | .select c a b => shareSelRoot (.select c.shareSel a.shareSel b.shareSel)
  | .hash xs => .hash (Expr.shareSelList xs)
  | .phash h al xs => .phash h al (Expr.shareSelList xs)
  | .divmod q n a => .divmod q n a.shareSel
  | .disclose a => .disclose a.shareSel
  | e => e
def Expr.shareSelList : List Expr → List Expr
  | [] => []
  | x :: xs => x.shareSel :: Expr.shareSelList xs
end

/-- One hash of selected inputs for a conditional of two hashes, everywhere. -/
def Circuit.shareSelects (c : Circuit) : Circuit := c.mapExprs Expr.shareSel

/-! ## Hashes in ledger operands under complementary guards -/

/-- A replacement in one ledger statement: the operand `phash h al (as or
    bs)` (`as` if `pos`, `bs` otherwise) by `phash h al (zipSel c as bs)`. In
    the statement it is made in, the guard must be `c` if `pos` and the
    negation of `c` otherwise. -/
structure Repl where
  c : Expr
  h : Bool
  al : List AlignAtom
  as : List Expr
  bs : List Expr
  pos : Bool

/-- The operand a replacement replaces. -/
def Repl.old (r : Repl) : Expr := .phash r.h r.al (if r.pos then r.as else r.bs)

/-- What it is replaced by. -/
def Repl.new (r : Repl) : Expr := .phash r.h r.al (zipSel r.c r.as r.bs)

/-- Whether a replacement is sound in a ledger statement with guard `g` and
    reads `reads`, given what is known there. -/
def Repl.ok (D : Defs) (g : Expr) (reads : List Var) (r : Repl) : Bool :=
  phashMergeable r.al r.as r.bs &&
  (if r.pos then D.resolve g == r.c else D.isNot g r.c) &&
  (r.c.vars ++ Expr.varsList r.as ++ Expr.varsList r.bs).all (fun v => !reads.contains v)

/-- Replace each operand by the first verified replacement of it. -/
def replaceWith (rs : List Repl) (e : Expr) : Expr :=
  match rs.find? fun r => r.old == e with
  | some r => r.new
  | none => e

/-- A ledger statement with the replacements that are sound in it made; the
    instructions are kept as they were if the result would not pass
    `ledgerProblem`. -/
def shareStmt (D : Defs) (rs : List Repl) : Stmt → Stmt
  | .ledger g reads ops =>
      let ok := rs.filter (Repl.ok D g reads)
      let ops' := ops.map (·.map (replaceWith ok))
      if ok.isEmpty then .ledger g reads ops
      else .ledger g reads (if (IR.ledgerProblem reads ops').isNone then ops' else ops)
  | s => s

/-- Rewrite the statements, first to last; `plan i` proposes the replacements
    for the statement at index `i`. -/
def shareGo (plan : Nat → List Repl) : Defs → Nat → List Stmt → List Stmt
  | _, _, [] => []
  | D, i, s :: rest => shareStmt D (plan i) s :: shareGo plan (D.after s) (i + 1) rest

/-- A guard as a condition and a polarity: `select x 0 1` is `x` negated. -/
def guardForm (D : Defs) (g : Expr) : Expr × Bool :=
  match D.resolve g with
  | .select x (.const 0) (.const 1) => (x, false)
  | x => (x, true)

/-- The persistent hashes among the operands of ledger statements, with the
    statement's index and the condition and polarity of its guard. -/
def ledgerHashes : Defs → Nat → List Stmt → List (Nat × Expr × Bool × Bool × List AlignAtom × List Expr)
  | _, _, [] => []
  | D, i, s :: rest =>
      let here := match s with
        | .ledger g _ ops =>
            let (c, pos) := guardForm D g
            (ops.flatMap fun op => op.encode Expr.const).filterMap fun
              | .phash h al xs => some (i, c, pos, h, al, xs)
              | _ => none
        | _ => []
      here ++ ledgerHashes (D.after s) (i + 1) rest

/-- Pairs of hashes of the same shape in statements under a condition and its
    negation, as replacements per statement index. -/
def planShares (body : List Stmt) : List (Nat × Repl) :=
  let hs := ledgerHashes [] 0 body
  hs.flatMap fun (i, c, pos, h, al, as) =>
    if !pos then [] else
    hs.filterMap (fun (j, c', pos', h', al', bs) =>
      if !pos' && c' == c && h' == h && al' == al && phashMergeable al as bs then some (j, bs) else none)
    |>.head?.toList.flatMap fun (j, bs) =>
      [(i, { c, h, al, as, bs, pos := true }), (j, { c, h, al, as, bs, pos := false })]

/-- Share hashes between ledger operands under complementary guards. -/
def Circuit.shareGuarded (c : Circuit) : Circuit :=
  let body := c.body.toList
  let plan := planShares body
  { c with body := (shareGo (fun i => (plan.filter (·.1 == i)).map (·.2)) [] 0 body).toArray }

end Damp.IR
