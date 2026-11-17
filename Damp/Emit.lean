/-
Circuit IR to ZKIR v3.

Expressions are flattened to one instruction per operation, operands first and
left to right, sharing repeated subexpressions. Each ledger statement becomes
its reads as `public_input`s followed by one `impact` per VM instruction.

The functions here are written without a state monad: each takes the emitter
state and returns the instructions it adds and the new state. That is what
`Damp/EmitCorrect.lean` reasons about, and it is the code that runs.
-/
import Damp.IR
import Damp.Disclosure
import Damp.ZkirChecks

namespace Damp.Emit
open Damp.IR Damp.Zkir

structure State where
  /-- Number of the next register. -/
  next : Nat := 0
  /-- Where each IR variable lives. -/
  vars : List (Var × Operand) := []
  /-- Expressions already computed, and where. -/
  memo : List (Expr × Operand) := []

/-- A result, the instructions that compute it, and the state afterwards. -/
abbrev Res (α : Type) := Except String (α × List Instr × State)

/-- Add the instruction computing `e` into a fresh register, and remember it. -/
def finish (e : Expr) (hint : String) (mk : Ident → Instr) (pre : List Instr) (s : State) :
    Operand × List Instr × State :=
  let out : Ident := ⟨hint, s.next⟩
  (.var out, pre ++ [mk out], { s with next := s.next + 1, memo := (e, .var out) :: s.memo })

mutual
def expr (hint : String) : Expr → State → Res Operand
  | .var v, s =>
      match s.vars.lookup v with
      | some o => .ok (o, [], s)
      | none => .error s!"variable {v} used before it is bound"
  | .const c, s => .ok (.imm c, [], s)
  | .invalid msg, _ => .error msg
  | .disclose e, s => expr hint e s
  | e@(.add a b), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) =>
          match expr "t" b s1 with
          | .error m => .error m
          | .ok (b', is2, s2) => .ok (finish e hint (Instr.add · a' b') (is1 ++ is2) s2)
  | e@(.mul a b), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) =>
          match expr "t" b s1 with
          | .error m => .error m
          | .ok (b', is2, s2) => .ok (finish e hint (Instr.mul · a' b') (is1 ++ is2) s2)
  | e@(.neg a), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) => .ok (finish e hint (Instr.neg · a') is1 s1)
  | e@(.lt bits a b), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) =>
          match expr "t" b s1 with
          | .error m => .error m
          | .ok (b', is2, s2) => .ok (finish e hint (Instr.lessThan · a' b' bits) (is1 ++ is2) s2)
  | e@(.eq a b), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) =>
          match expr "t" b s1 with
          | .error m => .error m
          | .ok (b', is2, s2) => .ok (finish e hint (Instr.testEq · a' b') (is1 ++ is2) s2)
  | e@(.select c a b), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" c s with
        | .error m => .error m
        | .ok (c', is0, s0) =>
          match expr "t" a s0 with
          | .error m => .error m
          | .ok (a', is1, s1) =>
            match expr "t" b s1 with
            | .error m => .error m
            | .ok (b', is2, s2) =>
                .ok (finish e hint (Instr.condSelect · c' a' b') (is0 ++ is1 ++ is2) s2)
  | e@(.hash xs), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match exprs xs s with
        | .error m => .error m
        | .ok (xs', is1, s1) => .ok (finish e hint (Instr.transientHash · xs') is1 s1)
  | e@(.phash high align xs), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match exprs xs s with
        | .error m => .error m
        | .ok (xs', is1, s1) =>
            -- One hash yields both halves: `bytes_into_natives` returns the low
            -- 31 bytes first, then the top byte.
            let bytes : Ident := ⟨"bytes", s1.next⟩
            let lo : Ident := ⟨"t", s1.next + 1⟩
            let hi : Ident := ⟨"t", s1.next + 2⟩
            .ok (.var (if high then hi else lo),
              is1 ++ [.persistentHash bytes align xs', .bytesIntoNatives [lo, hi] (.var bytes)],
              { s1 with next := s1.next + 3, memo :=
                  (Expr.phash true align xs, .var hi) :: (Expr.phash false align xs, .var lo) :: s1.memo })
  | e@(.divmod quot bits a), s =>
      match s.memo.lookup e with
      | some o => .ok (o, [], s)
      | none =>
        match expr "t" a s with
        | .error m => .error m
        | .ok (a', is1, s1) =>
            -- One instruction yields both the quotient and the remainder.
            let q : Ident := ⟨"tmp", s1.next⟩
            let r : Ident := ⟨"tmp", s1.next + 1⟩
            .ok (.var (if quot then q else r),
              is1 ++ [.divModPowerOfTwo [q, r] a' bits],
              { s1 with next := s1.next + 2, memo :=
                  (Expr.divmod true bits a, .var q) :: (Expr.divmod false bits a, .var r) :: s1.memo })
def exprs : List Expr → State → Res (List Operand)
  | [], s => .ok ([], [], s)
  | x :: xs, s =>
      match expr "t" x s with
      | .error m => .error m
      | .ok (x', is1, s1) =>
        match exprs xs s1 with
        | .error m => .error m
        | .ok (xs', is2, s2) => .ok (x' :: xs', is1 ++ is2, s2)
end

/-- The instructions checking that `o` is in a range. -/
def constrain (o : Operand) (r : Range) (s : State) : List Instr × State :=
  match r with
  | .zero => ([.constrainEq o (.imm 0)], s)
  | .bool => ([.constrainToBoolean o], s)
  | .bits n => ([.constrainBits o n], s)
  | .below bound width =>
      let t : Ident := ⟨"tmp", s.next⟩
      ([.lessThan t o (.imm bound) width, .assert (.var t)], { s with next := s.next + 1 })

/-- A guard that is literally 1 is printed as "no guard" on input instructions. -/
def optGuard : Operand → Option Operand
  | .imm 1 => none
  | g => some g

/-- Give `v` a register. A variable may be bound only once: sharing of
    computed expressions relies on a variable never changing its meaning. -/
def bindVar (v : Var) (o : Operand) (s : State) : Except String State :=
  if (s.vars.lookup v).isSome then .error s!"variable {v} is bound twice"
  else .ok { s with vars := (v, o) :: s.vars }

/-- One input instruction per variable, each followed by its range check. -/
def reads (mk : Ident → Instr) : List (Var × Option Range) → State → Res Unit
  | [], s => .ok ((), [], s)
  | (v, range) :: rest, s =>
      let o : Ident := ⟨"t", s.next⟩
      match bindVar v (.var o) { s with next := s.next + 1 } with
      | .error m => .error m
      | .ok s1 =>
        let (cs, s2) := match range with
          | some r => constrain (.var o) r s1
          | none => ([], s1)
        match reads mk rest s2 with
        | .error m => .error m
        | .ok ((), is, s3) => .ok ((), mk o :: cs ++ is, s3)

/-- Compile the operands of each on-chain instruction, in order. -/
def operands : List (List Expr) → State → Res (List (List Operand))
  | [], s => .ok ([], [], s)
  | xs :: rest, s =>
      match exprs xs s with
      | .error m => .error m
      | .ok (os, is1, s1) =>
        match operands rest s1 with
        | .error m => .error m
        | .ok (oss, is2, s2) => .ok (os :: oss, is1 ++ is2, s2)

def stmt : Stmt → State → Res Unit
  | .bind v hint e, s =>
      match expr hint e s with
      | .error m => .error m
      | .ok (o, is, s1) =>
        match bindVar v o s1 with
        | .error m => .error m
        | .ok s2 => .ok ((), is, s2)
  | .assert cond _, s =>
      match expr "t" cond s with
      | .error m => .error m
      | .ok (o, is, s1) => .ok ((), is ++ [.assert o], s1)
  | .constrain e r, s =>
      match expr "t" e s with
      | .error m => .error m
      | .ok (o, is, s1) =>
        let (cs, s2) := constrain o r s1
        .ok ((), is ++ cs, s2)
  | .witness guard _ _ outs _, s =>
      match expr "t" guard s with
      | .error m => .error m
      | .ok (g, is, s1) =>
        match reads (fun o => .privateInput .native o (optGuard g)) outs s1 with
        | .error m => .error m
        | .ok ((), rs, s2) => .ok ((), is ++ rs, s2)
  | .ledger guard rds ops, s =>
      match expr "t" guard s with
      | .error m => .error m
      | .ok (g, is, s1) =>
        match reads (fun o => .publicInput .native o (optGuard g)) (rds.map fun v => (v, none)) s1 with
        | .error m => .error m
        | .ok ((), rs, s2) =>
          -- Operands of every instruction are computed before the first `impact`.
          match operands (ops.map fun op => op.encode Expr.const) s2 with
          | .error m => .error m
          | .ok (oss, os, s3) => .ok ((), is ++ rs ++ os ++ oss.map (Instr.impact g), s3)

def stmts : List Stmt → State → Res Unit
  | [], s => .ok ((), [], s)
  | st :: rest, s =>
      match stmt st s with
      | .error m => .error m
      | .ok ((), is1, s1) =>
        match stmts rest s1 with
        | .error m => .error m
        | .ok ((), is2, s2) => .ok ((), is1 ++ is2, s2)

/-- Give each circuit input a register. -/
def inputs : List Input → State → Except String (List (Ident × IrType) × State)
  | [], s => .ok ([], s)
  | i :: rest, s =>
      let n : Ident := ⟨i.name, s.next⟩
      match bindVar i.var (.var n) { s with next := s.next + 1 } with
      | .error m => .error m
      | .ok s1 =>
        match inputs rest s1 with
        | .error m => .error m
        | .ok (ins, s2) => .ok ((n, IrType.native) :: ins, s2)

/-- Emit a circuit exactly as given. -/
def circuitCore (c : Circuit) : Except String IrSource :=
  match inputs c.inputs {} with
  | .error m => .error m
  | .ok (ins, s0) =>
    match stmts c.body.toList s0 with
    | .error m => .error m
    | .ok ((), body, s1) =>
      match exprs c.outputs s1 with
      | .error m => .error m
      | .ok (outs, tail, _) =>
          .ok { inputs := ins, outputs := c.outputs.map fun _ => .native,
                instructions := (body ++ tail ++ if outs.isEmpty then [] else [Instr.output outs]).toArray }

/-- Variables a statement reads. -/
def uses : Stmt → List Var
  | .bind _ _ e => e.vars
  | .assert c _ => c.vars
  | .constrain e _ => e.vars
  | .witness g _ args _ _ => g.vars ++ Expr.varsList args
  | .ledger g _ ops =>
      g.vars ++ ops.flatMap fun op => (op.encode Expr.const).flatMap Expr.vars

/-- Drop `bind`s whose variable nothing later reads, so that guards which were
    named but never needed stay out of the circuit. -/
def pruneDeadBinds (c : Circuit) : Array Stmt :=
  let step (acc : List Stmt × List Var) (s : Stmt) : List Stmt × List Var :=
    let (kept, live) := acc
    match s with
    | .bind v _ _ => if live.contains v then (s :: kept, uses s ++ live) else (kept, live)
    | _ => (s :: kept, uses s ++ live)
  (c.body.foldr (fun s acc => step acc s) ([], c.outputs.flatMap Expr.vars)).1.toArray

/-- The circuit that is emitted: `c` without its unused bindings. -/
def pruned (c : Circuit) : Circuit := { c with body := pruneDeadBinds c }

def circuit (c : Circuit) : Except String IrSource := do
  if let e :: _ := c.errors then throw e
  let src ← circuitCore (pruned c)
  -- The obligations upstream's soundness result places on the producer.
  src.checkProducer
  return src

/-- A one-paragraph description of the emitted circuit. -/
def summary (c : Circuit) : String :=
  match circuit c with
  | .error e => s!"{c.name}: cannot be compiled: {e}"
  | .ok src =>
      let count (p : Instr → Bool) := (src.instructions.filter p).size
      let priv := count fun | .privateInput .. => true | _ => false
      let pub := count fun | .publicInput .. => true | _ => false
      let impacts := count fun | .impact .. => true | _ => false
      let asserts := count fun | .assert _ => true | _ => false
      let hashes := count fun | .transientHash .. | .persistentHash .. => true | _ => false
      s!"{c.name}: {src.instructions.size} instructions, {src.inputs.length} inputs, " ++
      s!"{src.outputs.length} outputs\n  {priv} private inputs, {pub} ledger reads, " ++
      s!"{impacts} ledger instructions, {asserts} asserts, {hashes} hashes"

/-- Why this circuit cannot be emitted, if it cannot. -/
def problem (c : Circuit) : Option String :=
  match (do let src ← circuit c; c.checkDisclosure; pure src) with
  | .ok _ => none
  | .error e => some e

end Damp.Emit
