/-
The disclosure check.

Private data must not reach public state by accident. As in Compact, a value
that depends on a circuit argument or a witness result has to pass through
`disclose` before it can

* be an operand of a ledger operation,
* decide whether a ledger operation happens, or
* (witness results only) be returned from the circuit.

Hashing does not disclose; a commitment does, because its opening hides the
value. Values read from the ledger are already public.

This is a lint for the contract author, not part of what a proof guarantees:
the circuit is the same with or without `disclose`.
-/
import Damp.IR.Basic

namespace Damp.IR

/-- Where an undisclosed value came from. -/
inductive Source where
  | argument (name : String)
  | witness (name : String)
  deriving BEq, Repr

def Source.describe : Source → String
  | .argument n => s!"argument `{n}`"
  | .witness n => s!"the result of witness `{n}`"

abbrev Taint := List Source

def Taint.union (a b : Taint) : Taint := b.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) a

def Taint.describe (t : Taint) : String := ", ".intercalate (t.map Source.describe)

mutual
/-- The undisclosed sources an expression depends on. -/
def Expr.taint (σ : List (Var × Taint)) : Expr → Taint
  | .var v => (σ.lookup v).getD []
  | .const _ | .invalid _ | .disclose _ => []
  | .add a b | .mul a b | .lt _ a b | .eq a b => (a.taint σ).union (b.taint σ)
  | .neg a | .divmod _ _ a => a.taint σ
  | .select c a b => ((c.taint σ).union (a.taint σ)).union (b.taint σ)
  | .hash xs | .phash _ _ xs => Expr.taintList σ xs
def Expr.taintList (σ : List (Var × Taint)) : List Expr → Taint
  | [] => []
  | x :: xs => (x.taint σ).union (Expr.taintList σ xs)
end

private def hint (t : Taint) : String :=
  s!"{t.describe}. If making it public is intended, wrap it in `disclose`"

/-- Check a circuit; the error says what leaks and from where. -/
def Circuit.checkDisclosure (c : Circuit) : Except String Unit := do
  let mut σ : List (Var × Taint) := c.inputs.map fun i => (i.var, [.argument i.name])
  for s in c.body do
    match s with
    | .bind v _ e => σ := (v, e.taint σ) :: σ
    | .assert .. | .constrain .. => pure ()
    | .witness _ name _ outs _ => σ := outs.map (fun (v, _) => (v, [Source.witness name])) ++ σ
    | .ledger guard reads ops =>
        let g := guard.taint σ
        unless g.isEmpty do
          throw s!"whether a ledger operation runs depends on {hint g}"
        let operands := ops.flatMap fun op => op.encode Expr.const
        let t := Expr.taintList σ operands
        unless t.isEmpty do
          throw s!"a ledger operation stores or looks up a value that depends on {hint t}"
        σ := reads.map (fun v => (v, [])) ++ σ
  -- Arguments were supplied by the caller, who may have them back; witness data may not leave.
  let returned := (Expr.taintList σ c.outputs).filter fun | .witness _ => true | _ => false
  unless returned.isEmpty do
    throw s!"the circuit returns a value that depends on {hint returned}"

end Damp.IR
