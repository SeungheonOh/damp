import Damp

/-! Short-circuit evaluation: `&&.`, `||.`, `select` and a value-level `if` evaluate
their second operand (the branch not taken) only where it is reached, as Compact's
`&&`, `||` and `?:` do. A `(← …)` there runs under the guard of the first operand
(docs/language.md, "Short-circuit evaluation"). The guards below read the IR each
circuit is built to: which guard each witness call and ledger operation carries. -/
namespace Examples.ShortCircuit
open Damp Damp.IR

enum Phase where
  | open_
  | closed

ledger
  phase : Cell Phase
  total : Cell Field
  hits : Counter

witness ticket : Field
witness spare : Field

/-- Compact: `assert(phase == Phase.open_ && ticket() == 7, "closed")`. The witness is
    asked only while the phase is open. -/
circuit enter : Unit := do
  require ((← phase.read) ==. Phase.open_ &&. (← ticket) ==. 7) "closed"
  hits.increment 1

/-- Compact: `assert(phase == Phase.closed || total == 0, "busy")`: `total` is read only
    while the phase is open. -/
circuit settle : Unit := do
  require ((← phase.read) ==. Phase.closed ||. (← total.read) ==. 0) "busy"
  phase.write Phase.closed

/-- Compact: `return phase == Phase.open_ ? some<Field>(total) : none<Field>();` -/
circuit peek : Maybe Field := do
  return if (← phase.read) ==. Phase.open_ then Maybe.some (← total.read) else Maybe.none

/-- `select` with actions in its branches: each witness is asked only on its side. -/
circuit pick (b : Boolean) : Field := do
  return disclose (select (disclose b) (← ticket) (← spare))

/-- An action in an `if%` branch that is not a `do` block runs inside the branch. -/
circuit store (b : Boolean) : Unit := do
  if% disclose b then total.write (disclose (← ticket))

/-- Operands without actions are values: `&&.` is `Boolean.and`, as before. -/
circuit both (a b : Boolean) : Boolean := return disclose (a &&. b)

/-- A value-level `if` in a plain definition is `select`. -/
def larger (x y : Uint16) : Uint16 := if x <. y then y else x

/-- `const` takes a tuple or `⟨…⟩` of names. -/
circuit sumProd (p : Field × Field) : Field := do
  const (a, b) := p
  const ⟨s, t⟩ ← pure (a + b, a * b)
  return s + t

contract shortCircuit

/-! ### What each circuit is built to -/

/-- The effects of a circuit, in order: what each is and the guard it runs under. -/
def effects (c : Circuit) : List (String × Expr) :=
  c.body.toList.filterMap fun
    | .witness g name _ _ _ => some (s!"witness {name}", g)
    | .ledger g _ _ => some ("ledger", g)
    | _ => none

/-- The expression a statement named `v`. -/
def binding (c : Circuit) (v : Var) : Option Expr :=
  c.body.toList.findSome? fun
    | .bind w _ e => if w == v then some e else none
    | _ => none

-- `enter`: the phase is read (variable 0) unconditionally, `phase == open_` is named
-- (variable 1) and the witness runs under it; the conjunction is `select v1 (ticket == 7) 0`.
#guard effects enter.circuit == [("ledger", .const 1), ("witness ticket", .var 1), ("ledger", .const 1)]
#guard binding enter.circuit 1 == some (.eq (.var 0) (.const 0))
#guard enter.circuit.body.toList.any fun
  | .assert (.select (.var 1) (.eq (.var 2) (.const 7)) (.const 0)) _ => true
  | _ => false

-- `settle`: `total` is read under `!(phase == closed)` (variable 2 names the negation).
#guard effects settle.circuit == [("ledger", .const 1), ("ledger", .var 2), ("ledger", .const 1)]
#guard binding settle.circuit 1 == some (.eq (.var 0) (.const 1))
#guard binding settle.circuit 2 == some (.select (.var 1) (.const 0) (.const 1))

-- `peek`: `total` is read under `phase == open_`.
#guard effects peek.circuit == [("ledger", .const 1), ("ledger", .var 1)]
#guard binding peek.circuit 1 == some (.eq (.var 0) (.const 0))

-- `pick`: `ticket` under `b`, `spare` under `!b`.
#guard (effects pick.circuit).map (·.1) == ["witness ticket", "witness spare"]
#guard (effects pick.circuit).map (·.2) != [.const 1, .const 1]

-- `store`: the witness runs under `b`, like the write.
#guard (effects store.circuit).all fun (_, g) => g != .const 1

-- `both`: no statement besides the inputs' range checks; `&&.` on values is `Boolean.and`.
#guard (both.circuit.body.toList.filter fun | .constrain .. => false | _ => true).isEmpty
example (a b : Boolean) : (a &&. b) = Boolean.and a b := rfl

example (x y : Uint16) : larger x y = select (x <. y) y x := rfl

-- `sumProd`: each part computed once, named after the pattern.
#guard (sumProd.circuit.body.toList.filterMap fun | .bind _ h _ => some h | _ => none) =
  ["a_b", "a_b", "s_t", "s_t"]

end Examples.ShortCircuit
