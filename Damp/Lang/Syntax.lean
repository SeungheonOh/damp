/-
Notation for writing contracts.

Everything here is a macro that expands to the plain functions of
`Damp/Lang/Contract.lean` and `Damp/Lang/Ledger.lean`. The one rewrite of the
user's terms is syntactic and local: a `(← …)` in the lazy operand of `&&.`, `||.`,
`select` or a conditional is moved into a `do` block of its own, so that it runs
under that operand's guard ("Short-circuit evaluation" below). A contract written
with this notation is still an ordinary Lean value, and can equally be written
without it.

    struct Point where
      x : Field
      y : Uint8

    ledger
      total : Cell Field
      seen  : Map Uint16 Point

    witness secret : Field

    circuit add (p : Point) (on : Boolean) : Field := do
      const s ← secret
      if% on then total.write (p.x + s)
      total.read

    contract Example
-/
import Lean
import Damp.Compile.Build

namespace Damp
open Lean

/-! ## Operators

Circuit comparisons return a circuit `Boolean`, so they cannot reuse `<`, `==`
and friends, which produce `Prop` or `Bool`. They carry a trailing dot instead,
with the precedences of their Lean counterparts. -/

infix:50 " <. " => cmpLt
infix:50 " >. " => cmpGt
infix:50 " <=. " => cmpLe
infix:50 " >=. " => cmpGe
infix:50 " ==. " => cmpEq
infix:50 " !=. " => cmpNe
prefix:max "!." => Boolean.not

/-- `a &&. b`: the conjunction of two circuit `Boolean`s. As in Compact, `b` is
    evaluated only where `a` holds: a `(← …)` in `b` runs under that guard (see
    "Short-circuit evaluation" below). -/
syntax:35 (name := andOp) term:35 " &&. " term:36 : term
/-- `a ||. b`: the disjunction of two circuit `Boolean`s. As in Compact, `b` is
    evaluated only where `a` does not hold. -/
syntax:30 (name := orOp) term:30 " ||. " term:31 : term

macro_rules
  | `($a &&. $b) => `(Boolean.and $a $b)
  | `($a ||. $b) => `(Boolean.or $a $b)

/-! ## Conditionals -/

/-- `if% c then t else e`: both branches are built; effects are guarded by `c`
    and the results selected. Without `else`, `t` is run for its effects. -/
syntax (name := circuitIf) "if% " term " then " term (" else " term)? : term

macro_rules
  | `(if% $c then $t else $e) => `(Damp.cond $c $t $e)
  | `(if% $c then $t) => `(Damp.when_ $c $t)

/-! ### Plain `if`

With `open Damp`, Lean's own `if c then t else e` also works when `c` is a
circuit `Boolean`: as an expression, and as the last statement of a `do` block
or loop body, where it may assign `let mut` variables. An elaborator chooses
between expansions by looking at types: Lean's usual `ite c t e` unless the
condition is a circuit `Boolean`; then `Damp.condChecked c t e` when the `if`
is a `CircuitM` computation, and `Damp.select c t e` when it is known to be a
value (its expected type, or else the type of `t`, is known and is not
`CircuitM _`), as in a plain `def`. It does not rewrite the branches.

`do` notation moves the statements that follow an `if` into both of its
branches. That is harmless when only one branch runs, but here both are built,
so the rest of the block would be built twice. The branches reach this
elaborator already elaborated, so this cannot be seen in the syntax; instead
`Damp.condChecked` reports it when the circuit is built, by noticing that both
branches end with the same effect. Use `if%` for a conditional that has
statements after it. -/

/-- Chooses the meaning of `if` from the type of its condition. -/
syntax (name := ifDispatch) "if_dispatch% " term:max ppSpace term:max ppSpace term:max : term

open Lean.Elab Lean.Elab.Term Lean.Meta in
/-- Whether `c` elaborates to a circuit `Boolean`. Leaves no trace. -/
private def isCircuitCondition (c : Term) : TermElabM Bool := do
  let saved ← saveState
  let isCircuit ←
    try
      let ce ← withoutErrToSorry (elabTerm c none)
      synthesizeSyntheticMVarsNoPostponing
      let ty ← whnfR (← instantiateMVars (← inferType ce))
      pure (ty.isConstOf ``Damp.Boolean)
    catch _ => pure false
  saved.restore
  return isCircuit

open Lean.Elab Lean.Elab.Term Lean.Meta in
/-- Whether a type is known not to be a `CircuitM` computation: it is not a
    metavariable (or an application of one) and does not unify with `CircuitM ?β`. -/
private def knownNotCircuitM (ty : Expr) : TermElabM Bool := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.getAppFn.isMVar then return false
  withNewMCtxDepth do
    let β ← mkFreshTypeMVar
    return !(← isDefEq ty (mkApp (mkConst ``Damp.CircuitM) β))

open Lean.Elab Lean.Elab.Term Lean.Meta in
/-- Whether an `if` on a circuit `Boolean` is a value-level conditional (`select`)
    rather than a `CircuitM` one: its expected type, or failing that the type of its
    `then` branch, is known and is not `CircuitM _`. Leaves no trace. -/
private def isValueConditional (t : Term) (expectedType? : Option Expr) : TermElabM Bool := do
  if let some ty := expectedType? then
    if !(← instantiateMVars ty).getAppFn.isMVar then return ← knownNotCircuitM ty
  let saved ← saveState
  let r ←
    try
      let te ← withoutErrToSorry (elabTerm t none)
      synthesizeSyntheticMVarsNoPostponing
      knownNotCircuitM (← inferType te)
    catch _ => pure false
  saved.restore
  return r

open Lean.Elab Lean.Elab.Term Lean.Meta in
@[term_elab ifDispatch] def elabIfDispatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(if_dispatch% $c $t $e) =>
    if ← isCircuitCondition c then
      if ← isValueConditional t expectedType? then
        elabTerm (← `(Damp.select $c $t $e)) expectedType?
      else elabTerm (← `(Damp.condChecked $c $t $e)) expectedType?
    else elabTerm (← `(ite $c $t $e)) expectedType?
  | _ => throwUnsupportedSyntax

scoped macro_rules
  | `(if $c then $t else $e) => `(if_dispatch% ($c) ($t) ($e))

/-- `if_value% c t e`, `t e : CircuitM α`: a value-level conditional whose branches
    perform actions. `Damp.cond c t e` when `c` is a circuit `Boolean` (both branches
    are built, each one's effects guarded), `ite c t e` otherwise. Unlike a plain `if`
    in statement position nothing follows the conditional inside its branches, so
    there is no duplicate-effect check. -/
syntax (name := ifValue) "if_value% " term:max ppSpace term:max ppSpace term:max : term

open Lean.Elab Lean.Elab.Term Lean.Meta in
@[term_elab ifValue] def elabIfValue : TermElab := fun stx expectedType? => do
  match stx with
  | `(if_value% $c $t $e) =>
    if ← isCircuitCondition c then elabTerm (← `(Damp.cond $c $t $e)) expectedType?
    else elabTerm (← `(ite $c $t $e)) expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Short-circuit evaluation

In Compact `a && b`, `a || b` and `c ? x : y` evaluate their second operand (the
branch not taken) only when it is reached: a witness call, ledger operation or
assertion there happens only then, and compactc emits it under that guard. Lean's
`do` notation would instead lift every `(← …)` in an expression to a statement
before it, unconditionally. So, before that happens, each statement of a `do`
block is rewritten:

* `a &&. b`, where `b` contains a `(← …)`, becomes
  `(← Boolean.andThen a (do pure b))`: `b` is built under the guard `a`, and the
  result is `select a b false`, which is what compactc emits;
* `a ||. b` likewise becomes `(← Boolean.orElse a (do pure b))`: `b` under `!a`,
  result `select a true b`;
* `select c x y` (Damp's `select`), where `x` or `y` contains a `(← …)`, becomes
  `(← cond c (do pure x) (do pure y))`;
* with `open Damp`, a value-level `if c then x else y` likewise becomes
  `(← if_value% c (do pure x) (do pure y))` (`cond` on a circuit `Boolean`, Lean's
  `ite` on a `Bool` or `Prop`); without the rewrite Lean rejects a `(← …)` in a
  branch of an `if`-expression;
* `if% c then t else e`, where a branch that is not a `do` block contains a `(← …)`,
  gets `do` around its branches, so the action runs inside the branch, under its
  guard.

The left operand and the condition are evaluated as before, in place. An operand
without `(← …)` is untouched, so `a &&. b` on values is still `Boolean.and a b`:
a value has no effects to guard. The rewrite looks only at syntax; it does not
descend into a nested `do` block (which gets its own), and it never changes a
statement that has none of these forms. -/

namespace ShortCircuit

/-- Syntax that `do` notation does not lift a `(← …)` out of. -/
private def delimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.do || k == ``Parser.Term.doSeqIndent || k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn || k == ``Parser.Term.termUnless || k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

/-- Whether `stx` contains a `(← …)` that belongs to the `do` block around it. -/
partial def hasAction : Syntax → Bool
  | .node _ k args =>
    if delimiter k then false
    else if k == ``Parser.Term.nestedAction then true
    else args.any hasAction
  | _ => false

private def isDampSelect (f : Ident) : MacroM Bool := do
  let cands ← Macro.resolveGlobalName f.getId
  return cands.any fun (n, fields) => n == ``Damp.select && fields.isEmpty

/-- Rewrite the short-circuit forms in `stx` (see above); the flag records whether
    anything changed. `plainIf`: also Lean's `if … then … else …`. -/
partial def rewrite (plainIf : Bool) (stx : Syntax) : StateT Bool MacroM Syntax := do
  match stx with
  | .node info k args =>
    if delimiter k then return stx
    let go (s : Syntax) : StateT Bool MacroM Term := return ⟨← rewrite plainIf s⟩
    if (k == ``andOp || k == ``orOp) && args.size == 3 && hasAction args[2]! then
      let a ← go args[0]!
      let b : Term := ⟨args[2]!⟩
      set true
      return ← if k == ``andOp then `((← Damp.Boolean.andThen $a (do pure $b)))
        else `((← Damp.Boolean.orElse $a (do pure $b)))
    if k == ``circuitIf then
      match stx with
      | `(if% $c then $t else $e) =>
        if hasAction t || hasAction e then
          let c ← go c
          set true
          return ← `(if% $c then (do $t:term) else (do $e:term))
      | `(if% $c then $t) =>
        if hasAction t then
          let c ← go c
          set true
          return ← `(if% $c then (do $t:term))
      | _ => pure ()
    if plainIf && k == ``termIfThenElse then
      if let `(if $c then $t else $e) := stx then
        if hasAction t || hasAction e then
          let c ← go c
          set true
          return ← `((← if_value% ($c) (do pure $t) (do pure $e)))
    if k == ``Parser.Term.app then
      if let `($f:ident $c $x $y) := stx then
        if (hasAction x || hasAction y) && (← isDampSelect f) then
          let c ← go c
          set true
          return ← `((← Damp.cond $c (do pure $x) (do pure $y)))
    return .node info k (← args.mapM (rewrite plainIf))
  | _ => return stx

private def expand (plainIf : Bool) : Macro := fun stx => do
  let (stx', changed) ← (rewrite plainIf stx).run false
  if changed then return stx' else Macro.throwUnsupported

/-- `&&.`, `||.`, `select` and `if%`: Damp's own forms, rewritten wherever Damp is imported. -/
@[macro Lean.Parser.Term.doExpr, macro Lean.Parser.Term.doLet, macro Lean.Parser.Term.doLetElse,
  macro Lean.Parser.Term.doLetArrow, macro Lean.Parser.Term.doReassign, macro Lean.Parser.Term.doReassignArrow,
  macro Lean.Parser.Term.doIf, macro Lean.Parser.Term.doUnless, macro Lean.Parser.Term.doFor,
  macro Lean.Parser.Term.doMatch, macro Lean.Parser.Term.doReturn, macro Lean.Parser.Term.doHave,
  macro Lean.Parser.Term.doAssert, macro Lean.Parser.Term.doDbgTrace]
def expandOps : Macro := expand false

/-- The same, and Lean's value-level `if`: only with `open Damp`, like the circuit `if`. -/
def expandAll : Macro := expand true

end ShortCircuit

attribute [scoped macro Lean.Parser.Term.doExpr, scoped macro Lean.Parser.Term.doLet,
  scoped macro Lean.Parser.Term.doLetElse, scoped macro Lean.Parser.Term.doLetArrow,
  scoped macro Lean.Parser.Term.doReassign, scoped macro Lean.Parser.Term.doReassignArrow,
  scoped macro Lean.Parser.Term.doIf, scoped macro Lean.Parser.Term.doUnless, scoped macro Lean.Parser.Term.doFor,
  scoped macro Lean.Parser.Term.doMatch, scoped macro Lean.Parser.Term.doReturn, scoped macro Lean.Parser.Term.doHave,
  scoped macro Lean.Parser.Term.doAssert, scoped macro Lean.Parser.Term.doDbgTrace] ShortCircuit.expandAll

/-! ## Declarations -/

syntax circuitBinder := "(" ident+ " : " term ")"

private def binderNames (bs : Array (TSyntax ``circuitBinder)) : MacroM (Array Ident) := do
  let mut names := #[]
  for b in bs do
    match b with
    | `(circuitBinder| ($ids* : $_)) => names := names ++ ids
    | _ => Macro.throwUnsupported
  return names

private def toBracketed (bs : Array (TSyntax ``circuitBinder)) :
    MacroM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  bs.mapM fun b => match b with
    | `(circuitBinder| ($ids* : $ty)) => `(Parser.Term.bracketedBinderF| ($ids* : $ty))
    | _ => Macro.throwUnsupported

private def strLit (i : Ident) : StrLit := Syntax.mkStrLit i.getId.toString

initialize circuitRegistry : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

open Lean.Elab.Command in
/-- Records a circuit as part of the contract being declared in this namespace. -/
elab "register_circuit% " c:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload c
  let ns ← getCurrNamespace
  modifyEnv (circuitRegistry.addEntry · (ns, name))

/-! A circuit is checked where it is declared: the definition is evaluated and
emitted, and any problem is reported on its name. This runs the same compiler
the build runs; it reads nothing from the definition's syntax. -/

open Lean.Elab Lean.Elab.Command Lean.Meta in
private unsafe def checkCircuitUnsafe (c : Ident) : CommandElabM Unit := do
  let name ← liftCoreM <| realizeGlobalConstNoOverload c
  let problem ← liftTermElabM <| evalExpr (Option String)
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``String))
    (mkApp (mkConst ``Damp.circuitProblem) (mkConst name))
  if let some msg := problem then logErrorAt c m!"circuit cannot be compiled: {msg}"

open Lean.Elab.Command in
@[implemented_by checkCircuitUnsafe]
private opaque checkCircuit (c : Ident) : CommandElabM Unit

/-- `check_circuit% c` reports why the circuit `c` cannot be compiled, if it cannot. -/
elab "check_circuit% " c:ident : command => checkCircuit c

/--
`circuit f (a : A) … : R := body` defines `f : A → … → CircuitM R` as an
ordinary function, and `f.circuit`, the circuit built from it with the
argument names as input labels.
-/
syntax (name := circuitDecl)
  (docComment)? "circuit " ident (ppSpace circuitBinder)* " : " term " := " term : command

macro_rules
  | `($[$doc]? circuit $name $bs* : $ret := $body) => do
      let names := (← binderNames bs).map strLit
      let binders ← toBracketed bs
      let circ := mkIdentFrom name (name.getId ++ `circuit)
      `($[$doc]? def $name $binders* : Damp.CircuitM $ret := $body
        def $circ : Damp.IR.Circuit := Damp.mkCircuit $(strLit name) [$names,*] $name
        check_circuit% $circ
        register_circuit% $circ)

/--
`witness w (a : A) … : R` declares a private oracle call: `w : A → … → CircuitM R`.
Its implementation is supplied to the executor, outside the circuit.
-/
syntax (name := witnessDecl)
  (docComment)? "witness " ident (ppSpace circuitBinder)* " : " term : command

macro_rules
  | `($[$doc]? witness $name $bs* : $ret) => do
      let args ← binderNames bs
      let binders ← toBracketed bs
      let exprs ← args.foldrM (fun a acc => `(Damp.Value.toExprs $a ++ $acc)) (← `([]))
      `($[$doc]? def $name $binders* : Damp.CircuitM $ret :=
          Damp.askWitness $(strLit name) $ret $exprs)

/--
`ledger` followed by `name : Type` lines declares the contract's public state.
Each field becomes a definition, numbered in order, and `ledgerFields` lists
them.
-/
syntax (name := ledgerDecl) "ledger" (ppLine withPosition(ident " : " term))+ : command

/-- The shapes of the values a ledger field of this kind holds. -/
def LedgerKind.shapes : LedgerKind → List IR.Shape
  | .cell s | .set s | .list s | .merkleTree _ s | .historicMerkleTree _ s => [s]
  | .counter => []
  | .map k v => [k, v]
  | .mapOf k v => k :: v.shapes

/-- Why a ledger field of this kind cannot be declared: a `Uint` past Compact's limit. -/
def LedgerKind.problem (k : LedgerKind) : Option String :=
  (k.shapes.flatMap IR.Shape.tys).findSome? fun
    | .uint m => if m ≤ Uint.maxBound then none else some (Uint.tooLarge m)
    | _ => none

open Lean.Elab Lean.Elab.Command Lean.Meta in
private unsafe def checkLedgerFieldUnsafe (n : Ident) : CommandElabM Unit := do
  let problem ← liftTermElabM do
    let ty := mkApp (mkConst ``Option [Level.zero]) (mkConst ``String)
    let e ← Term.elabTermAndSynthesize
      (← `(Damp.LedgerKind.problem (Damp.LedgerType.decl $n "").kind)) (some ty)
    evalExpr (Option String) ty e
  if let some msg := problem then logErrorAt n m!"ledger field cannot be declared: {msg}"

open Lean.Elab.Command in
@[implemented_by checkLedgerFieldUnsafe]
private opaque checkLedgerField (n : Ident) : CommandElabM Unit

/-- `check_ledger% f` reports why the ledger field `f` cannot be declared, if it cannot. -/
elab "check_ledger% " n:ident : command => checkLedgerField n

macro_rules
  | `(ledger $[$names:ident : $tys:term]*) => do
      let mut cmds : Array (TSyntax `command) := #[]
      let mut decls : Array Term := #[]
      for i in [0:names.size] do
        let n : Ident := names[i]!
        cmds := cmds.push (← `(def $n : $(tys[i]!) := Damp.LedgerType.ofIndex $(quote i)))
        cmds := cmds.push (← `(check_ledger% $n))
        decls := decls.push (← `(Damp.LedgerType.decl $n $(strLit n)))
      let fields := mkIdent `ledgerFields
      cmds := cmds.push (← `(def $fields : List Damp.LedgerField := [$decls,*]))
      return mkNullNode cmds

/--
`struct S where` followed by `field : Type` lines defines a structure whose
values can be circuit arguments, results, witness values and ledger contents.
-/
syntax (name := structDecl) "struct " ident " where" (ppLine withPosition(ident " : " term))+ : command

macro_rules
  | `(struct $name where $[$fields:ident : $tys:term]*) => do
      let shapes ← tys.mapM fun t => `(Damp.Value.shape $t)
      let fieldNames := fields.map strLit
      let x ← `(x)
      let toExprs ← fields.foldrM
        (fun f acc => `(Damp.Value.toExprs ($x).$f:ident ++ $acc)) (← `([]))
      let built : Array Term := fields.map fun f => ⟨f.raw⟩
      let done ← `(⟨$built,*⟩)
      let rest ← `(rest)
      let ofExprs ← (fields.zip tys).foldrM
        (fun (f, t) acc => `(let ($f, $rest) := Damp.Value.take $t $rest; $acc)) done
      `(structure $name where
          $[$fields:ident : $tys]*
        instance : Damp.Value $name where
          shape := .struct $(strLit name) [$fieldNames,*] [$shapes,*]
          toExprs := fun $x => $toExprs
          ofExprs := fun $rest => $ofExprs
        instance : Damp.CmpEq $name $name := ⟨Damp.valueEq⟩)

/--
`enum E where` followed by `| variant` lines defines an enumeration. Variants
are `E.variant` and compare with `==.`.
-/
syntax (name := enumDecl) "enum " ident " where" (ppLine "| " ident)+ : command

macro_rules
  | `(enum $name where $[| $variants]*) => do
      let mut consts : Array (TSyntax `command) := #[]
      for i in [0:variants.size] do
        let v : Ident := variants[i]!
        let full := mkIdentFrom v (name.getId ++ v.getId)
        consts := consts.push (← `(def $full : $name := ⟨Damp.IR.Expr.const $(quote i)⟩))
      let main ← `(
        structure $name where
          code : Damp.IR.Expr
        instance : Damp.Value $name where
          shape := .prim (.enum $(quote (variants.size - 1)))
          toExprs := fun x => [x.code]
          ofExprs := fun xs => ⟨xs.headD (.const 0)⟩
        instance : Damp.CmpEq $name $name := ⟨Damp.valueEq⟩
        instance : Damp.EnumType $name := ⟨$(quote (variants.size - 1)), fun x => x.code, fun e => ⟨e⟩⟩)
      return mkNullNode (#[main.raw] ++ consts.map (·.raw))

/-! ### Named values

Inside a circuit, `const x := e` computes `e` once at that point and calls the
result `x`, as Compact's `const` does. `const x ← m` does the same for the
result of an action. Plain `let` only gives an expression a Lean name: it is
computed wherever it is first used, and again if it cannot be shared. -/

/-- Compute a value once, here, and name it. -/
syntax (name := constBind) "const " ident (" : " term)? " := " term : doElem
/-- Run an action and compute its result once, here, under this name. -/
syntax (name := constBindM) "const " ident (" : " term)? " ← " term : doElem

macro_rules
  | `(doElem| const $x:ident := $e) => `(doElem| let $x:ident ← Damp.val $e $(strLit x))
  | `(doElem| const $x:ident : $t := $e) => `(doElem| let $x:ident : $t ← Damp.val $e $(strLit x))
  | `(doElem| const $x:ident ← $e) => `(doElem| let $x:ident ← Damp.valM $e $(strLit x))
  | `(doElem| const $x:ident : $t ← $e) => `(doElem| let $x:ident : $t ← Damp.valM $e $(strLit x))

/-! `const (a, b) := e`, `const ⟨x, y⟩ ← m`: the same for a tuple or structure,
taken apart by a pattern of names (nested tuples and `⟨…⟩`, `_` for a part not
named). The whole value is computed once, here, as `const p := e` would, and each
name is bound to its part. -/

/-- A pattern `const` accepts: names and `_` inside tuples and `⟨…⟩`. -/
private partial def constPatternNames (p : Term) : MacroM (Array Ident) := do
  match p with
  | `($x:ident) => return #[x]
  | `(_) => return #[]
  | `(($p:term)) => constPatternNames p
  | `(($p:term, $ps:term,*)) => do
      let mut names ← constPatternNames p
      for q in ps.getElems do names := names ++ (← constPatternNames q)
      return names
  | `(⟨$ps:term,*⟩) => do
      let mut names := #[]
      for q in ps.getElems do names := names ++ (← constPatternNames q)
      return names
  | _ => Macro.throwErrorAt p "`const` takes a name, or a tuple `(a, b)` or `⟨a, b⟩` of names"

private def constHint (p : Term) : MacroM StrLit := do
  return Syntax.mkStrLit ("_".intercalate ((← constPatternNames p).map (·.getId.toString)).toList)

/-- Compute a tuple or structure once, here, and name its parts. -/
syntax (name := constPatBind) "const " (Parser.Term.tuple <|> Parser.Term.anonymousCtor)
  (" : " term)? " := " term : doElem
/-- Run an action, compute its result once, here, and name its parts. -/
syntax (name := constPatBindM) "const " (Parser.Term.tuple <|> Parser.Term.anonymousCtor)
  (" : " term)? " ← " term : doElem

/-- `const p (: t)? := e` / `← e`: the pattern, the optional type and the value are
    arguments 1, 2 and 4 of either form. -/
private def expandConstPat (monadic : Bool) : Macro := fun stx => do
  let p : Term := ⟨stx[1]⟩
  let e : Term := ⟨stx[4]⟩
  let ty? : Option Term := if stx[2].getNumArgs == 2 then some ⟨stx[2][1]⟩ else none
  let hint ← constHint p
  if monadic then
    let e ← match ty? with
      | some t => `(($e : Damp.CircuitM $t))
      | none => pure e
    `(doElem| let $p:term ← Damp.valM $e $hint)
  else
    let e ← match ty? with
      | some t => `(($e : $t))
      | none => pure e
    `(doElem| let $p:term ← Damp.val $e $hint)

@[macro constPatBind] private def expandConstPatBind : Macro := expandConstPat false
@[macro constPatBindM] private def expandConstPatBindM : Macro := expandConstPat true

/--
`constructor (a : A) … := body` declares what runs once when the contract is
deployed, after every ledger field has its default value. It may read and
write the ledger and call witnesses; nothing is proved about it.
-/
syntax (name := constructorDecl) "constructor" (ppSpace circuitBinder)* " := " term : command

macro_rules
  | `(constructor $bs* := $body) => do
      let names := (← binderNames bs).map strLit
      let binders ← toBracketed bs
      let fn := mkIdent `constructorBody
      let circ := mkIdent `constructorCircuit
      `(def $fn $binders* : Damp.CircuitM Unit := $body
        def $circ : Damp.IR.Circuit := Damp.mkCircuit "constructor" [$names,*] $fn
        check_circuit% $circ)

/-! ### Contract types

`interface Adder where` followed by `circuit (a : A) … : R` lines declares a
contract type, Compact's `contract Adder { circuit addTo(x: Field): Field; }`:
the circuits another contract must export for this contract to call them. It
defines

* `Adder`, the type of a reference to such a contract: its address, 32 bytes
  (`{ bytes }` in JS, as compactc represents a contract value). It can be a
  circuit or constructor argument, a witness result, ledger content (`Cell
  Adder`, a `Map` key or value, …) and compared with `==.`;
* `Adder.addTo (self : Adder) (x : Field) : CircuitM Field`, one method per
  declared circuit, so `(← adder.read).addTo (disclose x)` calls it
  (`Damp.contractCall`, `Damp/Lang/Calls.lean`);
* `Adder.declaration : Damp.Interface`, the declaration as data, which
  `contract` puts into `contract.json` for the executor;
* `Adder.ofAddress : Bytes 32 → Adder` and `Adder.address : Adder → Bytes 32`,
  and a `Damp.ContractType Adder` instance (`castContract Adder b`). Unlike
  Compact, any 32 bytes can be used as a reference of any contract type: the
  representation is the same, so the conversion is free, and unchecked.

A circuit with no arguments is written `name : R`. As in Compact, the circuit
names must be distinct (Lean rejects a repeated method); `bytes`, `ofAddress`,
`address` and `declaration` are taken. -/

initialize interfaceRegistry : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

open Lean.Elab.Command in
/-- Records a contract type as declared in this namespace. -/
elab "register_interface% " c:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload c
  let ns ← getCurrNamespace
  modifyEnv (interfaceRegistry.addEntry · (ns, name))

syntax (name := interfaceDecl)
  (docComment)? "interface " ident " where" (ppLine withPosition(ident (ppSpace circuitBinder)* " : " term))+ : command

macro_rules
  | `($[$doc]? interface $name where $[$cs:ident $bss:circuitBinder* : $rets:term]*) => do
      let iname := strLit name
      let decl := mkIdentFrom name (name.getId ++ `declaration)
      let ofAddr := mkIdentFrom name (name.getId ++ `ofAddress)
      let addr := mkIdentFrom name (name.getId ++ `address)
      let mut entries : Array Term := #[]
      let mut methods : Array (TSyntax `command) := #[]
      for i in [0:cs.size] do
        let c : Ident := cs[i]!
        let bs : Array (TSyntax ``circuitBinder) := bss[i]!
        let ret := rets[i]!
        let mut args : Array Term := #[]
        for h : j in [0:bs.size] do
          match bs[j] with
          | `(circuitBinder| ($ids* : $ty)) =>
              for id in ids do args := args.push (← `(($(strLit id), Damp.Value.shape $ty)))
          | _ => Macro.throwUnsupported
        entries := entries.push (← `({ name := $(strLit c), args := [$args,*], result := Damp.Value.shape $ret }))
        let argNames ← binderNames bs
        let binders ← toBracketed bs
        let exprs ← argNames.foldrM (fun a acc => `(Damp.Value.toExprs $a ++ $acc)) (← `([]))
        let fn := mkIdentFrom c (name.getId ++ c.getId)
        methods := methods.push (← `(
          def $fn (self : $name) $binders* : Damp.CircuitM $ret :=
            Damp.contractCall $ret $iname $(strLit c) self.bytes.limbs $exprs))
      let main ← `(
        $[$doc]? structure $name where
          bytes : Damp.Bytes 32
          deriving Inhabited
        instance : Damp.Value $name where
          shape := .struct $iname ["bytes"] [.prim (.bytes 32)]
          toExprs a := a.bytes.limbs
          ofExprs xs := ⟨⟨xs.take (Damp.IR.byteLimbs 32)⟩⟩
        instance : Damp.CmpEq $name $name := ⟨Damp.valueEq⟩
        def $decl : Damp.Interface := { name := $iname, circuits := [$entries,*] }
        def $ofAddr (b : Damp.Bytes 32) : $name := ⟨b⟩
        def $addr (r : $name) : Damp.Bytes 32 := r.bytes
        instance : Damp.ContractType $name := ⟨$decl, $ofAddr, $addr⟩
        register_interface% $decl)
      return mkNullNode (#[main.raw] ++ methods.map (·.raw))

/-! ### Contracts

`circuit` records each circuit it declares against the enclosing namespace, so
`contract` can gather them without their names being repeated; likewise
`interface` its contract type, and `contract` takes those declared in its
namespace or an enclosing one. -/

open Lean.Elab Lean.Elab.Command in
private def elabContract (name : Ident) (only : Option (Array Ident)) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let ifaces := (interfaceRegistry.getState env).filter (·.1.isPrefixOf ns) |>.map (·.2)
  let ifaces := ifaces.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
  let declared := (circuitRegistry.getState env).filter (·.1 == ns) |>.map (·.2)
  let chosen ← match only with
    | none => pure declared
    | some ids => ids.mapM fun id => do
        let full := ns ++ id.getId ++ `circuit
        unless declared.contains full do
          throwErrorAt id "`{id.getId}` is not a circuit declared in this namespace"
        pure full
  if chosen.isEmpty then
    throwErrorAt name "no circuits have been declared in this namespace"
  let fields := ns ++ `ledgerFields
  let state ← if env.contains fields then `($(mkCIdent fields)) else `([])
  let circuits := chosen.map mkCIdent
  let self := mkIdent `contract
  let ctorName := ns ++ `constructorCircuit
  let ctor ← if env.contains ctorName then `(some $(mkCIdent ctorName)) else `(none)
  let ifaceTerms := ifaces.map mkCIdent
  elabCommand (← `(def $self : Damp.Contract :=
    ⟨$(Syntax.mkStrLit name.getId.toString), $state, [$circuits,*], $ctor, [$ifaceTerms,*]⟩))

/--
`contract Name` defines `contract`: the ledger and every circuit declared so
far in this namespace, under the name `Name`, with the contract types declared
here or in an enclosing namespace. `contract Name exports c₁ c₂ …`
includes only the listed circuits.
-/
elab (name := contractDecl) "contract " name:ident : command => elabContract name none

@[inherit_doc contractDecl]
elab (name := contractDeclOnly) "contract " name:ident " exports" cs:(ppSpace ident)+ : command =>
  elabContract name (some cs)

/-- `#zkir f` prints the ZKIR emitted for circuit `f`. -/
macro "#zkir " c:ident : command => do
  let circ := mkIdentFrom c (c.getId ++ `circuit)
  `(#eval match Damp.Emit.circuit $circ with
      | .ok src => IO.println src.toJson.pretty
      | .error e => IO.eprintln e)

/-- `#circuit_info f` summarises the circuit emitted for `f`. -/
macro "#circuit_info " c:ident : command => do
  let circ := mkIdentFrom c (c.getId ++ `circuit)
  `(#eval IO.println (Damp.Emit.summary $circ))

end Damp
