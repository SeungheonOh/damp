/-
Notation for writing contracts.

Everything here is a macro that expands to the plain functions of
`Damp/Contract.lean` and `Damp/Ledger.lean`; nothing inspects or rewrites the
user's terms. A contract written with this notation is still an ordinary Lean
value, and can equally be written without it.

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
import Damp.Build

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
infixl:35 " &&. " => Boolean.and
infixl:30 " ||. " => Boolean.or
prefix:max "!." => Boolean.not

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
or loop body, where it may assign `let mut` variables. This is the one place an
elaborator is involved, and it only chooses between two expansions by looking
at the type of the condition: `Damp.cond c t e` for a circuit `Boolean`, Lean's
usual `ite c t e` otherwise. It does not rewrite the branches.

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
@[term_elab ifDispatch] def elabIfDispatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(if_dispatch% $c $t $e) =>
    let saved ← saveState
    let isCircuit ←
      try
        let ce ← withoutErrToSorry (elabTerm c none)
        synthesizeSyntheticMVarsNoPostponing
        let ty ← whnfR (← instantiateMVars (← inferType ce))
        pure (ty.isConstOf ``Damp.Boolean)
      catch _ => pure false
    saved.restore
    if isCircuit then elabTerm (← `(Damp.condChecked $c $t $e)) expectedType?
    else elabTerm (← `(ite $c $t $e)) expectedType?
  | _ => throwUnsupportedSyntax

scoped macro_rules
  | `(if $c then $t else $e) => `(if_dispatch% ($c) ($t) ($e))

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

macro_rules
  | `(ledger $[$names:ident : $tys:term]*) => do
      let mut cmds : Array (TSyntax `command) := #[]
      let mut decls : Array Term := #[]
      for i in [0:names.size] do
        let n : Ident := names[i]!
        cmds := cmds.push (← `(def $n : $(tys[i]!) := Damp.LedgerType.ofIndex $(quote i)))
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
        instance : Damp.CmpEq $name $name := ⟨Damp.valueEq⟩)
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
  (`Damp.contractCall`, `Damp/Calls.lean`);
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
