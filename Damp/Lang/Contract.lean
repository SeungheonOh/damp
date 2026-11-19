/-
The interface contracts are written against.

A circuit body is an ordinary Lean definition in the `CircuitM` monad over
typed values: `Field`, `Boolean`, `Uint max`, and structures, tuples and
vectors of those. Running it builds the circuit IR; no elaborator or `Expr`
traversal is involved. Lean itself is the compile-time language: recursion,
lists, higher-order functions and type classes are all available and all
disappear when the definition is evaluated.

Numeric rules mirror Compact: `Uint` addition and multiplication widen the
bound in the type, subtraction checks for underflow, narrowing is checked.
`Uint.toField` and `Field.unsafeToUint` step outside those rules.

`Damp/Lang/Syntax.lean` adds notation on top of this file; everything here is plain
functions.
-/
import Damp.IR.Basic

namespace Damp
open IR

/-! ## The builder monad -/

structure Build where
  next : Var := 0
  stmts : Array Stmt := #[]
  /-- The condition under which the code being built runs. -/
  guard : Expr := .const 1
  /-- Problems found so far; reported when the circuit is emitted. -/
  errors : Array String := #[]

/-- Circuit-building computations. Deliberately not reducible to a function type. -/
def CircuitM (α : Type) : Type := StateM Build α

namespace CircuitM
instance : Monad CircuitM := inferInstanceAs (Monad (StateM Build))
instance : LawfulMonad CircuitM := inferInstanceAs (LawfulMonad (StateM Build))

def run (m : CircuitM α) (s : Build := {}) : α × Build := StateT.run (m := Id) m s
def get : CircuitM Build := (MonadState.get : StateM Build Build)
def modify (f : Build → Build) : CircuitM Unit := (MonadState.modifyGet fun s => ((), f s) : StateM Build Unit)
end CircuitM

def freshVar : CircuitM Var := do
  let s ← CircuitM.get
  CircuitM.modify fun s => { s with next := s.next + 1 }
  return s.next

def emit (s : Stmt) : CircuitM Unit :=
  CircuitM.modify fun st => { st with stmts := st.stmts.push s }

def currentGuard : CircuitM Expr := return (← CircuitM.get).guard

/-- Record a problem with the circuit being built. It is reported when the
    circuit is emitted, so a contract with a mistake never compiles silently. -/
def buildError (msg : String) : CircuitM Unit :=
  CircuitM.modify fun st => { st with errors := st.errors.push msg }

/-! ## Typed values -/

structure Field where
  expr : Expr
  deriving Inhabited

structure Boolean where
  expr : Expr
  deriving Inhabited

/-- An unsigned integer known to be at most `max`. -/
structure Uint (max : Nat) where
  expr : Expr
  deriving Inhabited

/-- `n` bytes, as 31-byte limbs with the most significant limb first. -/
structure Bytes (n : Nat) where
  limbs : List Expr
  deriving Inhabited

abbrev Uint8 := Uint 255
abbrev Uint16 := Uint 65535
abbrev Uint32 := Uint 4294967295
abbrev Uint64 := Uint 18446744073709551615

/-- Compact's limit on `Uint`: values must fit in 248 bits. -/
def Uint.maxBound : Nat := 2 ^ 248 - 1

/-- The error for a `Uint` bound past Compact's limit. -/
def Uint.tooLarge (bound : Nat) : String :=
  s!"a Uint with maximum {bound} is too large: values must fit in 248 bits"

/-- `e`, unless the bound is past Compact's limit: then an `invalid` expression,
    which the emitter rejects. Every way of making a `Uint` goes through this,
    `Field.unsafeToUint` included. -/
def Uint.capped (bound : Nat) (e : Expr) : Expr :=
  if bound ≤ Uint.maxBound then e else .invalid (Uint.tooLarge bound)

/-- Types whose values are a fixed list of typed field elements. -/
class Value (α : Type) where
  shape : Shape
  toExprs : α → List Expr
  ofExprs : List Expr → α
  /-- A reason this particular value cannot be selected between branches. -/
  problem : α → Option String := fun _ => none

namespace Value
/-- The all-zero value, Compact's `default`. -/
def zero (α : Type) [Value α] : α :=
  Value.ofExprs (List.replicate ((Value.shape α).ranges.length) (.const 0))

/-- The primitive values a value of type `α` is made of. -/
def tys (α : Type) [Value α] : List Ty := (Value.shape α).tys
/-- Range checks for a value of type `α`, one per field element. -/
def ranges (α : Type) [Value α] : List (Option Range) := (Value.shape α).ranges
/-- Number of field elements a value of type `α` occupies. -/
def width (α : Type) [Value α] : Nat := (ranges α).length
/-- Read one value off the front of a list of expressions. -/
def take (α : Type) [Value α] (xs : List Expr) : α × List Expr :=
  (Value.ofExprs (xs.take (width α)), xs.drop (width α))
end Value

instance : Value Field where
  shape := .prim .field
  toExprs x := [x.expr]
  ofExprs xs := ⟨xs.headD (.const 0)⟩

instance : Value Boolean where
  shape := .prim .bool
  toExprs x := [x.expr]
  ofExprs xs := ⟨xs.headD (.const 0)⟩

instance {m : Nat} : Value (Uint m) where
  shape := .prim (.uint m)
  toExprs x := [x.expr]
  ofExprs xs := ⟨Uint.capped m (xs.headD (.const 0))⟩

instance : Value Unit where
  shape := .tuple []
  toExprs _ := []
  ofExprs _ := ()

instance {n : Nat} : Value (Bytes n) where
  shape := .prim (.bytes n)
  toExprs x := x.limbs
  ofExprs xs := ⟨xs.take (byteLimbs n)⟩

instance [Value α] [Value β] : Value (α × β) where
  shape := .tuple [Value.shape α, Value.shape β]
  toExprs p := Value.toExprs p.1 ++ Value.toExprs p.2
  ofExprs xs :=
    let (a, rest) := Value.take α xs
    (a, Value.ofExprs rest)

/-- `do` blocks carry `let mut` variables through a branch as an `MProd`. -/
instance [Value α] [Value β] : Value (MProd α β) where
  shape := .tuple [Value.shape α, Value.shape β]
  toExprs p := Value.toExprs p.1 ++ Value.toExprs p.2
  ofExprs xs :=
    let (a, rest) := Value.take α xs
    ⟨a, Value.ofExprs rest⟩

/-- A loop body inside a `for` yields its `let mut` variables in a `ForInStep`.
    Continuing is fine; `break` under a circuit condition cannot be compiled,
    because both branches of the condition always run. -/
instance [Value α] : Value (ForInStep α) where
  shape := Value.shape α
  toExprs
    | .yield a | .done a => Value.toExprs a
  ofExprs xs := .yield (Value.ofExprs xs)
  problem
    | .yield a => Value.problem a
    | .done _ => some "`break` under a circuit condition is not supported"

instance {n : Nat} [Value α] : Value (Vector α n) where
  shape := .vector n (Value.shape α)
  toExprs v := v.toList.flatMap Value.toExprs
  ofExprs xs := Vector.ofFn fun (i : Fin n) =>
    Value.ofExprs ((xs.drop (i.val * Value.width α)).take (Value.width α))

/-! ### Field -/

namespace Field
/-- A literal, as its canonical representative in `[0, p)`, `p` the field
    modulus: `p + 1` is `1`, as the field semantics says. Every immediate the
    emitter writes from a literal is then one Midnight's loader accepts. -/
instance : OfNat Field n := ⟨⟨.const (n % Fr.modulus : Nat)⟩⟩
/-- Addition, dropping a literal zero as Compact does. -/
def add (a b : Field) : Field :=
  match a.expr, b.expr with
  | .const 0, e | e, .const 0 => ⟨e⟩
  | x, y => ⟨.add x y⟩

instance : Add Field := ⟨add⟩
instance : Mul Field := ⟨fun a b => ⟨.mul a.expr b.expr⟩⟩
instance : Neg Field := ⟨fun a => ⟨.neg a.expr⟩⟩
instance : Sub Field := ⟨fun a b => ⟨.add a.expr (.neg b.expr)⟩⟩

/-- A number known while the circuit is built, as a field element (reduced
    modulo the field size, like a literal). -/
def ofNat (n : Nat) : Field := ⟨.const (n % Fr.modulus : Nat)⟩

/-- The bytes of a short string as a field element, first byte least
    significant: Compact's `"text" as Field`. At most 31 bytes. -/
def ofString (str : String) : Field :=
  ⟨.const (str.toUTF8.toList.foldr (fun b acc => acc * 256 + b.toNat) 0 % Fr.modulus : Nat)⟩

def eq (a b : Field) : Boolean := ⟨.eq a.expr b.expr⟩

/-- Reinterpret as a `Uint` with no range check. The caller is responsible for the
    value fitting the bound; the bound itself is capped like every other `Uint`'s. -/
def unsafeToUint (a : Field) (max : Nat) : Uint max := ⟨Uint.capped max a.expr⟩
end Field

/-! ### Boolean -/

namespace Boolean
def true : Boolean := ⟨.const 1⟩
def false : Boolean := ⟨.const 0⟩
/-- A condition decided while the circuit is built, as a circuit `Boolean`. -/
def ofBool (b : Bool) : Boolean := if b then true else false
def not (a : Boolean) : Boolean := ⟨.select a.expr (.const 0) (.const 1)⟩
def and (a b : Boolean) : Boolean := ⟨.sel a.expr b.expr (.const 0)⟩
def or (a b : Boolean) : Boolean := ⟨.sel a.expr (.const 1) b.expr⟩
def eq (a b : Boolean) : Boolean := ⟨.eq a.expr b.expr⟩
def toField (a : Boolean) : Field := ⟨a.expr⟩
end Boolean

/-- Equality of two values, element by element. -/
def valueEq [Value α] (a b : α) : Boolean :=
  match List.zipWith Expr.eq (Value.toExprs a) (Value.toExprs b) with
  | [] => ⟨.const 1⟩
  | e :: es => ⟨es.foldl (fun acc e => .select acc e (.const 0)) e⟩

/-- Declare that making `x` public is intended. Private data (circuit arguments
    and witness results) must pass through `disclose` before it reaches the
    ledger, or, for witness results, the circuit's result. -/
def disclose [Value α] (x : α) : α := Value.ofExprs ((Value.toExprs x).map .disclose)

/-- `a` where `c` holds, `b` elsewhere. Both are evaluated. -/
def select [Value α] (c : Boolean) (a b : α) : α :=
  Value.ofExprs (List.zipWith (Expr.sel c.expr) (Value.toExprs a) (Value.toExprs b))

/-! ### Uint -/

namespace Uint
/-- The constant `n`, typed with the tightest bound. -/
def lit (n : Nat) : Uint n := ⟨capped n (.const n)⟩

def ofNat {m : Nat} (n : Nat) (_h : n ≤ m := by decide) : Uint m := ⟨capped m (.const n)⟩

/-- Forget precision in the bound. Free: no constraint is needed (but the new
    bound must be within Compact's limit). -/
def widen (a : Uint m) (_h : m ≤ k := by decide) : Uint k := ⟨capped k a.expr⟩

def toField (a : Uint m) : Field := ⟨a.expr⟩

/-- A numeral is a `Uint m` when it is at most `m`. Instance search cannot
    decide that, so a larger numeral becomes an `invalid` expression, which the
    emitter reports when the circuit is checked at its declaration. -/
instance {m n : Nat} : OfNat (Uint m) n :=
  ⟨⟨if n ≤ m then capped m (.const n) else .invalid s!"the literal {n} does not fit a Uint whose maximum is {m}"⟩⟩

instance : HAdd (Uint m) (Uint k) (Uint (m + k)) := ⟨fun a b => ⟨capped (m + k) (.add a.expr b.expr)⟩⟩
instance : HMul (Uint m) (Uint k) (Uint (m * k)) := ⟨fun a b => ⟨capped (m * k) (.mul a.expr b.expr)⟩⟩

def lt (a : Uint m) (b : Uint k) : Boolean := ⟨.lt (max (bitLen m) (bitLen k)) a.expr b.expr⟩
def eq (a : Uint m) (b : Uint k) : Boolean := ⟨.eq a.expr b.expr⟩
end Uint

/-! ### Bytes -/

namespace Bytes
/-- The limbs of a byte string given least significant byte first. -/
def limbsOf (n : Nat) (bytes : List UInt8) : List Expr :=
  let x := (bytes.take n).foldr (fun b acc => acc * 256 + b.toNat) 0
  let limbs := byteLimbs n
  (List.range limbs).map fun j => .const (((x >>> (248 * (limbs - 1 - j))) % 2 ^ 248 : Nat) : Int)

/-- A constant; missing bytes are zero. -/
def ofBytes (n : Nat) (bytes : List UInt8) : Bytes n := ⟨limbsOf n bytes⟩

/-- The UTF-8 bytes of `s`, zero-padded to `n` bytes (Compact's `pad`). -/
def pad (n : Nat) (s : String) : Bytes n := ofBytes n s.toUTF8.toList

def zero (n : Nat) : Bytes n := ofBytes n []

/-- Limb by limb, most significant first. -/
def eq (a b : Bytes n) : Boolean := valueEq a b
end Bytes

/-! ### Maybe -/

/-- An optional value: a flag and a value, which is zero when absent. -/
structure Maybe (α : Type) where
  isSome : Boolean
  value : α

instance [Value α] : Value (Maybe α) where
  shape := .struct "Maybe" ["is_some", "value"] [.prim .bool, Value.shape α]
  toExprs m := m.isSome.expr :: Value.toExprs m.value
  ofExprs xs := ⟨⟨xs.headD (.const 0)⟩, Value.ofExprs xs.tail⟩

namespace Maybe
def some [Value α] (x : α) : Maybe α := ⟨.true, x⟩
def none [Value α] : Maybe α := ⟨.false, Value.zero α⟩
end Maybe

/-- A 32-byte value as a field element, dropping its top byte (Compact's
    `degradeToTransient`). -/
def degradeToTransient (b : Bytes 32) : Field := ⟨b.limbs.getD 1 (.const 0)⟩

/-- A field element as 32 bytes: its low 31 bytes, with a zero top byte
    (Compact's `upgradeFromTransient`). -/
def upgradeFromTransient (x : Field) : Bytes 32 := ⟨[.const 0, .divmod false 248 x.expr]⟩

/-- The persistent (SHA-256) hash of a value. -/
def persistentHash [Value α] (x : α) : Bytes 32 :=
  let align := (Value.tys α).map Ty.align
  let xs := Value.toExprs x
  ⟨[.phash true align xs, .phash false align xs]⟩

/-- A persistent commitment to `x` with opening `r`. -/
def persistentCommit [Value α] (x : α) (r : Bytes 32) : Bytes 32 :=
  let align := .bytes 32 :: (Value.tys α).map Ty.align
  let xs := r.limbs ++ Value.toExprs x
  -- A commitment hides what it commits to, so it is public by construction.
  ⟨[.disclose (.phash true align xs), .disclose (.phash false align xs)]⟩

/-- The transient (Poseidon) hash of a value. -/
def transientHash [Value α] (x : α) : Field := ⟨.hash (Value.toExprs x)⟩

/-- A transient commitment to `x` with opening `r`. -/
def transientCommit [Value α] (x : α) (r : Field) : Field :=
  ⟨.disclose (.hash (r.expr :: Value.toExprs x))⟩

/-! ### Comparisons

`lt` and `eq` are the primitives; the rest are derived the way Compact derives
them. A `Nat` on either side of a `Uint` comparison is a literal. -/

class CmpLt (α β : Type) where
  lt : α → β → Boolean

class CmpEq (α β : Type) where
  eq : α → β → Boolean

instance : CmpLt (Uint m) (Uint k) := ⟨Uint.lt⟩
instance : CmpLt (Uint m) Nat := ⟨fun a n => a.lt (Uint.lit n)⟩
instance : CmpLt Nat (Uint m) := ⟨fun n a => (Uint.lit n).lt a⟩
/-- With nothing else to go on, both sides of `==.` have the same type, so a
    literal or `.some x` on one side takes its type from the other. -/
@[default_instance high]
instance (priority := low) [Value α] : CmpEq α α := ⟨valueEq⟩

instance : CmpEq (Uint m) (Uint k) := ⟨Uint.eq⟩
instance : CmpEq (Uint m) Nat := ⟨fun a n => a.eq (Uint.lit n)⟩
instance : CmpEq Nat (Uint m) := ⟨fun n a => (Uint.lit n).eq a⟩
instance : CmpEq Field Field := ⟨Field.eq⟩
instance : CmpEq Boolean Boolean := ⟨Boolean.eq⟩
instance : CmpEq (Bytes n) (Bytes n) := ⟨Bytes.eq⟩
instance [Value α] : CmpEq (Maybe α) (Maybe α) := ⟨valueEq⟩
instance [Value α] [Value β] : CmpEq (α × β) (α × β) := ⟨valueEq⟩
instance [Value α] : CmpEq (Vector α n) (Vector α n) := ⟨valueEq⟩

def cmpLt [CmpLt α β] (a : α) (b : β) : Boolean := CmpLt.lt a b
def cmpGt [CmpLt β α] (a : α) (b : β) : Boolean := CmpLt.lt b a
def cmpLe [CmpLt β α] (a : α) (b : β) : Boolean := (CmpLt.lt b a).not
def cmpGe [CmpLt α β] (a : α) (b : β) : Boolean := (CmpLt.lt a b).not
def cmpEq [CmpEq α β] (a : α) (b : β) : Boolean := CmpEq.eq a b
def cmpNe [CmpEq α β] (a : α) (b : β) : Boolean := (CmpEq.eq a b).not

/-! ## Statements -/

/-- Compute a value once, at this point. `hint` only labels the registers it
    gets in the emitted circuit; `const x := e` supplies the binder's name. -/
def val [Value α] (x : α) (hint : String := "t") : CircuitM α := do
  let vs ← (Value.toExprs x).mapM fun e => do
    let v ← freshVar
    emit (.bind v hint e)
    pure (Expr.var v)
  return Value.ofExprs vs

/-- Run an action and compute its result once, at this point. -/
def valM [Value α] (m : CircuitM α) (hint : String := "t") : CircuitM α := do
  val (← m) hint

/-- `g ∧ c`. -/
def guardAnd (g c : Expr) : Expr :=
  match g with
  | .const 1 => c
  | g => .sel c g (.const 0)

/-- Name a guard at the point a branch is entered, unless it is already atomic.
    A guard nothing ends up using is dropped by the emitter. -/
def nameGuard : Expr → CircuitM Expr
  | e@(.var _) | e@(.const _) => pure e
  | e => do
      let v ← freshVar
      emit (.bind v "t" e)
      pure (.var v)

def underGuard (g : Expr) (body : CircuitM α) : CircuitM α := do
  let outer ← currentGuard
  CircuitM.modify fun s => { s with guard := g }
  let r ← body
  CircuitM.modify fun s => { s with guard := outer }
  return r

/-- Effects in `body` take place only when `c` holds. -/
def when_ (c : Boolean) (body : CircuitM Unit) : CircuitM Unit := do
  let g ← nameGuard (guardAnd (← currentGuard) c.expr)
  underGuard g body

/-- What an effect does, ignoring its guard and any computed operands. -/
def effectShape : Stmt → Option String
  | .witness _ name _ _ _ => some s!"a call to witness `{name}`"
  | .assert _ msg => some s!"the check \"{msg}\""
  | .ledger _ _ ops =>
      let key : Expr → String
        | .const c => toString c
        | _ => "_"
      some ("the same ledger operation (" ++
        " ".intercalate (ops.flatMap fun op => (op.map key).encode toString) ++ ")")
  | _ => none

private def condCore [Value α] (checked : Bool) (c : Boolean) (t e : CircuitM α) : CircuitM α := do
  let outer ← currentGuard
  let gt ← nameGuard (guardAnd outer c.expr)
  let ge ← nameGuard (guardAnd outer c.not.expr)
  let start := (← CircuitM.get).stmts.size
  let a ← underGuard gt t
  let mid := (← CircuitM.get).stmts.size
  let b ← underGuard ge e
  for p in [Value.problem a, Value.problem b] do
    if let some msg := p then buildError msg
  if checked then
    let stmts := (← CircuitM.get).stmts
    let lastEffect (lo hi : Nat) := (stmts.extract lo hi).toList.filterMap effectShape |>.getLast?
    if let (some x, some y) := (lastEffect start mid, lastEffect mid stmts.size) then
      if x == y then
        buildError ("both branches of an `if` end with " ++ x ++ ". In a `do` block the statements " ++
          "after an `if` are built once per branch: write `if% … then … else …` for a " ++
          "conditional with statements after it, or move the shared operation out of the `if`")
  return select c a b

/-- Both branches are built; effects are guarded and the results selected. -/
def cond [Value α] (c : Boolean) (t e : CircuitM α) : CircuitM α := condCore false c t e

/-- `cond`, reporting branches that end with the same effect. This is what a
    plain `if` on a circuit `Boolean` means. -/
def condChecked [Value α] (c : Boolean) (t e : CircuitM α) : CircuitM α := condCore true c t e

/-- `a && b` evaluated the way Compact evaluates it: `b`'s effects (witness calls,
    ledger operations, checks) take place only where `a` holds; the result is
    `select a b false`. This is what `a &&. b` means when `b` contains a `(← …)`. -/
def Boolean.andThen (a : Boolean) (b : CircuitM Boolean) : CircuitM Boolean := do
  let av ← nameGuard a.expr
  let g ← nameGuard (guardAnd (← currentGuard) av)
  let r ← underGuard g b
  return ⟨.sel av r.expr (.const 0)⟩

/-- `a || b` evaluated the way Compact evaluates it: `b`'s effects take place only
    where `a` does not hold; the result is `select a true b`. This is what `a ||. b`
    means when `b` contains a `(← …)`. -/
def Boolean.orElse (a : Boolean) (b : CircuitM Boolean) : CircuitM Boolean := do
  let av ← nameGuard a.expr
  let g ← nameGuard (guardAnd (← currentGuard) (Boolean.not ⟨av⟩).expr)
  let r ← underGuard g b
  return ⟨.sel av (.const 1) r.expr⟩

/-- Fails the transaction unless `c` holds whenever this point is reached. -/
def require (c : Boolean) (msg : String := "assertion failed") : CircuitM Unit := do
  let g ← currentGuard
  let cond := match g with
    | .const 1 => c.expr
    | g => .select g c.expr (.const 1)
  emit (.assert cond msg)

/-- Range-check a single field element as a value of a one-element type. -/
def constrainTy (e : Expr) (ty : Ty) : CircuitM Unit :=
  match ty.ranges with
  | [some r] => emit (.constrain e r)
  | _ => pure ()

/-- Record an error for every `Uint` among `tys` whose bound is past Compact's
    limit, so that such a type is rejected even where its value is never used. -/
def checkUintBounds (tys : List Ty) : CircuitM Unit :=
  tys.forM fun
    | .uint m => unless m ≤ Uint.maxBound do buildError (Uint.tooLarge m)
    | _ => pure ()

/-- Ask the private oracle for a value of type `α`. The result is range-checked. -/
def askWitness (name : String) (α : Type) [Value α] (args : List Expr := []) : CircuitM α := do
  let g ← currentGuard
  let outs ← (Value.ranges α).mapM fun r => do pure ((← freshVar), r)
  emit (.witness g name args outs (Value.shape α))
  checkUintBounds (Value.tys α)
  return Value.ofExprs (outs.map fun (v, _) => Expr.var v)

/-! ### Checked `Uint` operations -/

/-- `e` where the current guard holds and 0 elsewhere. As in Compact, a checked
    result in a branch not taken is 0, which every check accepts: otherwise a
    branch that does not run could still fail the circuit. -/
def guarded (e : Expr) : CircuitM Expr := do
  match (← currentGuard) with
  | .const 1 => pure e
  | g => pure (.select g e (.const 0))

/-- Subtraction; fails if `b > a`. -/
def Uint.sub (a : Uint m) (b : Uint k) : CircuitM (Uint m) := do
  require (a.lt b).not "result of subtraction would be negative"
  return ⟨← guarded (.add a.expr (.neg b.expr))⟩

/-- Narrow the bound; checked unless the new bound is no smaller. -/
def Uint.castTo (a : Uint m) (k : Nat) : CircuitM (Uint k) := do
  checkUintBounds [.uint k]
  if m ≤ k then return ⟨Uint.capped k a.expr⟩
  let e ← guarded a.expr
  constrainTy e (.uint k)
  return ⟨Uint.capped k e⟩

/-- Checked conversion from a field element. -/
def Field.toUint (a : Field) (max : Nat) : CircuitM (Uint max) := do
  checkUintBounds [.uint max]
  let e ← guarded a.expr
  constrainTy e (.uint max)
  return ⟨Uint.capped max e⟩

/-! ## Circuits -/

structure Signature where
  args : List (String × Shape) := []
  inputs : List Input := []
  result : Shape := .tuple []
  outputs : List Expr := []

/-- Functions from typed arguments to a `CircuitM` result. -/
class CircuitFn (φ : Type) where
  build : φ → List String → CircuitM Signature

instance [Value ρ] : CircuitFn (CircuitM ρ) where
  build m _ := do
    let r ← m
    return { result := Value.shape ρ, outputs := Value.toExprs r }

instance [Value α] [CircuitFn φ] : CircuitFn (α → φ) where
  build f names := do
    let name := names.headD "arg"
    let ins ← (Value.ranges α).mapM fun range => do
      let v ← freshVar
      pure ({ name, var := v, range } : Input)
    let a : α := Value.ofExprs (ins.map fun i => Expr.var i.var)
    let sig ← CircuitFn.build (f a) names.tail
    checkUintBounds (Value.tys α)
    return { sig with args := (name, Value.shape α) :: sig.args, inputs := ins ++ sig.inputs }

/-- Build the circuit for `f`. `argNames` only label the inputs. -/
def mkCircuit [CircuitFn φ] (name : String) (argNames : List String) (f : φ) : Circuit :=
  let (sig, st) := (CircuitFn.build f argNames).run
  -- Range checks on the inputs come first, in argument order.
  let checks := sig.inputs.filterMap fun i => i.range.map (Stmt.constrain (.var i.var))
  { name, args := sig.args, inputs := sig.inputs, body := checks.toArray ++ st.stmts,
    result := sig.result, outputs := sig.outputs, errors := st.errors.toList }

end Damp
