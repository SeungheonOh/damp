/-
Coins and tokens: Compact's standard-library token functions, written with
Damp's own interface.

Shielded tokens live in Zswap: a coin is a commitment in the global Merkle
tree, spent by revealing its nullifier. A contract cannot see the Zswap
transaction it is part of; it asks the user's machine to add inputs and
outputs to it (the built-in witnesses `createZswapInput` and
`createZswapOutput`, run by the executor itself) and then *claims* them in the
kernel by commitment or nullifier, which the ledger checks against the
transaction. Unshielded tokens are balances the kernel tracks directly.

Every function here follows `standard-library.compact` statement for statement,
so that a circuit calling it compiles to the instructions compactc 0.36.1
emits; `docs/tokens.md` records the evidence and the two places where the
circuits differ.

Disclosure follows Compact: commitments and nullifiers are persistent hashes,
which do not disclose what they hash, so a coin, value, nonce or recipient that
comes from a circuit argument or witness must be `disclose`d by the caller,
exactly where compactc demands it. `ownPublicKey` is the exception, as in
Compact: its result counts as public.
-/
import Damp.Lang.Syntax

namespace Damp

/-! ## Types -/

-- A user's Zswap coin public key.
struct ZswapCoinPublicKey where
  bytes : Bytes 32

-- A shielded coin: its nonce, its token type (`color`) and its value.
struct ShieldedCoinInfo where
  nonce : Bytes 32
  color : Bytes 32
  value : Uint128

-- A shielded coin together with its index in the Zswap Merkle tree, which is
-- what spending it requires.
struct QualifiedShieldedCoinInfo where
  nonce : Bytes 32
  color : Bytes 32
  value : Uint128
  mt_index : Uint64

-- What `sendShielded` produced: the coin sent, and the change returned to
-- this contract, if any.
struct ShieldedSendResult where
  change : Maybe ShieldedCoinInfo
  sent : ShieldedCoinInfo

-- What a coin commitment or nullifier hashes.
struct CoinPreimage where
  domain_sep : Bytes 21
  info : ShieldedCoinInfo
  dataType : Boolean
  data : Bytes 32

/-- Compact's `left<A, B>(v)`. -/
def left [Value β] (x : α) : Either α β := ⟨.true, x, Value.zero β⟩

/-- Compact's `right<A, B>(v)`. -/
def right [Value α] (y : β) : Either α β := ⟨.false, Value.zero α, y⟩

/-! ## Built-in witnesses

Run by the executor through the Compact runtime, never by user code; the names
are reserved. The two `create*` ones return nothing and only record the coin in
the call's Zswap local state. -/

/-- The coin public key of the user running the circuit. Public, as in Compact. -/
def ownPublicKey : CircuitM ZswapCoinPublicKey := do
  return disclose (← askWitness "ownPublicKey" ZswapCoinPublicKey)

/-- Add `coin` to the transaction's Zswap inputs (spend it). -/
def createZswapInput (coin : QualifiedShieldedCoinInfo) : CircuitM Unit :=
  askWitness "createZswapInput" Unit (Value.toExprs coin)

/-- Add `coin`, for `recipient`, to the transaction's Zswap outputs. -/
def createZswapOutput (coin : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress) :
    CircuitM Unit :=
  askWitness "createZswapOutput" Unit (Value.toExprs coin ++ Value.toExprs recipient)

/-! ## Shielded tokens -/

/-- The token type of the native token (all zeros). -/
def nativeToken : Bytes 32 := Bytes.pad 32 ""

/-- The token type a contract at `addr` mints under `domainSep`. -/
def tokenType (domainSep : Bytes 32) (addr : ContractAddress) : Bytes 32 :=
  persistentCommit (#v[domainSep, addr.bytes] : Vector (Bytes 32) 2) (Bytes.pad 32 "midnight:derive_token")

private def downcastQualifiedCoin (coin : QualifiedShieldedCoinInfo) : ShieldedCoinInfo :=
  { nonce := coin.nonce, color := coin.color, value := coin.value }

private def upcastQualifiedCoin (coin : ShieldedCoinInfo) : QualifiedShieldedCoinInfo :=
  { nonce := coin.nonce, color := coin.color, value := coin.value, mt_index := 0 }

/-- The commitment of `coin` sent to `recipient`. -/
def coinCommitment (coin : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress) :
    Bytes 32 :=
  persistentHash (α := CoinPreimage)
    { domain_sep := Bytes.pad 21 "midnight:zswap-cc[v1]"
      info := coin
      dataType := recipient.isLeft
      data := select recipient.isLeft recipient.left.bytes recipient.right.bytes }

/-- The nullifier of `coin` held by the contract at `addr`. -/
def coinNullifier (coin : ShieldedCoinInfo) (addr : ContractAddress) : Bytes 32 :=
  persistentHash (α := CoinPreimage)
    { domain_sep := Bytes.pad 21 "midnight:zswap-cn[v1]"
      info := coin
      dataType := .false
      data := addr.bytes }

/-- Mint `value` coins of this contract's token `domainSep`, as one new coin
    with nonce `nonce` for `recipient`. -/
def mintShieldedToken (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (recipient : Either ZswapCoinPublicKey ContractAddress) : CircuitM ShieldedCoinInfo := do
  const coin : ShieldedCoinInfo := { nonce, color := tokenType domainSep (← Kernel.self), value := value.widen }
  Kernel.mintShielded domainSep value
  createZswapOutput coin recipient
  -- compactc computes `!recipient.is_left` here, ahead of the commitment, and
  -- guards the `kernel.self()` read of the `&&` below with it.
  const notLeft := !. recipient.isLeft
  const cm := coinCommitment coin recipient
  Kernel.claimZswapCoinSpend cm
  -- Sent to this contract: it receives the coin as well. As in Compact,
  -- `kernel.self()` is read only when the recipient is a contract.
  let me ← underGuard (← nameGuard (guardAnd (← currentGuard) notLeft.expr)) Kernel.self
  if% (!. recipient.isLeft &&. (recipient.right.bytes ==. me.bytes)) then Kernel.claimZswapCoinReceive cm
  return coin

/-- A fresh nonce, derived from `nonce` and a counter `index`. -/
def evolveNonce (index : Uint128) (nonce : Bytes 32) : Bytes 32 :=
  upgradeFromTransient (transientHash
    #v[Field.ofString "midnight:kernel:nonce_evolve", index.toField, degradeToTransient nonce])

/-- A recipient that can never spend: sending there burns the coin. -/
def shieldedBurnAddress : Either ZswapCoinPublicKey ContractAddress := left (Value.zero ZswapCoinPublicKey)

/-- Receive `coin`, which the transaction sends to this contract. -/
def receiveShielded (coin : ShieldedCoinInfo) : CircuitM Unit := do
  const recipient := (right (← Kernel.self) : Either ZswapCoinPublicKey ContractAddress)
  createZswapOutput coin recipient
  Kernel.claimZswapCoinReceive (coinCommitment coin recipient)

/-- The nonce of a coin derived from one with nonce `nonce`, under `domain`. -/
private def derivedNonce (domain : String) (nonce : Bytes 32) : Bytes 32 :=
  upgradeFromTransient (transientHash #v[Field.ofString domain, degradeToTransient nonce])

/-- Send `value` out of the contract's coin `input` to `recipient`; the rest
    comes back to the contract as change. Fails if `value` exceeds the coin. -/
def sendShielded (input : QualifiedShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) : CircuitM ShieldedSendResult := do
  const selfAddr ← Kernel.self
  createZswapInput input
  Kernel.claimZswapNullifier (coinNullifier (downcastQualifiedCoin input) selfAddr)
  const change ← input.value.sub value
  const output : ShieldedCoinInfo :=
    { nonce := derivedNonce "midnight:kernel:nonce_evolve" input.nonce, color := input.color, value }
  createZswapOutput output recipient
  -- compactc hashes the commitment again for the receive (see docs/tokens.md);
  -- here it is computed once.
  const cm := coinCommitment output recipient
  Kernel.claimZswapCoinSpend cm
  if% (!. recipient.isLeft &&. (recipient.right.bytes ==. selfAddr.bytes)) then
    Kernel.claimZswapCoinReceive cm
  cond (change ==. (0 : Uint128))
    (pure { change := Maybe.none, sent := output })
    (do
      const changeCoin : ShieldedCoinInfo :=
        { nonce := derivedNonce "midnight:kernel:nonce_evolve/2" input.nonce, color := input.color,
          value := change }
      createZswapOutput changeCoin (right selfAddr)
      const cm := coinCommitment changeCoin (right selfAddr)
      Kernel.claimZswapCoinSpend cm
      Kernel.claimZswapCoinReceive cm
      return { change := Maybe.some changeCoin, sent := output })

/-- `sendShielded` of a coin created earlier in the same transaction. -/
def sendImmediateShielded (input : ShieldedCoinInfo) (target : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) : CircuitM ShieldedSendResult :=
  sendShielded (upcastQualifiedCoin input) target value

/-- Merge two of the contract's coins of the same color into one. -/
def mergeCoin (a b : QualifiedShieldedCoinInfo) : CircuitM ShieldedCoinInfo := do
  const selfAddr ← Kernel.self
  createZswapInput a
  Kernel.claimZswapNullifier (coinNullifier (downcastQualifiedCoin a) selfAddr)
  createZswapInput b
  Kernel.claimZswapNullifier (coinNullifier (downcastQualifiedCoin b) selfAddr)
  require (a.color ==. b.color) "Can only merge coins of the same color"
  const nonce := derivedNonce "midnight:kernel:nonce_evolve" a.nonce
  let value ← (a.value + b.value).castTo 340282366920938463463374607431768211455
  let newCoin : ShieldedCoinInfo := { nonce, color := a.color, value }
  createZswapOutput newCoin (right selfAddr)
  const cm := coinCommitment newCoin (right selfAddr)
  Kernel.claimZswapCoinSpend cm
  Kernel.claimZswapCoinReceive cm
  return newCoin

/-- `mergeCoin` where the second coin was created earlier in the same transaction. -/
def mergeCoinImmediate (a : QualifiedShieldedCoinInfo) (b : ShieldedCoinInfo) : CircuitM ShieldedCoinInfo :=
  mergeCoin a (upcastQualifiedCoin b)

/-! ## Unshielded tokens -/

/-- Whether `recipient` is this contract (reading `kernel.self()` only when the
    recipient is a contract). -/
private def isSelfU (recipient : Either ContractAddress UserAddress) : CircuitM Boolean :=
  cond recipient.isLeft (do return recipient.left.bytes ==. (← Kernel.self).bytes) (pure .false)

/-- Mint `amount` of this contract's unshielded token `domainSep` for
    `recipient`; returns the token type. -/
def mintUnshieldedToken (domainSep : Bytes 32) (amount : Uint64) (recipient : Either ContractAddress UserAddress) :
    CircuitM (Bytes 32) := do
  Kernel.mintUnshielded domainSep amount
  const color := tokenType domainSep (← Kernel.self)
  Kernel.claimUnshieldedCoinSpend (left color) recipient amount.widen
  if% (← isSelfU recipient) then Kernel.incUnshieldedInputs (left color) amount.widen
  return color

/-- Send `amount` of the contract's unshielded token `color` to `recipient`. -/
def sendUnshielded (color : Bytes 32) (amount : Uint128) (recipient : Either ContractAddress UserAddress) :
    CircuitM Unit := do
  Kernel.incUnshieldedOutputs (left color) amount
  Kernel.claimUnshieldedCoinSpend (left color) recipient amount
  if% (← isSelfU recipient) then Kernel.incUnshieldedInputs (left color) amount

/-- Accept `amount` of unshielded token `color` that the transaction sends to
    this contract. -/
def receiveUnshielded (color : Bytes 32) (amount : Uint128) : CircuitM Unit :=
  Kernel.incUnshieldedInputs (left color) amount

/-- The contract's balance of `color` when the transaction started (sends and
    receives in this call do not change it). -/
def unshieldedBalance (color : Bytes 32) : CircuitM Uint128 := Kernel.balance (left color)

def unshieldedBalanceLt (color : Bytes 32) (amount : Uint128) : CircuitM Boolean :=
  Kernel.balanceLessThan (left color) amount

def unshieldedBalanceGte (color : Bytes 32) (amount : Uint128) : CircuitM Boolean :=
  return (← unshieldedBalanceLt color amount).not

def unshieldedBalanceGt (color : Bytes 32) (amount : Uint128) : CircuitM Boolean :=
  Kernel.balanceGreaterThan (left color) amount

def unshieldedBalanceLte (color : Bytes 32) (amount : Uint128) : CircuitM Boolean :=
  return (← unshieldedBalanceGt color amount).not

/-! ## Storing a received coin

`writeCoin`, `insertCoin` and `pushFrontCoin` (Compact's "update with coin
check" operations, `compiler/midnight-ledger.ss`) store a coin that is an
output of the current transaction as a `QualifiedShieldedCoinInfo`: the ledger
looks its commitment up in the context's commitment indices (context slot 1;
an `idx` whose last key comes from the stack) and appends the index it finds
to the coin (`concat cached 91`). The index is only known when the
transaction runs, which is why these are ledger operations. They fail when
the commitment is not an output of the transaction. Sequences as compactc
0.36.1 emits them (`docs/tokens.md`). -/

namespace CoinStore
open IR Impact

private def aligned [Value α] (x : α) : Aligned Expr :=
  { align := (Value.tys α).map Ty.align, vals := Value.toExprs x }

/-- With the context `depth` below the top of the stack, push `coin` qualified
    with the Merkle-tree index of its commitment for `recipient`. -/
def qualify (depth : Nat) (coin : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress) :
    List (Op Expr) :=
  [.dup depth,
   .push false (aligned (coinCommitment coin recipient)),
   .idxStack [fieldKey 1],
   .push false (aligned coin),
   .swap 0,
   .concatCached 91]

def run (ops : List (Op Expr)) : CircuitM Unit := do
  emit (.ledger (← currentGuard) [] ops)
end CoinStore

open CoinStore in
/-- Store `coin`, an output of this transaction for `recipient`, qualified with
    its Merkle-tree index. -/
def Cell.writeCoin (c : Cell QualifiedShieldedCoinInfo) (coin : ShieldedCoinInfo)
    (recipient : Either ZswapCoinPublicKey ContractAddress) : CircuitM Unit :=
  run ([.push false (fieldKey c.index)] ++ qualify 3 coin recipient ++ [.ins false 1])

open CoinStore in
/-- Store `coin` (an output of this transaction for `recipient`) at `k`, qualified. -/
def Map.insertCoin [Value κ] (m : Map κ QualifiedShieldedCoinInfo) (k : κ) (coin : ShieldedCoinInfo)
    (recipient : Either ZswapCoinPublicKey ContractAddress) : CircuitM Unit :=
  run ([.idx false true m.path, .push false (CoinStore.aligned k)] ++
    qualify (3 + 2 * m.path.length) coin recipient ++ [.ins false 1, .ins true m.path.length])

open CoinStore in
/-- Add `coin` (an output of this transaction for `recipient`), qualified, to the set. -/
def Set.insertCoin (s : Set QualifiedShieldedCoinInfo) (coin : ShieldedCoinInfo)
    (recipient : Either ZswapCoinPublicKey ContractAddress) : CircuitM Unit :=
  run ([.idx false true s.path] ++ qualify (2 + 2 * s.path.length) coin recipient ++
    [.pushNull true, .ins false 1, .ins true s.path.length])

open CoinStore in
/-- Push `coin` (an output of this transaction for `recipient`), qualified, onto the list. -/
def LedgerList.pushFrontCoin (l : LedgerList QualifiedShieldedCoinInfo) (coin : ShieldedCoinInfo)
    (recipient : Either ZswapCoinPublicKey ContractAddress) : CircuitM Unit :=
  run ([.idx false true l.path,
    .dup 0,
    .idx false false [fieldKey 2],
    .addi (.const 1),
    .pushState true (.array [.null, .null, .null]),
    .push false (fieldKey 0)] ++
    qualify (5 + 2 * l.path.length) coin recipient ++
    [.ins true 1,
     .swap 0,
     .push false (fieldKey 2),
     .swap 0,
     .ins true 1,
     .swap 0,
     .push false (fieldKey 1),
     .swap 0,
     .ins true (l.path.length + 1)])

end Damp
