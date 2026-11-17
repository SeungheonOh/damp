import Damp

/-! The Lean counterpart of `test/oracle/tokens.compact`: every coin and token
function of the standard library (`Damp/Tokens.lean`), with the recipients
chosen so that both the constant and the run-time cases of each are compiled. -/
namespace Examples.Tokens
open Damp

ledger
  treasury : Cell QualifiedShieldedCoinInfo
  last : Cell ShieldedCoinInfo
  change : Cell (Maybe ShieldedCoinInfo)
  color : Cell (Bytes 32)
  nonce : Cell (Bytes 32)
  owner : Cell ZswapCoinPublicKey
  held : Cell QualifiedShieldedCoinInfo
  heldMap : Map Field QualifiedShieldedCoinInfo
  heldSet : Set QualifiedShieldedCoinInfo
  heldList : LedgerList QualifiedShieldedCoinInfo

abbrev Recipient := Either ZswapCoinPublicKey ContractAddress
abbrev URecipient := Either ContractAddress UserAddress

circuit mint (amount : Uint64) (n : Bytes 32) (to : ZswapCoinPublicKey) : Unit := do
  last.write (← mintShieldedToken (Bytes.pad 32 "damp:token") (disclose amount) (disclose n)
    (left (disclose to)))

circuit mintSelf (amount : Uint64) (n : Bytes 32) : Unit := do
  last.write (← mintShieldedToken (Bytes.pad 32 "damp:token") (disclose amount) (disclose n)
    (right (← Kernel.self)))

circuit mintTo (amount : Uint64) (n : Bytes 32) (to : Recipient) : Unit := do
  last.write (← mintShieldedToken (Bytes.pad 32 "damp:token") (disclose amount) (disclose n) (disclose to))

circuit deposit (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  last.write (disclose coin)

circuit setTreasury (coin : QualifiedShieldedCoinInfo) : Unit := do
  treasury.write (disclose coin)

circuit pay (to : Recipient) (value : Uint128) : Unit := do
  const r ← sendShielded (← treasury.read) (disclose to) (disclose value)
  last.write r.sent
  change.write r.change

circuit payImm (coin : ShieldedCoinInfo) (to : Recipient) (value : Uint128) : Unit := do
  const r ← sendImmediateShielded (disclose coin) (disclose to) (disclose value)
  last.write r.sent
  change.write r.change

circuit burn (value : Uint128) : Unit := do
  const r ← sendShielded (← treasury.read) shieldedBurnAddress (disclose value)
  last.write r.sent

circuit merge (b : QualifiedShieldedCoinInfo) : Unit := do
  last.write (← mergeCoin (← treasury.read) (disclose b))

circuit mergeImm (b : ShieldedCoinInfo) : Unit := do
  last.write (← mergeCoinImmediate (← treasury.read) (disclose b))

circuit evolve (i : Uint128) : Unit := do
  nonce.write (evolveNonce (disclose i) (← nonce.read))

circuit whoami : ZswapCoinPublicKey := do
  const k ← ownPublicKey
  owner.write k
  return k

circuit native : Unit := do
  color.write nativeToken

circuit derive (ds : Bytes 32) : Bytes 32 := do
  const t := tokenType ds (← Kernel.self)
  color.write t
  return t

circuit mintU (amount : Uint64) (who : UserAddress) : Unit := do
  color.write (← mintUnshieldedToken (Bytes.pad 32 "damp:u") (disclose amount) (right (disclose who)))

circuit mintUTo (amount : Uint64) (to : URecipient) : Unit := do
  color.write (← mintUnshieldedToken (Bytes.pad 32 "damp:u") (disclose amount) (disclose to))

circuit sendU (amount : Uint128) (to : URecipient) : Unit := do
  sendUnshielded (← color.read) (disclose amount) (disclose to)

circuit recvU (amount : Uint128) : Unit := do
  receiveUnshielded (← color.read) (disclose amount)

circuit balU : Uint128 := do
  unshieldedBalance (← color.read)

circuit cmpU (amount : Uint128) : Vector Boolean 4 := do
  const lt ← unshieldedBalanceLt (← color.read) (disclose amount)
  const gte ← unshieldedBalanceGte (← color.read) (disclose amount)
  const gt ← unshieldedBalanceGt (← color.read) (disclose amount)
  const lte ← unshieldedBalanceLte (← color.read) (disclose amount)
  return #v[lt, gte, gt, lte]

/-! Holding coins: receive one and store it qualified with its Merkle-tree
index, then spend and merge the stored coins, storing the change. -/

def toSelf : CircuitM Recipient := return right (← Kernel.self)

circuit keep (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  held.writeCoin (disclose coin) (← toSelf)

circuit keepOnly (coin : ShieldedCoinInfo) (to : Recipient) : Unit := do
  held.writeCoin (disclose coin) (disclose to)

circuit keepMap (k : Field) (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  heldMap.insertCoin (disclose k) (disclose coin) (← toSelf)

circuit keepSet (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  heldSet.insertCoin (disclose coin) (← toSelf)

circuit keepList (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  heldList.pushFrontCoin (disclose coin) (← toSelf)

circuit spend (to : Recipient) (value : Uint128) : Unit := do
  const r ← sendShielded (← held.read) (disclose to) (disclose value)
  last.write r.sent
  if% r.change.isSome then do held.writeCoin r.change.value (← toSelf)

circuit mergeKept (k : Field) : Unit := do
  const m ← mergeCoin (← held.read) (← heldMap.lookup (disclose k))
  held.writeCoin m (← toSelf)

circuit mergeHeld (coin : ShieldedCoinInfo) : Unit := do
  receiveShielded (disclose coin)
  const m ← mergeCoinImmediate (← held.read) (disclose coin)
  held.writeCoin m (← toSelf)

contract tokens

end Examples.Tokens
