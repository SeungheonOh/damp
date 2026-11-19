import Damp

/-! `bench/compact/unshielded_tokens.compact` (Compact's
test-center/compact/unshielded-tokens.compact): every token operation as its own circuit. -/
namespace Bench.UnshieldedTokens
open Damp

abbrev UR := Either ContractAddress UserAddress
abbrev SR := Either ZswapCoinPublicKey ContractAddress

circuit mintUnshieldedToSelfTest (domainSep : Bytes 32) (amount : Uint64) : Bytes 32 := do
  mintUnshieldedToken (disclose domainSep) (disclose amount) (left (← Kernel.self) : UR)

circuit mintUnshieldedToContractTest (domainSep : Bytes 32) (address : ContractAddress) (amount : Uint64) : Bytes 32 :=
  mintUnshieldedToken (disclose domainSep) (disclose amount) (left (disclose address) : UR)

circuit mintUnshieldedToUserTest (domainSep : Bytes 32) (address : UserAddress) (amount : Uint64) : Bytes 32 :=
  mintUnshieldedToken (disclose domainSep) (disclose amount) (right (disclose address) : UR)

circuit sendUnshieldedToSelfTest (color : Bytes 32) (amount : Uint128) : Unit := do
  sendUnshielded (disclose color) (disclose amount) (left (← Kernel.self) : UR)

circuit sendUnshieldedToContractTest (color : Bytes 32) (amount : Uint128) (address : ContractAddress) : Unit :=
  sendUnshielded (disclose color) (disclose amount) (left (disclose address) : UR)

circuit sendUnshieldedToUserTest (color : Bytes 32) (amount : Uint128) (address : UserAddress) : Unit :=
  sendUnshielded (disclose color) (disclose amount) (right (disclose address) : UR)

circuit receiveUnshieldedTest (color : Bytes 32) (amount : Uint128) : Unit :=
  receiveUnshielded (disclose color) (disclose amount)

circuit getUnshieldedBalanceTest (color : Bytes 32) : Uint128 :=
  unshieldedBalance (disclose color)

circuit getUnshieldedBalanceGtTest (color : Bytes 32) (amount : Uint128) : Boolean :=
  unshieldedBalanceGt (disclose color) (disclose amount)

circuit getUnshieldedBalanceLtTest (color : Bytes 32) (amount : Uint128) : Boolean :=
  unshieldedBalanceLt (disclose color) (disclose amount)

circuit mintShieldedToSelfTest (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32) : ShieldedCoinInfo := do
  mintShieldedToken (disclose domainSep) (disclose value) (disclose nonce) (right (← Kernel.self) : SR)

circuit mintShieldedToContractTest (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (address : ContractAddress) : ShieldedCoinInfo :=
  mintShieldedToken (disclose domainSep) (disclose value) (disclose nonce) (right (disclose address) : SR)

circuit mintShieldedToUserTest (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (publicKey : ZswapCoinPublicKey) : ShieldedCoinInfo :=
  mintShieldedToken (disclose domainSep) (disclose value) (disclose nonce) (left (disclose publicKey) : SR)

circuit receiveShieldedTest (coin : ShieldedCoinInfo) : Unit :=
  receiveShielded (disclose coin)

circuit sendShieldedToSelfTest (input : QualifiedShieldedCoinInfo) (value : Uint128) : ShieldedSendResult := do
  sendShielded (disclose input) (right (← Kernel.self) : SR) (disclose value)

circuit sendShieldedToContractTest (input : QualifiedShieldedCoinInfo) (address : ContractAddress)
    (value : Uint128) : ShieldedSendResult :=
  sendShielded (disclose input) (right (disclose address) : SR) (disclose value)

circuit sendShieldedToUserTest (input : QualifiedShieldedCoinInfo) (publicKey : ZswapCoinPublicKey)
    (value : Uint128) : ShieldedSendResult :=
  sendShielded (disclose input) (left (disclose publicKey) : SR) (disclose value)

circuit sendImmediateShieldedToSelfTest (input : ShieldedCoinInfo) (value : Uint128) : ShieldedSendResult := do
  sendImmediateShielded (disclose input) (right (← Kernel.self) : SR) (disclose value)

circuit sendImmediateShieldedToContractTest (input : ShieldedCoinInfo) (address : ContractAddress)
    (value : Uint128) : ShieldedSendResult :=
  sendImmediateShielded (disclose input) (right (disclose address) : SR) (disclose value)

circuit sendImmediateShieldedToUserTest (input : ShieldedCoinInfo) (publicKey : ZswapCoinPublicKey)
    (value : Uint128) : ShieldedSendResult :=
  sendImmediateShielded (disclose input) (left (disclose publicKey) : SR) (disclose value)

contract unshielded_tokens

end Bench.UnshieldedTokens
