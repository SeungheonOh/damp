import Damp

/-! `bench/compact/zerocash_core.compact` (Compact's examples/zerocash.compact without its
`Opaque` ciphertexts; see the header of the Compact file). -/
namespace Bench.ZerocashCore
open Damp

struct Nonce where
  bytes : Bytes 32
struct opening where
  bytes : Bytes 32
struct nullifier where
  bytes : Bytes 32
struct zk_secret_key where
  bytes : Bytes 32
struct zk_public_key where
  bytes : Bytes 32
struct commitment where
  bytes : Bytes 32

struct coin_info where
  nonce : Nonce
  opening : opening

struct public_key where
  zk : zk_public_key

witness private_zk_secret_key : zk_secret_key
witness private_remove_coin (coin : coin_info) : Unit
witness private_zk_public_key : zk_public_key
witness private_add_coin (coin : coin_info) : Unit
witness context_path_of (cm : commitment) : MerkleTreePath 32 commitment
witness context_new_coin_info : coin_info

ledger
  nullifiers : Set nullifier
  commitments : HistoricMerkleTree 32 commitment

def deriveNullifier (coin : coin_info) (sk : zk_secret_key) : nullifier :=
  ⟨disclose (persistentHash #v[Bytes.pad 32 "lares:zerocash:commit", coin.nonce.bytes,
    coin.opening.bytes, sk.bytes])⟩

def deriveZkPublicKey (sk : zk_secret_key) : zk_public_key :=
  ⟨persistentHash sk.bytes⟩

def commitmentFromCoinInfo (coin : coin_info) (pk : zk_public_key) : commitment :=
  ⟨disclose (persistentHash #v[Bytes.pad 32 "lares:zerocash:commit", coin.nonce.bytes,
    coin.opening.bytes, pk.bytes])⟩

circuit spend (dest_public_key : public_key) (input_coin : coin_info) : Unit := do
  const sourceSecretKey ← private_zk_secret_key
  const oldNullifier := deriveNullifier input_coin sourceSecretKey
  require (!.(← nullifiers.member oldNullifier)) "spend: Coin already spent"
  nullifiers.insert oldNullifier
  const sourcePublicKey := deriveZkPublicKey sourceSecretKey
  const oldCommitment := commitmentFromCoinInfo input_coin sourcePublicKey
  const commitmentPath ← context_path_of oldCommitment
  require ((← commitments.checkRoot (disclose (← merkleTreePathRoot commitmentPath))) &&.
           oldCommitment ==. commitmentPath.leaf)
    "spend: Illegal state: merkle path not recognized by public state"
  const freshCoinInfo ← context_new_coin_info
  const freshCommitment := commitmentFromCoinInfo freshCoinInfo dest_public_key.zk
  commitments.insert freshCommitment
  private_remove_coin input_coin

circuit zerocash_mint : Unit := do
  const coin ← context_new_coin_info
  const pk ← private_zk_public_key
  private_add_coin coin
  const cm := commitmentFromCoinInfo coin pk
  commitments.insert cm

contract zerocash_core exports zerocash_mint spend

end Bench.ZerocashCore
