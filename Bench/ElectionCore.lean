import Damp

/-! `bench/compact/election_core.compact` (Compact's examples/election.compact with a `Field`
topic in place of its `Opaque<"string">` one; see the header of the Compact file). -/
namespace Bench.ElectionCore
open Damp

enum PublicState where
  | setup
  | commit
  | reveal
  | final

enum PrivateState where
  | initial
  | committed
  | revealed

enum PermissibleVotes where
  | yes
  | no

ledger
  authority : Cell (Bytes 32)
  state : Cell PublicState
  topic : Cell (Maybe Field)
  tally_yes : Counter
  tally_no : Counter
  committed_votes : MerkleTree 10 (Bytes 32)
  eligible_voters : MerkleTree 10 (Bytes 32)
  committed : Set (Bytes 32)
  revealed : Set (Bytes 32)

witness private_secret_key : Bytes 32
witness private_state : PrivateState
witness private_state_advance : Unit
witness private_vote_record (ballot : PermissibleVotes) : Unit
witness private_vote : PermissibleVotes
witness context_eligible_voters_path_of (pk : Bytes 32) : Maybe (MerkleTreePath 10 (Bytes 32))
witness context_committed_votes_path_of (cm : Bytes 32) : Maybe (MerkleTreePath 10 (Bytes 32))

def ballotRepr (ballot : PermissibleVotes) : Bytes 32 :=
  select (ballot ==. PermissibleVotes.yes) (Bytes.pad 32 "yes") (Bytes.pad 32 "no")

def commitmentNullifier (sk : Bytes 32) : Bytes 32 :=
  disclose (persistentHash #v[Bytes.pad 32 "lares:election:cm-nul:", sk])

def revealNullifier (sk : Bytes 32) : Bytes 32 :=
  disclose (persistentHash #v[Bytes.pad 32 "lares:election:rv-nul:", sk])

def publicKey (sk : Bytes 32) : Bytes 32 :=
  disclose (persistentHash #v[Bytes.pad 32 "lares:election:pk:", sk])

def commitWithSk (ballot : Bytes 32) (sk : Bytes 32) : Bytes 32 :=
  disclose (persistentHash #v[ballot, sk])

def successor (s : PublicState) : PublicState :=
  select (s ==. PublicState.setup) PublicState.commit
    (select (s ==. PublicState.commit) PublicState.reveal PublicState.final)

circuit vote_commit (ballot : PermissibleVotes) : Unit := do
  require ((← state.read) ==. PublicState.commit &&. (← private_state) ==. PrivateState.initial)
    "In illegal state for committing"
  private_vote_record ballot
  const sk ← private_secret_key
  const comNul := commitmentNullifier sk
  require (!.(← committed.member comNul)) "Unexpected attempt to double use of nullifier"
  const pk := publicKey sk
  const path := disclose (← context_eligible_voters_path_of pk)
  require (path.isSome &&.
           (← eligible_voters.checkRoot (disclose (← merkleTreePathRoot path.value))) &&.
           pk ==. path.value.leaf) "Attempted to vote without authorization - need to add-voter"
  const cm := commitWithSk (ballotRepr ballot) sk
  committed_votes.insert cm
  committed.insert comNul
  private_state_advance

circuit vote_reveal : Unit := do
  require ((← state.read) ==. PublicState.reveal &&. (← private_state) ==. PrivateState.committed)
    "In illegal state for revealing"
  const sk ← private_secret_key
  const revNul := revealNullifier sk
  require (!.(← revealed.member revNul)) "Attempted to double vote"
  const vote ← private_vote
  const cm := commitWithSk (ballotRepr vote) sk
  const path := disclose (← context_committed_votes_path_of cm)
  require (path.isSome &&.
           (← committed_votes.checkRoot (disclose (← merkleTreePathRoot path.value))) &&.
           cm ==. path.value.leaf) "Attempted to reveal incorrectly"
  if% disclose vote ==. PermissibleVotes.yes then tally_yes.increment 1 else tally_no.increment 1
  revealed.insert revNul
  private_state_advance

circuit advance : Unit := do
  const sk ← private_secret_key
  const apk := publicKey sk
  require (apk ==. (← authority.read)) "Attempted to advance state without authorization"
  require (← topic.read).isSome "Attempted to start election without a topic"
  state.write (successor (← state.read))

circuit set_topic (t : Field) : Unit := do
  const sk ← private_secret_key
  const apk := publicKey sk
  require (apk ==. (← authority.read)) "Attempted to set topic without authorization"
  require ((← state.read) ==. PublicState.setup) "Attempted to set topic after setup phase"
  topic.write (Maybe.some (disclose t))

circuit add_voter (pk : Bytes 32) : Unit := do
  require (!.(← context_eligible_voters_path_of pk).isSome) "Attempted to add a voter twice"
  const sk ← private_secret_key
  const apk := publicKey sk
  require (apk ==. (← authority.read)) "Attempted to add a voter without authorization"
  require ((← state.read) ==. PublicState.setup) "Attempted to add a voter after setup phase"
  eligible_voters.insert (disclose pk)

contract election_core exports vote_commit vote_reveal advance set_topic add_voter

end Bench.ElectionCore
