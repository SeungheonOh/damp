import Damp

/-! `bench/compact/coracle.compact` (Compact's examples/camelCase/new/coracle.compact): a
two-player guessing game with a pot of shielded coins. The generic `Committable<A>` and
`Commitment<A>` are used only at `A = Board` and are written for it. -/
namespace Bench.Coracle
open Damp

enum Player where
  | red
  | blue

enum State where
  | no_game
  | red_started
  | blue_started
  | red_turn
  | blue_turn
  | red_wins
  | blue_wins

struct Board where
  position : Field

struct Committable where
  nonce : Field
  contents : Board

struct Commitment where
  value : Field

struct WithdrawnCoins where
  wager : ShieldedCoinInfo
  deposit : ShieldedCoinInfo

abbrev Recipient := Either ZswapCoinPublicKey ContractAddress

ledger
  red : Cell (Bytes 32)
  blue : Cell (Bytes 32)
  red_board : Cell Commitment
  blue_board : Cell Commitment
  last_guess : Cell (Maybe Field)
  state : Cell State
  pot : Cell QualifiedShieldedCoinInfo
  red_deposit : Cell QualifiedShieldedCoinInfo
  blue_deposit : Cell QualifiedShieldedCoinInfo

witness local_secret_key : Bytes 32
witness local_board : Committable
witness local_set_board (board : Committable) : Unit
witness fresh_nonce : Field

constructor := do
  state.write State.no_game
  last_guess.write Maybe.none

def commit (c : Committable) : Commitment :=
  ⟨transientCommit c.contents c.nonce⟩

def isMatch (c : Committable) (b : Commitment) : Boolean :=
  (commit c).value ==. b.value

circuit red_pk (sk : Bytes 32) : Bytes 32 :=
  return disclose (persistentHash #v[sk, Bytes.pad 32 "coracle:red"])

circuit is_red (sk : Bytes 32) (pk : Bytes 32) : Boolean :=
  return disclose (pk ==. persistentHash #v[sk, Bytes.pad 32 "coracle:red"])

circuit blue_pk (sk : Bytes 32) : Bytes 32 :=
  return disclose (persistentHash #v[sk, Bytes.pad 32 "coracle:blue"])

circuit is_blue (sk : Bytes 32) (pk : Bytes 32) : Boolean :=
  return disclose (pk ==. persistentHash #v[sk, Bytes.pad 32 "coracle:blue"])

def isValidPos (pos : Field) : Boolean :=
  pos ==. (1 : Field) ||. pos ==. (2 : Field) ||. pos ==. (3 : Field) ||. pos ==. (4 : Field) ||.
  pos ==. (5 : Field) ||. pos ==. (6 : Field) ||. pos ==. (7 : Field) ||. pos ==. (8 : Field) ||.
  pos ==. (9 : Field)

def isValidBoard (board : Board) : Boolean := isValidPos board.position

def isPlayerHonest (localBoard : Committable) (remoteBoard : Commitment) : Boolean :=
  isValidBoard localBoard.contents &&. isMatch localBoard remoteBoard

def isBlueTurn (s : State) : Boolean := s ==. State.blue_turn ||. s ==. State.blue_started

def isRedTurn (s : State) : Boolean := s ==. State.red_turn

circuit is_player_alive (localBoard : Committable) (guess : Field) : Boolean :=
  return !.(localBoard.contents.position ==. guess)

circuit start (pos : Field) (wager_in deposit_in : ShieldedCoinInfo) : Player := do
  const wager := disclose wager_in
  const deposit := disclose deposit_in
  require ((← state.read) ==. State.no_game ||. (← state.read) ==. State.red_started)
    "The game already has two players"
  if% (← state.read) ==. State.red_started then
    require (wager.value ==. (← pot.read).value &&. wager.color ==. (← pot.read).color)
      "Blue must match Reds wager"
  require (deposit.value ==. 100000 &&. deposit.color ==. nativeToken) "Invalid deposit"
  const b : Board := ⟨pos⟩
  require (isValidBoard b) "Initial board is not valid"
  receiveShielded wager
  receiveShielded deposit
  const sk ← local_secret_key
  const n ← fresh_nonce
  const cb : Committable := ⟨n, b⟩
  if% (← state.read) ==. State.no_game then do
    pot.writeCoin wager (right (← Kernel.self) : Recipient)
    red_deposit.writeCoin deposit (right (← Kernel.self) : Recipient)
    red.write (← red_pk sk)
    red_board.write (commit cb)
    state.write State.red_started
    local_set_board cb
    return Player.red
  else do
    pot.writeCoin (← mergeCoinImmediate (← pot.read) wager) (right (← Kernel.self) : Recipient)
    blue_deposit.writeCoin deposit (right (← Kernel.self) : Recipient)
    blue.write (← blue_pk sk)
    blue_board.write (commit cb)
    state.write State.blue_started
    local_set_board cb
    return Player.blue

def redGuess (myGuess : Field) : CircuitM Unit := do
  const sk ← local_secret_key
  const lb ← local_board
  require (← is_red sk (← red.read)) "Not player Red"
  require (isPlayerHonest lb (← red_board.read)) "Red player is not honest"
  require (isRedTurn (← state.read)) "Not Red's turn"
  require (← is_player_alive lb (← last_guess.read).value) "Red player is not alive"
  require (isValidPos myGuess) "Red guess is not a valid position"
  last_guess.write (Maybe.some (disclose myGuess))
  state.write State.blue_turn

def blueGuess (myGuess : Field) : CircuitM Unit := do
  const sk ← local_secret_key
  const lb ← local_board
  require (← is_blue sk (← blue.read)) "Not player Blue"
  require (isPlayerHonest lb (← blue_board.read)) "Blue player is not honest"
  require (isBlueTurn (← state.read)) "Not Blue's turn"
  require (← is_player_alive lb (← last_guess.read).value) "Blue player is not alive"
  require (isValidPos myGuess) "Blue guess is not a valid position"
  last_guess.write (Maybe.some (disclose myGuess))
  state.write State.red_turn

circuit guess (position : Field) : Unit := do
  const sk ← local_secret_key
  const playerIsRed ← is_red sk (← red.read)
  const playerIsBlue ← is_blue sk (← blue.read)
  require (playerIsRed ||. playerIsBlue) "Not a player"
  if% playerIsRed then redGuess position else blueGuess position

def redConcede : CircuitM ShieldedCoinInfo := do
  const sk ← local_secret_key
  const lb ← local_board
  require (← is_red sk (← red.read)) "Not player Red"
  require (isPlayerHonest lb (← red_board.read)) "Red player is not honest"
  require (isRedTurn (← state.read)) "Not Red's turn"
  require (!.(← is_player_alive lb (← last_guess.read).value)) "Red player is still alive"
  state.write State.blue_wins
  return (← sendShielded (← red_deposit.read) (left (← ownPublicKey) : Recipient)
    (← red_deposit.read).value).sent

def blueConcede : CircuitM ShieldedCoinInfo := do
  const sk ← local_secret_key
  const lb ← local_board
  require (← is_blue sk (← blue.read)) "Not player Blue"
  require (isPlayerHonest lb (← blue_board.read)) "Blue player is not honest"
  require (isBlueTurn (← state.read)) "Not Blue's turn"
  require (!.(← is_player_alive lb (← last_guess.read).value)) "Blue player is still alive"
  state.write State.red_wins
  return (← sendShielded (← blue_deposit.read) (left (← ownPublicKey) : Recipient)
    (← blue_deposit.read).value).sent

circuit concede : ShieldedCoinInfo := do
  const sk ← local_secret_key
  const playerIsRed ← is_red sk (← red.read)
  const playerIsBlue ← is_blue sk (← blue.read)
  require (playerIsRed ||. playerIsBlue) "Not a player"
  const r ← if% playerIsRed then redConcede else blueConcede
  return disclose r

def redWithdraw : CircuitM WithdrawnCoins := do
  const sk ← local_secret_key
  require (← is_red sk (← red.read)) "Not player Red"
  require ((← state.read) ==. State.red_wins) "Red hasn't won"
  const wager := (← sendShielded (← pot.read) (left (← ownPublicKey) : Recipient) (← pot.read).value).sent
  const deposit := (← sendShielded (← red_deposit.read) (left (← ownPublicKey) : Recipient)
    (← red_deposit.read).value).sent
  return ⟨wager, deposit⟩

def blueWithdraw : CircuitM WithdrawnCoins := do
  const sk ← local_secret_key
  require (← is_blue sk (← blue.read)) "Not player Blue"
  require ((← state.read) ==. State.blue_wins) "Blue hasn't won"
  const wager := (← sendShielded (← pot.read) (left (← ownPublicKey) : Recipient) (← pot.read).value).sent
  const deposit := (← sendShielded (← blue_deposit.read) (left (← ownPublicKey) : Recipient)
    (← blue_deposit.read).value).sent
  return ⟨wager, deposit⟩

circuit withdraw : WithdrawnCoins := do
  const sk ← local_secret_key
  const playerIsRed ← is_red sk (← red.read)
  const playerIsBlue ← is_blue sk (← blue.read)
  require (playerIsRed ||. playerIsBlue) "Not a player"
  const r ← if% playerIsRed then redWithdraw else blueWithdraw
  return disclose r

contract coracle exports red_pk is_red blue_pk is_blue is_player_alive start guess concede withdraw

end Bench.Coracle
