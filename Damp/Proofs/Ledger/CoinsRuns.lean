/-
The coin-storing operations end to end through the executor (`XRuns`, as in
`TokensRuns.lean`), under a guard meaning `gb`, against the modelled ledger
(`oracles H (Damp.Exec.liftWitness w)`).

The coin means `coinFs` (stored by the VM as `cv`), the recipient
`Fr.ofBool u :: rl ++ rr`; nothing is assumed about the hash: the commitment
the circuit computes (`phashFs` of `ccPre`, `coinCommitment_is`) is `cm`,
pushed as the 32-byte atom `cmv`. With the guard on, the operation completes
exactly when the commitment has an index in the context (slot 1, `idx`) and
the qualified coin fits the VM's bound (`qualifyAV cv idx cmv` is some `q`);
then the field holds `q` and nothing else changes (private state, effects,
context, other fields). With the guard off, nothing is asked and nothing
changes. `qualifyAV_index` (`Coins.lean`) says what `q` is.
-/
import Damp.Proofs.Ledger.Coins

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section
variable {ω : Type} (H : Hooks) (p : Zkir.Prims) (w : String → List Fr → ω → Option (List Fr × ω))
  (coin : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
  {s : Build} {st : Exec.State ω LedgerState} {gb : Bool}
  (coinFs : List Fr) (cv : AV) (u : Bool) (rl rr : List Fr) (cm : List Fr) (cmv : AV)
  (fields cfs : List SV) (idx : List (AV × SV))

/-- **`Cell.writeCoin coin recipient`, run by the executor.** -/
theorem Cell.writeCoin_runs (c : Cell QualifiedShieldedCoinInfo) (hg : GuardIs p s st.runState gb)
    (hcoin : Stable s.next st.env (fun e => Value.Is p e coin coinFs))
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (hcm : phashFs p coinPreimageAlign (ccPre coinFs u rl rr) = some cm)
    (hcmv : AV.ofFields [.bytes 32] cm = some cmv)
    (hst : st.ledger.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256)
    (hwf : st.ledger.WF) (hctx : st.ledger.context = .array cfs) (hidx : cfs[1]? = some (.map idx)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (c.writeCoin coin recipient) s st (gb = true → (qualifyAV cv idx cmv).isSome = true)
      (fun _ _ w' l => w' = st.private_ ∧
        (if gb then ∃ q, qualifyAV cv idx cmv = some q ∧ l = st.ledger.setField c.index (.cell q)
         else l = st.ledger)) :=
  XRuns.mapOp rfl (by simp) hg fun e he =>
    Cell.writeCoin_spec H p e st.ledger fields cfs idx coin recipient coinFs cm cv cmv c hst hi hb hwf hctx hidx
      (hcoin e he) hcv (coinCommitment_is (hcoin e he) hsh hrl (hr e he) hcm) hcmv

/-- **`Map.insertCoin k coin recipient`, run by the executor**, on a top-level map. -/
theorem Map.insertCoin_runs {κ : Type} [Value κ] (mp : Map κ QualifiedShieldedCoinInfo) (m : List (AV × SV))
    (k : κ) (ks : List Fr) (kv : AV) (hg : GuardIs p s st.runState gb)
    (hk : Stable s.next st.env (fun e => Value.Is p e k ks)) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hcoin : Stable s.next st.env (fun e => Value.Is p e coin coinFs))
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (hcm : phashFs p coinPreimageAlign (ccPre coinFs u rl rr) = some cm)
    (hcmv : AV.ofFields [.bytes 32] cm = some cmv)
    (hpath : mp.path = [fieldKey mp.index]) (hst : st.ledger.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256)
    (hwf : st.ledger.WF) (hctx : st.ledger.context = .array cfs) (hidx : cfs[1]? = some (.map idx)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mp.insertCoin k coin recipient) s st (gb = true → (qualifyAV cv idx cmv).isSome = true)
      (fun _ _ w' l => w' = st.private_ ∧
        (if gb then ∃ q, qualifyAV cv idx cmv = some q ∧
            l = st.ledger.setField mp.index (.map (assocSet kv (.cell q) m))
         else l = st.ledger)) :=
  XRuns.mapOp rfl (by simp) hg fun e he =>
    Map.insertCoin_spec H p e st.ledger fields cfs idx coin recipient coinFs cm cv cmv mp m k ks kv hpath hst hf hb
      hwf hctx hidx (hk e he) hkv (hcoin e he) hcv (coinCommitment_is (hcoin e he) hsh hrl (hr e he) hcm) hcmv

/-- **`Set.insertCoin coin recipient`, run by the executor**, on a top-level set. -/
theorem Set.insertCoin_runs (st' : Set QualifiedShieldedCoinInfo) (m : List (AV × SV))
    (hg : GuardIs p s st.runState gb)
    (hcoin : Stable s.next st.env (fun e => Value.Is p e coin coinFs))
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (hcm : phashFs p coinPreimageAlign (ccPre coinFs u rl rr) = some cm)
    (hcmv : AV.ofFields [.bytes 32] cm = some cmv)
    (hpath : st'.path = [fieldKey st'.index]) (hst : st.ledger.state = .array fields)
    (hf : fields[st'.index]? = some (.map m)) (hb : st'.index < 256)
    (hwf : st.ledger.WF) (hctx : st.ledger.context = .array cfs) (hidx : cfs[1]? = some (.map idx)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (st'.insertCoin coin recipient) s st (gb = true → (qualifyAV cv idx cmv).isSome = true)
      (fun _ _ w' l => w' = st.private_ ∧
        (if gb then ∃ q, qualifyAV cv idx cmv = some q ∧
            l = st.ledger.setField st'.index (.map (assocSet q .null m))
         else l = st.ledger)) :=
  XRuns.mapOp rfl (by simp) hg fun e he =>
    Set.insertCoin_spec H p e st.ledger fields cfs idx coin recipient coinFs cm cv cmv st' m hpath hst hf hb
      hwf hctx hidx (hcoin e he) hcv (coinCommitment_is (hcoin e he) hsh hrl (hr e he) hcm) hcmv

/-- **`LedgerList.pushFrontCoin coin recipient`, run by the executor**, on a
    top-level list holding `xs`. -/
theorem LedgerList.pushFrontCoin_runs (l : LedgerList QualifiedShieldedCoinInfo) (xs : List AV)
    (hg : GuardIs p s st.runState gb)
    (hcoin : Stable s.next st.env (fun e => Value.Is p e coin coinFs))
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (hcm : phashFs p coinPreimageAlign (ccPre coinFs u rl rr) = some cm)
    (hcmv : AV.ofFields [.bytes 32] cm = some cmv)
    (hpath : l.path = [fieldKey l.index]) (hst : st.ledger.state = .array fields)
    (hf : fields[l.index]? = some (listRepr xs)) (hb : l.index < 256) (hlen : xs.length + 1 < 2 ^ 64)
    (hwf : st.ledger.WF) (hctx : st.ledger.context = .array cfs) (hidx : cfs[1]? = some (.map idx)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (l.pushFrontCoin coin recipient) s st (gb = true → (qualifyAV cv idx cmv).isSome = true)
      (fun _ _ w' l' => w' = st.private_ ∧
        (if gb then ∃ q, qualifyAV cv idx cmv = some q ∧ l' = st.ledger.setField l.index (listRepr (q :: xs))
         else l' = st.ledger)) :=
  XRuns.mapOp rfl (by simp) hg fun e he =>
    LedgerList.pushFrontCoin_spec H p e st.ledger fields cfs idx coin recipient coinFs cm cv cmv l xs hpath hst hf hb
      hwf hlen hctx hidx (hcoin e he) hcv (coinCommitment_is (hcoin e he) hsh hrl (hr e he) hcm) hcmv

end

end Damp.Ledger
