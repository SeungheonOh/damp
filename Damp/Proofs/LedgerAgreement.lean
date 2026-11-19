/-
What the executor sends to the ledger is what the circuit declares.

Midnight's model (Kachina) rests on this: the public inputs of a circuit are
the field encoding of exactly the instructions the ledger ran, with what they
read. The executor (`Damp/Executor/Spec.lean`) sends one thing to the ledger, the
`request`, with operands evaluated before the reads and every `popeq` result
blank, and declares another, `ledgerGroups`, with operands evaluated after the
reads are bound. Midnight's checker would catch a mismatch at proving time, as
an unprovable call; this file rules it out statically.

The condition is `IR.Stmt.ledgerWellFormed`: the `popeq` results, read left to
right, are exactly the read variables (each a plain variable), these are
distinct, and no other operand mentions one of them. Under it:

* `ledgerGroups_eq_transcript`: the public inputs are the field encoding of
  the *transcript*, the instructions with operands evaluated after the reads
  (this one needs no condition; it rests on `evalList_encode`, encoding
  commutes with evaluating operands);
* `request_eq_transcript`: the request is the transcript with its `popeq`
  results blanked, and exists whenever the transcript does;
* `results_transcript`: the `popeq` results of the transcript, in order, are
  the values the ledger returned;
* `step_ledger_agrees`: so the groups an executor step appends for a ledger
  statement encode the request it sent with the ledger's answers filled in
  (`fill`, which distributes the flat answers over the `popeq`s by the widths
  the statement fixes; `fill_unique` says why that determines the result);
* `run_groups_fromLedger`: every active group of a whole call arises that way.

`IR.Circuit.checkLedger` checks the condition on a circuit.
-/
import Damp.Executor.Spec
import Damp.IR.LedgerCheck

namespace Damp.Impact

variable {α β : Type}

/-! ## `mapM` in `Option` -/

/-- `List.mapM` changes nothing when the two functions agree on the list. -/
theorem list_mapM_congr {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.mapM_cons]
      rw [h x (by simp), list_mapM_congr xs (fun y hy => h y (by simp [hy]))]

/-- `List.mapM` succeeds when the function succeeds on every element. -/
theorem list_mapM_isSome {f : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | x :: xs, h => by
      have hx := h x (by simp)
      have hxs := list_mapM_isSome xs (fun y hy => h y (by simp [hy]))
      simp only [List.mapM_cons]
      cases hf : f x with
      | none => simp [hf] at hx
      | some y =>
        cases hm : xs.mapM f with
        | none => simp [hm] at hxs
        | some ys => rfl

/-- `List.mapM` keeps the length. -/
theorem list_mapM_length {f : α → Option β} :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | x :: xs, l', h => by
      simp only [List.mapM_cons] at h
      cases hf : f x with
      | none => simp [hf] at h
      | some y =>
        cases hm : xs.mapM f with
        | none => simp [hf, hm] at h
        | some ys =>
          simp [hf, hm] at h; subst h
          simp [list_mapM_length xs ys hm]

/-- Rewriting the values in a list of state values keeps its length. -/
theorem StateLit.mapMList_length {f : α → Option β} :
    ∀ (es : List (StateLit α)) (es' : List (StateLit β)), StateLit.mapMList f es = some es' →
      es'.length = es.length
  | [], es', h => by simp [StateLit.mapMList] at h; subst h; rfl
  | e :: es, es', h => by
      simp only [StateLit.mapMList] at h
      cases hf : StateLit.mapM f e with
      | none => simp [hf] at h
      | some y =>
        cases hm : StateLit.mapMList f es with
        | none => simp [hf, hm] at h
        | some ys =>
          simp [hf, hm] at h; subst h
          simp [StateLit.mapMList_length es ys hm]

/-! ## Encoding commutes with mapping the operands -/

section Encode
set_option linter.unusedSectionVars false
variable (c : Int → α) (c' : Int → β) (f : α → Option β) (hc : ∀ k, f (c k) = some (c' k))
include hc

/-- Mapping over encoded alignment atoms, which are constants, always succeeds. -/
theorem atoms_mapM (l : List Zkir.AlignAtom) :
    (l.map fun a => c (atomCode a)).mapM f = some (l.map fun a => c' (atomCode a)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.mapM_cons, hc, ih]; rfl

/-- Mapping over the encoding of an aligned value maps the value. -/
theorem Aligned.encode_mapM (v : Aligned α) :
    (v.encode c).mapM f = (v.mapM f).map (·.encode c') := by
  cases v with
  | mk align vals =>
    simp only [Aligned.encode, Aligned.mapM, List.mapM_cons, List.mapM_append, hc,
      atoms_mapM c c' f hc]
    cases vals.mapM f <;> rfl

mutual
/-- Mapping over the encoding of a state value maps the value. -/
theorem StateLit.encode_mapM : ∀ v : StateLit α,
    (v.encode c).mapM f = (v.mapM f).map (·.encode c')
  | .null => by simp [StateLit.encode, StateLit.mapM, hc]
  | .cell v => by
      simp only [StateLit.encode, StateLit.mapM, List.mapM_cons, hc,
        Aligned.encode_mapM c c' f hc]
      cases v.mapM f <;> rfl
  | .emptyMap => by simp [StateLit.encode, StateLit.mapM, hc]
  | .array es => by
      simp only [StateLit.encode, StateLit.mapM, List.mapM_cons, hc,
        StateLit.encodeList_mapM es]
      cases h : StateLit.mapMList f es with
      | none => rfl
      | some es' => simp [StateLit.encode, StateLit.mapMList_length es es' h]
  | .emptyMerkleTree d => by simp [StateLit.encode, StateLit.mapM, hc]
/-- `StateLit.encode_mapM` for lists. -/
theorem StateLit.encodeList_mapM : ∀ es : List (StateLit α),
    (StateLit.encodeList c es).mapM f = (StateLit.mapMList f es).map (StateLit.encodeList c')
  | [] => by simp [StateLit.encodeList, StateLit.mapMList]
  | e :: es => by
      simp only [StateLit.encodeList, StateLit.mapMList, List.mapM_append,
        StateLit.encode_mapM e, StateLit.encodeList_mapM es]
      cases StateLit.mapM f e <;> cases StateLit.mapMList f es <;> rfl
end

/-- Mapping over the encoding of a path maps the path. -/
theorem path_encode_mapM : ∀ path : List (Aligned α),
    (path.flatMap (·.encode c)).mapM f =
      (path.mapM (fun x : Aligned α => x.mapM f)).map (·.flatMap (·.encode c'))
  | [] => rfl
  | v :: vs => by
      simp only [List.flatMap_cons, List.mapM_append, List.mapM_cons,
        Aligned.encode_mapM c c' f hc, path_encode_mapM vs]
      cases v.mapM f <;> cases vs.mapM (fun x : Aligned α => x.mapM f) <;> rfl

/-- Mapping over the encoding of an instruction maps the instruction: the field
    elements of an instruction are those of the instruction with its operands
    mapped, and one fails exactly when the other does. -/
theorem Op.encode_mapM (op : Op α) :
    (op.encode c).mapM f = (op.mapM f).map (·.encode c') := by
  cases op <;> simp only [Op.encode, Op.mapM, List.mapM_cons, List.mapM_append, hc,
    atoms_mapM c c' f hc, Aligned.encode_mapM c c' f hc, StateLit.encode_mapM c c' f hc,
    path_encode_mapM c c' f hc]
  case idx cached pushPath path =>
    cases h : path.mapM (fun x : Aligned α => x.mapM f) with
    | none => rfl
    | some path' => simp [list_mapM_length path path' h]
  case idxStack pre =>
    cases h : pre.mapM (fun x : Aligned α => x.mapM f) with
    | none => rfl
    | some pre' => simp [list_mapM_length pre pre' h]
  case popeq r => cases r.mapM f <;> rfl
  case addi i => cases f i <;> rfl
  case subi i => cases f i <;> rfl
  case push v => cases v.mapM f <;> rfl
  case pushState v => cases v.mapM f <;> rfl
  all_goals rfl

end Encode

/-! ## Reads, blanks and widths under mapping -/

/-- A mapped instruction reads the mapped values. -/
theorem Op.results_mapM {f : α → Option β} {op : Op α} {op' : Op β} (h : op.mapM f = some op') :
    op.results.mapM f = some op'.results := by
  cases op <;> simp only [Op.mapM] at h
  case popeq c a r =>
    cases hr : r.mapM f with
    | none => simp [hr] at h
    | some r' => simp [hr] at h; subst h; simpa [Op.results] using hr
  all_goals
    first
    | (cases h; rfl)
    | (revert h; split <;> simp_all [Op.results])
    | (simp only [bind, Option.bind] at h; split at h <;> simp_all [Op.results]; subst h; rfl)

/-- Mapping keeps how many values an instruction reads. -/
theorem Op.width_mapM {f : α → Option β} {op : Op α} {op' : Op β} (h : op.mapM f = some op') :
    op'.width? = op.width? := by
  cases op <;> simp only [Op.mapM] at h
  case popeq c a r =>
    cases hr : r.mapM f with
    | none => simp [hr] at h
    | some r' => simp [hr] at h; subst h; simp [Op.width?, list_mapM_length r r' hr]
  all_goals
    first
    | (cases h; rfl)
    | (simp only [bind, Option.bind] at h; split at h <;> simp_all; subst h; rfl)

/-- Blanking commutes with mapping, provided what the instruction reads maps. -/
theorem Op.blank_mapM {f : α → Option β} (op : Op α) (hs : ∀ x ∈ op.results, (f x).isSome) :
    (op.mapM f).map Op.blank = op.blank.mapM f := by
  cases op
  case popeq c a r =>
    have := list_mapM_isSome r (by simpa [Op.results] using hs)
    simp only [Op.mapM, Op.blank, List.mapM_nil]
    cases hr : r.mapM f with
    | none => simp [hr] at this
    | some r' => rfl
  case addi i => simp only [Op.mapM, Op.blank]; cases f i <;> rfl
  case subi i => simp only [Op.mapM, Op.blank]; cases f i <;> rfl
  case push st v => simp only [Op.mapM, Op.blank]; cases v.mapM f <;> rfl
  case idx c pp path =>
    simp only [Op.mapM, Op.blank]; cases path.mapM (fun x : Aligned α => x.mapM f) <;> rfl
  case idxStack pre =>
    simp only [Op.mapM, Op.blank]; cases pre.mapM (fun x : Aligned α => x.mapM f) <;> rfl
  case pushState st v => simp only [Op.mapM, Op.blank]; cases v.mapM f <;> rfl
  all_goals rfl

/-! ## Mapping depends only on the operands -/

section Congr
variable {c : Int → α} {f g : α → Option β}

/-- Mapping an aligned value depends only on the operands in its encoding. -/
theorem Aligned.mapM_congr (v : Aligned α) (h : ∀ x ∈ v.encode c, f x = g x) :
    v.mapM f = v.mapM g := by
  simp only [Aligned.mapM]
  rw [list_mapM_congr v.vals (fun x hx => h x (by simp [Aligned.encode, hx]))]

mutual
/-- Mapping a state value depends only on the operands in its encoding. -/
theorem StateLit.mapM_congr : ∀ v : StateLit α, (∀ x ∈ v.encode c, f x = g x) →
    v.mapM f = v.mapM g
  | .null, _ | .emptyMap, _ | .emptyMerkleTree _, _ => rfl
  | .cell v, h => by
      simp only [StateLit.mapM]
      rw [Aligned.mapM_congr (c := c) v (fun x hx => h x (by simp [StateLit.encode, hx]))]
  | .array es, h => by
      simp only [StateLit.mapM]
      rw [StateLit.mapMList_congr es (fun x hx => h x (by simp [StateLit.encode, hx]))]
/-- `StateLit.mapM_congr` for lists. -/
theorem StateLit.mapMList_congr : ∀ es : List (StateLit α),
    (∀ x ∈ StateLit.encodeList c es, f x = g x) →
    StateLit.mapMList f es = StateLit.mapMList g es
  | [], _ => rfl
  | e :: es, h => by
      simp only [StateLit.mapMList]
      rw [StateLit.mapM_congr e (fun x hx => h x (by simp [StateLit.encodeList, hx])),
        StateLit.mapMList_congr es (fun x hx => h x (by simp [StateLit.encodeList, hx]))]
end

/-- Mapping an instruction depends only on the operands in its encoding. -/
theorem Op.mapM_congr (op : Op α) (h : ∀ x ∈ op.encode c, f x = g x) :
    op.mapM f = op.mapM g := by
  cases op
  case popeq cd a r =>
    simp only [Op.mapM]
    rw [list_mapM_congr r (fun x hx => h x (by simp [Op.encode, hx]))]
  case addi i => simp only [Op.mapM]; rw [h i (by simp [Op.encode])]
  case subi i => simp only [Op.mapM]; rw [h i (by simp [Op.encode])]
  case push st v =>
    simp only [Op.mapM]; rw [Aligned.mapM_congr (c := c) v (fun x hx => h x (by simp [Op.encode, hx]))]
  case idx cd pp path =>
    simp only [Op.mapM]
    rw [list_mapM_congr path (fun v hv => Aligned.mapM_congr (c := c) v
      (fun x hx => h x (by simp only [Op.encode, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨v, hv, hx⟩)))]
  case idxStack pre =>
    simp only [Op.mapM]
    rw [list_mapM_congr pre (fun v hv => Aligned.mapM_congr (c := c) v
      (fun x hx => h x (by
        simp only [Op.encode]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨v, hv, hx⟩)))))]
  case pushState st v =>
    simp only [Op.mapM]
    rw [StateLit.mapM_congr (c := c) v (fun x hx => h x (by simp [Op.encode, hx]))]
  all_goals rfl

end Congr

/-! ## Filling in what was read -/

/-- Fill one instruction: a `popeq` takes the next `w` values, `w` the next width. -/
def fillOne : Op α → List Nat → List α → Option (Op α × List Nat × List α)
  | .popeq cached align _, w :: ws, vals =>
      if w ≤ vals.length then some (.popeq cached align (vals.take w), ws, vals.drop w) else none
  | .popeq .., [], _ => none
  | op, ws, vals => some (op, ws, vals)

/-- Put the values `vals` that a ledger returned, flat and in order, into the
    `popeq`s of the instructions `req` that were sent, the `i`-th `popeq`
    taking `ws[i]` of them. Fails unless the counts match exactly. -/
def fill : List Nat → List (Op α) → List α → Option (List (Op α))
  | ws, [], vals => if ws.isEmpty && vals.isEmpty then some [] else none
  | ws, op :: ops, vals => do
      let (op', ws', vals') ← fillOne op ws vals
      let rest ← fill ws' ops vals'
      pure (op' :: rest)

/-- Filling the blanked instructions with what they read, by their widths,
    gives the instructions back. -/
theorem fill_blank : ∀ t : List (Op α),
    fill (popeqWidths t) (t.map Op.blank) (allResults t) = some t
  | [] => rfl
  | op :: t => by
      have ih := fill_blank t
      cases op
      case popeq cd a r =>
        simp [popeqWidths, allResults, Op.width?, Op.blank, Op.results, fill, fillOne] at ih ⊢
        simp [ih]
      all_goals
        simp only [popeqWidths, allResults] at ih
        simp [popeqWidths, allResults, Op.width?, Op.blank, Op.results, fill, fillOne,
          List.filterMap_cons, ih]

/-- Why `fill` is the right notion: an instruction list is determined by its
    blanked form, what its `popeq`s read (flat), and how many each reads. -/
theorem fill_unique {t₁ t₂ : List (Op α)} (hb : t₁.map Op.blank = t₂.map Op.blank)
    (hr : allResults t₁ = allResults t₂) (hw : popeqWidths t₁ = popeqWidths t₂) : t₁ = t₂ := by
  have h1 := fill_blank t₁
  rw [hb, hr, hw, fill_blank t₂] at h1
  exact (Option.some.inj h1).symm

end Damp.Impact

/-! ## The condition -/

namespace Damp.IR
open Impact

/-- The well-formedness of a ledger statement, as propositions. -/
structure LedgerWF (reads : List Var) (ops : List (Op Expr)) : Prop where
  results : allResults ops = reads.map Expr.var
  nodup : reads.Nodup
  fresh : ∀ op ∈ ops, ∀ v ∈ Expr.varsList (op.blank.encode Expr.const), v ∉ reads

/-- A well-formed ledger statement satisfies `LedgerWF`. -/
theorem ledgerWF_of {g : Expr} {reads : List Var} {ops : List (Op Expr)}
    (h : (Stmt.ledger g reads ops).ledgerWellFormed = true) : LedgerWF reads ops := by
  simp only [Stmt.ledgerWellFormed, Stmt.ledgerProblem, ledgerProblem] at h
  by_cases h1 : (allResults ops == reads.map Expr.var) = true
  · by_cases h2 : reads.Nodup
    · cases h3 : (ops.flatMap fun op => Expr.varsList (op.blank.encode Expr.const)).find?
          reads.contains with
      | some v => simp [h1, h2, h3] at h
      | none =>
        refine ⟨by simpa using h1, h2, fun op hop v hv hr => ?_⟩
        rw [List.find?_eq_none] at h3
        exact h3 v (List.mem_flatMap.2 ⟨op, hop, hv⟩) (by simpa using hr)
    · simp [h1, h2] at h
  · simp [h1] at h

/-- A circuit that passes `checkLedger` has only well-formed statements. -/
theorem checkLedgerFrom_ok {name : String} :
    ∀ (i : Nat) (ss : List Stmt), checkLedgerFrom name i ss = .ok () →
      ∀ s ∈ ss, s.ledgerWellFormed = true
  | _, [], _ => by simp
  | i, s :: ss, h => by
      simp only [checkLedgerFrom] at h
      cases hp : s.ledgerProblem with
      | some why => simp [hp] at h
      | none =>
        simp only [hp] at h
        intro s' hs'
        cases List.mem_cons.1 hs' with
        | inl e => subst e; simp [Stmt.ledgerWellFormed, hp]
        | inr m => exact checkLedgerFrom_ok (i + 1) ss h s' m

/-- Every statement of a circuit that passes `checkLedger` is well formed. -/
theorem Circuit.checkLedger_ok {c : Circuit} (h : c.checkLedger = .ok ()) :
    ∀ s ∈ c.body.toList, s.ledgerWellFormed = true :=
  checkLedgerFrom_ok 0 _ h

end Damp.IR

/-! ## The transcript, and what the executor sends and declares -/

namespace Damp.Exec
open IR Impact
open Damp.Zkir (Prims Group)

/-- The instructions of a ledger statement with their operands evaluated, what
    a `popeq` reads included: what the circuit declares. In the executor, `env`
    is the environment after the reads are bound. -/
def transcript (p : Prims) (env : Env) : List (Op Expr) → Option (List (Op Fr))
  | [] => some []
  | op :: ops => do
      let op' ← op.mapM (Expr.eval p env)
      let rest ← transcript p env ops
      pure (op' :: rest)

/-- The public-input group of an instruction that ran. -/
def ledgerGroup (op : Op Fr) : Group := { active := true, vals := op.encode Fr.ofInt }

/-- The executor's `blank` is `Op.blank`. -/
theorem blank_eq_opBlank : Exec.blank = Op.blank := by
  funext op; cases op <;> rfl

section Lemmas
variable (p : Prims)

/-- Evaluating a list of expressions is `List.mapM` of evaluation. -/
theorem evalList_eq_mapM (env : Env) : ∀ xs : List Expr,
    Expr.evalList p env xs = xs.mapM (Expr.eval p env)
  | [] => rfl
  | x :: xs => by simp only [Expr.evalList, List.mapM_cons, evalList_eq_mapM env xs]

/-- Encoding commutes with evaluating the operands: the field elements of an
    instruction's operands, evaluated, are the encoding of the instruction with
    its operands evaluated, and one fails exactly when the other does. -/
theorem evalList_encode (env : Env) (op : Op Expr) :
    Expr.evalList p env (op.encode Expr.const) =
      (op.mapM (Expr.eval p env)).map (·.encode Fr.ofInt) := by
  rw [evalList_eq_mapM]
  exact Op.encode_mapM Expr.const Fr.ofInt _ (fun k => by simp [Expr.eval]) op

mutual
/-- An expression's value depends only on the variables in it. -/
theorem eval_agree {e₁ e₂ : Env} :
    ∀ e : Expr, (∀ w ∈ e.vars, e₁ w = e₂ w) → e.eval p e₁ = e.eval p e₂
  | .var v, h => by simp only [Expr.eval]; rw [h v (by simp [Expr.vars])]
  | .const _, _ => rfl
  | .invalid _, _ => rfl
  | .disclose a, h => by
      simp only [Expr.eval]; exact eval_agree a (by simpa [Expr.vars] using h)
  | .neg a, h => by
      simp only [Expr.eval]; rw [eval_agree a (by simpa [Expr.vars] using h)]
  | .divmod _ _ a, h => by
      simp only [Expr.eval]; rw [eval_agree a (by simpa [Expr.vars] using h)]
  | .add a b, h | .mul a b, h | .eq a b, h | .lt _ a b, h => by
      simp only [Expr.vars, List.mem_append] at h
      simp only [Expr.eval]
      rw [eval_agree a (fun w hw => h w (Or.inl hw)), eval_agree b (fun w hw => h w (Or.inr hw))]
  | .select c a b, h => by
      simp only [Expr.vars, List.mem_append] at h
      simp only [Expr.eval]
      rw [eval_agree c (fun w hw => h w (Or.inl (Or.inl hw))),
        eval_agree a (fun w hw => h w (Or.inl (Or.inr hw))),
        eval_agree b (fun w hw => h w (Or.inr hw))]
  | .hash xs, h | .phash _ _ xs, h => by
      simp only [Expr.vars] at h
      simp only [Expr.eval]; rw [evalList_agree xs h]
/-- `eval_agree` for lists. -/
theorem evalList_agree {e₁ e₂ : Env} :
    ∀ xs : List Expr, (∀ w ∈ Expr.varsList xs, e₁ w = e₂ w) →
      Expr.evalList p e₁ xs = Expr.evalList p e₂ xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [Expr.varsList, List.mem_append] at h
      simp only [Expr.evalList]
      rw [eval_agree x (fun w hw => h w (Or.inl hw)), evalList_agree xs (fun w hw => h w (Or.inr hw))]
end

/-- A variable of an element is a variable of the list. -/
theorem mem_varsList {x : Expr} {w : Var} : ∀ {xs : List Expr}, x ∈ xs → w ∈ x.vars →
    w ∈ Expr.varsList xs
  | _ :: xs, hx, hw => by
      simp only [Expr.varsList, List.mem_append]
      cases List.mem_cons.1 hx with
      | inl e => subst e; exact Or.inl hw
      | inr m => exact Or.inr (mem_varsList m hw)

/-- Binding distinct variables to values: they get those values, and nothing
    else changes. -/
theorem assign_reads : ∀ (reads : List Var) (env env' : Env) (vals : List Fr), reads.Nodup →
    assign env (reads.map fun v => (v, none)) vals = some env' →
      reads.map env' = vals ∧ ∀ w, w ∉ reads → env' w = env w
  | [], env, env', vals, _, h => by
      cases vals <;> simp [assign] at h; subst h; simp
  | v :: rest, env, env', vals, hnd, h => by
      cases vals with
      | nil => simp [assign] at h
      | cons x xs =>
        simp only [List.map_cons, assign] at h
        rw [List.nodup_cons] at hnd
        obtain ⟨h1, h2⟩ := assign_reads rest _ env' xs hnd.2 h
        refine ⟨?_, fun w hw => ?_⟩
        · simp [h1, h2 v hnd.1, Env.set]
        · simp only [List.mem_cons, not_or] at hw
          rw [h2 w hw.2]; simp [Env.set, hw.1]

/-- Evaluating plain variables gives their values. -/
theorem mapM_eval_vars (env : Env) : ∀ reads : List Var,
    (reads.map Expr.var).mapM (Expr.eval p env) = some (reads.map env)
  | [] => rfl
  | v :: rest => by simp [List.mapM_cons, Expr.eval, mapM_eval_vars env rest]

/-- The request is the transcript, in the same environment, blanked. -/
theorem request_eq_map (env : Env) : ∀ ops : List (Op Expr),
    request p env ops = (transcript p env ops).map (·.map Exec.blank)
  | [] => rfl
  | op :: ops => by
      simp only [request, transcript, request_eq_map env ops]
      cases op.mapM (Expr.eval p env) <;> cases transcript p env ops <;> rfl

/-- What the `popeq`s of a transcript read is what their results evaluate to. -/
theorem transcript_results (env : Env) : ∀ (ops : List (Op Expr)) (t : List (Op Fr)),
    transcript p env ops = some t →
      (allResults ops).mapM (Expr.eval p env) = some (allResults t)
  | [], t, h => by simp [transcript] at h; subst h; rfl
  | op :: ops, t, h => by
      simp only [transcript] at h
      cases h1 : op.mapM (Expr.eval p env) with
      | none => simp [h1] at h
      | some op' =>
        cases h2 : transcript p env ops with
        | none => simp [h1, h2] at h
        | some rest =>
          simp [h1, h2] at h; subst h
          simp only [allResults, List.flatMap_cons, List.mapM_append,
            Op.results_mapM h1]
          have := transcript_results env ops rest h2
          simp only [allResults] at this
          simp [this]

/-- A transcript's `popeq`s read as many values as the statement's. -/
theorem transcript_widths (env : Env) : ∀ (ops : List (Op Expr)) (t : List (Op Fr)),
    transcript p env ops = some t → popeqWidths t = popeqWidths ops
  | [], t, h => by simp [transcript] at h; subst h; rfl
  | op :: ops, t, h => by
      simp only [transcript] at h
      cases h1 : op.mapM (Expr.eval p env) with
      | none => simp [h1] at h
      | some op' =>
        cases h2 : transcript p env ops with
        | none => simp [h1, h2] at h
        | some rest =>
          simp [h1, h2] at h; subst h
          have := transcript_widths env ops rest h2
          simp only [popeqWidths] at this
          simp [popeqWidths, List.filterMap_cons, Op.width_mapM h1, this]

/-- Blanked transcripts in two environments agree when each instruction does. -/
theorem transcript_blank_congr (env env' : Env) : ∀ ops : List (Op Expr),
    (∀ op ∈ ops, (op.mapM (Expr.eval p env)).map Op.blank =
      (op.mapM (Expr.eval p env')).map Op.blank) →
    (transcript p env ops).map (·.map Op.blank) = (transcript p env' ops).map (·.map Op.blank)
  | [], _ => rfl
  | op :: ops, h => by
      have h1 := h op (by simp)
      have h2 := transcript_blank_congr env env' ops (fun o ho => h o (by simp [ho]))
      simp only [transcript]
      cases hx : op.mapM (Expr.eval p env) <;> cases hy : op.mapM (Expr.eval p env') <;>
        cases hr : transcript p env ops <;> cases hr' : transcript p env' ops <;>
        simp_all

/-- The groups of an inactive ledger statement are all inactive. -/
theorem ledgerGroups_inactive (env : Env) : ∀ (ops : List (Op Expr)) (gs : List Group),
    ledgerGroups p env false ops = some gs → ∀ g ∈ gs, g.active = false
  | [], gs, h => by simp [ledgerGroups] at h; subst h; simp
  | op :: ops, gs, h => by
      simp only [ledgerGroups] at h
      cases h1 : Expr.evalList p env (op.encode Expr.const) with
      | none => simp [h1] at h
      | some vs =>
        cases h2 : ledgerGroups p env false ops with
        | none => simp [h1, h2] at h
        | some rest =>
          simp [h1, h2] at h; subst h
          intro g hg
          cases List.mem_cons.1 hg with
          | inl e => subst e; rfl
          | inr m => exact ledgerGroups_inactive env ops rest h2 g m


/-! ## The theorems -/

/-- **The public inputs are the encoding of the transcript.** An active ledger
    statement declares, for each instruction, its field encoding with the
    operands evaluated; this holds for every statement, well formed or not. -/
theorem ledgerGroups_eq_transcript (env : Env) : ∀ ops : List (Op Expr),
    ledgerGroups p env true ops = (transcript p env ops).map (·.map ledgerGroup)
  | [] => rfl
  | op :: ops => by
      simp only [ledgerGroups, transcript, evalList_encode, ledgerGroups_eq_transcript env ops]
      cases op.mapM (Expr.eval p env) <;> cases transcript p env ops <;> rfl

/-- `ledgerGroups_eq_transcript`, as it is used: the groups exist exactly when
    the transcript does, and are its encoding. -/
theorem ledgerGroups_iff (env : Env) (ops : List (Op Expr)) (gs : List Group) :
    ledgerGroups p env true ops = some gs ↔
      ∃ t, transcript p env ops = some t ∧ gs = t.map ledgerGroup := by
  rw [ledgerGroups_eq_transcript]
  cases transcript p env ops <;> simp [eq_comm]

section WellFormed
variable {p} {reads : List Var} {ops : List (Op Expr)} {env env' : Env} {vals : List Fr}
  (wf : LedgerWF reads ops) (ha : assign env (reads.map fun v => (v, none)) vals = some env')
include wf ha

/-- One instruction, blanked, is the same before and after the reads. -/
theorem blank_agree (op : Op Expr) (hop : op ∈ ops) :
    (op.mapM (Expr.eval p env)).map Op.blank = (op.mapM (Expr.eval p env')).map Op.blank := by
  obtain ⟨_, hagree⟩ := assign_reads reads env env' vals wf.nodup ha
  have hvars : ∀ x ∈ op.results, ∃ v, x = Expr.var v := by
    intro x hx
    have : x ∈ allResults ops := List.mem_flatMap.2 ⟨op, hop, hx⟩
    rw [wf.results] at this
    obtain ⟨v, _, hv⟩ := List.mem_map.1 this
    exact ⟨v, hv.symm⟩
  have hsome : ∀ e : Env, ∀ x ∈ op.results, (Expr.eval p e x).isSome := by
    intro e x hx
    obtain ⟨v, rfl⟩ := hvars x hx
    simp [Expr.eval]
  rw [Op.blank_mapM op (hsome env), Op.blank_mapM op (hsome env')]
  apply Op.mapM_congr (c := Expr.const)
  intro x hx
  apply eval_agree
  intro w hw
  exact (hagree w (wf.fresh op hop w (mem_varsList hx hw))).symm

/-- **What was sent is what is declared.** The request, computed before the
    reads, is the transcript, computed after them, with its `popeq` results
    blanked; in particular it exists whenever the transcript does. -/
theorem request_eq_transcript :
    request p env ops = (transcript p env' ops).map (·.map Exec.blank) := by
  rw [request_eq_map, blank_eq_opBlank]
  exact transcript_blank_congr p env env' ops (fun op hop => blank_agree wf ha op hop)

/-- **What was read is what is declared.** The `popeq` results of the
    transcript, in order, are the values the ledger returned. -/
theorem results_transcript {t : List (Op Fr)} (ht : transcript p env' ops = some t) :
    allResults t = vals := by
  obtain ⟨hvals, _⟩ := assign_reads reads env env' vals wf.nodup ha
  have := transcript_results p env' ops t ht
  rw [wf.results, mapM_eval_vars] at this
  rw [← hvals]; exact (Option.some.inj this).symm

/-- The transcript is the request with the ledger's answers filled in. -/
theorem fill_request {t : List (Op Fr)} (ht : transcript p env' ops = some t) :
    request p env ops = some (t.map Exec.blank) ∧
      fill (popeqWidths ops) (t.map Exec.blank) vals = some t := by
  refine ⟨by rw [request_eq_transcript wf ha, ht]; rfl, ?_⟩
  rw [← results_transcript wf ha ht, ← transcript_widths p env' ops t ht, blank_eq_opBlank]
  exact fill_blank t

end WellFormed

/-- **The executor declares what it ran.** When the executor completes a
    well-formed ledger statement whose guard holds, the groups it appends are
    the encoding of the instructions it sent to the ledger with the ledger's
    answers filled into the `popeq`s; these are also the instructions with
    operands evaluated after the reads (`transcript`). -/
theorem step_ledger_agrees {O : Oracles ω σ} {s s' : State ω σ} {guard : Expr} {reads : List Var}
    {ops : List (Op Expr)} {g : Fr}
    (hwf : (Stmt.ledger guard reads ops).ledgerWellFormed = true) (hops : ops ≠ [])
    (hg : guard.eval p s.env = some g) (hact : asBool g = some true)
    (hstep : step p O s (.ledger guard reads ops) = some s') :
    ∃ req vals t, request p s.env ops = some req ∧
      O.ledger req s.ledger = some (vals, s'.ledger) ∧
      fill (popeqWidths ops) req vals = some t ∧
      transcript p s'.env ops = some t ∧
      s'.pub = s.pub ++ vals ∧
      s'.groups = s.groups ++ t.map ledgerGroup := by
  have wf := ledgerWF_of hwf
  have hne : (reads.isEmpty && ops.isEmpty) = false := by
    cases ops with
    | nil => exact absurd rfl hops
    | cons _ _ => simp
  simp only [step, hg, hne, hact, bind, Option.bind, Bool.false_eq_true, ite_false, ite_true] at hstep
  cases hreq : request p s.env ops with
  | none => simp [hreq] at hstep
  | some req =>
    cases hled : O.ledger req s.ledger with
    | none => simp [hreq, hled] at hstep
    | some r =>
      obtain ⟨vals, σ'⟩ := r
      cases hasg : assign s.env (reads.map fun v => (v, none)) vals with
      | none => simp [hreq, hled, hasg] at hstep
      | some env' =>
        cases hgs : ledgerGroups p env' true ops with
        | none => simp [hreq, hled, hasg, hgs] at hstep
        | some gs =>
          simp [hreq, hled, hasg, hgs, pure] at hstep
          subst hstep
          obtain ⟨t, ht, rfl⟩ := (ledgerGroups_iff p env' ops gs).1 hgs
          obtain ⟨hr, hf⟩ := fill_request wf hasg ht
          rw [hreq] at hr
          cases hr
          exact ⟨_, vals, t, rfl, hled, hf, ht, rfl, rfl⟩


/-! ## A whole call -/

/-- A step other than a ledger statement declares nothing. -/
theorem step_groups_other {O : Oracles ω σ} {s s' : State ω σ} {st : Stmt}
    (hst : ∀ g r o, st ≠ .ledger g r o) (h : step p O s st = some s') : s'.groups = s.groups := by
  cases st
  case ledger g r o => exact absurd rfl (hst g r o)
  all_goals
    simp only [step, bind, Option.bind_eq_some_iff, pure] at h
    repeat' (first
      | (obtain ⟨_, _, h⟩ := h)
      | (simp only [Option.bind_eq_some_iff] at h)
      | (split at h)
      | (cases h; done)
      | (subst h; done))
  all_goals first | rfl | contradiction | (cases h; rfl)

/-- A group that arises from one of the ledger statements `stmts`: the
    encoding of an instruction of a request the executor computed for it and
    the ledger answered, with the ledger's answers filled into the `popeq`s. -/
def FromLedger (O : Oracles ω σ) (stmts : List Stmt) (grp : Group) : Prop :=
  ∃ guard reads ops env σ₀ req vals σ₁ t,
    Stmt.ledger guard reads ops ∈ stmts ∧ request p env ops = some req ∧
    O.ledger req σ₀ = some (vals, σ₁) ∧ fill (popeqWidths ops) req vals = some t ∧
    grp ∈ t.map ledgerGroup

/-- `FromLedger` holds for any larger list of statements. -/
theorem FromLedger.mono {O : Oracles ω σ} {l l' : List Stmt} {grp : Group}
    (h : FromLedger p O l grp) (hl : ∀ st ∈ l, st ∈ l') : FromLedger p O l' grp := by
  obtain ⟨g, r, o, env, σ₀, req, vals, σ₁, t, hm, h1, h2, h3, h4⟩ := h
  exact ⟨g, r, o, env, σ₀, req, vals, σ₁, t, hl _ hm, h1, h2, h3, h4⟩

/-- Every active group one well-formed step appends arises from that statement. -/
theorem step_groups {O : Oracles ω σ} {s s' : State ω σ} {st : Stmt}
    (hwf : st.ledgerWellFormed = true) (h : step p O s st = some s') :
    ∃ gs, s'.groups = s.groups ++ gs ∧
      ∀ grp ∈ gs, grp.active = true → FromLedger p O [st] grp := by
  cases st
  case ledger guard reads ops =>
    have wf := ledgerWF_of hwf
    cases hg : guard.eval p s.env with
    | none => simp [step, hg, bind, Option.bind] at h
    | some g =>
      by_cases hne : (reads.isEmpty && ops.isEmpty) = true
      · simp [step, hg, hne, bind, Option.bind] at h
        subst h; exact ⟨[], by simp, by simp⟩
      · cases hb : asBool g with
        | none => simp [step, hg, hne, hb, bind, Option.bind] at h
        | some b =>
          cases b
          · -- Not run: every group it declares is inactive.
            simp [step, hg, hne, hb, Option.bind_eq_some_iff] at h
            obtain ⟨env, _, gs, hgs, rfl⟩ := h
            exact ⟨gs, rfl, fun grp hm hact => by
              rw [ledgerGroups_inactive p env ops gs hgs grp hm] at hact; contradiction⟩
          · have hops : ops ≠ [] := by
              intro e; subst e
              have := wf.results
              simp [allResults] at this
              cases reads <;> simp_all
            obtain ⟨req, vals, t, hreq, hled, hf, _, _, hgr⟩ :=
              step_ledger_agrees p hwf hops hg hb h
            exact ⟨t.map ledgerGroup, hgr, fun grp hm _ =>
              ⟨guard, reads, ops, s.env, s.ledger, req, vals, s'.ledger, t,
                by simp, hreq, hled, hf, hm⟩⟩
  all_goals exact ⟨[], by simp [step_groups_other p (by simp) h], by simp⟩

/-- Every active group a run of well-formed statements appends arises from one of them. -/
theorem steps_groups {O : Oracles ω σ} : ∀ (stmts : List Stmt) (s s' : State ω σ),
    (∀ st ∈ stmts, st.ledgerWellFormed = true) → steps p O stmts s = some s' →
    ∃ gs, s'.groups = s.groups ++ gs ∧
      ∀ grp ∈ gs, grp.active = true → FromLedger p O stmts grp
  | [], s, s', _, h => by simp [steps] at h; subst h; exact ⟨[], by simp, by simp⟩
  | st :: rest, s, s', hwf, h => by
      simp only [steps, bind, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      obtain ⟨gs1, e1, f1⟩ := step_groups p (hwf st (by simp)) h1
      obtain ⟨gs2, e2, f2⟩ := steps_groups rest s1 s' (fun x hx => hwf x (by simp [hx])) h2
      refine ⟨gs1 ++ gs2, by rw [e2, e1, List.append_assoc], fun grp hm hact => ?_⟩
      cases List.mem_append.1 hm with
      | inl m => exact (f1 grp m hact).mono p (fun x hx => by simp_all)
      | inr m => exact (f2 grp m hact).mono p (fun x hx => by simp [hx])

/-- **Every active public input of a call is the encoding of an instruction
    the ledger ran.** For a circuit that passes `checkLedger`, every active
    group a completed call records encodes an instruction of a request the
    executor made for one of the circuit's ledger statements, with the
    ledger's answers to that request filled into the `popeq`s. -/
theorem run_groups_fromLedger {O : Oracles ω σ} {c : Circuit} {inputs : List Fr} {w : ω} {l : σ}
    {r : Result ω σ} (hc : c.checkLedger = .ok ()) (hr : run p O c inputs w l = some r) :
    ∀ grp ∈ r.groups, grp.active = true → FromLedger p O c.body.toList grp := by
  simp only [run, bind, Option.bind_eq_some_iff, pure] at hr
  obtain ⟨env, _, s, hs, _, _, hrr⟩ := hr
  injection hrr with hrr; subst hrr
  obtain ⟨gs, e, f⟩ := steps_groups p _ _ s (Circuit.checkLedger_ok hc) hs
  intro grp hm hact
  simp only [e, List.nil_append] at hm
  exact f grp hm hact

end Lemmas
end Damp.Exec
