/-
`contract.json` reads back: the executor's input is pinned to the contract.

`Export.contract c` (`Damp/Compile/Export.lean`) is what `Contract.writeFiles`
writes, as `Json.pretty` text, to `contract.json`; `Export.ofJson` reads it.
The file does not carry everything in a `Contract`: `disclose` wrappers, the
names and ranges of circuit inputs, and a circuit's `errors` are not written.
`Contract.exported c` is `c` with exactly those erased. This file proves

    Export.ofJson (Text.reorder (Export.contract c)) = .ok c.exported
                                                      (Export.ofJson_reorder)
    Text.lex text = .ok (Text.toks (Export.contract c)) →
      Export.parse text = .ok c.exported              (Export.ofText)

`reorder` is what parsing the text gives (`Damp/Proofs/JsonText.lean`). That
the `Json.pretty` text written to the file satisfies the hypothesis is checked
on every contract of Examples and Bench by `test/jsontext.sh`.
-/
import Damp.Compile.Export
import Damp.Proofs.JsonText
import Std.Data.String.ToInt
import Std.Data.String.ToNat

namespace Damp
open Lean (Json JsonNumber)
open IR
open Zkir.Text (reorder depth frag)

/-! ## What the file carries -/

mutual
/-- `e` without `disclose` wrappers. -/
def IR.Expr.erase : Expr → Expr
  | .var v => .var v
  | .const c => .const c
  | .invalid m => .invalid m
  | .disclose e => e.erase
  | .add a b => .add a.erase b.erase
  | .mul a b => .mul a.erase b.erase
  | .neg a => .neg a.erase
  | .lt n a b => .lt n a.erase b.erase
  | .eq a b => .eq a.erase b.erase
  | .select c a b => .select c.erase a.erase b.erase
  | .divmod q n a => .divmod q n a.erase
  | .hash xs => .hash (Expr.eraseList xs)
  | .phash h al xs => .phash h al (Expr.eraseList xs)
def IR.Expr.eraseList : List Expr → List Expr
  | [] => []
  | e :: es => e.erase :: Expr.eraseList es
end

/-- An aligned value without `disclose` wrappers. -/
def Impact.Aligned.erase (v : Impact.Aligned Expr) : Impact.Aligned Expr :=
  { align := v.align, vals := v.vals.map Expr.erase }

mutual
def Impact.StateLit.erase : Impact.StateLit Expr → Impact.StateLit Expr
  | .null => .null
  | .cell v => .cell v.erase
  | .emptyMap => .emptyMap
  | .array es => .array (Impact.StateLit.eraseList es)
  | .emptyMerkleTree d => .emptyMerkleTree d
def Impact.StateLit.eraseList : List (Impact.StateLit Expr) → List (Impact.StateLit Expr)
  | [] => []
  | e :: es => e.erase :: Impact.StateLit.eraseList es
end

def Impact.Op.erase : Impact.Op Expr → Impact.Op Expr
  | .popeq c a r => .popeq c a (r.map Expr.erase)
  | .addi i => .addi i.erase
  | .subi i => .subi i.erase
  | .push s v => .push s v.erase
  | .idx c p path => .idx c p (path.map Impact.Aligned.erase)
  | .pushState s v => .pushState s v.erase
  | .idxStack pre => .idxStack (pre.map Impact.Aligned.erase)
  | o => o

def IR.Stmt.erase : Stmt → Stmt
  | .bind v h e => .bind v h e.erase
  | .assert c m => .assert c.erase m
  | .constrain e r => .constrain e.erase r
  | .witness g name args outs sh => .witness g.erase name (args.map Expr.erase) outs sh
  | .ledger g reads ops => .ledger g.erase reads (ops.map Impact.Op.erase)

/-- What `contract.json` carries of a circuit: inputs without names or
    ranges, no `disclose` wrappers, no errors. -/
def IR.Circuit.exported (c : Circuit) : Circuit :=
  { name := c.name, args := c.args, inputs := c.inputs.map fun i => { name := "", var := i.var, range := none },
    body := c.body.map Stmt.erase, result := c.result, outputs := c.outputs.map Expr.erase }

/-- What `contract.json` carries of a contract. -/
def Contract.exported (c : Contract) : Contract :=
  { c with circuits := c.circuits.map Circuit.exported, constructor := c.constructor.map Circuit.exported }

namespace ExportRT
open Export (Read.field)

theorem field_mkObj (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (k : String) :
    Export.Read.field (reorder (Json.mkObj l)) k =
      match l.lookup k with
      | some v => .ok (reorder v)
      | none => .error s!"property not found: {k}" :=
  Zkir.Text.getObjVal?_reorder_mkObj l k hd

theorem depth_field (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (k : String) (v : Json)
    (h : l.lookup k = some v) : depth (reorder v) < depth (reorder (Json.mkObj l)) :=
  Zkir.Text.depth_lt_getObjVal? _ k _ (by rw [Zkir.Text.getObjVal?_reorder_mkObj l k hd, h])

theorem depth_field_lt (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (k : String) (v : Json)
    (hl : l.lookup k = some v) {n : Nat} (h : depth (reorder (Json.mkObj l)) < n + 1) : depth (reorder v) < n := by
  have := depth_field l hd k v hl; omega

theorem depth_elem (l : List Json) (x : Json) (hx : x ∈ l) :
    depth (reorder x) < depth (reorder (.arr l.toArray)) := by
  rw [Zkir.Text.reorder_arr]
  apply Zkir.Text.depth_lt_arr
  simp only [List.map_toArray, List.toList_toArray]
  exact List.mem_map_of_mem hx

theorem reorder_arr_list (l : List Json) : reorder (.arr l.toArray) = .arr (l.map reorder).toArray := by
  rw [Zkir.Text.reorder_arr]; simp

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : ((Except.ok a : Except ε α) >>= f) = f a := rfl
theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
theorem ok_map {ε α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

theorem getNat?_nat (n : Nat) : Json.getNat? (n : Json) = .ok n := rfl

theorem toNat?_toString (n : Nat) : (toString n).toNat? = some n := by
  rw [Nat.toString_eq_repr]; exact Nat.toNat?_repr n

theorem toInt?_toString (i : Int) : (toString i).toInt? = some i := Int.toInt?_repr i

/-- The rewrites that read back one level of a printed value. -/
macro "rt_simp" : tactic =>
  `(tactic| simp (disch := simp) only [Export.tag_eq, Export.int_eq, Export.nat_eq, Export.Read.kind,
      Export.Read.str, Export.Read.num, Export.Read.bool, Export.Read.natStr, Export.Read.intStr, Export.Read.arr,
      Export.Read.asStr, Export.Read.asNum, field_mkObj, List.lookup, Zkir.Text.reorder_str, Zkir.Text.reorder_num,
      Zkir.Text.reorder_bool, Zkir.Text.reorder_null, reorder_arr_list, List.toList_toArray, ok_bind, pure_ok,
      ok_map, getNat?_nat, toNat?_toString, toInt?_toString, beq_self_eq_true, String.reduceBEq,
      String.reduceEq, ↓reduceIte, List.map_map])

theorem exprs_eq : ∀ xs : List Expr, Export.exprs xs = xs.map Export.expr
  | [] => by simp [Export.exprs]
  | x :: xs => by simp [Export.exprs, exprs_eq xs]

theorem depth_arr_field (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (k : String) (L : List Json)
    (hl : l.lookup k = some (.arr L.toArray)) {n : Nat} (h : depth (reorder (Json.mkObj l)) < n + 1) :
    ∀ x ∈ L, depth (reorder x) < n := by
  intro x hx
  have := depth_field l hd k _ hl
  have := depth_elem L x hx
  omega

theorem mapM_ok {α β : Type} (f : α → Except String β) (g : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (g x)) → xs.mapM f = .ok (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.mapM_cons, h x (by simp), mapM_ok f g xs (fun y hy => h y (by simp [hy]))]; rfl

theorem eraseList_eq : ∀ xs : List Expr, Expr.eraseList xs = xs.map Expr.erase
  | [] => by simp [Expr.eraseList]
  | x :: xs => by simp [Expr.eraseList, eraseList_eq xs]

theorem atom_rt (a : Zkir.AlignAtom) : Export.Read.atom (reorder (Export.atom a)) = .ok a := by
  cases a <;> simp only [Export.atom, Export.Read.atom] <;> rt_simp

theorem atoms_rt (al : List Zkir.AlignAtom) :
    (al.map (reorder ∘ Export.atom)).mapM Export.Read.atom = .ok al := by
  rw [List.mapM_map]
  have := mapM_ok (Export.Read.atom ∘ (reorder ∘ Export.atom)) id al (fun a _ => atom_rt a)
  simpa using this

theorem expr_rt : ∀ (e : Expr) (n : Nat), depth (reorder (Export.expr e)) < n →
    Export.Read.expr n (reorder (Export.expr e)) = .ok e.erase
  | .disclose e, n, h => by
      simp only [Export.expr, Expr.erase] at h ⊢; exact expr_rt e n h
  | .var v, n + 1, _ => by simp only [Export.expr, Export.Read.expr, Expr.erase]; rt_simp
  | .const c, n + 1, _ => by simp only [Export.expr, Export.Read.expr, Expr.erase]; rt_simp
  | .invalid m, n + 1, _ => by simp only [Export.expr, Export.Read.expr, Expr.erase]; rt_simp
  | .add a b, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      have hb := expr_rt b n (depth_field_lt _ (by simp) "b" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha, hb]; rfl
  | .mul a b, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      have hb := expr_rt b n (depth_field_lt _ (by simp) "b" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha, hb]; rfl
  | .eq a b, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      have hb := expr_rt b n (depth_field_lt _ (by simp) "b" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha, hb]; rfl
  | .lt bits a b, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      have hb := expr_rt b n (depth_field_lt _ (by simp) "b" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha, hb]; rfl
  | .neg a, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha]; rfl
  | .divmod q bits a, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [ha]; rfl
  | .select c a b, n + 1, h => by
      simp only [Export.expr, Export.tag_eq] at h ⊢
      have hc := expr_rt c n (depth_field_lt _ (by simp) "c" _ rfl h)
      have ha := expr_rt a n (depth_field_lt _ (by simp) "a" _ rfl h)
      have hb := expr_rt b n (depth_field_lt _ (by simp) "b" _ rfl h)
      simp only [Export.Read.expr, Expr.erase]; rt_simp; rw [hc, ha, hb]; rfl
  | .hash xs, n + 1, h => by
      simp only [Export.expr, Export.tag_eq, exprs_eq] at h ⊢
      have hd := depth_arr_field _ (by simp) "xs" _ rfl h
      have hl : (xs.map (reorder ∘ Export.expr)).mapM (Export.Read.expr n) = .ok (xs.map Expr.erase) := by
        rw [List.mapM_map]
        exact mapM_ok _ _ xs (fun x hx => expr_rt x n (hd _ (List.mem_map_of_mem hx)))
      simp only [Export.Read.expr, Expr.erase, eraseList_eq]; rt_simp; rw [hl]; rfl
  | .phash high al xs, n + 1, h => by
      simp only [Export.expr, Export.tag_eq, exprs_eq] at h ⊢
      have hd := depth_arr_field _ (by simp) "xs" _ rfl h
      have hl : (xs.map (reorder ∘ Export.expr)).mapM (Export.Read.expr n) = .ok (xs.map Expr.erase) := by
        rw [List.mapM_map]
        exact mapM_ok _ _ xs (fun x hx => expr_rt x n (hd _ (List.mem_map_of_mem hx)))
      simp only [Export.Read.expr, Expr.erase, eraseList_eq, Export.Read.atoms]; rt_simp; rw [atoms_rt, hl]; rfl
termination_by e => e
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) | (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

theorem ty_rt (t : Ty) : Export.Read.ty (reorder (Export.ty t)) = .ok t := by
  cases t <;> simp only [Export.ty, Export.Read.ty] <;> rt_simp

theorem shapes_eq : ∀ ss : List Shape, Export.shapes ss = ss.map Export.shape
  | [] => by simp [Export.shapes]
  | x :: xs => by simp [Export.shapes, shapes_eq xs]

theorem shape_rt : ∀ (s : Shape) (n : Nat), depth (reorder (Export.shape s)) < n →
    Export.Read.shape n (reorder (Export.shape s)) = .ok s
  | .prim t, n + 1, _ => by
      cases t <;> simp only [Export.shape, Export.ty, Export.Read.shape] <;> rt_simp <;>
        simp only [Export.Read.ty] <;> rt_simp
  | .vector k e, n + 1, h => by
      simp only [Export.shape, Export.tag_eq] at h ⊢
      have he := shape_rt e n (depth_field_lt _ (by simp) "elem" _ rfl h)
      simp only [Export.Read.shape]; rt_simp; rw [he]; rfl
  | .tuple es, n + 1, h => by
      simp only [Export.shape, Export.tag_eq, shapes_eq] at h ⊢
      have hd := depth_arr_field _ (by simp) "elems" _ rfl h
      have hl : (es.map (reorder ∘ Export.shape)).mapM (Export.Read.shape n) = .ok es := by
        rw [List.mapM_map]
        have := mapM_ok (Export.Read.shape n ∘ reorder ∘ Export.shape) id es (fun x hx => shape_rt x n (hd _ (List.mem_map_of_mem hx)))
        rwa [List.map_id] at this
      simp only [Export.Read.shape]; rt_simp; rw [hl]; rfl
  | .struct name fns fs, n + 1, h => by
      simp only [Export.shape, Export.tag_eq, shapes_eq] at h ⊢
      have hd := depth_arr_field _ (by simp) "fields" _ rfl h
      have hl : (fs.map (reorder ∘ Export.shape)).mapM (Export.Read.shape n) = .ok fs := by
        rw [List.mapM_map]
        have := mapM_ok (Export.Read.shape n ∘ reorder ∘ Export.shape) id fs (fun x hx => shape_rt x n (hd _ (List.mem_map_of_mem hx)))
        rwa [List.map_id] at this
      have hn : (fns.map (reorder ∘ Json.str)).mapM Export.Read.asStr = .ok fns := by
        rw [List.mapM_map]
        have := mapM_ok (Export.Read.asStr ∘ reorder ∘ Json.str) id fns (fun x _ => rfl)
        rwa [List.map_id] at this
      simp only [Export.Read.shape]; rt_simp; rw [hn, hl]; rfl
termination_by s => s
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) |
  (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega) | (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ fs›; omega)

theorem range_rt (r : Range) : Export.Read.range (reorder (Export.range r)) = .ok r := by
  cases r <;> simp only [Export.range, Export.Read.range] <;> rt_simp

theorem exprs_rt (xs : List Expr) (n : Nat) (h : ∀ x ∈ xs, depth (reorder (Export.expr x)) < n) :
    (xs.map (reorder ∘ Export.expr)).mapM (Export.Read.expr n) = .ok (xs.map Expr.erase) := by
  rw [List.mapM_map]
  exact mapM_ok _ _ xs (fun x hx => expr_rt x n (h x hx))

theorem aligned_rt (v : Impact.Aligned Expr) (n : Nat) (h : depth (reorder (Export.aligned v)) < n + 1) :
    Export.Read.aligned n (reorder (Export.aligned v)) = .ok v.erase := by
  simp only [Export.aligned] at h ⊢
  have hd := depth_arr_field _ (by simp) "vals" _ rfl h
  simp only [Export.Read.aligned, Export.Read.atoms, Export.Read.exprs]; rt_simp
  rw [atoms_rt, exprs_rt _ n (fun x hx => hd _ (List.mem_map_of_mem hx))]
  rfl

theorem mapM_rt {α β : Type} (f : Json → Except String β) (g : α → Json) (k : α → β) (xs : List α)
    (hx : ∀ x ∈ xs, f (reorder (g x)) = .ok (k x)) : (xs.map (reorder ∘ g)).mapM f = .ok (xs.map k) := by
  rw [List.mapM_map]; exact mapM_ok _ _ xs hx

theorem stateLits_eq : ∀ ss : List (Impact.StateLit Expr), Export.stateLits ss = ss.map Export.stateLit
  | [] => by simp [Export.stateLits]
  | x :: xs => by simp [Export.stateLits, stateLits_eq xs]

theorem stateLit_eraseList : ∀ ss : List (Impact.StateLit Expr),
    Impact.StateLit.eraseList ss = ss.map Impact.StateLit.erase
  | [] => by simp [Impact.StateLit.eraseList]
  | x :: xs => by simp [Impact.StateLit.eraseList, stateLit_eraseList xs]

theorem stateLit_rt : ∀ (v : Impact.StateLit Expr) (n : Nat), depth (reorder (Export.stateLit v)) < n →
    Export.Read.stateLit n (reorder (Export.stateLit v)) = .ok v.erase
  | .null, n + 1, _ => by simp only [Export.stateLit, Export.Read.stateLit, Impact.StateLit.erase]; rt_simp
  | .emptyMap, n + 1, _ => by simp only [Export.stateLit, Export.Read.stateLit, Impact.StateLit.erase]; rt_simp
  | .emptyMerkleTree d, n + 1, _ => by
      simp only [Export.stateLit, Export.Read.stateLit, Impact.StateLit.erase]; rt_simp
  | .cell v, n + 1, h => by
      simp only [Export.stateLit, Export.tag_eq] at h ⊢
      have hv := aligned_rt v n (Nat.lt_succ_of_lt (depth_field_lt _ (by simp) "value" _ rfl h))
      simp only [Export.Read.stateLit, Impact.StateLit.erase]; rt_simp; rw [hv]; rfl
  | .array es, n + 1, h => by
      simp only [Export.stateLit, Export.tag_eq, stateLits_eq] at h ⊢
      have hd := depth_arr_field _ (by simp) "elems" _ rfl h
      have hl := mapM_rt (Export.Read.stateLit n) Export.stateLit Impact.StateLit.erase es
        (fun x hx => stateLit_rt x n (hd _ (List.mem_map_of_mem hx)))
      simp only [Export.Read.stateLit, Impact.StateLit.erase, stateLit_eraseList]; rt_simp; rw [hl]; rfl
termination_by v => v
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) |
  (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)

/-- A field of an object of depth at most `n` has depth below `n`. -/
theorem field_lt (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (k : String) (v : Json)
    (hl : l.lookup k = some v) {n : Nat} (h : depth (reorder (Json.mkObj l)) < n + 1) :
    depth (reorder v) < n := depth_field_lt l hd k v hl h

theorem alignedList_rt (path : List (Impact.Aligned Expr)) (n : Nat)
    (hd : ∀ x ∈ path.map Export.aligned, depth (reorder x) < n) :
    (path.map (reorder ∘ Export.aligned)).mapM (Export.Read.aligned n) = .ok (path.map Impact.Aligned.erase) :=
  mapM_rt _ _ _ path (fun x hx => aligned_rt x n (Nat.lt_succ_of_lt (hd _ (List.mem_map_of_mem hx))))

set_option maxHeartbeats 4000000 in
theorem op_rt (o : Impact.Op Expr) (n : Nat) (h : depth (reorder (Export.op o)) < n + 1) :
    Export.Read.op n (reorder (Export.op o)) = .ok o.erase := by
  cases o
  case popeq c al r =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have hd := depth_arr_field _ (by simp) "result" _ rfl h
    simp only [Export.Read.op, Export.Read.atoms, Export.Read.exprs, Impact.Op.erase]; rt_simp
    rw [atoms_rt, exprs_rt _ n (fun x hx => hd _ (List.mem_map_of_mem hx))]; rfl
  case addi i =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := expr_rt i n (field_lt _ (by simp) "immediate" _ rfl h)
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  case subi i =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := expr_rt i n (field_lt _ (by simp) "immediate" _ rfl h)
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  case push st v =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := aligned_rt v n (Nat.lt_succ_of_lt (field_lt _ (by simp) "value" _ rfl h))
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  case idx c p path =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := alignedList_rt path n (depth_arr_field _ (by simp) "path" _ rfl h)
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  case idxStack path =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := alignedList_rt path n (depth_arr_field _ (by simp) "path" _ rfl h)
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  case pushState st v =>
    simp only [Export.op, Export.tag_eq] at h ⊢
    have := stateLit_rt v n (field_lt _ (by simp) "value" _ rfl h)
    simp only [Export.Read.op, Impact.Op.erase]; rt_simp; rw [this]; rfl
  all_goals (simp only [Export.op, Export.Read.op, Impact.Op.erase]; rt_simp)

theorem reorder_mkObj_ne_null (l : List (String × Json)) : reorder (Json.mkObj l) ≠ .null := by
  rw [Json.mkObj, Zkir.Text.reorder_obj, Json.mkObj]; intro h; cases h

theorem stmt_rt (st : Stmt) (n : Nat) (h : depth (reorder (Export.stmt st)) < n + 1) :
    Export.Read.stmt n (reorder (Export.stmt st)) = .ok st.erase := by
  cases st
  case bind v hint e =>
    simp only [Export.stmt, Export.tag_eq] at h ⊢
    have := expr_rt e n (field_lt _ (by simp) "expr" _ rfl h)
    simp only [Export.Read.stmt, Stmt.erase]; rt_simp; rw [this]; rfl
  case assert c m =>
    simp only [Export.stmt, Export.tag_eq] at h ⊢
    have := expr_rt c n (field_lt _ (by simp) "cond" _ rfl h)
    simp only [Export.Read.stmt, Stmt.erase]; rt_simp; rw [this]; rfl
  case constrain e r =>
    simp only [Export.stmt, Export.tag_eq] at h ⊢
    have := expr_rt e n (field_lt _ (by simp) "expr" _ rfl h)
    simp only [Export.Read.stmt, Stmt.erase]; rt_simp; rw [this, range_rt]; rfl
  case witness g name args outs sh =>
    simp only [Export.stmt, Export.tag_eq] at h ⊢
    have hg := expr_rt g n (field_lt _ (by simp) "guard" _ rfl h)
    have hs := shape_rt sh n (field_lt _ (by simp) "shape" _ rfl h)
    have ha := exprs_rt args n (fun x hx => depth_arr_field _ (by simp) "args" _ rfl h _ (List.mem_map_of_mem hx))
    simp only [Export.Read.stmt, Export.Read.exprs, Stmt.erase]; rt_simp
    rw [hg, ha, hs]
    simp only [ok_bind, pure_ok]
    rw [mapM_rt Export.Read.witnessOut _ id outs ?_, List.map_id]
    · rfl
    · intro o _
      obtain ⟨v, r⟩ := o
      cases r with
      | none => simp only [Function.comp, id, Export.Read.witnessOut]; rt_simp
      | some r =>
          have hr := range_rt r
          have hn : reorder (Export.range r) ≠ .null := by
            cases r <;> simp only [Export.range, Export.tag_eq] <;> exact reorder_mkObj_ne_null _
          simp only [id, Export.Read.witnessOut]; rt_simp
          split
          · rename_i h; exact absurd h hn
          · rw [hr]; rfl
  case ledger g reads ops =>
    simp only [Export.stmt, Export.tag_eq] at h ⊢
    have hg := expr_rt g n (field_lt _ (by simp) "guard" _ rfl h)
    have hr := mapM_rt Export.Read.asNum (fun (v : Nat) => (v : Json)) id reads (fun v _ => rfl)
    have ho := mapM_rt (Export.Read.op n) Export.op Impact.Op.erase ops
      (fun o ho => op_rt o n (Nat.lt_succ_of_lt (depth_arr_field _ (by simp) "ops" _ rfl h _ (List.mem_map_of_mem ho))))
    rw [List.map_id] at hr
    simp only [Export.Read.stmt, Stmt.erase]; rt_simp
    rw [hg, hr, ho]; rfl

theorem args_rt (args : List (String × Shape)) (n : Nat) (G : String × Shape → Json)
    (hG : ∀ a, G a = Json.mkObj [("name", Json.str a.1), ("shape", Export.shape a.2)])
    (hd : ∀ x ∈ args.map G, depth (reorder x) < n) :
    (args.map (reorder ∘ G)).mapM (Export.Read.arg n) = .ok args := by
  rw [mapM_rt _ G id args, List.map_id]
  intro a ha
  have hx := hd _ (List.mem_map_of_mem ha)
  rw [hG] at hx ⊢
  have := shape_rt a.2 n (Nat.lt_trans (depth_field _ (by simp) "shape" _ rfl) hx)
  simp only [Export.Read.arg]; rt_simp; rw [this]; rfl

set_option maxHeartbeats 1000000 in
theorem circuit_rt (c : Circuit) (n : Nat) (h : depth (reorder (Export.circuit c)) < n + 1) :
    Export.Read.circuit n (reorder (Export.circuit c)) = .ok c.exported := by
  simp only [Export.circuit] at h ⊢
  have hargs := args_rt c.args n _ (fun a => rfl) (depth_arr_field _ (by simp) "args" _ rfl h)
  have hres := shape_rt c.result n (field_lt _ (by simp) "result" _ rfl h)
  have hout := exprs_rt c.outputs n
    (fun x hx => depth_arr_field _ (by simp) "outputs" _ rfl h _ (List.mem_map_of_mem hx))
  have hin := mapM_rt Export.Read.input (fun (i : Input) => (i.var : Json))
    (fun i => ({ name := "", var := i.var, range := none } : Input)) c.inputs (fun _ _ => rfl)
  have hbd : depth (reorder (.arr (c.body.map Export.stmt))) < n := field_lt _ (by simp) "body" _ rfl h
  rw [Zkir.Text.reorder_arr] at hbd
  have hbody := mapM_rt (Export.Read.stmt n) Export.stmt Stmt.erase c.body.toList (fun st hs => stmt_rt st n (by
    have := Zkir.Text.depth_lt_arr _ (reorder (Export.stmt st))
      (by rw [Array.toList_map, Array.toList_map]; exact List.mem_map_of_mem (List.mem_map_of_mem hs))
    omega))
  simp only [Export.Read.circuit, Export.Read.exprs]; rt_simp
  simp only [Zkir.Text.reorder_arr, Array.toList_map, List.map_map, Export.Read.arr, Export.Read.field] at *
  rt_simp
  rw [hargs, hin, hbody, hres, hout]
  simp only [Circuit.exported, ok_bind, pure_ok, Except.ok.injEq]
  congr 1
  apply Array.ext'
  simp

theorem ledgerKind_rt : ∀ (k : LedgerKind) (n : Nat), depth (reorder (Export.ledgerKind k)) < n →
    Export.Read.ledgerKind n (reorder (Export.ledgerKind k)) = .ok k
  | .counter, n + 1, _ => by simp only [Export.ledgerKind, Export.Read.ledgerKind]; rt_simp
  | .cell sh, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have := shape_rt sh n (field_lt _ (by simp) "shape" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [this]; rfl
  | .map a b, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have ha := shape_rt a n (field_lt _ (by simp) "key" _ rfl h)
      have hb := shape_rt b n (field_lt _ (by simp) "value" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [ha, hb]; rfl
  | .mapOf a b, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have ha := shape_rt a n (field_lt _ (by simp) "key" _ rfl h)
      have hb := ledgerKind_rt b n (field_lt _ (by simp) "value" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [ha, hb]; rfl
  | .set e, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have := shape_rt e n (field_lt _ (by simp) "elem" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [this]; rfl
  | .list e, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have := shape_rt e n (field_lt _ (by simp) "elem" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [this]; rfl
  | .merkleTree d e, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have := shape_rt e n (field_lt _ (by simp) "elem" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [this]; rfl
  | .historicMerkleTree d e, n + 1, h => by
      simp only [Export.ledgerKind, Export.tag_eq] at h ⊢
      have := shape_rt e n (field_lt _ (by simp) "elem" _ rfl h)
      simp only [Export.Read.ledgerKind]; rt_simp; rw [this]; rfl

theorem ledgerField_rt (f : LedgerField) (n : Nat) (h : depth (reorder (Export.ledgerField f)) < n + 1) :
    Export.Read.ledgerField n (reorder (Export.ledgerField f)) = .ok f := by
  simp only [Export.ledgerField] at h ⊢
  have := ledgerKind_rt f.kind n (field_lt _ (by simp) "type" _ rfl h)
  simp only [Export.Read.ledgerField]; rt_simp; rw [this]; rfl

theorem interfaceCircuit_rt (k : InterfaceCircuit) (n : Nat)
    (h : depth (reorder (Export.interfaceCircuit k)) < n + 1) :
    Export.Read.interfaceCircuit n (reorder (Export.interfaceCircuit k)) = .ok k := by
  simp only [Export.interfaceCircuit] at h ⊢
  have hargs := args_rt k.args n _ (fun a => rfl) (depth_arr_field _ (by simp) "args" _ rfl h)
  have hres := shape_rt k.result n (field_lt _ (by simp) "result" _ rfl h)
  simp only [Export.Read.interfaceCircuit]; rt_simp; rw [hargs, hres]; rfl

theorem interface_rt (i : Interface) (n : Nat) (h : depth (reorder (Export.«interface» i)) < n + 1) :
    Export.Read.«interface» n (reorder (Export.«interface» i)) = .ok i := by
  simp only [Export.«interface»] at h ⊢
  have hd := depth_arr_field _ (by simp) "circuits" _ rfl h
  have := mapM_rt (Export.Read.interfaceCircuit n) Export.interfaceCircuit id i.circuits
    (fun k hk => interfaceCircuit_rt k n (Nat.lt_succ_of_lt (hd _ (List.mem_map_of_mem hk))))
  rw [List.map_id] at this
  simp only [Export.Read.«interface»]; rt_simp; rw [this]; rfl

theorem constructor_some (k : Circuit) (n : Nat) (h : depth (reorder (Export.circuit k)) < n + 1) :
    Export.Read.constructor n (reorder (Export.circuit k)) = .ok (some k.exported) := by
  have hn : reorder (Export.circuit k) ≠ .null := by
    simp only [Export.circuit]; exact reorder_mkObj_ne_null _
  unfold Export.Read.constructor
  split
  · rename_i h'; exact absurd h' hn
  · rw [circuit_rt k n h]; rfl

theorem constructor_none (n : Nat) : Export.Read.constructor n (reorder .null) = .ok none := rfl

set_option maxHeartbeats 2000000 in
theorem contract_rt (c : Contract) (n : Nat) (h : depth (reorder (Export.contract c)) < n + 1) :
    Export.Read.contract n (reorder (Export.contract c)) = .ok c.exported := by
  obtain ⟨name, ledger, circuits, constructor, interfaces⟩ := c
  have hl := fun (h : ∀ x ∈ ledger.map Export.ledgerField, depth (reorder x) < n) =>
    mapM_rt (Export.Read.ledgerField n) Export.ledgerField id ledger (fun f hf =>
      ledgerField_rt f n (Nat.lt_succ_of_lt (h _ (List.mem_map_of_mem hf))))
  have hc := fun (h : ∀ x ∈ circuits.map Export.circuit, depth (reorder x) < n) =>
    mapM_rt (Export.Read.circuit n) Export.circuit Circuit.exported circuits (fun k hk =>
      circuit_rt k n (Nat.lt_succ_of_lt (h _ (List.mem_map_of_mem hk))))
  have hi := fun (h : ∀ x ∈ interfaces.map Export.«interface», depth (reorder x) < n) =>
    mapM_rt (Export.Read.«interface» n) Export.«interface» id interfaces (fun k hk =>
      interface_rt k n (Nat.lt_succ_of_lt (h _ (List.mem_map_of_mem hk))))
  simp only [List.map_id] at hl hi
  cases constructor <;> cases interfaces <;>
    simp only [Export.contract, List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, List.cons_append, List.nil_append] at h ⊢
  all_goals
    have hl' := hl (depth_arr_field _ (by simp) "ledger" _ rfl h)
    have hc' := hc (depth_arr_field _ (by simp) "circuits" _ rfl h)
    simp only [Export.Read.contract, Export.Read.interfaces]; rt_simp
    simp (disch := simp) only [Zkir.Text.getObjVal?_reorder_mkObj, List.lookup, String.reduceBEq,
      Bool.false_eq_true, ↓reduceIte, reorder_arr_list, List.toList_toArray, List.map_map]
    rw [hl', hc']
  · rfl
  · rw [hi (depth_arr_field _ (by simp) "interfaces" _ rfl h)]; rfl
  · rw [constructor_some _ n (Nat.lt_succ_of_lt (field_lt _ (by simp) "constructor" _ rfl h))]; rfl
  · rw [hi (depth_arr_field _ (by simp) "interfaces" _ rfl h),
      constructor_some _ n (Nat.lt_succ_of_lt (field_lt _ (by simp) "constructor" _ rfl h))]; rfl

end ExportRT
open ExportRT

/-- **`contract.json` reads back** (at the level of the JSON value that parsing
    its text gives): `Export.ofJson` returns the contract, with what the file
    does not carry erased. -/
theorem Export.ofJson_reorder (c : Contract) : Export.ofJson (reorder (Export.contract c)) = .ok c.exported :=
  contract_rt c _ (by omega)


/-! ## The written value is in the fragment -/

namespace ExportFrag

theorem frag_mkObj_eq (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) :
    frag (Json.mkObj l) = l.all (fun p => frag p.2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hmem := Zkir.Text.mem_toListModel_ofList hd
    unfold Json.mkObj at h
    generalize ht : Std.TreeMap.Raw.ofList l compare = m at h hmem
    obtain ⟨⟨t⟩⟩ := m
    simp only [frag, Zkir.Text.fragT_eq, Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.all_eq_true]
    intro p hp
    exact h.2 ⟨p.1, p.2⟩ ((hmem p.1 p.2).mpr hp)
  · intro h
    exact Zkir.Text.frag_mkObj l hd (fun p hp => (List.all_eq_true.mp h) p hp)

macro "frag_simp" : tactic =>
  `(tactic| simp (disch := simp) only [frag_mkObj_eq, Zkir.Text.frag_arr, Zkir.Text.frag_str, Zkir.Text.frag_bool,
      Zkir.Text.frag_null, Zkir.Text.frag_nat, Export.tag_eq, Export.int_eq, Export.nat_eq, List.all_cons,
      List.all_nil, List.all_map, List.toList_toArray, Bool.and_true, Bool.true_and, Function.comp,
      List.all_eq_true, Array.toList_map])

theorem frag_atom (a : Zkir.AlignAtom) : frag (Export.atom a) = true := by
  cases a <;> simp only [Export.atom] <;> frag_simp

theorem frag_expr : ∀ e : Expr, frag (Export.expr e) = true
  | .disclose e => by simp only [Export.expr]; exact frag_expr e
  | .var _ | .const _ | .invalid _ => by simp only [Export.expr]; frag_simp
  | .add a b | .mul a b | .eq a b | .lt _ a b => by
      simp only [Export.expr]; frag_simp; simp [frag_expr a, frag_expr b]
  | .neg a | .divmod _ _ a => by simp only [Export.expr]; frag_simp; exact frag_expr a
  | .select c a b => by simp only [Export.expr]; frag_simp; simp [frag_expr c, frag_expr a, frag_expr b]
  | .hash xs => by
      simp only [Export.expr, ExportRT.exprs_eq]; frag_simp
      intro x hx; exact frag_expr x
  | .phash _ al xs => by
      simp only [Export.expr, ExportRT.exprs_eq]; frag_simp
      simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
      exact ⟨fun a _ => frag_atom a, fun x _ => frag_expr x⟩
termination_by e => e
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) |
  (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

theorem frag_ty (t : Ty) : frag (Export.ty t) = true := by
  cases t <;> simp only [Export.ty] <;> frag_simp

theorem frag_shape : ∀ s : Shape, frag (Export.shape s) = true
  | .prim t => by simp only [Export.shape]; exact frag_ty t
  | .vector _ e => by simp only [Export.shape]; frag_simp; try simp [frag_shape e]
  | .tuple es => by
      simp only [Export.shape, ExportRT.shapes_eq]; frag_simp
      try simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
      intro x _; exact frag_shape x
  | .struct _ _ fs => by
      simp only [Export.shape, ExportRT.shapes_eq]; frag_simp
      simp only [Bool.and_eq_true, List.all_eq_true, Function.comp, Zkir.Text.frag_str, implies_true, true_and]
      intro x _; exact frag_shape x
termination_by s => s
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) |
  (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega) | (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ fs›; omega)

theorem frag_range (r : Range) : frag (Export.range r) = true := by
  cases r <;> simp only [Export.range] <;> frag_simp

macro "frag_close" : tactic =>
  `(tactic| (try simp only [Bool.and_eq_true, List.all_eq_true, Function.comp, Zkir.Text.frag_str,
      Zkir.Text.frag_bool, Zkir.Text.frag_nat, Zkir.Text.frag_null, implies_true, true_and, and_true]) <;>
    (try simp [frag_expr, frag_atom, frag_shape, frag_range, frag_ty]))

theorem frag_aligned (v : Impact.Aligned Expr) : frag (Export.aligned v) = true := by
  simp only [Export.aligned]; frag_simp; frag_close

theorem frag_stateLit : ∀ v : Impact.StateLit Expr, frag (Export.stateLit v) = true
  | .null | .emptyMap | .emptyMerkleTree _ => by simp only [Export.stateLit]; frag_simp
  | .cell v => by simp only [Export.stateLit]; frag_simp; try simp [frag_aligned v]
  | .array es => by
      simp only [Export.stateLit, ExportRT.stateLits_eq]; frag_simp
      try simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
      intro x _; exact frag_stateLit x
termination_by v => v
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega) |
  (simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)

theorem frag_op (o : Impact.Op Expr) : frag (Export.op o) = true := by
  cases o <;> simp only [Export.op] <;> frag_simp <;> frag_close <;>
    simp [frag_aligned, frag_stateLit]

theorem frag_stmt (st : Stmt) : frag (Export.stmt st) = true := by
  cases st with
  | witness g name args outs sh =>
      simp only [Export.stmt]; frag_simp
      simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
      refine ⟨frag_expr g, fun x _ => frag_expr x, frag_shape sh, ?_⟩
      intro ⟨v, r⟩ _
      cases r <;> frag_simp <;> simp [frag_range]
  | _ => simp only [Export.stmt]; frag_simp; frag_close <;> simp [frag_op]

theorem frag_arg (a : String × Shape) :
    frag (Json.mkObj [("name", Json.str a.1), ("shape", Export.shape a.2)]) = true := by
  frag_simp; exact frag_shape a.2

theorem frag_circuit (c : Circuit) : frag (Export.circuit c) = true := by
  simp only [Export.circuit]; frag_simp
  simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
  refine ⟨fun a _ => frag_arg a, frag_shape _, fun _ _ => Zkir.Text.frag_nat _, fun st _ => frag_stmt st,
    fun x _ => frag_expr x⟩

theorem frag_ledgerKind : ∀ k : LedgerKind, frag (Export.ledgerKind k) = true
  | .mapOf a b => by simp only [Export.ledgerKind]; frag_simp; simp [frag_shape, frag_ledgerKind b]
  | .counter => by simp only [Export.ledgerKind]; frag_simp
  | .cell _ | .map _ _ | .set _ | .list _ | .merkleTree _ _ | .historicMerkleTree _ _ => by
      simp only [Export.ledgerKind]; frag_simp; frag_close

theorem frag_ledgerField (f : LedgerField) : frag (Export.ledgerField f) = true := by
  simp only [Export.ledgerField]; frag_simp; exact frag_ledgerKind f.kind

theorem frag_interfaceCircuit (k : InterfaceCircuit) : frag (Export.interfaceCircuit k) = true := by
  simp only [Export.interfaceCircuit]; frag_simp
  simp only [Bool.and_eq_true, List.all_eq_true, Function.comp]
  exact ⟨fun a _ => frag_arg a, frag_shape _⟩

theorem frag_interface (i : Interface) : frag (Export.«interface» i) = true := by
  simp only [Export.«interface»]; frag_simp
  intro k _; exact frag_interfaceCircuit k

theorem frag_contract (c : Contract) : frag (Export.contract c) = true := by
  obtain ⟨name, ledger, circuits, constructor, interfaces⟩ := c
  cases constructor <;> cases interfaces <;>
    simp only [Export.contract, List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, List.cons_append, List.nil_append] <;>
    frag_simp <;>
    simp [frag_ledgerField, frag_circuit, frag_interface]

end ExportFrag
open ExportFrag

/-- **The text of `contract.json` reads back as the contract** (with what the
    file does not carry erased): any text that lexes as the tokens of
    `Export.contract c` (the compact text, or any layout of the same tokens
    with JSON whitespace between them) is read by `Export.parse` as
    `c.exported`. -/
theorem Export.ofText (c : Contract) (text : String)
    (hl : Zkir.Text.lex text = .ok (Zkir.Text.toks (Export.contract c))) :
    Export.parse text = .ok c.exported := by
  simp only [Export.parse, Zkir.Text.parse_of_lex _ (frag_contract c) text hl, bind, Except.bind,
    Export.ofJson_reorder]

theorem Export.ofText_render (c : Contract) :
    Export.parse (Zkir.Text.render (Export.contract c)) = .ok c.exported :=
  Export.ofText c _ (Zkir.Text.lex_render _ (frag_contract c))

end Damp
