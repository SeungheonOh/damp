/-
The ZKIR file text reads back as the circuit.

`Damp/Proofs/ZkirJson.lean` proves `IrSource.ofJson src.toJson = .ok src`, at
the level of Lean's `Json` values. `Damp/Proofs/JsonText.lean` proves that the
reference parser reads any text that lexes as the tokens of a value `j` in the
fragment as `Text.reorder j` (the same value with every object rebuilt in text
order, as `Json.parse` builds it). This file joins the two:

    Text.lex text = .ok (Text.toks src.toJson) →
      (Text.parse text >>= IrSource.ofJson) = .ok src         (IrSource.ofText)

for every `src` whose immediates the loader accepts, so for everything
`Emit.circuit` returns (`IrSource.ofText_of_emitted`). The compact text
`Text.render src.toJson` satisfies the hypothesis (`Text.lex_render`); that
the `Json.pretty` text written to the `.zkir` file does is checked, for every
circuit of Examples and Bench at every level, by `test/jsontext.sh`.
-/
import Damp.Proofs.JsonText
import Damp.Proofs.ZkirJson

namespace Damp.Zkir
open Lean (Json JsonNumber)
open JsonRT
open Text (reorder frag)

namespace ZkirText

/-! ## The printed circuit is in the fragment -/

theorem frag_mkObj' (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup)
    (h : l.all (fun p => frag p.2) = true) : frag (Json.mkObj l) = true :=
  Text.frag_mkObj l hd (fun p hp => (List.all_eq_true.mp h) p hp)

theorem frag_operand (o : Operand) : frag o.toJson = true := by
  rw [Operand.toJson_eq]; rfl

theorem frag_atom (a : AlignAtom) : frag a.toJson = true := by
  cases a <;>
    (apply frag_mkObj' _ (by simp)
     simp only [List.all_cons, List.all_nil, Text.frag_str, Bool.true_and, Bool.and_true]
     apply frag_mkObj' _ (by simp)
     simp [Text.frag_str, Text.frag_nat])

local macro "frag_simp" : tactic =>
  `(tactic| simp [Instr.json, jobj, jops, jids, jguard, frag_operand, frag_atom, Text.frag_str,
      Text.frag_nat, Text.frag_null, Text.frag_arr, IrType.toJson_eq, List.all_eq_true])

theorem frag_instr (i : Instr) : frag i.toJson = true := by
  rw [Instr.toJson_eq_json]
  cases i
  all_goals (apply frag_mkObj' _ (by simp))
  all_goals (try (rename_i g; cases g))
  all_goals frag_simp

theorem frag_toJson (src : IrSource) : frag src.toJson = true := by
  unfold IrSource.toJson
  apply frag_mkObj' _ (by simp)
  have h1 : frag (Json.mkObj [("major", (3 : Json)), ("minor", (1 : Json))]) = true := by decide
  have h2 : frag (.arr (src.inputs.map fun (n, t) => Json.mkObj [("name", (n : Json)), ("type", t.toJson)]).toArray)
      = true := by
    rw [Text.frag_arr]
    simp only [List.toList_toArray, List.all_map, List.all_eq_true, Function.comp]
    intro x _
    exact frag_mkObj' _ (by simp) (by simp [Text.frag_str, IrType.toJson_eq])
  have h3 : frag (.arr (src.outputs.map IrType.toJson).toArray) = true := by
    rw [Text.frag_arr]
    simp [IrType.toJson_eq, Text.frag_str]
  have h4 : frag (.arr (src.instructions.map Instr.toJson)) = true := by
    rw [Text.frag_arr]
    simp [frag_instr]
  simp only [List.all_cons, List.all_nil, h1, h2, h3, h4, Text.frag_bool, Bool.and_true]

/-! ## The reader reads `reorder src.toJson` as `src` -/

theorem reorder_operand (o : Operand) : reorder o.toJson = o.toJson := by
  rw [Operand.toJson_eq]; rfl

theorem reorder_ops (l : List Operand) :
    reorder (.arr (l.map Operand.toJson).toArray) = .arr (l.map Operand.toJson).toArray := by
  rw [Text.reorder_arr]; simp [reorder_operand]

theorem reorder_ids (l : List Ident) :
    reorder (.arr (l.map fun i => Json.str i.toString).toArray) = .arr (l.map fun i => Json.str i.toString).toArray := by
  rw [Text.reorder_arr]; simp [Text.reorder_str]

theorem reorder_types (l : List IrType) :
    reorder (.arr (l.map IrType.toJson).toArray) = .arr (l.map IrType.toJson).toArray := by
  rw [Text.reorder_arr]; simp [IrType.toJson_eq, Text.reorder_str]

theorem reorder_atoms (l : List AlignAtom) :
    reorder (.arr (l.map AlignAtom.toJson).toArray) = .arr (l.map fun a => reorder a.toJson).toArray := by
  rw [Text.reorder_arr]; simp

theorem parseAtom_reorder (a : AlignAtom) : parseAtom (reorder a.toJson) = .ok a := by
  cases a <;>
    simp (disch := simp) [AlignAtom.toJson, parseAtom, getStr, getField, Text.getObjVal?_reorder_mkObj, List.lookup,
      getNat, getNat?_nat, Text.reorder_str, Text.reorder_num, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map]

theorem mapM_parseAtom_reorder : ∀ l : List AlignAtom,
    (l.map fun a => reorder a.toJson).mapM parseAtom = .ok l
  | [] => rfl
  | a :: l => by
      simp [List.mapM_cons, parseAtom_reorder, mapM_parseAtom_reorder l, bind, Except.bind, pure, Except.pure]

theorem guard_reorder (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (g : Option Operand)
    (hg : ∀ o ∈ g.toList, o.OK) (hl : l.lookup "guard" = some (jguard g)) :
    guard (reorder (Json.mkObj l)) = .ok g := by
  simp only [guard, Text.getObjVal?_reorder_mkObj l _ hd, hl]
  cases g with
  | none => rfl
  | some o =>
      simp only [jguard, reorder_operand, Operand.toJson_eq, Text.reorder_str]
      simp [parseOperandStr_str o (hg o (by simp)), Functor.map, Except.map]

/-- The rewrites that read a reordered printed instruction back. -/
local macro "rinstr_simp" : tactic =>
  `(tactic| simp (disch := simp_all) only [Instr.json, jobj, jops, jids, parseInstr, getStr, getField,
      Text.getObjVal?_reorder_mkObj, List.lookup, operand, operands, ident, idents, getArr, getNat, getNat?_nat,
      guard, jguard, IrType.toJson_eq, parseType_str, reorder_operand, reorder_ops, reorder_ids, reorder_atoms,
      Text.reorder_str, Text.reorder_num, Text.reorder_null, Operand.toJson_eq,
      parseOperandStr_str, mapM_parseOperand, mapM_parseIdent, parseIdent_toString, mapM_parseAtom_reorder,
      List.toList_toArray, ok_bind', pure_ok', ok_map', beq_self_eq_true, String.reduceBEq])

set_option maxHeartbeats 4000000 in
theorem parseInstr_reorder (i : Instr) (h : i.OK) : parseInstr (reorder i.toJson) = .ok i := by
  rw [Instr.toJson_eq_json]
  unfold Instr.OK at h
  cases i
  all_goals simp only [Instr.uses, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Option.toList] at h
  case publicInput t o g => cases g <;> (try simp only [List.not_mem_nil, List.mem_cons, or_false, forall_eq] at h) <;>
      rinstr_simp
  case privateInput t o g => cases g <;> (try simp only [List.not_mem_nil, List.mem_cons, or_false, forall_eq] at h) <;>
      rinstr_simp
  all_goals rinstr_simp

theorem mapM_parseInstr_reorder : ∀ l : List Instr, (∀ i ∈ l, i.OK) →
    (l.map fun i => reorder i.toJson).mapM parseInstr = .ok l
  | [], _ => rfl
  | i :: l, h => by
      rw [List.map_cons, List.mapM_cons, parseInstr_reorder i (h i (by simp)),
        mapM_parseInstr_reorder l (fun j hj => h j (by simp [hj]))]
      rfl

theorem mapM_parseInput_reorder : ∀ l : List (Ident × IrType),
    List.mapM (fun i => do
        let a ← ident i "name"
        let b ← getStr i "type"
        let c ← parseType b
        Except.ok (a, c))
      (l.map fun x => reorder (Json.mkObj [("name", Json.str x.fst.toString), ("type", x.snd.toJson)])) = .ok l
  | [] => rfl
  | (n, t) :: l => by
      rw [List.map_cons, List.mapM_cons, mapM_parseInput_reorder l]
      simp (disch := simp) only [ident, getStr, getField, Text.getObjVal?_reorder_mkObj, List.lookup,
        IrType.toJson_eq, Text.reorder_str, parseType_str, parseIdent_toString, ok_bind', pure_ok',
        beq_self_eq_true, String.reduceBEq]

theorem mapM_parseOutput_reorder : ∀ l : List IrType,
    ((l.map IrType.toJson).mapM fun t => do parseType (← asStr t)) = .ok l :=
  mapM_parseOutput

end ZkirText
open ZkirText

/-- Damp's reader reads `reorder src.toJson` — what parsing the text of
    `src.toJson` gives — as `src`. -/
theorem IrSource.ofJson_reorder_toJson (src : IrSource) (h : src.OK) :
    IrSource.ofJson (reorder src.toJson) = .ok src := by
  have hins : ((src.instructions.map Instr.toJson).map reorder).mapM parseInstr = .ok src.instructions := by
    rw [Array.mapM_eq_mapM_toList, Array.toList_map, Array.toList_map, List.map_map]
    rw [show (reorder ∘ Instr.toJson) = fun i => reorder i.toJson from rfl, mapM_parseInstr_reorder _ h]
    rfl
  have h3 : Json.getNat? (reorder (3 : Json)) = .ok 3 := rfl
  have hin := mapM_parseInput_reorder src.inputs
  simp (disch := simp) only [IrSource.ofJson, IrSource.toJson, getField, Text.getObjVal?_reorder_mkObj,
    List.lookup, getNat, getArr, h3, Text.reorder_bool, Text.reorder_arr,
    hins, ok_bind', pure_ok', beq_self_eq_true, String.reduceBEq, ↓reduceIte]
  have ht : ∀ (f : IrType → Json) (l : List IrType),
      (Array.map reorder (l.map f).toArray).toList = (l.map f).map reorder := by
    intro f l; simp
  rw [ht, show (List.map IrType.toJson src.outputs).map reorder = src.outputs.map IrType.toJson by
    simp [IrType.toJson_eq, Text.reorder_str], mapM_parseOutput]
  have hi : (Array.map reorder (List.map (fun x : Ident × IrType =>
        Json.mkObj [("name", Json.str x.fst.toString), ("type", x.snd.toJson)]) src.inputs).toArray).toList =
      List.map (fun x => reorder (Json.mkObj [("name", Json.str x.fst.toString), ("type", x.snd.toJson)]))
        src.inputs := by
    simp [Function.comp_def]
  rw [hi, hin]
  rfl

/-- **The text of a circuit reads back as the circuit.** Any text that lexes as
    the tokens of `src.toJson` (the compact text `Text.render src.toJson`, or
    any layout of the same tokens with JSON whitespace between them) parses,
    with the reference parser, to a value that Damp's reader reads as `src`,
    provided every immediate is a field element the loader accepts. -/
theorem IrSource.ofText (src : IrSource) (h : src.OK) (text : String)
    (hl : Text.lex text = .ok (Text.toks src.toJson)) :
    (Text.parse text >>= IrSource.ofJson) = .ok src := by
  rw [Text.parse_of_lex _ (frag_toJson src) text hl]
  exact IrSource.ofJson_reorder_toJson src h

/-- The compact text of a circuit lexes as its tokens, so it reads back as the circuit. -/
theorem IrSource.ofText_render (src : IrSource) (h : src.OK) :
    (Text.parse (Text.render src.toJson) >>= IrSource.ofJson) = .ok src :=
  IrSource.ofText src h _ (Text.lex_render _ (frag_toJson src))

/-- What the emitter returns: every immediate passed `checkProducer`. -/
theorem IrSource.ofText_of_emitted {c : IR.Circuit} {src : IrSource} (he : Emit.circuit c = .ok src)
    (text : String) (hl : Text.lex text = .ok (Text.toks src.toJson)) :
    (Text.parse text >>= IrSource.ofJson) = .ok src := by
  apply IrSource.ofText src _ text hl
  apply IrSource.ok_of_okB
  apply IrSource.okB_of_checkProducer
  unfold Emit.circuit at he
  split at he
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at he
  · cases hcore : Emit.circuitCore (Emit.pruned c) with
    | error m => simp [hcore, bind, Except.bind] at he
    | ok src' =>
        cases hchk : src'.checkProducer with
        | error m => simp [hcore, hchk, bind, Except.bind] at he
        | ok u =>
            simp [hcore, hchk, bind, Except.bind, pure, Except.pure] at he
            subst he; cases u; exact hchk

end Damp.Zkir
