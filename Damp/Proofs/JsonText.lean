/-
JSON text reads back: the reference parser inverts the reference printer.

`Damp/Zkir/JsonText.lean` defines, totally, the token sequence `Text.toks j` of a
JSON value in the order `Json.pretty` prints it, a compact printer
`Text.render`, a lexer `Text.lex` and a parser `Text.parse`. This file proves,
for every value in the fragment Damp writes (`Text.frag`: natural numbers,
distinct keys, any strings):

    Text.lex (Text.render j) = .ok (Text.toks j)                 (lex_render)
    Text.parseToks (Text.toks j) = .ok (Text.reorder j)           (parseToks_toks)
    Text.lex text = .ok (Text.toks j) → Text.parse text = .ok (Text.reorder j)
                                                                  (parse_of_lex)

`reorder j` is `j` with every object rebuilt by inserting its members in the
order the text lists them (which is what `Json.parse` does); it has the same
members (`getObjVal?_reorder_mkObj`). The hypothesis of `parse_of_lex` admits
every layout of the tokens with whitespace between them; that `Json.pretty`'s
output is such a layout, and that `Text.parse` agrees with `Json.parse`, is
what `test/jsontext.sh` checks (Lean core's printer and parser are `partial`).
-/
import Damp.Zkir.JsonText
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

namespace Damp.Zkir.Text
open Lean (Json JsonNumber)
open Std.DTreeMap.Internal (Impl)

/-! ## Induction on JSON values -/

section Induction
variable {P : Json → Prop} (hnull : P .null) (hbool : ∀ b, P (.bool b)) (hnum : ∀ n, P (.num n))
  (hstr : ∀ s, P (.str s)) (harr : ∀ l : List Json, (∀ j ∈ l, P j) → P (.arr ⟨l⟩))
  (hobj : ∀ t : Tree, (∀ p ∈ t.toListModel, P p.2) → P (.obj ⟨⟨t⟩⟩))
include hnull hbool hnum hstr harr hobj

set_option linter.unusedSectionVars false

mutual
theorem json_ind : ∀ j : Json, P j
  | .null => hnull
  | .bool b => hbool b
  | .num n => hnum n
  | .str s => hstr s
  | .arr ⟨l⟩ => harr l (json_indL l)
  | .obj ⟨⟨t⟩⟩ => hobj t (json_indT t)
termination_by structural j => j
theorem json_indL : ∀ l : List Json, ∀ j ∈ l, P j
  | [] => fun _ h => absurd h List.not_mem_nil
  | j :: l => fun x h =>
      (List.mem_cons.mp h).elim (fun e => by rw [e]; exact json_ind j) (fun h => json_indL l x h)
termination_by structural l => l
theorem json_indT : ∀ t : Tree, ∀ p ∈ t.toListModel, P p.2
  | .leaf => fun _ h => by simp at h
  | .inner _ k v l r => fun p h =>
      (List.mem_append.mp (by simpa only [Impl.toListModel_inner] using h)).elim (fun h => json_indT l p h)
        (fun h => (List.mem_cons.mp h).elim (fun e => by subst e; exact json_ind v) (fun h => json_indT r p h))
termination_by structural t => t
end
end Induction

/-! ## The mutual definitions, as maps over lists -/

theorem toksL_eq : ∀ l : List Json, toksL l = l.map toks
  | [] => by simp [toksL]
  | j :: l => by simp [toksL, toksL_eq l]

theorem toksT_eq : ∀ t : Tree, toksT t = t.toListModel.reverse.map fun p => (p.1, toks p.2)
  | .leaf => by simp [toksT]
  | .inner _ k v l r => by simp [toksT, toksT_eq l, toksT_eq r]

theorem reorderL_eq : ∀ l : List Json, reorderL l = l.map reorder
  | [] => by simp [reorderL]
  | j :: l => by simp [reorderL, reorderL_eq l]

theorem reorderT_eq : ∀ t : Tree, reorderT t = t.toListModel.reverse.map fun p => (p.1, reorder p.2)
  | .leaf => by simp [reorderT]
  | .inner _ k v l r => by simp [reorderT, reorderT_eq l, reorderT_eq r]

theorem fragL_eq : ∀ l : List Json, fragL l = l.all frag
  | [] => by simp [fragL]
  | j :: l => by simp [fragL, fragL_eq l]

theorem fragT_eq : ∀ t : Tree, fragT t = t.toListModel.all fun p => frag p.2
  | .leaf => by simp [fragT]
  | .inner _ k v l r => by simp [fragT, fragT_eq l, fragT_eq r, Bool.and_assoc]

theorem constToList_eq (t : Tree) : Impl.Const.toList t = t.toListModel.map fun e => (e.1, e.2) :=
  Impl.Const.toList_eq_toListModel_map

/-! ## Lexing -/

/-- `g` lexes back as itself, followed by anything that does not start with a digit. -/
def LexOK (g : List Tok) : Prop :=
  ∀ (rest : List Char) (out : List Tok), (∀ c ∈ rest.head?, c.isDigit = false) →
    lexGo .top (g.flatMap Tok.text ++ rest) out = lexGo .top rest (g.reverse ++ out)

/-- A token other than a number lexes back as itself, followed by anything. -/
theorem lex_closed (t : Tok) (ht : t ∈ [Tok.lbrace, .rbrace, .lbrack, .rbrack, .colon, .comma, .tru, .fls, .null])
    (rest : List Char) (out : List Tok) :
    lexGo .top (t.text ++ rest) out = lexGo .top rest (t :: out) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Tok.text, lexGo, isWs]

theorem lex_escChar (c : Char) (acc : List Char) (rest : List Char) (out : List Tok) :
    lexGo (.str acc) (escChar c ++ rest) out = lexGo (.str (c :: acc)) rest out := by
  unfold escChar
  by_cases h1 : c = '"'
  · subst h1; simp [lexGo]
  by_cases h2 : c = '\\'
  · subst h2; simp [lexGo]
  by_cases h3 : c = '\n'
  · subst h3; simp [lexGo]
  by_cases h4 : c = '\x0d'
  · subst h4; simp [lexGo]
  by_cases h5 : 0x20 ≤ c.val
  · simp only [h1, h2, h3, h4, h5, ite_false, ite_true, List.cons_append, List.nil_append]
    rw [lexGo]
    have : ¬ c.val < 0x20 := fun h => absurd h (UInt32.not_lt.mpr h5)
    simp [h1, h2, this]
  · simp only [h1, h2, h3, h4, h5, ite_false]
    have hn : c.toNat < 32 := by
      rw [UInt32.le_iff_toNat_le] at h5
      simp only [Char.toNat]
      exact Nat.lt_of_not_le (by simpa using h5)
    have hd : ∀ d, d < 16 → hexDigit (Nat.digitChar d) = some d := by decide
    have e1 : c.toNat / 4096 = 0 := by omega
    have e2 : c.toNat % 4096 / 256 = 0 := by omega
    have e3 : c.toNat % 256 / 16 < 16 := by omega
    have e4 : c.toNat % 16 < 16 := by omega
    have hv : 16 * (16 * (16 * (16 * 0 + 0) + 0) + c.toNat % 256 / 16) + c.toNat % 16 = c.toNat := by omega
    have hu : uniChar c.toNat = .ok c := by
      unfold uniChar
      rw [if_neg (by omega)]
      simp [Char.ofNat_toNat]
    rw [e1, e2]
    simp only [List.cons_append, List.nil_append]
    rw [lexGo]; simp only [show ('\\' : Char) = '"' ↔ False by decide, ite_false, ite_true]
    rw [lexGo]; simp only [show ('u' : Char) = '"' ↔ False by decide, show ('u' : Char) = '\\' ↔ False by decide,
      show ('u' : Char) = '/' ↔ False by decide, show ('u' : Char) = 'b' ↔ False by decide,
      show ('u' : Char) = 'f' ↔ False by decide, show ('u' : Char) = 'n' ↔ False by decide,
      show ('u' : Char) = 'r' ↔ False by decide, show ('u' : Char) = 't' ↔ False by decide, ite_false, ite_true]
    rw [lexGo, hd 0 (by omega)]; simp only [show ¬ (4 ≤ 1) by decide, ite_false, show 4 - 1 = 3 by rfl]
    rw [lexGo, hd 0 (by omega)]; simp only [show ¬ (3 ≤ 1) by decide, ite_false, show 3 - 1 = 2 by rfl]
    rw [lexGo, hd _ e3]; simp only [show ¬ (2 ≤ 1) by decide, ite_false, show 2 - 1 = 1 by rfl]
    rw [lexGo, hd _ e4]; simp only [show (1 ≤ 1) by decide, ite_true]
    rw [hv, hu]

theorem lex_strBody (cs acc rest : List Char) (out : List Tok) :
    lexGo (.str acc) (cs.flatMap escChar ++ rest) out = lexGo (.str (cs.reverse ++ acc)) rest out := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
      rw [List.flatMap_cons, List.append_assoc, lex_escChar, ih]
      simp

theorem lex_strTok (s : String) (rest : List Char) (out : List Tok) :
    lexGo .top ((Tok.str s).text ++ rest) out = lexGo .top rest (.str s :: out) := by
  simp only [Tok.text, List.cons_append, List.append_assoc, List.singleton_append]
  rw [lexGo]
  simp only [isWs, show ('"' : Char) = ' ' ↔ False by decide, show ('"' : Char) = '\t' ↔ False by decide,
    show ('"' : Char) = '\n' ↔ False by decide, show ('"' : Char) = '\x0d' ↔ False by decide,
    decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    show ('"' : Char) = '{' ↔ False by decide, show ('"' : Char) = '}' ↔ False by decide,
    show ('"' : Char) = '[' ↔ False by decide, show ('"' : Char) = ']' ↔ False by decide,
    show ('"' : Char) = ':' ↔ False by decide, show ('"' : Char) = ',' ↔ False by decide, ite_true]
  rw [lex_strBody]
  rw [lexGo]
  simp

theorem lex_str (s : String) : LexOK [.str s] := by
  intro rest out _
  simpa using lex_strTok s rest out

theorem lex_digits (ds rest : List Char) (out : List Tok) :
    ∀ cs : List Char, (∀ c ∈ cs, c.isDigit = true) →
      lexGo (.num ds) (cs ++ rest) out = lexGo (.num (cs.reverse ++ ds)) rest out := by
  intro cs
  induction cs generalizing ds with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro h
      rw [List.cons_append, lexGo, if_pos (h c (by simp)), ih _ (fun x hx => h x (by simp [hx]))]
      simp

theorem toDigits_head_ne_zero : ∀ m : Nat, m ≠ 0 → (Nat.toDigits 10 m).head? ≠ some '0' := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i hlt
      have : ∀ m, m < 10 → m ≠ 0 → Nat.digitChar m ≠ '0' := by decide
      simpa using this m hlt hm
    · rename_i hge
      have hne := Nat.toDigits_ne_nil (b := 10) (n := m / 10)
      have := ih (m / 10) (by omega) (by omega)
      cases h : Nat.toDigits 10 (m / 10) with
      | nil => exact absurd h hne
      | cons a as => rw [h] at this; simpa using this

theorem finishNum_toDigits (m : Nat) : finishNum (Nat.toDigits 10 m) = .ok (.num m) := by
  unfold finishNum
  split
  · rename_i x xs h
    have hm : m ≠ 0 := by intro h0; subst h0; simp [Nat.toDigits_zero] at h
    exact absurd (by rw [h]; rfl) (toDigits_head_ne_zero m hm)
  · simp

theorem lex_num (m : Nat) : LexOK [.num m] := by
  intro rest out hrest
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.text, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]
  have hdig : ∀ c ∈ Nat.toDigits 10 m, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  cases h : Nat.toDigits 10 m with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons c cs =>
      rw [h] at hdig
      have hc := hdig c (by simp)
      rw [List.cons_append, lexGo]
      have hns : ∀ x : Char, x.isDigit = true → ¬ (isWs x = true) ∧ x ≠ '{' ∧ x ≠ '}' ∧ x ≠ '[' ∧ x ≠ ']' ∧
          x ≠ ':' ∧ x ≠ ',' ∧ x ≠ '"' := by
        intro x hx
        simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hx
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
          first
          | (subst he; simp at hx)
          | (simp only [isWs, Bool.or_eq_true, decide_eq_true_eq] at he
             rcases he with ((he | he) | he) | he <;> subst he <;> simp at hx)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hns c hc
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, hc, ite_false, ite_true, Bool.false_eq_true]
      rw [lex_digits _ _ _ cs (fun x hx => hdig x (by simp [hx]))]
      have hfin : finishNum (cs.reverse ++ [c]).reverse = .ok (.num m) := by
        rw [List.reverse_append, List.reverse_reverse]; simp only [List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append]
        rw [← h]; exact finishNum_toDigits m
      cases rest with
      | nil => rw [lexGo.eq_def]; simp only [hfin]
      | cons x xs =>
          have hx : x.isDigit = false := hrest x (by simp)
          rw [lexGo.eq_def]; simp only [hx, hfin]; rfl

theorem lex_closed_ok (t : Tok) (ht : t ∈ [Tok.lbrace, .rbrace, .lbrack, .rbrack, .colon, .comma, .tru, .fls, .null]) :
    LexOK [t] := by
  intro rest out _
  simpa using lex_closed t ht rest out

theorem LexOK.cons_closed {t : Tok} {g : List Tok}
    (ht : t ∈ [Tok.lbrace, .rbrace, .lbrack, .rbrack, .colon, .comma, .tru, .fls, .null]) (hg : LexOK g) :
    LexOK (t :: g) := by
  intro rest out hrest
  rw [List.flatMap_cons, List.append_assoc, lex_closed t ht, hg rest _ hrest]
  simp

theorem LexOK.member {k : String} {g : List Tok} (hg : LexOK g) : LexOK (member k g) := by
  intro rest out hrest
  unfold Text.member
  rw [List.flatMap_cons, List.append_assoc, lex_strTok k,
    List.flatMap_cons, List.append_assoc, lex_closed .colon (by simp), hg rest _ hrest]
  simp

/-- Groups separated by commas, then a closing character. -/
theorem lex_sepBy (c : Char) (hc : c.isDigit = false) :
    ∀ G : List (List Tok), (∀ g ∈ G, LexOK g) → ∀ (rest : List Char) (out : List Tok),
      lexGo .top ((sepBy G).flatMap Tok.text ++ c :: rest) out =
        lexGo .top (c :: rest) ((sepBy G).reverse ++ out)
  | [], _, rest, out => rfl
  | [g], hG, rest, out => by
      exact hG g (by simp) (c :: rest) out (by simpa using hc)
  | g :: g' :: gs, hG, rest, out => by
      have ih := lex_sepBy c hc (g' :: gs) (fun x hx => hG x (List.mem_cons_of_mem _ hx)) rest
      have e : sepBy (g :: g' :: gs) = g ++ .comma :: sepBy (g' :: gs) := rfl
      rw [e]
      generalize sepBy (g' :: gs) = S at ih
      rw [List.flatMap_append, List.flatMap_cons, List.append_assoc, List.append_assoc,
        hG g (by simp) _ out (by simp [Tok.text]), lex_closed .comma (by simp), ih]
      simp

theorem lex_bracketed (op cl : Tok) (c : Char) (hc : c.isDigit = false) (hcl : cl.text = [c])
    (hop : op ∈ [Tok.lbrace, .rbrace, .lbrack, .rbrack, .colon, .comma, .tru, .fls, .null])
    (hcl' : cl ∈ [Tok.lbrace, .rbrace, .lbrack, .rbrack, .colon, .comma, .tru, .fls, .null])
    (G : List (List Tok)) (hG : ∀ g ∈ G, LexOK g) : LexOK (op :: (sepBy G ++ [cl])) := by
  intro rest out _
  rw [List.flatMap_cons, List.append_assoc, lex_closed op hop, List.flatMap_append, List.append_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, hcl, List.singleton_append,
    lex_sepBy c hc G hG, ← List.singleton_append, ← hcl, lex_closed cl hcl']
  simp

/-- **Every value in the fragment lexes back as its tokens**, followed by anything
    that does not start with a digit. -/
theorem lexOK_toks : ∀ j : Json, frag j = true → LexOK (toks j) := by
  refine json_ind ?_ ?_ ?_ ?_ ?_ ?_
  · intro _; exact lex_closed_ok .null (by simp)
  · intro b _; cases b
    · exact lex_closed_ok .fls (by simp)
    · exact lex_closed_ok .tru (by simp)
  · intro n _; exact lex_num _
  · intro s _; exact lex_str s
  · intro l ih hf
    simp only [frag, fragL_eq, List.all_eq_true] at hf
    simp only [toks, toksL_eq]
    exact lex_bracketed .lbrack .rbrack ']' (by decide) rfl (by simp) (by simp) _
      (fun g hg => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
        exact ih j hj (hf j hj))
  · intro t ih hf
    simp only [frag, fragT_eq, Bool.and_eq_true, List.all_eq_true] at hf
    simp only [toks, toksT_eq, List.map_map]
    exact lex_bracketed .lbrace .rbrace '}' (by decide) rfl (by simp) (by simp) _
      (fun g hg => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
        have hp' := List.mem_reverse.mp hp
        exact (ih p hp' (hf.2 p hp')).member)

/-- **The compact text of a value lexes as its tokens.** -/
theorem lex_render (j : Json) (h : frag j = true) : lex (render j) = .ok (toks j) := by
  unfold lex render
  rw [String.toList_ofList, ← List.append_nil ((toks j).flatMap Tok.text), lexOK_toks j h [] [] (by simp)]
  simp [lexGo]

/-! ## Parsing tokens -/

/-- `g` parses, with any fuel at least its length, as `v`, leaving what follows. -/
def ParseOK (g : List Tok) (v : Json) : Prop :=
  ∀ n, g.length ≤ n → ∀ rest, pVal n (g ++ rest) = .ok (v, rest)

theorem toks_head (j : Json) : ∃ t ts, toks j = t :: ts ∧ t ≠ .rbrack ∧ t ≠ .rbrace ∧ t ≠ .comma := by
  match j with
  | .null => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | .bool true => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | .bool false => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | .num _ => exact ⟨_, _, rfl, by simp, by simp, by simp⟩
  | .str _ => exact ⟨_, _, rfl, by simp, by simp, by simp⟩
  | .arr ⟨_⟩ => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | .obj ⟨⟨_⟩⟩ => exact ⟨_, _, rfl, by decide, by decide, by decide⟩

theorem pVal_lbrack {t : Tok} (ht : t ≠ .rbrack) (n : Nat) (ts : List Tok) :
    pVal (n + 1) (.lbrack :: t :: ts) =
      match pElems n (t :: ts) with
      | .ok (vs, ts) => .ok (.arr ⟨vs⟩, ts)
      | .error e => .error e := by
  cases t <;> first | exact absurd rfl ht | rfl

theorem parseOK_leaf (t : Tok) (v : Json) (h : ∀ n rest, pVal (n + 1) (t :: rest) = .ok (v, rest)) :
    ParseOK [t] v := by
  intro n hn rest
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
  exact h m rest

theorem pElems_ok : ∀ l : List Json, l ≠ [] → (∀ j ∈ l, ParseOK (toks j) (reorder j)) →
    ∀ m, (sepBy (l.map toks)).length + 1 ≤ m → ∀ rest,
      pElems m (sepBy (l.map toks) ++ .rbrack :: rest) = .ok (l.map reorder, rest)
  | [], h, _, _, _, _ => absurd rfl h
  | [j], _, hl, m, hm, rest => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have := hl j (by simp) m (by simp [sepBy] at hm; omega) (.rbrack :: rest)
      simp only [List.map_cons, List.map_nil, sepBy] at this ⊢
      simp [pElems, this]
  | j :: j' :: l, _, hl, m, hm, rest => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have e : sepBy ((j :: j' :: l).map toks) = toks j ++ .comma :: sepBy ((j' :: l).map toks) := rfl
      rw [e] at hm ⊢
      simp only [List.length_append, List.length_cons] at hm
      have ih := pElems_ok (j' :: l) (by simp) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) m (by omega) rest
      have hj := hl j (by simp) m (by omega) (.comma :: (sepBy ((j' :: l).map toks) ++ .rbrack :: rest))
      rw [List.append_assoc, List.cons_append, pElems, hj]
      simp only []
      rw [ih]
      rfl

theorem pMembers_ok : ∀ ps : List (String × Json), ps ≠ [] → (∀ p ∈ ps, ParseOK (toks p.2) (reorder p.2)) →
    ∀ m, (sepBy (ps.map fun p => member p.1 (toks p.2))).length + 1 ≤ m → ∀ rest,
      pMembers m (sepBy (ps.map fun p => member p.1 (toks p.2)) ++ .rbrace :: rest) =
        .ok (ps.map fun p => (p.1, reorder p.2), rest)
  | [], h, _, _, _, _ => absurd rfl h
  | [(k, v)], _, hl, m, hm, rest => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have := hl (k, v) (by simp) m (by simp [sepBy, member] at hm ⊢; omega) (.rbrace :: rest)
      simp only [List.map_cons, List.map_nil, sepBy, member] at this ⊢
      simp [pMembers, this]
  | (k, v) :: p' :: l, _, hl, m, hm, rest => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have e : sepBy (((k, v) :: p' :: l).map fun p => member p.1 (toks p.2)) =
          member k (toks v) ++ .comma :: sepBy ((p' :: l).map fun p => member p.1 (toks p.2)) := rfl
      rw [e] at hm ⊢
      have hlen : (member k (toks v)).length = (toks v).length + 2 := by simp [member]
      simp only [List.length_append, List.length_cons, hlen] at hm
      generalize hS : sepBy ((p' :: l).map fun p => member p.1 (toks p.2)) = S at hm ⊢
      have ih := pMembers_ok (p' :: l) (by simp) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) m
        (by rw [hS]; omega) rest
      rw [hS] at ih
      have hj : pVal m (toks v ++ .comma :: (S ++ .rbrace :: rest)) = .ok (reorder v, .comma :: (S ++ .rbrace :: rest)) :=
        hl (k, v) (by simp) m (by show (toks v).length ≤ m; omega) _
      have e2 : (member k (toks v) ++ .comma :: S) ++ .rbrace :: rest =
          .str k :: .colon :: (toks v ++ .comma :: (S ++ .rbrace :: rest)) := by simp [member]
      rw [e2, pMembers, hj]
      simp only []
      rw [ih]
      rfl

/-- **Every value in the fragment parses back from its tokens**, as `reorder j`. -/
theorem parseOK_toks : ∀ j : Json, frag j = true → ParseOK (toks j) (reorder j) := by
  refine json_ind ?_ ?_ ?_ ?_ ?_ ?_
  · intro _; exact parseOK_leaf _ _ (fun n rest => by simp [pVal, reorder])
  · intro b _; cases b
    · exact parseOK_leaf _ _ (fun n rest => by simp [pVal, reorder, toks])
    · exact parseOK_leaf _ _ (fun n rest => by simp [pVal, reorder, toks])
  · intro x hf
    obtain ⟨m, e⟩ := x
    simp only [frag, decide_eq_true_eq] at hf
    obtain ⟨hm, he⟩ := hf
    subst he
    refine parseOK_leaf _ _ (fun n rest => ?_)
    simp only [pVal, reorder]
    congr
    simp [JsonNumber.fromNat, Int.toNat_of_nonneg hm]
  · intro s _; exact parseOK_leaf _ _ (fun n rest => by simp [pVal, reorder, toks])
  · intro l ih hf
    simp only [frag, fragL_eq, List.all_eq_true] at hf
    intro n hn rest
    simp only [toks, toksL_eq, List.length_cons, List.length_append, List.length_singleton] at hn ⊢
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [reorder, reorderL_eq]
    cases l with
    | nil => simp [sepBy, pVal]
    | cons j l =>
        obtain ⟨t, ts, hj, ht, -, -⟩ := toks_head j
        have hp := pElems_ok (j :: l) (by simp) (fun x hx => ih x hx (hf x hx)) n (by omega) rest
        have e : sepBy ((j :: l).map toks) = t :: (ts ++ (sepBy ((j :: l).map toks)).drop (toks j).length) := by
          cases l with
          | nil => simp [sepBy, hj]
          | cons j' l => simp [sepBy, hj]
        rw [e] at hp
        rw [List.cons_append, List.append_assoc, e, List.cons_append, List.singleton_append, pVal_lbrack ht]
        simp only [List.cons_append, List.append_assoc] at hp ⊢
        rw [hp]
  · intro t ih hf
    simp only [frag, fragT_eq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hnd, hf⟩ := hf
    intro n hn rest
    let ps : List (String × Json) := t.toListModel.reverse.map fun p => (p.1, p.2)
    have hG : (toksT t).map (fun p => member p.1 p.2) = ps.map fun p => member p.1 (toks p.2) := by
      simp [ps, toksT_eq]
    have hV : reorderT t = ps.map fun p => (p.1, reorder p.2) := by simp [ps, reorderT_eq]
    have hmem : ∀ p ∈ ps, ∃ q ∈ t.toListModel, p = (q.1, q.2) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ⟨q, List.mem_reverse.mp hq, rfl⟩
    have hkeys : (ps.map fun p => (p.1, reorder p.2)).map Prod.fst = ((Impl.Const.toList t).map Prod.fst).reverse := by
      simp [ps, constToList_eq, List.map_reverse]
    simp only [toks, hG, List.length_cons, List.length_append, List.length_singleton] at hn ⊢
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [reorder, hV]
    cases hps : ps with
    | nil => simp [sepBy, pVal]
    | cons p ps' =>
        rw [hps] at hkeys hn hmem
        have hp := pMembers_ok (p :: ps') (by simp)
          (fun x hx => by
            obtain ⟨q, hq, rfl⟩ := hmem x hx
            exact ih q hq (hf q hq)) n (by omega) rest
        obtain ⟨k, v⟩ := p
        have e : sepBy (((k, v) :: ps').map fun p => member p.1 (toks p.2)) =
            .str k :: (sepBy (((k, v) :: ps').map fun p => member p.1 (toks p.2))).tail := by
          cases ps' with
          | nil => simp [sepBy, member]
          | cons _ _ => simp [sepBy, member]
        rw [e] at hp
        rw [List.cons_append, List.append_assoc, e, List.cons_append, List.singleton_append]
        rw [List.cons_append] at hp
        have hnd' : ((((k, v) :: ps').map fun p => (p.1, reorder p.2)).map Prod.fst).Nodup := by
          rw [hkeys]; exact List.pairwise_reverse.mpr (hnd.imp fun h e => h e.symm)
        simp only [pVal, hp, hnd', ite_true]

/-- **The tokens of a value in the fragment parse as `reorder j`.** -/
theorem parseToks_toks (j : Json) (h : frag j = true) : parseToks (toks j) = .ok (reorder j) := by
  unfold parseToks
  have := parseOK_toks j h ((toks j).length + 1) (by omega) []
  rw [List.append_nil] at this
  rw [this]

/-- **Any text that lexes as the tokens of `j` parses as `reorder j`**: in
    particular the compact text (`parse_render`), and every layout of the same
    tokens with JSON whitespace between them. -/
theorem parse_of_lex (j : Json) (h : frag j = true) (text : String) (hl : lex text = .ok (toks j)) :
    parse text = .ok (reorder j) := by
  simp only [parse, hl, bind, Except.bind, parseToks_toks j h]

theorem parse_render (j : Json) (h : frag j = true) : parse (render j) = .ok (reorder j) :=
  parse_of_lex j h _ (lex_render j h)

/-! ## Objects built by `Json.mkObj`

What `reorder` does to an object built from a list of distinct keys: the same
members, so every field reads the same. -/

theorem lookup_mem {l : List (String × Json)} {k : String} {v : Json} (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons a l ih =>
      obtain ⟨a, b⟩ := a
      simp only [List.lookup] at h
      split at h
      · rename_i hk; simp at hk; subst hk; cases h; simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {l : List (String × Json)} (hd : (l.map Prod.fst).Nodup) {k : String} {v : Json}
    (h : (k, v) ∈ l) : l.lookup k = some v := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      obtain ⟨a, b⟩ := a
      rw [List.map_cons, List.nodup_cons] at hd
      simp only [List.lookup]
      rcases List.mem_cons.mp h with e | hm
      · cases e; simp
      · have hka : k ≠ a := by
          intro e
          exact hd.1 (List.mem_map.mpr ⟨(k, v), hm, e⟩)
        simp only [show (k == a) = false by simpa using hka]
        exact ih hd.2 hm

theorem lookup_none {l : List (String × Json)} {k : String} (h : l.lookup k = none) (v : Json) : (k, v) ∉ l := by
  intro hm
  induction l with
  | nil => simp at hm
  | cons a l ih =>
      obtain ⟨a, b⟩ := a
      simp only [List.lookup] at h
      split at h
      · cases h
      · rename_i hk
        rcases List.mem_cons.mp hm with e | hm
        · cases e; simp at hk
        · exact ih h hm

/-- A field of an object built by `Json.mkObj` from distinct keys is what the
    list gives for it. -/
theorem getObjVal?_mkObj (l : List (String × Json)) (k : String) (hd : (l.map Prod.fst).Nodup) :
    (Json.mkObj l).getObjVal? k =
      match l.lookup k with
      | some v => .ok v
      | none => .error s!"property not found: {k}" := by
  simp only [Json.mkObj, Json.getObjVal?]
  have hpw : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    have := List.pairwise_map.mp hd
    exact this.imp (fun h e => h (Std.LawfulEqCmp.eq_of_compare e))
  cases hl : l.lookup k with
  | some v =>
      rw [Std.TreeMap.Raw.get?_eq_getElem?,
        Std.TreeMap.Raw.getElem?_ofList_of_mem (Std.ReflCmp.compare_self) hpw (lookup_mem hl)]
      rfl
  | none =>
      have hc : (l.map Prod.fst).contains k = false := by
        cases h : (l.map Prod.fst).contains k
        · rfl
        · obtain ⟨⟨k', v⟩, hm, e⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
          cases e
          exact absurd hm (lookup_none hl v)
      rw [Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false hc]
      rfl

/-- The members of `Json.mkObj l`, in its tree, are those of `l` when its keys are distinct. -/
theorem mem_toListModel_ofList {l : List (String × Json)} (hd : (l.map Prod.fst).Nodup) (k : String) (v : Json) :
    (⟨k, v⟩ : (_ : String) × Json) ∈ (Std.TreeMap.Raw.ofList l compare).inner.inner.toListModel ↔ (k, v) ∈ l := by
  have hpw : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    have := List.pairwise_map.mp hd
    exact this.imp (fun h e => h (Std.LawfulEqCmp.eq_of_compare e))
  have hwf : (Std.TreeMap.Raw.ofList l compare).WF := Std.TreeMap.Raw.WF.ofList
  have e1 : (⟨k, v⟩ : (_ : String) × Json) ∈ (Std.TreeMap.Raw.ofList l compare).inner.inner.toListModel ↔
      (k, v) ∈ (Std.TreeMap.Raw.ofList l compare).toList := by
    show _ ↔ (k, v) ∈ Impl.Const.toList _
    rw [constToList_eq]
    constructor
    · intro h; exact List.mem_map.mpr ⟨_, h, rfl⟩
    · intro h
      obtain ⟨⟨k', v'⟩, hh, e⟩ := List.mem_map.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact hh
  rw [e1, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf]
  constructor
  · intro h
    cases hl : l.lookup k with
    | some v' =>
        have := Std.TreeMap.Raw.getElem?_ofList_of_mem (Std.ReflCmp.compare_self) hpw (lookup_mem hl)
        rw [this] at h; cases h; exact lookup_mem hl
    | none =>
        have hc : (l.map Prod.fst).contains k = false := by
          cases h' : (l.map Prod.fst).contains k
          · rfl
          · obtain ⟨⟨k', v⟩, hm, e⟩ := List.mem_map.mp (List.contains_iff_mem.mp h')
            cases e
            exact absurd hm (lookup_none hl v)
        rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false hc] at h; cases h
  · intro h
    exact Std.TreeMap.Raw.getElem?_ofList_of_mem (Std.ReflCmp.compare_self) hpw h

theorem keys_nodup_ofList (l : List (String × Json)) :
    ((Impl.Const.toList (Std.TreeMap.Raw.ofList l compare).inner.inner).map Prod.fst).Nodup := by
  have := Std.TreeMap.Raw.distinct_keys_toList (Std.TreeMap.Raw.WF.ofList (l := l) (cmp := compare))
  apply List.pairwise_map.mpr
  exact this.imp fun h e => h (by rw [e]; exact Std.ReflCmp.compare_self)

theorem reorder_obj (m : Std.TreeMap.Raw String Json compare) :
    reorder (.obj m) = Json.mkObj (reorderT m.inner.inner) := by
  obtain ⟨⟨t⟩⟩ := m; rfl

theorem reorder_arr (a : Array Json) : reorder (.arr a) = .arr (a.map reorder) := by
  obtain ⟨l⟩ := a; simp [reorder, reorderL_eq]

theorem reorder_str (s : String) : reorder (.str s) = .str s := rfl
theorem reorder_num (n : JsonNumber) : reorder (.num n) = .num n := rfl
theorem reorder_bool (b : Bool) : reorder (.bool b) = .bool b := rfl
theorem reorder_null : reorder .null = .null := rfl

/-- **A field of `reorder (Json.mkObj l)`** is `reorder` of what `l` gives for it. -/
theorem getObjVal?_reorder_mkObj (l : List (String × Json)) (k : String) (hd : (l.map Prod.fst).Nodup) :
    (reorder (Json.mkObj l)).getObjVal? k =
      match l.lookup k with
      | some v => .ok (reorder v)
      | none => .error s!"property not found: {k}" := by
  rw [Json.mkObj, reorder_obj]
  generalize ht : (Std.TreeMap.Raw.ofList l compare) = m
  have hmem := mem_toListModel_ofList hd
  rw [ht] at hmem
  have hkeys := keys_nodup_ofList l
  rw [ht] at hkeys
  have hL : ((reorderT m.inner.inner).map Prod.fst).Nodup := by
    rw [reorderT_eq, constToList_eq] at *
    simp only [List.map_map, List.map_reverse] at hkeys ⊢
    exact List.pairwise_reverse.mpr (hkeys.imp fun h e => h e.symm)
  rw [getObjVal?_mkObj _ _ hL]
  cases hl : l.lookup k with
  | some v =>
      have : (reorderT m.inner.inner).lookup k = some (reorder v) := by
        apply lookup_of_mem hL
        rw [reorderT_eq]
        exact List.mem_map.mpr ⟨⟨k, v⟩, List.mem_reverse.mpr ((hmem k v).mpr (lookup_mem hl)), rfl⟩
      rw [this]
  | none =>
      cases h : (reorderT m.inner.inner).lookup k with
      | none => rfl
      | some w =>
          have := lookup_mem h
          rw [reorderT_eq] at this
          obtain ⟨⟨k', v⟩, hp, e⟩ := List.mem_map.mp this
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, -⟩ := e
          exact absurd ((hmem k' v).mp (List.mem_reverse.mp hp)) (lookup_none hl v)

/-- An object built by `Json.mkObj` from distinct keys and values in the fragment is in the fragment. -/
theorem frag_mkObj (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (h : ∀ p ∈ l, frag p.2 = true) :
    frag (Json.mkObj l) = true := by
  unfold Json.mkObj
  generalize ht : (Std.TreeMap.Raw.ofList l compare) = m
  have hmem := mem_toListModel_ofList hd
  have hkeys := keys_nodup_ofList l
  rw [ht] at hmem hkeys
  obtain ⟨⟨t⟩⟩ := m
  simp only [frag, hkeys, decide_true, Bool.true_and, fragT_eq, List.all_eq_true]
  intro p hp
  exact h (p.1, p.2) ((hmem p.1 p.2).mp hp)

theorem frag_arr (a : Array Json) : frag (.arr a) = a.toList.all frag := by
  obtain ⟨l⟩ := a; simp [frag, fragL_eq]

theorem frag_str (s : String) : frag (.str s) = true := rfl
theorem frag_bool (b : Bool) : frag (.bool b) = true := rfl
theorem frag_null : frag .null = true := rfl
theorem frag_nat (n : Nat) : frag (n : Json) = true := by
  simp [frag, JsonNumber.fromNat]

end Damp.Zkir.Text
