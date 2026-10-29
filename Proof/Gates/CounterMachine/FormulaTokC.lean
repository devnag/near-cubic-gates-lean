import Proof.Gates.CounterMachine.FormulaToks

/-! # RG machine, part 10: counted token printers

Each printer appends the marked words of its tokens to the scratch stream `S` and counts them in `F 16`, ending
exactly in `emitT σ ts` (stream heads it moved are given explicitly): `litC` (a fixed token), `powC` (`pow v`, `v` a
register), `constRegC` (a nonnegative constant from a register), `constInC` (a nonnegative constant copied from a
framed natural on a stream), `rateC` (the constant `L[i]` of a framed list, `i` in a register: the rates `a_j` of
the digits, `sec:finite`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section TokC
variable (S : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

theorem emitT_one (σ : WState ns nr) (t : Tok) :
    emitT S F σ [t] = (appendO σ S (F 7) (marks (tokWord t))).setv (F 16) (σ.val (F 16) + 1) := by
  simp [emitT]

theorem appendO_val16 (σ : WState ns nr) (w : List Bool) :
    (appendO σ S (F 7) w).val (F 16) = σ.val (F 16) := by
  simp [appendO, Function.update_of_ne (F.injective.ne (show (16 : Fin 24) ≠ 7 by decide))]

theorem emitT_seth (X : Fin (ns + 1)) (hX : X ≠ S) (σ : WState ns nr) (x : ℕ) (ts : List Tok) :
    emitT S F (σ.seth X x) ts = (emitT S F σ ts).seth X x := by
  unfold emitT
  apply WState.eq
  · funext j; by_cases hj : j = X
    · subst hj; simp [appendO, Function.update_of_ne hX]
    · by_cases hjS : j = S
      · subst hjS; simp [appendO, Function.update_of_ne hj]
      · simp [appendO, Function.update_of_ne hj, Function.update_of_ne hjS]
  · simp [appendO]
  · simp [appendO]
  · simp [appendO]

theorem emitT_sh_ne (X : Fin (ns + 1)) (hX : X ≠ S) (σ : WState ns nr) (ts : List Tok) :
    (emitT S F σ ts).sh X = σ.sh X := by simp [emitT, appendO, Function.update_of_ne hX]

theorem emitT_st_ne (X : Fin (ns + 1)) (hX : X ≠ S) (σ : WState ns nr) (ts : List Tok) :
    (emitT S F σ ts).st X = σ.st X := by simp [emitT, appendO, Function.update_of_ne hX]

theorem emitT_val_ne (r : Fin nr) (h7 : r ≠ F 7) (h16 : r ≠ F 16) (σ : WState ns nr) (ts : List Tok) :
    (emitT S F σ ts).val r = σ.val r := by
  simp [emitT, appendO, Function.update_of_ne h7, Function.update_of_ne h16]

/-- A fixed token. -/
def litC (t : Tok) : WM ns nr := .seq (tokLit S (Rf F) t) (.inc (F 16))

theorem litC_spec (t : Tok) (σ : WState ns nr) (h : TRest S F σ)
    (hcap : σ.val (F 7) + 2 * (tokWord t).length ≤ cap) (hc : σ.val (F 16) < cap) :
    WExec cap (litC S F t) σ (emitT S F σ [t]) (16 * (tokWord t).length + 4) := by
  have e1 := tokLit_spec cap S (Rf F) t σ h.pr hcap
  have e2 := WExec.inc (cap := cap) (F 16) (appendO σ S (Rf F 7) (marks (tokWord t)))
    (by rw [show Rf F 7 = F 7 from rfl, appendO_val16]; exact hc)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  rw [emitT_one, show Rf F 7 = F 7 from rfl, appendO_val16]

/-- `pow v` with `v` in a register. -/
def powC (v : Fin nr) : WM ns nr := .seq (tokTagReg S (Rf F) 6 v) (.inc (F 16))

theorem powC_spec (v : Fin nr) (hv : ∀ i : Fin 24, F i ≠ v) (σ : WState ns nr) (h : TRest S F σ)
    (hcap : σ.val (F 7) + 2 * (natWord 6).length + 7 * σ.val v + 12 ≤ cap) (hc : σ.val (F 16) < cap) :
    WExec cap (powC S F v) σ (emitT S F σ [Tok.pow (σ.val v)])
      (16 * (natWord 6).length + 1 + printCost (σ.val v) + 4) := by
  have e1 := tokTagReg_spec cap S (Rf F) 6 v (fun i _ => by rw [Rf_apply]; exact hv _) σ h.pr hcap
  have e2 := WExec.inc (cap := cap) (F 16) (appendO σ S (Rf F 7) (marks (natWord 6 ++ natWord (σ.val v))))
    (by rw [show Rf F 7 = F 7 from rfl, appendO_val16]; exact hc)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  rw [emitT_one, show Rf F 7 = F 7 from rfl, appendO_val16]; rfl

/-- A nonnegative constant from a register. -/
def constRegC (v : Fin nr) : WM ns nr :=
  .seq (emitMarks S (F 7) (natWord 0)) (.seq (tokTagReg S (Rf F) 0 v) (.inc (F 16)))

theorem constRegC_spec (v : Fin nr) (hv : ∀ i : Fin 24, F i ≠ v) (σ : WState ns nr) (h : TRest S F σ)
    (hcap : σ.val (F 7) + 4 * (natWord 0).length + 7 * σ.val v + 12 ≤ cap) (hc : σ.val (F 16) < cap) :
    WExec cap (constRegC S F v) σ (emitT S F σ [Tok.const (σ.val v : ℤ)])
      (16 * (natWord 0).length + 1 + (16 * (natWord 0).length + 1 + printCost (σ.val v) + 4)) := by
  have e1 := emitMarks_spec cap S (F 7) (natWord 0) σ h.pr.out (by omega)
  have hv7 : F 7 ≠ v := hv 7
  have h1 : TRest S F (appendO σ S (F 7) (marks (natWord 0))) := by
    have := h.emitT S F []
    refine TRest.of_zero S F (by simp [appendO, h.pr.out]) (fun i hi => ?_)
    have k : i ≠ 7 := by revert i; decide
    simp [appendO, Function.update_of_ne (F.injective.ne k)]; exact h.zero S F i hi
  have ev : (appendO σ S (F 7) (marks (natWord 0))).val v = σ.val v := by
    simp [appendO, Function.update_of_ne hv7.symm]
  have e2 := tokTagReg_spec cap S (Rf F) 0 v (fun i _ => by rw [Rf_apply]; exact hv _) _ h1.pr
    (by rw [ev]; simp only [show Rf F 7 = F 7 from rfl, appendO, WState.setv_val, Function.update_self,
          WState.seth_val, WState.sets_val, marks_length]; omega)
  rw [ev] at e2
  have e3 := WExec.inc (cap := cap) (F 16)
    (appendO (appendO σ S (F 7) (marks (natWord 0))) S (Rf F 7) (marks (natWord 0 ++ natWord (σ.val v))))
    (by rw [show Rf F 7 = F 7 from rfl, appendO_val16, appendO_val16]; exact hc)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  rw [emitT_one, show Rf F 7 = F 7 from rfl, appendO_val16, appendO_val16, appendO_append, ← marksApp,
    tokWord_const_nat]
  simp [List.append_assoc]

/-- A nonnegative constant copied from a framed natural on `I`. -/
def constInC (I : Fin (ns + 1)) : WM ns nr :=
  .seq (emitMarks S (F 7) (natWord 0 ++ natWord 0)) (.seq (copyNat true I S (wR (Rf F))) (.inc (F 16)))

theorem constInC_spec (I : Fin (ns + 1)) (hIS : I ≠ S) (x : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (h : TRest S F σ) (hst : σ.st I = pre ++ enc true (natWord x) ++ rest) (hsh : σ.sh I = pre.length)
    (hcap : σ.val (F 7) + 2 * (natWord 0 ++ natWord 0).length + 2 * (natWord x).length + 2 ≤ cap)
    (hc : σ.val (F 16) < cap) :
    WExec cap (constInC S F I) σ ((emitT S F σ [Tok.const (x : ℤ)]).seth I (pre.length + 2 * (natWord x).length))
      (16 * (natWord 0 ++ natWord 0).length + 1 + (60 * (natWord x).length + 60 + 1 + 3)) := by
  have e1 := emitMarks_spec cap S (F 7) (natWord 0 ++ natWord 0) σ h.pr.out (by omega)
  set σ1 := appendO σ S (F 7) (marks (natWord 0 ++ natWord 0)) with hσ1
  have z1 : σ1.val (F 1) = 0 := by
    simp [hσ1, appendO, Function.update_of_ne (F.injective.ne (show (1 : Fin 24) ≠ 7 by decide))]
    exact h.zero S F 1 (by decide)
  have z2 : σ1.val (F 2) = 0 := by
    simp [hσ1, appendO, Function.update_of_ne (F.injective.ne (show (2 : Fin 24) ≠ 7 by decide))]
    exact h.zero S F 2 (by decide)
  have e2 := copyNat_spec cap true I S hIS (wR (Rf F)) x pre rest σ1
    (by simp [hσ1, appendO, Function.update_of_ne hIS, hst]) (by simp [hσ1, appendO, Function.update_of_ne hIS, hsh])
    (by simp [hσ1, appendO, h.pr.out]) z1 z2
    (by simp only [hσ1, appendO, show wR (Rf F) 7 = F 7 from rfl, WState.setv_val, WState.seth_val,
          WState.sets_val, Function.update_self, marks_length]; omega)
  have e3 := WExec.inc (cap := cap) (F 16)
    ((appendO σ1 S (wR (Rf F) 7) (marks (natWord x))).seth I (pre.length + stp true * (natWord x).length))
    (by simp only [WState.seth_val, show wR (Rf F) 7 = F 7 from rfl, hσ1, appendO_val16]; exact hc)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  rw [emitT_one]
  apply WState.eq
  · funext j; by_cases hj : j = I
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hIS, stp]
    · by_cases hjS : j = S
      · subst hjS; simp [hσ1, appendO, Function.update_of_ne hj, tokWord_const_nat, marksApp]; ring
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjS]
  · funext j; by_cases hjS : j = S
    · subst hjS; simp [hσ1, appendO, Function.update_of_ne hIS.symm, tokWord_const_nat, marksApp]
    · simp [hσ1, appendO, Function.update_of_ne hjS]
  · funext r; by_cases r16 : r = F 16
    · subst r16; simp [hσ1, appendO, show wR (Rf F) 7 = F 7 from rfl,
        Function.update_of_ne (F.injective.ne (show (16 : Fin 24) ≠ 7 by decide))]
    · by_cases r7 : r = F 7
      · subst r7; simp [hσ1, appendO, show wR (Rf F) 7 = F 7 from rfl, Function.update_of_ne r16,
          tokWord_const_nat, marksApp]; ring
      · simp [hσ1, appendO, show wR (Rf F) 7 = F 7 from rfl, Function.update_of_ne r16, Function.update_of_ne r7]
  · simp [hσ1, appendO]

/-! ## Cost classes of the stage printer and the seek -/

theorem skipIntCost_le (z : ℤ) (Λ : ℕ) (hz : natBitLength z.natAbs ≤ Λ) : skipIntCost z ≤ 20 * Λ + 81 := by
  have hs : natBitLength (if z < 0 then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
  unfold skipIntCost; omega

theorem blockCost_le (G Λ : ℕ) (b : List ℤ) (hG : G ≤ Λ) (hb : b.length ≤ Λ)
    (hz : ∀ z ∈ b, natBitLength z.natAbs ≤ Λ) : blockCost G b ≤ 110 * (Λ + 1) ^ 2 := by
  have h1 := sum_map_le b (fun z => skipIntCost z + 4) (20 * Λ + 85) (fun z hz' => by
    have := skipIntCost_le z Λ (hz z hz'); omega)
  have h2 : b.length * (20 * Λ + 85) ≤ Λ * (20 * Λ + 85) := Nat.mul_le_mul_right _ hb
  unfold blockCost; nlinarith

/-- The exact cost of `stP` (`stP_spec`). -/
def stCost (G s o lb : ℕ) (blocks : List (List ℤ)) : ℕ :=
  18 * s + 3 + 1 + ((((blocks.take s).map fun b => blockCost G b + 4).sum + 1) + 1 + (18 * o + 3 + 1 +
    (linCost o blocks[s]! + 1 + (3 * (o + G) + 1 + 1 + (18 * lb + 3 + 1 + (5 * lb + 1 + 1 +
      (4 * (18 * G + 3) + 7)))))))

theorem stCost_le (G s o lb Λ : ℕ) (blocks : List (List ℤ)) (hb : ∀ b ∈ blocks, b.length = G) (hs : s < blocks.length)
    (hsΛ : s ≤ Λ) (hoG : o + G ≤ Λ) (hlb : lb ≤ Λ) (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ) :
    stCost G s o lb blocks ≤ 4000 * (Λ + 1) ^ 3 := by
  have hsum := sum_map_le (blocks.take s) (fun b => blockCost G b + 4) (110 * (Λ + 1) ^ 2 + 4) (fun b hb' => by
    have hbm := List.mem_of_mem_take hb'
    have := blockCost_le G Λ b (by omega) (by rw [hb b hbm]; omega) (hz b hbm); omega)
  have hts : (blocks.take s).length ≤ Λ := by simp; omega
  have h2 : (blocks.take s).length * (110 * (Λ + 1) ^ 2 + 4) ≤ Λ * (110 * (Λ + 1) ^ 2 + 4) :=
    Nat.mul_le_mul_right _ hts
  have hbs : blocks[s]! = blocks[s] := by simp [hs]
  have hlin := linCost_le o blocks[s] Λ (by rw [hb _ (List.getElem_mem hs)]; omega)
    (hz _ (List.getElem_mem hs))
  unfold stCost; rw [hbs]
  have : (Λ + 1) ^ 3 = (Λ + 1) * (Λ + 1) ^ 2 := by ring
  nlinarith

theorem seekCost_le (b i Λ : ℕ) (L : List ℕ) (hb : b ≤ Λ) (hi : i ≤ Λ) (hL : ∀ x ∈ L, natBitLength x ≤ Λ) :
    seekCost b i L ≤ 100 * (Λ + 1) ^ 2 := by
  have hsum := sum_map_le (L.take i) (fun x => 20 * natBitLength x + 20 + 4) (20 * Λ + 24) (fun x hx => by
    have := hL x (List.mem_of_mem_take hx); omega)
  have ht : (L.take i).length ≤ Λ := by simp; omega
  have h2 : (L.take i).length * (20 * Λ + 24) ≤ Λ * (20 * Λ + 24) := Nat.mul_le_mul_right _ ht
  unfold seekCost; nlinarith

/-! ## A constant of a framed list -/

theorem encN_cons (a : ℕ) (l : List ℕ) : encN (a :: l) = enc true (natWord a) ++ encN l := by simp [encN]

theorem encN_split (L : List ℕ) (i : ℕ) (hi : i < L.length) :
    encN L = encN (L.take i) ++ enc true (natWord L[i]) ++ encN (L.drop (i + 1)) := by
  have e : L = L.take i ++ L[i] :: L.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [e]
  rw [encN_append, encN_cons, List.append_assoc]

theorem encN_take_succ (L : List ℕ) (i : ℕ) (hi : i < L.length) :
    (encN (L.take (i + 1))).length = (encN (L.take i)).length + 2 * (natWord L[i]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  rw [encN_append, List.length_append]
  simp [encN, enc_length, stp]

/-- `const L[i]`, `i` in the register `Jp` (the list on `FA`, `LBF` a bound on the read prefix). -/
def rateC (FA : Fin (ns + 1)) (LBF Jp : Fin nr) : WM ns nr :=
  .seq (seekP FA LBF Jp (F 19) (F 18) (F 1) (F 2) (F 8))
  (.seq (constInC S F FA) (.seq (copyR LBF (F 19) (F 8)) (WM.rewind FA (F 19))))

theorem rateC_spec (FA : Fin (ns + 1)) (hFS : FA ≠ S) (LBF Jp : Fin nr) (hLF : ∀ i : Fin 24, F i ≠ LBF)
    (hJp : ∀ i : Fin 24, F i ≠ Jp) (hLJ : LBF ≠ Jp) (L : List ℕ) (rest : List Bool) (i lbf Λ : ℕ)
    (hi : i < L.length) (σ : WState ns nr) (h : TRest S F σ) (hst : σ.st FA = encN L ++ rest) (hsh : σ.sh FA = 0)
    (hJv : σ.val Jp = i) (hLv : σ.val LBF = lbf) (hlb : (encN (L.take (i + 1))).length ≤ lbf)
    (hΛ : lbf ≤ Λ) (hiΛ : i ≤ Λ) (hL : ∀ x ∈ L, natBitLength x ≤ Λ)
    (hcap : σ.val (F 7) + 2 * (natWord 0 ++ natWord 0).length + 2 * (natWord L[i]).length + 2 ≤ cap)
    (hcap2 : lbf + i + 1 ≤ cap) (hfit : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hc : σ.val (F 16) < cap) :
    WExec cap (rateC S F FA LBF Jp) σ (emitT S F σ [Tok.const (L[i] : ℤ)]) (600 * (Λ + 1) ^ 2) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have hz := h.zero S F
  have hd : [LBF, Jp, F 19, F 18, F 1, F 2, F 8].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    refine ⟨⟨hLJ, (hLF 19).symm, (hLF 18).symm, (hLF 1).symm, (hLF 2).symm, (hLF 8).symm⟩,
      ⟨(hJp 19).symm, (hJp 18).symm, (hJp 1).symm, (hJp 2).symm, (hJp 8).symm⟩,
      ⟨hne (by decide), hne (by decide), hne (by decide), hne (by decide)⟩,
      ⟨hne (by decide), hne (by decide), hne (by decide)⟩, ⟨hne (by decide), hne (by decide)⟩, hne (by decide)⟩
  have e1 := seekP_spec cap FA LBF Jp (F 19) (F 18) (F 1) (F 2) (F 8) hd L rest σ hst (by rw [hsh]; omega)
    (by rw [hJv]; omega) (hz 19 (by decide)) (hz 18 (by decide)) (hz 1 (by decide)) (hz 2 (by decide))
    (hz 8 (by decide)) hfit (by rw [hLv, hJv]; exact hcap2)
  rw [hJv, hLv] at e1
  set σ1 := σ.seth FA (encN (L.take i)).length with hσ1
  have h1 : TRest S F σ1 := ⟨⟨by simp [hσ1, Function.update_of_ne hFS.symm, h.pr.out], h.pr.zero⟩,
    h.z9, h.z10, h.z17, h.z18, h.z19⟩
  have e2 := constInC_spec cap S F FA hFS L[i] (encN (L.take i)) (encN (L.drop (i + 1)) ++ rest) σ1 h1
    (by simp only [hσ1, WState.seth_st]; rw [hst, encN_split L i hi]; simp [List.append_assoc])
    (by simp [hσ1]) (by simpa [hσ1] using hcap) (by simpa [hσ1] using hc)
  set σ2 := (emitT S F σ1 [Tok.const (L[i] : ℤ)]).seth FA ((encN (L.take i)).length + 2 * (natWord L[i]).length)
    with hσ2
  have v2 : ∀ r, r ≠ F 7 → r ≠ F 16 → σ2.val r = σ.val r := fun r h7 h16 => by
    simp [hσ2, hσ1, emitT, appendO, Function.update_of_ne h7, Function.update_of_ne h16]
  have e3 := copyR_spec cap (v := LBF) (d := F 19) (t := F 8) (hLF 19).symm (hLF 8).symm (hne (by decide)) σ2
    (by rw [v2 _ (hne (by decide)) (hne (by decide))]; exact hz 8 (by decide))
    (by rw [v2 _ (hne (by decide)) (hne (by decide)), v2 _ (hLF 7).symm (hLF 16).symm, hz 19 (by decide), hLv]
        omega)
  rw [v2 _ (hne (by decide)) (hne (by decide)), v2 _ (hLF 7).symm (hLF 16).symm, hz 19 (by decide), hLv,
    Nat.zero_add] at e3
  have e4 := wrewind_spec cap FA (F 19) lbf (σ2.setv (F 19) lbf) (by simp) (by simp; omega)
  have hsh2 : σ2.sh FA = (encN (L.take i)).length + 2 * (natWord L[i]).length := by simp [hσ2]
  have hpos : (σ2.setv (F 19) lbf).sh FA - lbf = 0 := by
    have := encN_take_succ L i hi
    simp only [WState.setv_sh]; rw [hsh2]; omega
  rw [hpos] at e4
  have hσ2' : σ2 = (emitT S F σ [Tok.const (L[i] : ℤ)]).seth FA
      ((encN (L.take i)).length + 2 * (natWord L[i]).length) := by
    rw [hσ2, hσ1, emitT_seth S F FA hFS, wseth_seth]
  have hτ19 : (emitT S F σ [Tok.const (L[i] : ℤ)]).val (F 19) = 0 := by
    rw [emitT_val_ne S F _ (hne (by decide)) (hne (by decide))]; exact hz 19 (by decide)
  have hτFA : (emitT S F σ [Tok.const (L[i] : ℤ)]).sh FA = 0 := by rw [emitT_sh_ne S F FA hFS, hsh]
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ ?_
  · rw [hσ2']
    generalize emitT S F σ [Tok.const (L[i] : ℤ)] = τ at hτ19 hτFA ⊢
    apply WState.eq
    · funext j; by_cases hj : j = FA
      · subst hj; simp [hτFA]
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases r19 : r = F 19
      · subst r19; simp [hτ19]
      · simp [Function.update_of_ne r19]
    · simp
  · have hsk := seekCost_le lbf i Λ L hΛ hiΛ hL
    have hn : natBitLength L[i] ≤ Λ := hL _ (List.getElem_mem hi)
    have e00 : (natWord 0 ++ natWord 0).length = 6 := by decide
    rw [e00, natWord_length']
    nlinarith

theorem emitT_setv (r : Fin nr) (h7 : r ≠ F 7) (h16 : r ≠ F 16) (σ : WState ns nr) (x : ℕ) (ts : List Tok) :
    emitT S F (σ.setv r x) ts = (emitT S F σ ts).setv r x := by
  unfold emitT
  apply WState.eq
  · simp [appendO]
  · simp [appendO]
  · funext q; by_cases hq : q = r
    · subst hq; simp [appendO, Function.update_of_ne h7, Function.update_of_ne h16]
    · by_cases q16 : q = F 16
      · subst q16; simp [appendO, Function.update_of_ne (Ne.symm h16)]
      · by_cases q7 : q = F 7
        · subst q7; simp [appendO, Function.update_of_ne (Ne.symm h7), Function.update_of_ne q16]
        · simp [appendO, Function.update_of_ne hq, Function.update_of_ne q16, Function.update_of_ne q7]
  · simp [appendO]

theorem TRest.setv {σ : WState ns nr} (h : TRest S F σ) (r : Fin nr) (hr : ∀ i : Fin 24, F i ≠ r) (x : ℕ) :
    TRest S F (σ.setv r x) :=
  TRest.of_zero S F (by simp [h.pr.out]) (fun i hi => by
    simp [Function.update_of_ne (hr i)]; exact h.zero S F i hi)

/-- Room for printing the tokens `ts` from `σ` (output position and count), with slack `Λ`. -/
def TCap (σ : WState ns nr) (ts : List Tok) (Λ : ℕ) : Prop :=
  σ.val (F 7) + 2 * (ts.flatMap tokWord).length + 8 * Λ + 100 ≤ cap ∧ σ.val (F 16) + ts.length + 4 * Λ + 2 ≤ cap

theorem emitT_val7 (σ : WState ns nr) (ts : List Tok) :
    (emitT S F σ ts).val (F 7) = σ.val (F 7) + 2 * (ts.flatMap tokWord).length := by
  simp [emitT, appendO, Function.update_of_ne (F.injective.ne (show (7 : Fin 24) ≠ 16 by decide)), marks_length]

theorem emitT_val16 (σ : WState ns nr) (ts : List Tok) :
    (emitT S F σ ts).val (F 16) = σ.val (F 16) + ts.length := by simp [emitT]

theorem TCap.left {σ : WState ns nr} {a b : List Tok} {Λ : ℕ} (h : TCap cap F σ (a ++ b) Λ) : TCap cap F σ a Λ := by
  unfold TCap at *; simp only [List.flatMap_append, List.length_append] at h; omega

theorem TCap.right {σ : WState ns nr} {a b : List Tok} {Λ : ℕ} (h : TCap cap F σ (a ++ b) Λ) :
    TCap cap F (emitT S F σ a) b Λ := by
  unfold TCap at *; rw [emitT_val7, emitT_val16]; simp only [List.flatMap_append, List.length_append] at h; omega

theorem TCap.setv {σ : WState ns nr} {ts : List Tok} {Λ : ℕ} (h : TCap cap F σ ts Λ) (r : Fin nr)
    (hr : ∀ i : Fin 24, F i ≠ r) (x : ℕ) : TCap cap F (σ.setv r x) ts Λ := by
  unfold TCap at *
  simp only [WState.setv_val, Function.update_of_ne (hr 7), Function.update_of_ne (hr 16)]; exact h

theorem TCap.seth {σ : WState ns nr} {ts : List Tok} {Λ : ℕ} (h : TCap cap F σ ts Λ) (X : Fin (ns + 1)) (x : ℕ) :
    TCap cap F (σ.seth X x) ts Λ := h

/-- **The stage printer in its class.** -/
theorem stP_run (CW : Fin (ns + 1)) (hSC : S ≠ CW) (Gr off LB Sj : Fin nr) (hG : ∀ i : Fin 24, F i ≠ Gr)
    (ho : ∀ i : Fin 24, F i ≠ off) (hL : ∀ i : Fin 24, F i ≠ LB) (hJ : ∀ i : Fin 24, F i ≠ Sj)
    (G s o lb Λ : ℕ) (blocks : List (List ℤ)) (hb : ∀ b ∈ blocks, b.length = G) (hs : s < blocks.length)
    (rest : List Bool) (σ : WState ns nr) (h : TRest S F σ)
    (hst : σ.st CW = encI blocks.flatten ++ rest) (hsh : σ.sh CW = 0)
    (hGv : σ.val Gr = G) (hov : σ.val off = o) (hLv : σ.val LB = lb) (hJv : σ.val Sj = s)
    (hlb : (encI (blocks.take (s + 1)).flatten).length ≤ lb)
    (hsΛ : s ≤ Λ) (hoG : o + G ≤ Λ) (hlbΛ : lb ≤ Λ) (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ)
    (hcap : TCap cap F σ (linToks o blocks[s]) Λ) :
    WExec cap (stP S CW F Gr off LB Sj) σ (emitT S F σ (linToks o blocks[s])) (4000 * (Λ + 1) ^ 3) := by
  have hlt := linToks_length o blocks[s]
  rw [hb _ (List.getElem_mem hs)] at hlt
  unfold TCap at hcap
  have e := stP_spec cap S CW F hSC Gr off LB Sj hG ho hL hJ G s o lb blocks hb hs rest σ h hst hsh hGv hov hLv hJv
    hlb (σ.val (F 7) + (marks ((linToks o blocks[s]).flatMap tokWord)).length) le_rfl
    (by rw [marks_length]; omega) (by omega) (by omega) (by omega) (fun b hb' z hz' => by have := hz b hb' z hz'; omega)
  refine WExec.mono e ?_
  have := stCost_le G s o lb Λ blocks hb hs hsΛ hoG hlbΛ hz
  unfold stCost at this
  have hbs : blocks[s]! = blocks[s] := by simp [hs]
  rw [hbs] at this
  exact this

end TokC

end NearCubicGates.Close.CounterMachine
