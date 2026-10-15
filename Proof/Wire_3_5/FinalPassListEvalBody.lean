import Proof.Wire_3_5.FinalPassListEvalStep

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The loop body: one record of the table word. -/
def body : LProg :=
  .seq fwdT (.seq (RM.readU 1 rTP rU) (.seq readWcyc (.seq scanRow (.seq sub2P (.seq (RM.clear rU)
    (.seq decidePart (RM.move rC rP)))))))

section
variable (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ)

/-- The streams: the framed point, the table word, the compared state. -/
def streams : Fin 3 → List Bool := ![frame Z, levelWord M J W row, unary s]

/-- The table word's length. -/
def wordLen : ℕ := (levelWord M J W row).length

/-- **The loop invariant** before the records `js` with the fold value `acc = (followed state, last count)`. -/
def Inv (js : List ℕ) (acc : Option ℕ × ℕ) (σ : LState) : Prop :=
  (levelWord M J W row).drop (σ.sh 1) = js.flatMap (record J W row) ++ [false] ∧
  σ.val rTP = σ.sh 1 ∧ σ.sh 0 = 0 ∧ σ.sh 2 = 0 ∧
  σ.val rMR = M ∧ σ.val rP = acc.2 ∧ acc.2 ≤ Z.length ∧
  σ.val rF ≤ 1 ∧ σ.val rS ≤ 3 * wordLen M J W row ∧
  (∀ t, acc.1 = some t → σ.val rF = 0 ∧ σ.val rS = t) ∧ (acc.1 = none → σ.val rF = 1) ∧
  σ.val rC = 0 ∧ σ.val rW = 0 ∧ σ.val rV = 0 ∧ σ.val rU = 0 ∧ σ.val rT = 0 ∧ σ.val rR = 0 ∧
  σ.val rSP = 0 ∧ σ.val rX = 0 ∧ σ.val rT1 = 0 ∧ σ.val rT2 = 0

end

/-! ## Reading unary fields and word lengths -/

theorem ones_of_drop {l t : List Bool} {p n : ℕ} (h : l.drop p = List.replicate n true ++ false :: t) :
    (∀ k < n, readTapeBit l (p + k) = true) ∧ readTapeBit l (p + n) = false := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [readTapeBit_drop, h]
    unfold readTapeBit
    rw [List.getD_append _ _ _ _ (by simpa using hk)]
    simp [hk]
  · rw [readTapeBit_drop, h]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem drop_len_le {l t : List Bool} {p : ℕ} (h : l.drop p = t) (hne : t ≠ []) : p + t.length = l.length := by
  have := congrArg List.length h
  rw [List.length_drop] at this
  have hp : p < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact hne h.symm
  omega

theorem record_length (J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) :
    (record J W row j).length = 3 + pow (topW J W j) + topW J W j + (row j).length := by
  simp [record, unary]; omega

theorem word_M_le (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) : M + 1 ≤ wordLen M J W row := by
  simp [wordLen, levelWord, unary]

theorem resid_eq (P W c cp : ℕ) (hP : 0 < P) :
    (((0 + W) % P + c) % P + 2 * cp * (P - 1)) % P = cyc P ((c : ℤ) + W - 2 * cp) := by
  have h1 : (((0 + W) % P + c) % P + 2 * cp * (P - 1)) % P = (W + c + 2 * cp * (P - 1)) % P := by
    rw [Nat.zero_add, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod, ← Nat.add_assoc]
  unfold cyc
  rw [h1]
  have h2 : ((c : ℤ) + W - 2 * cp) % (P : ℤ) = (((W + c + 2 * cp * (P - 1) : ℕ) : ℤ)) % (P : ℤ) := by
    have e : (((W + c + 2 * cp * (P - 1) : ℕ) : ℤ)) = ((c : ℤ) + W - 2 * cp) + (2 * cp) * P := by
      push_cast [Nat.cast_sub (show 1 ≤ P from hP)]; ring
    rw [e, Int.add_mul_emod_self_right]
  rw [h2, ← Int.natCast_emod, Int.toNat_natCast]

/-- The step count of one record. -/
def bodyCost (cap : ℕ) : ℕ := 40 * (cap + 1) * (cap + 1)

theorem streams_one (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) :
    streams M J W row Z s 1 = levelWord M J W row := rfl

theorem streams_zero (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) :
    streams M J W row Z s 0 = frame Z := rfl

theorem decState_sh (x : LState) : (decState x).sh = x.sh := by unfold decState; split_ifs <;> rfl

theorem decState_keep (x : LState) (r : Fin 15) (h1 : r ≠ rS) (h2 : r ≠ rF) (h3 : r ≠ rV) (h4 : r ≠ rW) :
    (decState x).val r = x.val r := by
  unfold decState
  split_ifs <;> simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4]

theorem decState_V (x : LState) : (decState x).val rV = 0 := by unfold decState; split_ifs <;> simp

theorem decState_W (x : LState) : (decState x).val rW = 0 := by unfold decState; split_ifs <;> simp

theorem decState_failed (x : LState) (h : x.val rF ≠ 0) :
    (decState x).val rF = x.val rF ∧ (decState x).val rS = x.val rS := by
  unfold decState; rw [if_pos h]; simp

theorem decState_over (x : LState) (h : x.val rF = 0) (hM : x.val rMR < x.val rS) :
    (decState x).val rF = 1 ∧ (decState x).val rS = x.val rS := by
  unfold decState; rw [if_neg (by omega), if_pos hM]; simp

theorem decState_arith (x : LState) (h : x.val rF = 0) (hM : ¬ x.val rMR < x.val rS) :
    (decState x).val rF = (if 2 * x.val rS + x.val rV < x.val rW then 1 else 0) ∧
      (decState x).val rS = 2 * x.val rS + x.val rV - x.val rW := by
  unfold decState; rw [if_neg (by omega), if_neg hM]; simp

theorem body_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (js : List ℕ) (j : ℕ)
    (acc : Option ℕ × ℕ) (σ : LState) (hj : (row j).length = Z.length)
    (hinv : Inv M J W row Z (j :: js) acc σ) :
    ∃ τ, RExec (streams M J W row Z s) (capOf M J W row Z.length) body σ τ
        (bodyCost (capOf M J W row Z.length)) ∧
      Inv M J W row Z js (levelStep M (topW J W j) acc.2 (hits (row j) Z) acc.1, hits (row j) Z) τ := by
  rcases acc with ⟨o, cp⟩
  obtain ⟨hd, hTP, hs0, hs2, hMR, hP, hPL, hF1, hSB, hsome, hnone, hC, hW, hV, hU, hT, hR, hSP, hX, hT1, hT2⟩ := hinv
  simp only at hP hPL hsome hnone ⊢
  generalize hinp : streams M J W row Z s = inp
  generalize hcapv : capOf M J W row Z.length = cap
  generalize hB : wordLen M J W row = B at hSB ⊢
  generalize hL : Z.length = L at hj hPL hcapv ⊢
  generalize hWp : topW J W j = Wp
  generalize hPw : pow Wp = Pw
  generalize hc : hits (row j) Z = c
  have hPos : 0 < Pw := by rw [← hPw]; exact pow_pos _
  have hcapB : cap = 4 * (B + L + 1) := by rw [← hcapv, ← hB]; rfl
  have hrest := hd
  rw [List.flatMap_cons, List.append_assoc] at hrest
  have hin1 : inp 1 = levelWord M J W row := by rw [← hinp]; rfl
  have hin0 : inp 0 = frame Z := by rw [← hinp]; rfl
  have hdrop : (inp 1).drop (σ.sh 1) = record J W row j ++ (js.flatMap (record J W row) ++ [false]) := by
    rw [hin1]; exact hrest
  have hrec : record J W row j = true :: (List.replicate Pw true ++ false :: (List.replicate Wp true ++ false ::
      row j)) := by
    rw [← hPw, ← hWp]; simp [record, unary]
  have hlen := drop_len_le hdrop (by simp [record])
  rw [List.length_append, record_length, hj, hWp, hPw] at hlen
  have hBl : (inp 1).length = B := by rw [hin1, ← hB]; rfl
  have hcL : c ≤ L := by rw [← hc, ← hL]; exact hits_le _ _
  have hM1 : M + 1 ≤ B := by rw [← hB]; exact word_M_le M J W row
  -- 1. the record marker
  have s1 := fwdC_spec inp cap 1 rTP σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : LState, τ = (σ.seth 1 (σ.sh 1 + 1)).setv rTP (σ.val rTP + 1) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have hd1 : (inp 1).drop (σ1.sh 1) = List.replicate Pw true ++ false :: (List.replicate Wp true ++ false ::
      (row j ++ (js.flatMap (record J W row) ++ [false]))) := by
    have : σ1.sh 1 = σ.sh 1 + 1 := by rw [hσ1]; simp
    rw [this]
    exact drop_succ_of_cons (a := true) (by rw [hdrop, hrec]; simp)
  -- 2. the modulus into U
  obtain ⟨ho2, he2⟩ := ones_of_drop hd1
  have s2 := readU_spec inp cap 1 rTP rU (by decide) Pw σ1 ho2 he2 (by rw [hσ1]; simp; omega)
    (by rw [hσ1]; simp; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : LState,
      τ = ((σ1.seth 1 (σ1.sh 1 + Pw + 1)).setv rTP (σ1.val rTP + Pw + 1)).setv rU (σ1.val rU + Pw) := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have hc2 : CycOk Pw 0 σ2 := ⟨by rw [hσ2, hσ1]; simp [hV], by rw [hσ2, hσ1]; simp [hU], hPos⟩
  have hd2 : (inp 1).drop (σ2.sh 1) = List.replicate Wp true ++ false ::
      (row j ++ (js.flatMap (record J W row) ++ [false])) := by
    have : σ2.sh 1 = σ1.sh 1 + (List.replicate Pw true ++ [false]).length := by rw [hσ2]; simp; omega
    rw [this]
    exact drop_add_of_append (by rw [hd1]; simp)
  -- 3. the window into W and the residue
  have s3 := readWcyc_spec inp cap Pw Wp 0 (row j ++ (js.flatMap (record J W row) ++ [false])) σ2 hPos (by omega)
    hd2 hc2 (by rw [hσ2, hσ1]; simp; omega) (by rw [hσ2, hσ1]; simp [hW]; omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ : LState,
      τ = ((wState Pw 0 Wp σ2).seth 1 (σ2.sh 1 + Wp + 1)).setv rTP (σ2.val rTP + Wp + 1) := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have hc3 : CycOk Pw ((0 + Wp) % Pw) σ3 := by
    refine ⟨?_, ?_, Nat.mod_lt _ hPos⟩ <;> rw [hσ3] <;> simp [wState, setCyc]
  have hd3 : (inp 1).drop (σ3.sh 1) = row j ++ (js.flatMap (record J W row) ++ [false]) := by
    have : σ3.sh 1 = σ2.sh 1 + (List.replicate Wp true ++ [false]).length := by
      rw [hσ3]; simp [wState, setCyc]; omega
    rw [this]
    exact drop_add_of_append (by rw [hd2]; simp)
  have h3s0 : σ3.sh 0 = 0 := by rw [hσ3, hσ2, hσ1]; simp [wState, setCyc, hs0]
  have h3R : σ3.val rR = 0 := by rw [hσ3, hσ2, hσ1]; simp [wState, setCyc, hR]
  have h3C : σ3.val rC = 0 := by rw [hσ3, hσ2, hσ1]; simp [wState, setCyc, hC]
  have h3TP : σ3.val rTP = σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) := by
    rw [hσ3, hσ2, hσ1]; simp [wState, setCyc, hTP]; omega
  -- 4. the row: c_j into C and the residue
  have s4 := scanRow_spec inp cap Pw (js.flatMap (record J W row) ++ [false]) (row j) Z ((0 + Wp) % Pw) σ3 hPos
    (by omega) (by rw [hj, hL]) hin0 h3s0 h3R hd3 hc3 (by rw [h3C, hL]; omega) (by rw [hL]; omega)
    (by rw [h3TP, hL]; omega)
  rw [hL, hc] at s4
  obtain ⟨σ4, hσ4⟩ : ∃ τ : LState,
      τ = ((hState Pw ((0 + Wp) % Pw) c σ3).seth 1 (σ3.sh 1 + L)).setv rTP (σ3.val rTP + L) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have hc4 : CycOk Pw (((0 + Wp) % Pw + c) % Pw) σ4 := by
    refine ⟨?_, ?_, Nat.mod_lt _ hPos⟩ <;> rw [hσ4] <;> simp [hState, setCyc]
  have h4P : σ4.val rP = cp := by rw [hσ4, hσ3, hσ2, hσ1]; simp [hState, setCyc, wState, hP]
  -- 5. minus twice the previous count
  have s5 := sub2P_spec inp cap Pw hPos (by omega) cp _ σ4 h4P (by omega) hc4
  obtain ⟨v5, hv5⟩ : ∃ x, x = ((((0 + Wp) % Pw + c) % Pw) + 2 * cp * (Pw - 1)) % Pw := ⟨_, rfl⟩
  rw [← hv5] at s5
  have hv5lt : v5 < Pw := by rw [hv5]; exact Nat.mod_lt _ hPos
  obtain ⟨σ5, hσ5⟩ : ∃ τ : LState, τ = setCyc Pw v5 (σ4.setv rP 0) := ⟨_, rfl⟩
  rw [← hσ5] at s5
  -- 6. clear U
  have s6 := clear_spec inp cap rU (Pw - v5) σ5 (by rw [hσ5]; simp [setCyc]) (by rw [hσ5]; simp [setCyc]; omega)
  obtain ⟨σ6, hσ6⟩ : ∃ τ : LState, τ = σ5.setv rU 0 := ⟨_, rfl⟩
  rw [← hσ6] at s6
  have e6 : σ6 = (((((((σ.seth 1 (σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) + L)).setv rTP
      (σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) + L)).setv rC c).setv rW Wp).setv rV v5).setv rU 0).setv rP 0) := by
    rw [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
    rs_eq [hState, setCyc, wState, hTP, hC, hW, hV, hU]
  -- 7. the decision
  have s7 := decidePart_spec inp cap σ6 ⟨by rw [e6]; simp [hT], by rw [e6]; simp [hT1], by rw [e6]; simp [hT2]⟩
    (by rw [e6]; simpa using hF1) (by rw [e6]; simp [hMR]; omega) (by rw [e6]; simp; omega)
    (by rw [e6]; simp [hMR]; omega) (by rw [e6]; simp; omega) (by omega)
  -- 8. the count becomes the previous count
  have h7C : (decState σ6).val rC = c := by rw [e6]; unfold decState; split_ifs <;> simp
  have h7P : (decState σ6).val rP = 0 := by rw [e6]; unfold decState; split_ifs <;> simp
  have s8 := move_spec inp cap rC rP (by decide) c (decState σ6) h7C (by omega) (by rw [h7P, h7C]; omega)
  refine ⟨_, RExec.mono (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 (RExec.seq s6
    (RExec.seq s7 s8))))))) ?_, ?_⟩
  · have k1 : Wp * (7 * cap + 20) ≤ B * (7 * cap + 20) := Nat.mul_le_mul_right _ (by omega)
    have k3 : cp * (14 * cap + 22) ≤ L * (14 * cap + 22) := Nat.mul_le_mul_right _ hPL
    have k4 : 4 * (B * (7 * cap + 20) + L * (7 * cap + 50) + L * (14 * cap + 22)) ≤ cap * (21 * cap + 72) := by
      have e2 : B * (7 * cap + 20) ≤ B * (21 * cap + 72) := Nat.mul_le_mul_left _ (by omega)
      have e3 : (4 * B + 4 * L) * (21 * cap + 72) ≤ cap * (21 * cap + 72) := Nat.mul_le_mul_right _ (by omega)
      have e1 : 4 * (B * (21 * cap + 72) + L * (7 * cap + 50) + L * (14 * cap + 22)) =
          (4 * B + 4 * L) * (21 * cap + 72) := by ring
      omega
    have hPv : Pw - v5 ≤ Pw := Nat.sub_le _ _
    have hPB : Pw ≤ B := by omega
    have hc8 : 8 ≤ cap := by omega
    have hcc : 8 * cap ≤ cap * cap := Nat.mul_le_mul_right _ hc8
    have hB4 : 4 * B ≤ cap := by omega
    have hL4 : 4 * L ≤ cap := by omega
    have hWB : Wp ≤ B := by omega
    unfold bodyCost
    generalize Pw - v5 = d at hPv ⊢
    linarith [hcL, hcc, hB4, hL4, hWB, hPB, hPv, k1, k3, k4]
  · have h6 : ∀ r : Fin 15, r ≠ rTP → r ≠ rC → r ≠ rW → r ≠ rV → r ≠ rU → r ≠ rP → σ6.val r = σ.val r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [e6]
      simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
        Function.update_of_ne h5, Function.update_of_ne h6]
    have h6sh : σ6.sh = Function.update σ.sh 1 (σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) + L) := by rw [e6]; rfl
    have h6F : σ6.val rF = σ.val rF := h6 rF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h6S : σ6.val rS = σ.val rS := h6 rS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h6M : σ6.val rMR = M := by
      rw [h6 rMR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hMR]
    have h6V : σ6.val rV = v5 := by rw [e6]; simp
    have h6W : σ6.val rW = Wp := by rw [e6]; simp
    have h6TP : σ6.val rTP = σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) + L := by rw [e6]; simp
    have h6U : σ6.val rU = 0 := by rw [e6]; simp
    have hrl : (record J W row j).length = 1 + (Pw + 1) + (Wp + 1) + L := by
      rw [record_length, hj, hWp, hPw]; omega
    have hres : v5 = cyc Pw ((c : ℤ) + Wp - 2 * cp) := by rw [hv5, ← hPw]; exact resid_eq _ _ _ _ (pow_pos _)
    have hkeep := decState_keep σ6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [RState.setv_sh, decState_sh, h6sh, Function.update_self]
      rw [show σ.sh 1 + 1 + (Pw + 1) + (Wp + 1) + L = σ.sh 1 + (record J W row j).length by rw [hrl]; omega]
      exact drop_add_of_append hrest
    · simp only [RState.setv_val, RState.setv_sh, decState_sh, h6sh, Function.update_self]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rTP (by decide) (by decide) (by decide) (by decide), h6TP]
    · simp [decState_sh, h6sh, hs0]
    · simp [decState_sh, h6sh, hs2]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rMR (by decide) (by decide) (by decide) (by decide), h6M]
    · simp [h7P, h7C]
    · rw [hL]; exact hcL
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      by_cases hf : σ6.val rF ≠ 0
      · rw [(decState_failed σ6 hf).1, h6F]; exact hF1
      · by_cases hMt : σ6.val rMR < σ6.val rS
        · rw [(decState_over σ6 (by omega) hMt).1]
        · rw [(decState_arith σ6 (by omega) hMt).1]; split_ifs <;> omega
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      by_cases hf : σ6.val rF ≠ 0
      · rw [(decState_failed σ6 hf).2, h6S, hB]; exact hSB
      · by_cases hMt : σ6.val rMR < σ6.val rS
        · rw [(decState_over σ6 (by omega) hMt).2, h6S, hB]; exact hSB
        · rw [(decState_arith σ6 (by omega) hMt).2, h6S, h6V, h6W, hB]
          rw [h6M, h6S] at hMt
          omega
    · intro t ht
      simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      cases o with
      | none => simp [levelStep] at ht
      | some t0 =>
        obtain ⟨hF0, hS0⟩ := hsome t0 rfl
        simp only [levelStep] at ht
        by_cases hcond : t0 ≤ M ∧ Wp ≤ 2 * t0 + cyc (pow Wp) ((c : ℤ) + Wp - 2 * cp)
        · rw [if_pos hcond] at ht
          simp only [Option.some.injEq] at ht
          rw [hPw, ← hres] at hcond ht
          have hMt : ¬ σ6.val rMR < σ6.val rS := by rw [h6M, h6S, hS0]; omega
          obtain ⟨e1, e2⟩ := decState_arith σ6 (by rw [h6F, hF0]) hMt
          rw [e1, e2, h6S, h6V, h6W, hS0]
          refine ⟨?_, ?_⟩
          · rw [if_neg (by omega)]
          · omega
        · rw [if_neg hcond] at ht; cases ht
    · intro ht
      simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      cases o with
      | none =>
        have hF1' := hnone rfl
        rw [(decState_failed σ6 (by rw [h6F, hF1']; simp)).1, h6F, hF1']
      | some t0 =>
        obtain ⟨hF0, hS0⟩ := hsome t0 rfl
        simp only [levelStep] at ht
        by_cases hcond : t0 ≤ M ∧ Wp ≤ 2 * t0 + cyc (pow Wp) ((c : ℤ) + Wp - 2 * cp)
        · rw [if_pos hcond] at ht; cases ht
        · rw [hPw, ← hres] at hcond
          by_cases hMt : σ6.val rMR < σ6.val rS
          · rw [(decState_over σ6 (by rw [h6F, hF0]) hMt).1]
          · obtain ⟨e1, _⟩ := decState_arith σ6 (by rw [h6F, hF0]) hMt
            rw [e1, h6S, h6V, h6W, hS0]
            rw [h6M, h6S, hS0] at hMt
            rw [if_pos (by omega)]
    · simp
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), decState_W]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), decState_V]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rU (by decide) (by decide) (by decide) (by decide), h6U]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rT (by decide) (by decide) (by decide) (by decide),
        h6 rT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hT]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rR (by decide) (by decide) (by decide) (by decide),
        h6 rR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hR]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rSP (by decide) (by decide) (by decide) (by decide),
        h6 rSP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSP]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rX (by decide) (by decide) (by decide) (by decide),
        h6 rX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hX]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rT1 (by decide) (by decide) (by decide) (by decide),
        h6 rT1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hT1]
    · simp only [RState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hkeep rT2 (by decide) (by decide) (by decide) (by decide),
        h6 rT2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hT2]

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
