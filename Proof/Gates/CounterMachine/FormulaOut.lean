import Proof.Gates.CounterMachine.FormulaLink
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section Out
variable (S O PFX : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

/-- Rewind stream `I` by the value of `F 7` (scratch `F 19`, `F 8`). -/
def rew7 (I : Fin (ns + 1)) : WM ns nr := .seq (copyR (F 7) (F 19) (F 8)) (WM.rewind I (F 19))

theorem rew7_spec (I : Fin (ns + 1)) (σ : WState ns nr) (h8 : σ.val (F 8) = 0) (h19 : σ.val (F 19) = 0)
    (hle : σ.sh I ≤ σ.val (F 7)) (hcap : σ.val (F 7) ≤ cap) :
    WExec cap (rew7 F I) σ (σ.seth I 0) (23 * σ.val (F 7) + 6) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have e1 := copyR_spec cap (v := F 7) (d := F 19) (t := F 8) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h8 (by rw [h19]; omega)
  rw [h19, Nat.zero_add] at e1
  have e2 := wrewind_spec cap I (F 19) (σ.val (F 7)) (σ.setv (F 19) (σ.val (F 7))) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  rw [wsetv_setv, show (0 : ℕ) = σ.val (F 19) from h19.symm, wsetv_same]
  simp only [WState.setv_sh]; rw [show σ.sh I - σ.val (F 7) = 0 by omega, ← h19]

/-- The request word from the prefix stream and the scratch tokens. -/
def formulaOut : WM ns nr :=
  .seq (.wr S false)
  (.seq (rew7 F S)
  (.seq (.whs PFX (copyPairW PFX O (F 7)))
  (.seq (printReg O (Rf F) (F 16))
  (.seq (copyFrameW S O (F 7))
  (.seq (rew7 F O) (.seq (rew7 F PFX) (.seq (rew7 F S) (.seq (WM.clear (F 16)) (WM.clear (F 7))))))))))

theorem formulaOut_spec (hSO : S ≠ O) (hSP : S ≠ PFX) (hOP : O ≠ PFX) (σ : WState ns nr) (h : TRest S F σ)
    (w pw rest : List Bool) (cnt : ℕ) (hS : σ.st S = marks w) (hSh : σ.sh S = (marks w).length)
    (h7 : σ.val (F 7) = (marks w).length) (h16 : σ.val (F 16) = cnt) (hP : σ.st PFX = RepairOrdinary.frame pw ++ rest)
    (hPh : σ.sh PFX = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hcap : 20 * (pw.length + w.length + cnt + 1) ≤ cap) :
    WExec cap (formulaOut S O PFX F) σ
      (((((σ.sets O (RepairOrdinary.frame (pw ++ natWord cnt ++ w))).sets S (marks w ++ [false])).seth S 0).setv
        (F 16) 0).setv (F 7) 0) (5000 * (pw.length + w.length + cnt + 1) ^ 2) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have hz := h.zero S F
  have hml : ∀ x : List Bool, (marks x).length = 2 * x.length := marks_length
  have hfl : ∀ x : List Bool, (RepairOrdinary.frame x).length = 2 * x.length + 1 := fun x => by
    rw [frame_eq_marks, List.length_append, hml]; simp
  have hnc : (natWord cnt).length ≤ 2 * cnt + 3 := by rw [natWord_length']; have := nbl_le cnt; omega
  -- 1. close `S` with a blank
  have s1 := WExec.wr (cap := cap) S false σ
  rw [hSh, ← hS, writeTapeBit_end'] at s1
  set σ1 := σ.sets S (σ.st S ++ [false]) with hσ1
  -- 2. rewind `S`
  have s2 := rew7_spec cap F S σ1 (by simp [hσ1]; exact hz 8 (by decide)) (by simp [hσ1]; exact hz 19 (by decide))
    (by simp [hσ1, hSh, h7]) (by simp [hσ1, h7, hml]; omega)
  simp only [hσ1, WState.sets_val] at s2
  rw [h7] at s2
  set σ2 := σ1.seth S 0 with hσ2
  -- 3. the prefix
  have s3 := copyFrame_loop cap PFX O hOP.symm (F 7) rest pw [] σ2 (by simp [hσ2, hσ1, Function.update_of_ne hSP.symm, hP])
    (by simp [hσ2, hσ1, Function.update_of_ne hSP.symm, hPh]) (by simp [hσ2, hσ1, Function.update_of_ne hSO.symm, hO, hOh])
    (by simp [hσ2, hσ1, h7, hml]; omega)
  simp only [List.length_nil, Nat.zero_add] at s3
  set σ3 := (appendO σ2 O (F 7) (marks pw)).seth PFX (2 * pw.length) with hσ3
  -- 4. the token count
  have hpr3 : PrRest O (Rf F) σ3 := ⟨by simp [hσ3, appendO, Function.update_of_ne hOP, hσ2, hσ1,
      Function.update_of_ne hSO.symm, hO, hOh], fun i hi => by
    rw [Rf_apply]
    have k : Fin.castLE (by norm_num : 16 ≤ 24) i ≠ 7 := by revert i; decide
    simp [hσ3, appendO, Function.update_of_ne (hne k), hσ2, hσ1]
    exact hz _ (by revert i; decide)⟩
  have v3_7 : σ3.val (F 7) = 2 * w.length + 2 * pw.length := by
    simp only [hσ3, WState.seth_val, appendO, WState.setv_val, Function.update_self, hσ2, hσ1, WState.sets_val, h7, hml]
  have v3 : ∀ r, r ≠ F 7 → σ3.val r = σ.val r := fun r hr => by
    simp [hσ3, appendO, Function.update_of_ne hr, hσ2, hσ1]
  have s4 := printReg_spec cap O (Rf F) (F 16) (fun i _ => by rw [Rf_apply]; exact hne (by revert i; decide)) σ3 hpr3
    (by rw [show Rf F 7 = F 7 from rfl, v3 (F 16) (hne (by decide)), h16, v3_7]; omega)
  rw [v3 (F 16) (hne (by decide)), h16] at s4
  set σ4 := appendO σ3 O (Rf F 7) (marks (natWord cnt)) with hσ4
  -- 5. the tokens
  have s5 := copyFrameW_spec cap S O hSO (F 7) w [] σ4
    (by simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hSO, Function.update_of_ne hSP, hS, frame_eq_marks])
    (by simp [hσ4, hσ3, hσ2, appendO, Function.update_of_ne hSO, Function.update_of_ne hSP])
    (by simp [hσ4, appendO, hpr3.out])
    (by have : σ4.val (F 7) = 2 * w.length + 2 * pw.length + 2 * (natWord cnt).length := by
          simp only [hσ4, appendO, show Rf F 7 = F 7 from rfl, WState.setv_val, Function.update_self, WState.seth_val,
            WState.sets_val, v3_7, hml]
        rw [this]; omega)
  set σ5 := (appendO σ4 O (F 7) (RepairOrdinary.frame w)).seth S (2 * w.length) with hσ5
  have v5_7 : σ5.val (F 7) = 2 * w.length + 2 * pw.length + 2 * (natWord cnt).length + (2 * w.length + 1) := by
    simp [hσ5, hσ4, hσ3, appendO, show Rf F 7 = F 7 from rfl, hσ2, hσ1, h7, hml, hfl]
  have v5 : ∀ r, r ≠ F 7 → σ5.val r = σ.val r := fun r hr => by
    simp [hσ5, hσ4, appendO, show Rf F 7 = F 7 from rfl, Function.update_of_ne hr]; exact v3 r hr
  have hO5 : σ5.st O = RepairOrdinary.frame (pw ++ natWord cnt ++ w) := by
    simp [hσ5, hσ4, hσ3, appendO, show Rf F 7 = F 7 from rfl, Function.update_of_ne hOP, hσ2, hσ1,
      Function.update_of_ne hSO.symm, hO, frame_eq_marks, marksApp]
  have hOh5 : σ5.sh O = (RepairOrdinary.frame (pw ++ natWord cnt ++ w)).length := by
    simp [hσ5, hσ4, hσ3, appendO, show Rf F 7 = F 7 from rfl, Function.update_of_ne hOP, Function.update_of_ne hSO.symm,
      hσ2, hσ1, hOh, hfl, hml]; ring
  have hP5 : σ5.sh PFX = 2 * pw.length := by
    simp [hσ5, Function.update_of_ne hSP.symm, hσ4, appendO, Function.update_of_ne hOP.symm, hσ3]
  have hS5 : σ5.sh S = 2 * w.length := by simp [hσ5]
  -- 6.–8. rewind `O`, `PFX`, `S`
  have s6 := rew7_spec cap F O σ5 (by rw [v5 _ (hne (by decide))]; exact hz 8 (by decide))
    (by rw [v5 _ (hne (by decide))]; exact hz 19 (by decide)) (by rw [hOh5, v5_7, hfl]; simp; omega)
    (by rw [v5_7]; omega)
  rw [v5_7] at s6
  have s7 := rew7_spec cap F PFX (σ5.seth O 0) (by simp; rw [v5 _ (hne (by decide))]; exact hz 8 (by decide))
    (by simp; rw [v5 _ (hne (by decide))]; exact hz 19 (by decide))
    (by simp only [WState.seth_sh, WState.seth_val, Function.update_of_ne hOP.symm]; rw [hP5, v5_7]; omega)
    (by simp; rw [v5_7]; omega)
  simp only [WState.seth_val] at s7
  rw [v5_7] at s7
  have s8 := rew7_spec cap F S ((σ5.seth O 0).seth PFX 0) (by simp; rw [v5 _ (hne (by decide))]; exact hz 8 (by decide))
    (by simp; rw [v5 _ (hne (by decide))]; exact hz 19 (by decide))
    (by simp only [WState.seth_sh, WState.seth_val, Function.update_of_ne hSP, Function.update_of_ne hSO]
        rw [hS5, v5_7]; omega)
    (by simp; rw [v5_7]; omega)
  simp only [WState.seth_val] at s8
  rw [v5_7] at s8
  -- 9.–10. clear the count and the position
  have s9 := wclear_spec cap (F 16) cnt (((σ5.seth O 0).seth PFX 0).seth S 0)
    (by simp; rw [v5 _ (hne (by decide)), h16]) (by simp; rw [v5 _ (hne (by decide)), h16]; omega)
  have s10 := wclear_spec cap (F 7) _ ((((σ5.seth O 0).seth PFX 0).seth S 0).setv (F 16) 0)
    (by simp [Function.update_of_ne (hne (show (7 : Fin 24) ≠ 16 by decide))]; exact v5_7) (by
      simp [Function.update_of_ne (hne (show (7 : Fin 24) ≠ 16 by decide))]; rw [v5_7]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 s10))))))))) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases jS : j = S
      · subst jS; simp [Function.update_of_ne hSO, Function.update_of_ne hSP]
      · by_cases jP : j = PFX
        · subst jP; simp [Function.update_of_ne jS, Function.update_of_ne hOP.symm, hPh]
        · by_cases jO : j = O
          · subst jO; simp [Function.update_of_ne jS, Function.update_of_ne jP, hOh]
          · simp [Function.update_of_ne jS, Function.update_of_ne jP, Function.update_of_ne jO, hσ5, hσ4, hσ3, hσ2,
              hσ1, appendO]
    · funext j
      by_cases jO : j = O
      · subst jO; rw [← hO5]; simp [Function.update_of_ne hSO.symm]
      · by_cases jS : j = S
        · subst jS
          simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hSO, Function.update_of_ne hSP, hS]
        · simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne jO, Function.update_of_ne jS]
    · funext r
      by_cases r7 : r = F 7
      · subst r7; simp
      · by_cases r16 : r = F 16
        · subst r16; simp [Function.update_of_ne r7]
        · simp [Function.update_of_ne r7, Function.update_of_ne r16]; exact v5 r r7
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO]
  · have hp := printCost_le cnt (pw.length + w.length + cnt) (by omega)
    have h1 : 1 ≤ (pw.length + w.length + cnt + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hL : pw.length + w.length + cnt + 1 ≤ (pw.length + w.length + cnt + 1) ^ 2 := by nlinarith
    rw [hml]
    nlinarith

/-- **A whole request word**: any counted token printer `P` (ending in `emitT σ ts` from the empty scratch stream),
then `formulaOut`: the output stream holds `frame (pw ++ natWord |ts| ++ words of ts)`. -/
theorem formulaReq_spec (hSO : S ≠ O) (hSP : S ≠ PFX) (hOP : O ≠ PFX) (P : WM ns nr) (ts : List Tok) (cP : ℕ)
    (σ : WState ns nr) (h : TRest S F σ) (hP : WExec cap P σ (emitT S F σ ts) cP)
    (hS : σ.st S = []) (hSh : σ.sh S = 0) (h7 : σ.val (F 7) = 0) (h16 : σ.val (F 16) = 0)
    (pw rest : List Bool) (hPF : σ.st PFX = RepairOrdinary.frame pw ++ rest) (hPh : σ.sh PFX = 0)
    (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hcap : 20 * (pw.length + (ts.flatMap tokWord).length + ts.length + 1) ≤ cap) :
    ∃ τ, WExec cap (.seq P (formulaOut S O PFX F)) σ τ (cP + 1 + 5000 * (pw.length + (ts.flatMap tokWord).length +
        ts.length + 1) ^ 2) ∧
      τ.st O = RepairOrdinary.frame (pw ++ natWord ts.length ++ ts.flatMap tokWord) ∧ τ.sh O = 0 ∧
      τ.st S = marks (ts.flatMap tokWord) ++ [false] ∧ τ.sh S = 0 ∧ τ.sh PFX = 0 ∧
      (∀ X, X ≠ O → X ≠ S → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧ (∀ r, τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  set w := ts.flatMap tokWord with hw
  set E := emitT S F σ ts with hE
  have hES : E.st S = marks w := by simp [hE, emitT, appendO, hS, hw]
  have hESh : E.sh S = (marks w).length := by simp [hE, emitT, appendO, hSh, hw, marks_length]
  have hE7 : E.val (F 7) = (marks w).length := by
    rw [hE, emitT_val7, h7, marks_length, hw, Nat.zero_add]
  have hE16 : E.val (F 16) = ts.length := by rw [hE, emitT_val16, h16]; simp
  have e2 := formulaOut_spec cap S O PFX F hSO hSP hOP E (h.emitT S F ts) w pw rest ts.length hES hESh hE7 hE16
    (by rw [hE, emitT_st_ne S F PFX hSP.symm, hPF]) (by rw [hE, emitT_sh_ne S F PFX hSP.symm, hPh])
    (by rw [hE, emitT_st_ne S F O hSO.symm, hO]) (by rw [hE, emitT_sh_ne S F O hSO.symm, hOh]) hcap
  refine ⟨_, WExec.seq hP e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne hSO.symm]
  · simp [Function.update_of_ne hSO.symm, hE, emitT, appendO, Function.update_of_ne hSO.symm, hOh]
  · simp
  · simp
  · simp [Function.update_of_ne hSP.symm, Function.update_of_ne hOP.symm, hE, emitT, appendO, hPh]
  · intro X hXO hXS
    simp [Function.update_of_ne hXO, Function.update_of_ne hXS, hE, emitT, appendO]
  · intro r
    by_cases r7 : r = F 7
    · subst r7; simp; exact h7.symm
    · by_cases r16 : r = F 16
      · subst r16; simp [Function.update_of_ne r7]; exact h16.symm
      · simp [Function.update_of_ne r7, Function.update_of_ne r16, hE, emitT, appendO]
  · simp [hE, emitT, appendO]

end Out

end NearCubicGates.Close.CounterMachine
