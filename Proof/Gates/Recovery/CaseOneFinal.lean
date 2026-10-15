import Proof.Gates.Recovery.CaseOneRun

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.CaseOneMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

/-- Compiled tape `j` goes to ambient tape `slotCaseOne j`: the streams `W, A, Q` (tapes `0, 2, 3`) to `0, 1, 2`, the cell
tape `1` to `3`, every other tape stays. -/
def slotCaseOne (T : ℕ) (hT : 4 ≤ T) (j : Fin T) : Fin T :=
  ⟨if j.val = 1 then 3 else if 2 ≤ j.val ∧ j.val ≤ 3 then j.val - 1 else j.val, by
    have := j.isLt; split_ifs <;> omega⟩

theorem slotCaseOne_val (T : ℕ) (hT : 4 ≤ T) (j : Fin T) :
    (slotCaseOne T hT j).val = if j.val = 1 then 3 else if 2 ≤ j.val ∧ j.val ≤ 3 then j.val - 1 else j.val := rfl

theorem slotCaseOne_inj (T : ℕ) (hT : 4 ≤ T) : Function.Injective (slotCaseOne T hT) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slotCaseOne_val, slotCaseOne_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sTape_val'' {ns nr : ℕ} (i : Fin (ns + 1)) :
    (sTape (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl

theorem coldBank_initCaseOne (tA : ℕ) (word addr : List Bool) (q : ℕ) (j : Fin (NS tA + 2 + 16)) :
    coldBank (initCaseOne tA word addr q) j =
      if j.val = 0 then word else if hj2 : 2 ≤ j.val ∧ j.val ≤ 3 then
        Recovery.threeWords word addr q ⟨j.val - 1, by omega⟩ else [] := by
  have hNS : 49 ≤ NS tA := by unfold NS; omega
  rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [coldBank_s]
    have hst : (initCaseOne tA word addr q).st i =
        if hi : i.val < 3 then Recovery.threeWords word addr q ⟨i.val, hi⟩ else [] := rfl
    rw [hst]
    have hv := sTape_val'' (nr := 16) i
    by_cases h0 : i.val = 0
    · rw [if_pos h0] at hv
      rw [dif_pos (show i.val < 3 by omega), if_pos hv]
      simp [Recovery.threeWords, h0]
    · rw [if_neg h0] at hv
      rw [if_neg (show ¬ (sTape (nr := 16) i).val = 0 by omega)]
      by_cases h3 : i.val < 3
      · rw [dif_pos h3, dif_pos (show 2 ≤ (sTape (nr := 16) i).val ∧ (sTape (nr := 16) i).val ≤ 3 by omega)]
        congr 1; apply Fin.ext; simp only []; omega
      · rw [dif_neg h3, dif_neg (show ¬ (2 ≤ (sTape (nr := 16) i).val ∧ (sTape (nr := 16) i).val ≤ 3) by omega)]
  · rw [coldBank_c]
    have hc : (cTape (ns := NS tA) (nr := 16)).val = 1 := rfl
    rw [if_neg (by omega), dif_neg (by omega)]
  · rw [coldBank_r]
    have : (rTape (ns := NS tA) (nr := 16) r).val = NS tA + 2 + r.val := rfl
    rw [if_neg (by omega), dif_neg (by omega)]

theorem bank_slotCaseOne (tA : ℕ) (word addr : List Bool) (q : ℕ) (j : Fin (NS tA + 2 + 16 + 1)) :
    Recovery.oneInput (NS tA + 2 + 16 + 1) word addr q (slotCaseOne _ (by unfold NS; omega) j) =
      Fin.addCases (coldBank (initCaseOne tA word addr q)) (fun _ => []) j := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, coldBank_initCaseOne]
    unfold Recovery.oneInput
    have hs := slotCaseOne_val (NS tA + 2 + 16 + 1) (by unfold NS; omega) (Fin.castAdd 1 j)
    simp only [Fin.val_castAdd] at hs
    by_cases h0 : j.val = 0
    · rw [dif_pos (by rw [hs]; simp [h0]), if_pos h0]
      simp only [hs, h0]; rfl
    · by_cases h1 : j.val = 1
      · rw [dif_neg (by rw [hs]; simp [h1]), if_neg h0, dif_neg (by omega)]
      · by_cases h23 : 2 ≤ j.val ∧ j.val ≤ 3
        · rw [dif_pos (by rw [hs]; simp [h1, h23]; omega), if_neg h0, dif_pos h23]
          congr 1; apply Fin.ext; simp only [hs, h1, h23]; simp
        · rw [dif_neg (by rw [hs]; simp [h1, h23]; omega), if_neg h0, dif_neg h23]
  · rw [Fin.addCases_right]
    unfold Recovery.oneInput
    have hs := slotCaseOne_val (NS tA + 2 + 16 + 1) (by unfold NS; omega) (Fin.natAdd (NS tA + 2 + 16) j)
    simp only [Fin.val_natAdd] at hs
    rw [dif_neg (by rw [hs]; have := j.isLt; unfold NS; split_ifs <;> omega)]

/-- The fuel bound. -/
theorem caseOneCost_le {c d : ℕ} (amplifier : RepairSource.OrdinaryScheduleAmplifier c d) (q n : ℕ) (hqn : q ≤ n) :
    2 * caseOneCost amplifier q n + 2 ≤ 140000 * (2 ^ n + 1) ^ (2 * max 1 amplifier.constructionExponent) := by
  have hE2 : 2 ≤ 2 * max 1 amplifier.constructionExponent := by
    have := Nat.le_max_left 1 amplifier.constructionExponent; omega
  have hV1 : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hVE : (2 ^ n + 1) ^ 2 ≤ (2 ^ n + 1) ^ (2 * max 1 amplifier.constructionExponent) :=
    Nat.pow_le_pow_right hV1 hE2
  have hV2 : 1 ≤ (2 ^ n + 1) ^ 2 := Nat.one_le_pow _ _ hV1
  have hn2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hq1 : q + 1 ≤ 2 ^ n + 1 := by omega
  have hq2 : 2 ^ q + 1 ≤ 2 ^ n + 1 := by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hqn; omega
  have hb : buildCost q ≤ 200 * (2 ^ n + 1) ^ 2 := by
    unfold buildCost
    rw [sq, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hq1 hq2)
  unfold caseOneCost
  omega

theorem caseOneRuns : Recovery.CaseOneRuns := by
  intro c d amplifier
  set T := tA amplifier with hTd
  have hT4 : 4 ≤ NS T + 2 + 16 + 1 := by unfold NS; omega
  refine ⟨NS T + 2 + 16 + 1, _,
    RecoveryFocus.machine (slotCaseOne _ hT4) (Rewind.machine (caseOneW amplifier).compile),
    ⟨49 + T, by unfold NS; omega⟩, by show 3 ≤ 49 + T; omega, 140000, 2 * max 1 amplifier.constructionExponent, ?_⟩
  intro a q w rest n point hq hqn hn
  obtain ⟨τ, n', e, hn', hout⟩ := caseOne_exec amplifier a q w rest n point hq hqn hn (buildCap a q) le_rfl
  obtain ⟨out, hrun, hst⟩ := WXExec.readyRewound e (fun _ => rfl) (fun _ => rfl) rfl
  have hf := ClockJoin.ReadyRun.focus hrun (slotCaseOne _ hT4) (slotCaseOne_inj _ hT4) _
    (bank_slotCaseOne T _ _ q)
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ hf ?_, ?_⟩
  · have h1 := caseOneCost_le amplifier q n hqn
    omega
  · have hslot : (⟨49 + T, by unfold NS; omega⟩ : Fin (NS T + 2 + 16 + 1)) =
        slotCaseOne _ hT4 ((sTape (nr := 16) (bV T 44)).castAdd 1) := by
      apply Fin.ext
      rw [slotCaseOne_val]
      have hsv : ((sTape (nr := 16) (bV T 44)).castAdd 1 : Fin (NS T + 2 + 16 + 1)).val = 49 + T := by
        simp only [Fin.val_castAdd]
        rw [sTape_val'', bV_val, if_neg (by omega)]
        show 4 + T + 44 + 1 = 49 + T
        ring
      rw [hsv, if_neg (by omega), if_neg (by omega)]
    rw [hslot, RecoveryRootRound.install_slot _ (slotCaseOne_inj _ hT4), hst, hout]

end NearCubicGates.Close.Recovery.CaseOneMachine
