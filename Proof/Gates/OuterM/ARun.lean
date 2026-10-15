import Proof.Gates.OuterM.ARunCost
import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

theorem readyRun_mono {t s : ℕ} {p : Machine t s} {f f' : ℕ} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p f input out) (hf : f ≤ f') : ClockJoin.ReadyRun p f' input out := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, ht, hh, hs.trans hf⟩
  have := run_moreFuel p f (f' - f) input r hr
  rwa [Nat.add_sub_of_le hf] at this

theorem natBitLength_le_bits (v : ℕ) : natBitLength v ≤ v.bits.length + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [natBitLength]
  · have h1 : v < 2 ^ v.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self v
    have h2 : Nat.log 2 v < v.bits.length := Nat.log_lt_of_lt_pow (by omega) h1
    unfold natBitLength; omega

/-- The A-run's start: the raw description on stream `0`, `1^ν` on stream `1`, every other stream empty. -/
def startA (ns : ℕ) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : WState ns nrA :=
  ⟨fun _ => 0, fun i => if i.val = 0 then PCPPNative.descriptor B else if i.val = 1 then List.replicate ν true else [],
    fun _ => 0, false⟩

section
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G)

/-- The time program: lem:succinct-verifier (i)'s word function, rewound. -/
noncomputable def timeProg : Program := Rewind.program SV.timeWord.program

/-- The imported constructor (imp:short-pcp applied to `𝒱_G`), rewound. -/
noncomputable def consProg : Program := Rewind.program (Outer.alg mw SV).constructor.program

/-- The A-run's word program. -/
noncomputable def aProg : WMX (nsL (timeProg SV) (consProg mw SV)) nrA :=
  .seq (phaseA (five_le_nsL _ _) G) (.seq (phaseB (timeProg SV) (consProg mw SV))
    (.seq (phaseC (timeProg SV) (consProg mw SV) SV.timeExp SV.timeCoefficient) (phaseD (timeProg SV) (consProg mw SV))))

/-- The A-run's register capacity. -/
noncomputable def capR (ν : ℕ) : ℕ :=
  capA G ν + (2 * ν + 2) + capC SV.timeExp SV.timeCoefficient ν + 4 * Outer.instLength G ν +
    4 * bmax SV.timeExp SV.timeCoefficient ν + 8

theorem time_bits_le (ν : ℕ) :
    (SV.T (Outer.instLength G ν)).bits.length ≤ bmax SV.timeExp SV.timeCoefficient ν := by
  obtain ⟨outT, hT, hTout⟩ := CheckedPCPP.wordFunction_ready SV.timeWord ν
  have hlen := CheckedPCPP.Dock.ready_len hT (2 * ν + 1) (fun i => by
    rw [CheckedPCPP.program_inputTapes]
    split_ifs
    · rw [RepairOrdinary.frame_length]; simp
    · simp) (Rewind.program SV.timeWord.program).outputTape
  rw [hTout] at hlen
  have : (ν + 1) ^ SV.timeExp * (2 * SV.timeCoefficient) = 2 * (SV.timeCoefficient * (ν + 1) ^ SV.timeExp) := by ring
  unfold bmax; omega

/-- **The A-run's run.** -/
theorem aProg_run (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) :
    ∃ τ, WXExec (capR SV ν) (aProg mw SV) (startA _ ν B) τ
        (costT G SV.timeExp SV.timeCoefficient (Outer.alg mw SV).coefficient (Outer.alg mw SV).constructionExp ν
          (Outer.instLength G ν) (walkEnd (cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν + 1)) 0)
          (SV.T (Outer.instLength G ν)).bits.length (natBitLength (SV.T (Outer.instLength G ν)))) ∧
      τ.st ⟨0, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩ = PCPPNative.descriptor B ∧
      τ.st ⟨1, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩ = List.replicate ν true ∧
      τ.st ⟨2, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩ = [decide (Outer.SrcFits G ν B)] ∧
      τ.st (sW (timeProg SV) (consProg mw SV)) = (Outer.outC mw SV ν B).word := by
  set pT := timeProg SV with hpT
  set pA := consProg mw SV with hpA
  have hns := five_le_nsL pT pA
  set L := Outer.instLength G ν with hL
  set cap := capR SV ν with hcap
  set σ0 := startA (nsL pT pA) ν B with hσ0
  -- phase A
  obtain ⟨τA, eA, hAD, hAN, hAF, hAS, hASh, hA2, hA3, hA4, hA10, hA20, hA5, hA6, hA7, hA8, hAo⟩ :=
    phaseA_spec hns G ν B cap σ0 (by simp [σ0, startA]) (by simp [σ0, startA]) (by simp [σ0, startA])
      (by simp [σ0, startA]) (by simp [σ0, startA]) (by simp [σ0, startA]) (by simp [σ0, startA])
      (by simp [σ0, startA]) (by simp [σ0, startA]) (by rw [hcap]; unfold capR; omega)
  have hσ0st : ∀ i : Fin (nsL pT pA + 1), 3 ≤ i.val → σ0.st i = [] ∧ σ0.sh i = 0 := by
    intro i hi; refine ⟨?_, rfl⟩
    show (if i.val = 0 then _ else if i.val = 1 then _ else []) = []
    rw [if_neg (by omega), if_neg (by omega)]
  -- phase B
  obtain ⟨outT, hT, hTout⟩ := CheckedPCPP.wordFunction_ready SV.timeWord ν
  obtain ⟨τB, eB, hBst, hBsh, hBval, hB3, hB20, hBo⟩ := phaseB_spec pT pA ν _ outT hT cap τA
    (by have := hAo (sTI pT pA) (by simp [sTI]); rw [this.1]; exact (hσ0st _ (by simp [sTI])).1)
    (by have := hAo (sTI pT pA) (by simp [sTI]); rw [this.2]; exact (hσ0st _ (by simp [sTI])).2)
    (fun j hj => by
      have hv : 6 ≤ (tmapT pT pA j).val := by rw [tmapT_val, if_neg hj]; omega
      have := hAo (tmapT pT pA j) (by omega)
      rw [this.1, this.2]; exact hσ0st _ (by omega))
    hA3 (hA20 20 (by decide)) (by rw [hcap]; unfold capR; omega)
  -- the time word's length
  have hTB : τB.st (sTB pT pA) = (SV.T L).bits := by rw [sTB, hBst]; exact hTout
  have hbits : (SV.T L).bits.length ≤ bmax SV.timeExp SV.timeCoefficient ν := time_bits_le SV ν
  -- phase C
  obtain ⟨τC, eC, hC21, hCst, hCsh, hCo, hCval⟩ := phaseC_spec pT pA SV.timeExp SV.timeCoefficient ν (SV.T L) cap τB
    hTB (by rw [sTB, hBsh]) (by rw [hBval 2 (by decide) (by decide), hA2])
    (by rw [hBval 4 (by decide) (by decide), hA4])
    ⟨by rw [hBval 6 (by decide) (by decide), hA6], by rw [hBval 7 (by decide) (by decide), hA7],
      by rw [hBval 8 (by decide) (by decide), hA8]⟩
    (fun r hr1 hr2 => by
      rw [hBval r (fun h => by rw [h] at hr1; exact absurd hr1 (by decide))
        (fun h => by rw [h] at hr1; exact absurd hr1 (by decide))]
      exact hA20 r (by omega))
    hbits (by rw [hcap]; unfold capR; omega)
  -- phase D
  obtain ⟨outA, hAr, hAout⟩ := CheckedPCPP.wordFunction_ready (Outer.alg mw SV).constructor (Outer.srcInput G ν B)
  have hinA : (Outer.srcInput G ν B).1 = L := rfl
  have hAr' : ClockJoin.ReadyRun pA.machine (2 * ((Outer.alg mw SV).coefficient *
      (L + natBitLength (SV.T L) + 1) ^ (Outer.alg mw SV).constructionExp) + 2)
      (pA.inputTapes (RepairOrdinary.frame (cellsOf (PCPPNative.descriptor B) L) ++
        RepairOrdinary.frame (SV.T L).bits)) outA := by
    have h1 := hAr
    simp only [Outer.srcInput] at h1
    rw [ofFn_srcBits_cells] at h1
    exact h1
  -- the streams phase D reads
  have hB_S : τB.st (sSL pT pA) = τA.st (sSL pT pA) ∧ τB.sh (sSL pT pA) = τA.sh (sSL pT pA) := by
    apply hBo
    intro j h
    have := congrArg Fin.val h; rw [tmapT_val] at this; simp [sSL] at this; split_ifs at this <;> omega
  have hS3 : sSL pT pA ≠ sTB pT pA := Ne.symm (sTB_ne_sSL pT pA)
  have hB_CI : τB.st (sCI pT pA) = τA.st (sCI pT pA) ∧ τB.sh (sCI pT pA) = τA.sh (sCI pT pA) := by
    apply hBo
    intro j h
    have := congrArg Fin.val h; rw [tmapT_val] at this; simp [sCI] at this; split_ifs at this <;> omega
  have hCI3 : sCI pT pA ≠ sTB pT pA := Ne.symm (sTB_ne_sCI pT pA)
  have hA_CI := hAo (sCI pT pA) (by simp [sCI])
  have hσ_CI := hσ0st (sCI pT pA) (by simp [sCI])
  obtain ⟨τD, eD, hDst, hDlow⟩ := phaseD_spec pT pA L (PCPPNative.descriptor B) (SV.T L).bits _ outA hAr' cap τC
    (by rw [(hCo _ hS3).1, hB_S.1]; exact hAS) (by rw [(hCo _ hS3).2, hB_S.2]; exact hASh)
    (by rw [hCval 10 (by decide), hBval 10 (by decide) (by decide), hA10])
    hCst hCsh hC21
    (by rw [hCval 26 (by decide), hBval 26 (by decide) (by decide)]; exact hA20 26 (by decide))
    (by rw [(hCo _ hCI3).1, hB_CI.1, hA_CI.1]; exact hσ_CI.1)
    (by rw [(hCo _ hCI3).2, hB_CI.2, hA_CI.2]; exact hσ_CI.2)
    (fun j hj => by
      have hv : 5 + pT.tapeCount ≤ (tmapA pT pA j).val := by rw [tmapA_val, if_neg hj]; omega
      have hneT : tmapA pT pA j ≠ sTB pT pA := fun h => by
        have := congrArg Fin.val h; rw [sTB_val] at this; have := pT.outputTape.isLt; omega
      have hnot : ∀ j', tmapT pT pA j' ≠ tmapA pT pA j := fun j' h => by
        have hj' := j'.isLt; have := congrArg Fin.val h; rw [tmapT_val] at this; split_ifs at this <;> omega
      rw [(hCo _ hneT).1, (hCo _ hneT).2, (hBo _ hnot).1, (hBo _ hnot).2, (hAo _ (by omega)).1, (hAo _ (by omega)).2]
      exact hσ0st _ (by omega))
    (by rw [hcap]; unfold capR; omega)
  refine ⟨τD, WXExec.seq' _ eA (WXExec.seq' _ eB (WXExec.seq' _ eC eD le_rfl) le_rfl) (by unfold costT; exact le_rfl),
    ?_, ?_, ?_, ?_⟩
  · have h0 : (⟨0, by omega⟩ : Fin (nsL pT pA + 1)) ≠ sTB pT pA := fun h => by
      have := congrArg Fin.val h; rw [sTB_val] at this; change 0 = _ at this; omega
    rw [hDlow _ (by simp), (hCo _ h0).1, (hBo _ (fun j h => by
      have := congrArg Fin.val h; rw [tmapT_val] at this; simp at this; split_ifs at this <;> omega)).1]
    exact hAD
  · have h0 : (⟨1, by omega⟩ : Fin (nsL pT pA + 1)) ≠ sTB pT pA := fun h => by
      have := congrArg Fin.val h; rw [sTB_val] at this; simp at this; omega
    rw [hDlow _ (by simp), (hCo _ h0).1, (hBo _ (fun j h => by
      have := congrArg Fin.val h; rw [tmapT_val] at this; simp at this; split_ifs at this <;> omega)).1]
    exact hAN
  · have h0 : (⟨2, by omega⟩ : Fin (nsL pT pA + 1)) ≠ sTB pT pA := fun h => by
      have := congrArg Fin.val h; rw [sTB_val] at this; simp at this; omega
    rw [hDlow _ (by simp), (hCo _ h0).1, (hBo _ (fun j h => by
      have := congrArg Fin.val h; rw [tmapT_val] at this; simp at this; split_ifs at this <;> omega)).1]
    exact hAF
  · rw [sW, hDst]
    exact hAout

end

/-! ## The ready run -/

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in
/-- The cold bank of the start is the A-run's input bank. -/
theorem bank_eq (ns : ℕ) (hns : 5 ≤ ns) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) :
    Fin.addCases (motive := fun _ => List Bool) (CheckedPCPP.coldBank (startA ns ν B)) (fun _ : Fin 1 => []) =
      aBank (Fin.castAdd 1 (sTape (nr := nrA) (⟨0, by omega⟩ : Fin (ns + 1))))
        (Fin.castAdd 1 (sTape (nr := nrA) (⟨1, by omega⟩ : Fin (ns + 1)))) ν B := by
  funext j
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left]
    unfold aBank
    rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [CheckedPCPP.coldBank_s]
      simp only [startA, Fin.ext_iff, Fin.val_castAdd, sTape_val]
      by_cases h0 : i.val = 0
      · simp [h0]
      · by_cases h1 : i.val = 1
        · simp [h1]
        · rw [if_neg h0, if_neg h1, if_neg (by simp [h0]), if_neg (by simp [h0]; omega)]
    · rw [CheckedPCPP.coldBank_c]
      simp [Fin.ext_iff, Fin.val_castAdd, sTape_val, cTape_val]
    · rw [CheckedPCPP.coldBank_r]
      simp only [Fin.ext_iff, Fin.val_castAdd, sTape_val, rTape_val]
      rw [if_neg (by simp <;> omega), if_neg (by simp <;> omega)]
  · rw [Fin.addCases_right]
    unfold aBank
    simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, sTape_val]
    rw [if_neg (by simp <;> omega), if_neg (by simp <;> omega)]

section
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G)

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in

noncomputable def aRun : ARun mw SV where
  t := nsL (timeProg SV) (consProg mw SV) + 2 + nrA + 1
  st := (aProg mw SV).size + 2
  M := Rewind.machine (aProg mw SV).compile
  dIn := Fin.castAdd 1 (sTape (nr := nrA) ⟨0, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩)
  nIn := Fin.castAdd 1 (sTape (nr := nrA) ⟨1, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩)
  fOut := Fin.castAdd 1 (sTape (nr := nrA) ⟨2, by have := five_le_nsL (timeProg SV) (consProg mw SV); omega⟩)
  wOut := Fin.castAdd 1 (sTape (nr := nrA) (sW (timeProg SV) (consProg mw SV)))
  nodup := by
    have hw := sW_val (timeProg SV) (consProg mw SV)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      Fin.ext_iff, Fin.val_castAdd, sTape_val, hw]
    simp
    omega
  K := aK G SV.timeExp SV.timeCoefficient (Outer.alg mw SV).coefficient (Outer.alg mw SV).constructionExp
  e := aE G SV.timeExp (Outer.alg mw SV).constructionExp
  run := fun ν m B => by
    obtain ⟨τ, h, h0, h1, h2, hw⟩ := aProg_run mw SV ν B
    obtain ⟨out, hr, hout⟩ := CheckedPCPP.WXExec.readyRewound h (fun _ => rfl) (fun _ => rfl) rfl
    rw [bank_eq _ (five_le_nsL (timeProg SV) (consProg mw SV)) ν B] at hr
    refine ⟨out, readyRun_mono hr ?_, by rw [hout, h0], by rw [hout, h1], by rw [hout, h2], by rw [hout, hw]⟩
    apply costT_le
    · unfold Outer.instLength; exact Nat.pow_le_pow_left (by omega) _
    · have := walkEnd_le (cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν + 1)) 0
      have hl : (cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν + 1)).length = Outer.instLength G ν + 1 := by
        simp [cellsOf]
      rw [hl] at this; omega
    · exact time_bits_le SV ν
    · exact natBitLength_le_bits _

end

end NearCubicGates.Close.OuterM
