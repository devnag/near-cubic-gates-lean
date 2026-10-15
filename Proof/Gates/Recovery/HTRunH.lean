import Proof.Gates.Recovery.HTRunS

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

theorem honMap_zero (tK tE tH : ℕ) (j : Fin tH) (h : j.val = 0) : honMap tK tE tH j = HI tK tE tH := by
  simp [honMap, h]

theorem honMap_pos (tK tE tH : ℕ) (j : Fin tH) (h : j.val ≠ 0) : honMap tK tE tH j = bH tK tE tH j := by
  simp [honMap, h]

/-- The honest prover's input as written. -/
theorem hi_eq (cw sl : List Bool) : marks cw ++ marks sl ++ [false] = frame (cw ++ sl) := by
  rw [frame_marks, marks_append']

theorem hi_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) (cS : Fin (NS tK tE tH + 1)) (cw sl : List Bool)
    (hcA : cS ≠ AS tK tE tH) (hcH : cS ≠ HI tK tE tH)
    (hc : σ.st cS = frame cw) (hch : σ.sh cS = 0)
    (hAS : σ.st (AS tK tE tH) = marks sl) (hASh : σ.sh (AS tK tE tH) = (marks sl).length)
    (hOP : σ.val opAS = (marks sl).length)
    (hHI : σ.st (HI tK tE tH) = []) (hHIh : σ.sh (HI tK tE tH) = 0)
    (hz : ∀ r ∈ [scK, rT1, rT, scAS, opHI], σ.val r = 0) (hcap : 4 * (cw.length + sl.length) + 8 ≤ cap) :
    WXExec cap (hiW tK tE tH cS) σ
      (((((σ.sets (HI tK tE tH) (frame (cw ++ sl))).seth cS (2 * cw.length)).setv scK (2 * cw.length)).setv scAS
        (2 * sl.length))) (100 * (cw.length + sl.length + 1)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zK, zT1, zT, zSA, zOH⟩ := hz
  have dAH : AS tK tE tH ≠ HI tK tE tH := by hdst
  have dHA := Ne.symm dAH
  have dAc := Ne.symm hcA
  have dHc := Ne.symm hcH
  -- 1. HI := marks cw
  have x1 := pairLoop_spec (cap := cap) (src := cS) (dst := HI tK tE tH) (OP := opHI) (SC := scK) hcH (by decide)
    (emits_raw cap) (emits_raw cap) [false] rfl cw [] σ (by rw [hc, frame_marks]; simp) (by rw [hch]; rfl)
    (by rw [hHI, hHIh]; rfl) (by rw [zOH, flatMap_pair, marks_len]; omega) (by rw [zK]; omega)
  obtain ⟨s1, hs1, e1⟩ := named (WXExec.wm x1)
  rw [flatMap_pair] at hs1
  -- 2–3. rewind AS
  have x2 := addR_spec cap (A := opAS) (B := rT1) (T := rT) (by decide) (by decide) (by decide) s1
    (by rw [hs1, adv_val_other _ _ _ _ (by decide) (by decide), zT])
    (by rw [hs1, adv_val_other _ _ _ _ (by decide) (by decide), adv_val_other _ _ _ _ (by decide) (by decide), zT1,
      hOP, marks_len]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  have hT12 : s2.val rT1 = (marks sl).length := by
    rw [hs2]; simp only [WState.setv_val, Function.update_self]
    rw [hs1, adv_val_other _ _ _ _ (by decide) (by decide), adv_val_other _ _ _ _ (by decide) (by decide), zT1, hOP]
    simp
  have x3 := wrewind_spec (cap := cap) (AS tK tE tH) rT1 _ s2 hT12 (by rw [hT12, marks_len]; omega)
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.wm x3)
  -- 4. HI ++= marks sl
  have hAS3 : s3.st (AS tK tE tH) = [] ++ marks sl ++ [] := by
    rw [hs3, hs2]; simp only [WState.seth_st, WState.setv_st]; rw [hs1, adv_st_other _ _ _ _ dAH, hAS]; simp
  have hASh3 : s3.sh (AS tK tE tH) = ([] : List Bool).length := by
    rw [hs3]; simp only [WState.seth_sh, Function.update_self, WState.setv_sh]
    rw [hs2]; simp only [WState.setv_sh]; rw [hs1, adv_sh_other _ _ _ _ dAH dAc, hASh]; simp
  have hHI3 : s3.st (HI tK tE tH) = marks cw := by
    rw [hs3, hs2]; simp only [WState.seth_st, WState.setv_st]; rw [hs1, adv_st_dst, hHI]; simp
  have hHIh3 : s3.sh (HI tK tE tH) = (marks cw).length := by
    rw [hs3]; simp only [WState.seth_sh, WState.setv_sh]; rw [Function.update_of_ne dHA]
    rw [hs2]; simp only [WState.setv_sh]; rw [hs1, adv_sh_dst hcH, hHIh]; simp
  have hOH3 : s3.val opHI = (marks cw).length := by
    rw [hs3, hs2]; simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne (show opHI ≠ rT1 by decide), Function.update_of_ne (show opHI ≠ rT1 by decide), hs1,
      adv_val_OP (by decide), zOH]; simp
  have hSA3 : s3.val scAS = 0 := by
    rw [hs3, hs2]; simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne (show scAS ≠ rT1 by decide), Function.update_of_ne (show scAS ≠ rT1 by decide), hs1,
      adv_val_other _ _ _ _ (by decide) (by decide), zSA]
  have x4 := pairLoop_spec (cap := cap) (src := AS tK tE tH) (dst := HI tK tE tH) (OP := opHI) (SC := scAS) dAH
    (by decide) (emits_raw cap) (emits_raw cap) [] rfl sl [] s3 hAS3 hASh3 (by rw [hHI3, hHIh3])
    (by rw [hOH3, flatMap_pair, marks_len, marks_len]; omega) (by rw [hSA3]; omega)
  obtain ⟨s4, hs4, e4⟩ := named (WXExec.wm x4)
  rw [flatMap_pair] at hs4
  -- 5–6. the end marker, rewind HI
  have x5 := Codec.emitBit_spec cap (HI tK tE tH) opHI false s4
    (by rw [hs4, adv_st_dst, adv_sh_dst dAH, hHI3, hHIh3]; simp)
    (by rw [hs4, adv_val_OP (by decide), hOH3, marks_len, marks_len]; omega)
  obtain ⟨s5, hs5, e5⟩ := named (WXExec.wm x5)
  have hOH5 : s5.val opHI = (marks cw).length + (marks sl).length + 1 := by
    rw [hs5]; simp [appendO]; rw [hs4, adv_val_OP (by decide), hOH3]; simp [marks_len]
  have x6 := wrewind_spec (cap := cap) (HI tK tE tH) opHI _ s5 hOH5 (by rw [hOH5, marks_len, marks_len]; omega)
  obtain ⟨s6, hs6, e6⟩ := named (WXExec.wm x6)
  have dcA := hcA
  have hshH5 : s5.sh (HI tK tE tH) = (marks cw).length + (marks sl).length + 1 := by
    rw [hs5]; simp [appendO]; rw [hs4, adv_sh_dst dAH, hHIh3]; simp [marks_len]
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6)))))
    ?_ le_rfl) ?_
  · rw [hs6]
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases j1 : j = HI tK tE tH
      · subst j1; simp [hshH5, dHc, hHIh]
      · simp only [WState.seth_sh, WState.setv_sh, WState.sets_sh]
        rw [Function.update_of_ne j1, hs5]; simp only [appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne j1, hs4]
        by_cases j2 : j = AS tK tE tH
        · subst j2; rw [adv_sh_src, hASh3, Function.update_of_ne dAc, hASh, marks_len]; simp
        · rw [adv_sh_other _ _ _ _ j1 j2, hs3]; simp only [WState.seth_sh, WState.setv_sh]
          rw [Function.update_of_ne j2, hs2]; simp only [WState.setv_sh]; rw [hs1]
          by_cases j3 : j = cS
          · subst j3; rw [adv_sh_src, hch]; simp
          · rw [adv_sh_other _ _ _ _ j1 j3, Function.update_of_ne j3]
    · funext j
      by_cases j1 : j = HI tK tE tH
      · subst j1; simp only [WState.seth_st, WState.setv_st, WState.sets_st, Function.update_self]
        rw [hs5]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
        rw [hs4, adv_st_dst, hHI3, ← hi_eq]
      · simp only [WState.seth_st, WState.setv_st, WState.sets_st]; rw [Function.update_of_ne j1, hs5]
        simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st]; rw [Function.update_of_ne j1, hs4,
          adv_st_other _ _ _ _ j1, hs3]
        simp only [WState.seth_st, WState.setv_st]; rw [hs2]; simp only [WState.setv_st]
        rw [hs1, adv_st_other _ _ _ _ j1]
    · funext q
      by_cases q1 : q = opHI
      · subst q1; simp (config := { decide := true }) [zOH]
      · simp only [WState.seth_val, WState.setv_val, WState.sets_val]; rw [Function.update_of_ne q1, hs5]
        simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val]; rw [Function.update_of_ne q1, hs4]
        by_cases q2 : q = scAS
        · subst q2; rw [adv_val_SC, hSA3]; simp (config := { decide := true })
        · rw [adv_val_other _ _ _ _ q1 q2, hs3]; simp only [WState.seth_val, WState.setv_val]
          by_cases q3 : q = rT1
          · subst q3; simp (config := { decide := true }) [zT1]
          · rw [Function.update_of_ne q3, hs2]; simp only [WState.setv_val]; rw [Function.update_of_ne q3, hs1]
            by_cases q4 : q = scK
            · subst q4; rw [adv_val_SC, zK]; simp (config := { decide := true })
            · rw [adv_val_other _ _ _ _ q1 q4]
              simp (config := { decide := true }) [Function.update_apply, q2, q4]
    · rw [hs5, hs4, hs3, hs2, hs1]; simp [adv, appendO]
  · rw [show s1.val opAS = σ.val opAS by rw [hs1, adv_val_other _ _ _ _ (by decide) (by decide)], hOP]
    simp [marks_len]; omega

theorem honest_exec (tK tE cap : ℕ) (P : ThreeQueryPCPP) (ph : Program) (Kh eh : ℕ)
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a)))
    (σ : WState (NS tK tE ph.tapeCount) 64) (a : AcceptedCircuitInput) (sl : List Bool)
    (hHI : σ.st (HI tK tE ph.tapeCount) = frame (acceptedCircuitInputWord a)) (hHIh : σ.sh (HI tK tE ph.tapeCount) = 0)
    (hbH : ∀ j, σ.st (bH tK tE ph.tapeCount j) = [] ∧ σ.sh (bH tK tE ph.tapeCount j) = 0)
    (hAS : σ.st (AS tK tE ph.tapeCount) = marks sl) (hASh : σ.sh (AS tK tE ph.tapeCount) = (marks sl).length)
    (hOP : σ.val opAS = (marks sl).length) (hSH : σ.val scH = 0)
    (hcap : 2 * sl.length + 2 * (P.output a.1).proofBits + 2 ≤ cap) :
    ∃ τ, WXExec cap (.seq (.mach ph.machine (honMap tK tE ph.tapeCount)) (as2W tK tE ph.tapeCount
        (honMap tK tE ph.tapeCount ph.outputTape))) σ τ
        (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh + 40 * ((P.output a.1).proofBits + 1)) ∧
      τ.st (AS tK tE ph.tapeCount) = marks (sl ++ List.ofFn (P.honest a)) ∧
      τ.sh (AS tK tE ph.tapeCount) = 2 * (sl.length + (P.output a.1).proofBits) ∧
      τ.val = Function.update (Function.update σ.val opAS (2 * (sl.length + (P.output a.1).proofBits))) scH
        (2 * (P.output a.1).proofBits) ∧ τ.cell = σ.cell ∧
      (∀ y, (∀ j, honMap tK tE ph.tapeCount j ≠ y) → y ≠ AS tK tE ph.tapeCount → τ.st y = σ.st y ∧ τ.sh y = σ.sh y)
      := by
  obtain ⟨out, hrun, hout⟩ := hph a
  have hin : ∀ j, σ.st (honMap tK tE ph.tapeCount j) = ph.inputTapes (acceptedCircuitInputWord a) j := by
    intro j
    by_cases hj : j.val = 0
    · rw [honMap_zero tK tE ph.tapeCount j hj, hHI]; simp [Program.inputTapes, hj]
    · rw [honMap_pos tK tE ph.tapeCount j hj, (hbH j).1]; simp [Program.inputTapes, hj]
  have h0 : ∀ j, σ.sh (honMap tK tE ph.tapeCount j) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · rw [honMap_zero tK tE ph.tapeCount j hj, hHIh]
    · rw [honMap_pos tK tE ph.tapeCount j hj, (hbH j).2]
  obtain ⟨τ1, e1, hd1⟩ := Dock.ready_mach cap hrun (honMap_inj tK tE ph.tapeCount) σ h0 hin
  have nAS : ∀ j, honMap tK tE ph.tapeCount j ≠ AS tK tE ph.tapeCount := by
    intro j e; have := congrArg Fin.val e; unfold honMap at this; split_ifs at this <;> simp at this <;> omega
  set src := honMap tK tE ph.tapeCount ph.outputTape with hsrc
  have dsA : src ≠ AS tK tE ph.tapeCount := nAS _
  have hsrc1 : τ1.st src = [] ++ marks (List.ofFn (P.honest a)) ++ [] := by
    rw [hd1.st, hout]; simp [FramedSim.pairs, marks]
  have hsrch1 : τ1.sh src = ([] : List Bool).length := by rw [hd1.sh]; rfl
  have hAS1 : τ1.st (AS tK tE ph.tapeCount) = marks sl := by rw [(hd1.other _ nAS).1, hAS]
  have hASh1 : τ1.sh (AS tK tE ph.tapeCount) = (marks sl).length := by rw [(hd1.other _ nAS).2, hASh]
  have hlen : (List.ofFn (P.honest a)).length = (P.output a.1).proofBits := List.length_ofFn
  have x2 := pairLoop_spec (cap := cap) (src := src) (dst := AS tK tE ph.tapeCount) (OP := opAS) (SC := scH) dsA
    (by decide) (emits_raw cap) (emits_raw cap) [] rfl (List.ofFn (P.honest a)) [] τ1 hsrc1 hsrch1
    (by rw [hAS1, hASh1]) (by rw [hd1.val, hOP, flatMap_pair, marks_len, marks_len, hlen]; omega)
    (by rw [hd1.val, hSH, hlen]; omega)
  obtain ⟨τ2, hτ2, e2⟩ := named (WXExec.wm x2)
  rw [flatMap_pair] at hτ2
  refine ⟨τ2, WXExec.mono (WXExec.seq e1 e2) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen]; omega
  · rw [hτ2, adv_st_dst, hAS1, marks_append']
  · rw [hτ2, adv_sh_dst dsA, hASh1, marks_len, marks_len, hlen]; ring
  · funext q
    by_cases q1 : q = scH
    · subst q1; rw [hτ2, adv_val_SC, hd1.val, hSH, hlen]; simp (config := { decide := true })
    · by_cases q2 : q = opAS
      · subst q2; rw [hτ2, adv_val_OP (by decide), hd1.val, hOP, marks_len, marks_len, hlen]
        simp (config := { decide := true }); ring
      · rw [hτ2, adv_val_other _ _ _ _ q2 q1, hd1.val]
        simp [Function.update_apply, q1, q2]
  · rw [hτ2]; simp [adv, appendO, hd1.cell]
  · intro y hy hyA
    have hyS : y ≠ src := fun e => hy ph.outputTape (e ▸ rfl)
    rw [hτ2, adv_st_other _ _ _ _ hyA, adv_sh_other _ _ _ _ hyA hyS]
    exact hd1.other y hy

end NearCubicGates.Close.Recovery.HT
