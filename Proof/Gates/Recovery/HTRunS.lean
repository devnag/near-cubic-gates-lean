import Proof.Gates.Recovery.HTRunE

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

theorem ofFn_addCases {m n : ℕ} (a : Fin m → Bool) (b : Fin n → Bool) :
    List.ofFn (Fin.addCases a b : Fin (m + n) → Bool) = List.ofFn a ++ List.ofFn b := List.ofFn_fin_append a b

theorem flatMap_single (l : List Bool) : (l.flatMap fun b => [b]) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem flatMap_pair (l : List Bool) : (l.flatMap fun b => [true] ++ [b]) = marks l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [marks] at ih ⊢ <;> exact ih

theorem encMap_zero (tK tE tH : ℕ) (j : Fin tE) (h : j.val = 0) : encMap tK tE tH j = EI tK tE tH := by
  simp [encMap, h]

theorem encMap_pos (tK tE tH : ℕ) (j : Fin tE) (h : j.val ≠ 0) : encMap tK tE tH j = bE tK tE tH j := by
  simp [encMap, h]

theorem sysEnc_exec (tK tH cap : ℕ) (P : ThreeQueryPCPP) (pe : Program) (Ke ee : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (σ : WState (NS tK pe.tapeCount tH) 64) (Rv : ℕ) (h2 : 2 ≤ Rv) (xp : BitInput Rv) (v : List Bool)
    (hR : σ.val rR = Rv)
    (hEI : σ.st (EI tK pe.tapeCount tH) = eiWord Rv (List.ofFn xp)) (hEIh : σ.sh (EI tK pe.tapeCount tH) = 0)
    (hbE : ∀ j, σ.st (bE tK pe.tapeCount tH j) = [] ∧ σ.sh (bE tK pe.tapeCount tH j) = 0)
    (hP2 : σ.st (P2 tK pe.tapeCount tH) = frame (List.ofFn xp ++ v)) (hP2h : σ.sh (P2 tK pe.tapeCount tH) = 0)
    (hAS : σ.st (AS tK pe.tapeCount tH) = []) (hASh : σ.sh (AS tK pe.tapeCount tH) = 0)
    (hz : ∀ r ∈ [rK, rT, opAS, scP2, scE], σ.val r = 0)
    (hcap : 8 * (Rv + P.code.length Rv) + 8 ≤ cap) :
    ∃ τ, WXExec cap (.seq (.mach pe.machine (encMap tK pe.tapeCount tH)) (asW tK pe.tapeCount tH
        (encMap tK pe.tapeCount tH pe.outputTape))) σ τ
        (Ke * ((messageWord ⟨Rv, ⟨xp, h2⟩⟩).length + 1) ^ ee + 100 * (Rv + P.code.length Rv + 1)) ∧
      τ.st (AS tK pe.tapeCount tH) = marks (List.ofFn (sysEnc P.code Rv xp)) ∧
      τ.sh (AS tK pe.tapeCount tH) = 2 * (Rv + P.code.length Rv) ∧
      τ.val = Function.update (Function.update σ.val opAS (2 * (Rv + P.code.length Rv))) scE
        (2 * P.code.length Rv) ∧ τ.cell = σ.cell ∧
      (∀ y, (∀ j, encMap tK pe.tapeCount tH j ≠ y) → y ≠ AS tK pe.tapeCount tH → τ.st y = σ.st y ∧ τ.sh y = σ.sh y)
      := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zK, zT, zOP, zSC, zSE⟩ := hz
  set L := P.code.length Rv with hL
  set m : MessageRequest := ⟨Rv, ⟨xp, h2⟩⟩ with hm
  obtain ⟨out, hrun, hout⟩ := hpe m
  have hmw : eiWord Rv (List.ofFn xp) = frame (messageWord m) := rfl
  have hin : ∀ j, σ.st (encMap tK pe.tapeCount tH j) = pe.inputTapes (messageWord m) j := by
    intro j
    by_cases hj : j.val = 0
    · rw [encMap_zero tK pe.tapeCount tH j hj, hEI, hmw]; simp [Program.inputTapes, hj]
    · rw [encMap_pos tK pe.tapeCount tH j hj, (hbE j).1]; simp [Program.inputTapes, hj]
  have h0 : ∀ j, σ.sh (encMap tK pe.tapeCount tH j) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · rw [encMap_zero tK pe.tapeCount tH j hj, hEIh]
    · rw [encMap_pos tK pe.tapeCount tH j hj, (hbE j).2]
  obtain ⟨τ1, e1, hd1⟩ := Dock.ready_mach cap hrun (encMap_inj tK pe.tapeCount tH) σ h0 hin
  have nP2 : ∀ j, encMap tK pe.tapeCount tH j ≠ P2 tK pe.tapeCount tH := by
    intro j e; have := congrArg Fin.val e; unfold encMap at this; split_ifs at this <;> simp at this <;> omega
  have nAS : ∀ j, encMap tK pe.tapeCount tH j ≠ AS tK pe.tapeCount tH := by
    intro j e; have := congrArg Fin.val e; unfold encMap at this; split_ifs at this <;> simp at this <;> omega
  have hP21 : τ1.st (P2 tK pe.tapeCount tH) = frame (List.ofFn xp ++ v) := by rw [(hd1.other _ nP2).1, hP2]
  have hP2h1 : τ1.sh (P2 tK pe.tapeCount tH) = 0 := by rw [(hd1.other _ nP2).2, hP2h]
  have hAS1 : τ1.st (AS tK pe.tapeCount tH) = [] := by rw [(hd1.other _ nAS).1, hAS]
  have hASh1 : τ1.sh (AS tK pe.tapeCount tH) = 0 := by rw [(hd1.other _ nAS).2, hASh]
  -- rK := 2R
  have x2 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) τ1 (by rw [hd1.val, zT])
    (by rw [hd1.val, zK, hR]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  have x3 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) s2
    (by simp (config := { decide := true }) [hs2, Function.update_apply, hd1.val, zT])
    (by simp (config := { decide := true }) [hs2, Function.update_apply, hd1.val, zK, hR]; omega)
  obtain ⟨s3, hs3, e3⟩ := named x3
  have hK3 : s3.val rK = (marks (List.ofFn xp)).length := by
    simp (config := { decide := true }) [hs3, hs2, Function.update_apply, hd1.val, zK, hR, marks_len]; omega
  -- AS := marks x
  have dPA : P2 tK pe.tapeCount tH ≠ AS tK pe.tapeCount tH := by hdst
  have x4 := cntLoop_spec (cap := cap) (src := P2 tK pe.tapeCount tH) (dst := AS tK pe.tapeCount tH) (OP := opAS) (SC := scP2) (K := rK)
    dPA (by decide) (by decide) (by decide) (emits_raw cap) (marks v ++ [false]) (marks (List.ofFn xp)) [] s3
    (by rw [hs3, hs2]; simp [hP21, frame_marks, marks_append'])
    (by rw [hs3, hs2]; simp [hP2h1]) (by rw [hs3, hs2]; simp [hAS1, hASh1]) hK3 (by rw [marks_len]; simp; omega)
    (by simp (config := { decide := true }) [hs3, hs2, Function.update_apply, hd1.val, zOP, marks_len]; omega)
    (by simp (config := { decide := true }) [hs3, hs2, Function.update_apply, hd1.val, zSC, marks_len]; omega)
  obtain ⟨s4, hs4, e4⟩ := named (WXExec.wm x4)
  rw [flatMap_single] at hs4
  -- AS ++= marks (Enc x)
  set src := encMap tK pe.tapeCount tH pe.outputTape with hsrc
  have hsrcb : src = bE tK pe.tapeCount tH pe.outputTape := encMap_pos tK pe.tapeCount tH _ pe.outputFresh
  have dsA : src ≠ AS tK pe.tapeCount tH := nAS _
  have dsP : src ≠ P2 tK pe.tapeCount tH := nP2 _
  have hsrc4 : s4.st src = [] ++ marks (List.ofFn (P.code.enc Rv xp)) ++ [] := by
    rw [hs4]; simp only [WState.setv_st]; rw [adv_st_other _ _ _ _ dsA, hs3, hs2]
    simp only [WState.setv_st]; rw [hd1.st, hout]; simp [FramedSim.pairs, marks]; rfl
  have hsrch4 : s4.sh src = ([] : List Bool).length := by
    rw [hs4]; simp only [WState.setv_sh]; rw [adv_sh_other _ _ _ _ dsA dsP, hs3, hs2]
    simp only [WState.setv_sh]; rw [hd1.sh]; rfl
  have hAS4 : s4.st (AS tK pe.tapeCount tH) = marks (List.ofFn xp) := by
    rw [hs4]; simp only [WState.setv_st]; rw [adv_st_dst, hs3, hs2]; simp [hAS1]
  have hASh4 : s4.sh (AS tK pe.tapeCount tH) = (marks (List.ofFn xp)).length := by
    rw [hs4]; simp only [WState.setv_sh]; rw [adv_sh_dst dPA, hs3, hs2]; simp [hASh1]
  have hOP4 : s4.val opAS = (marks (List.ofFn xp)).length := by
    rw [hs4]; simp only [WState.setv_val]
    rw [Function.update_of_ne (show opAS ≠ rK by decide), adv_val_OP (show opAS ≠ scP2 by decide), hs3, hs2]
    simp (config := { decide := true }) [Function.update_apply, hd1.val, zOP]
  have hSE4 : s4.val scE = 0 := by
    rw [hs4]; simp only [WState.setv_val]
    rw [Function.update_of_ne (show scE ≠ rK by decide), adv_val_other _ _ _ _ (by decide) (by decide), hs3, hs2]
    simp (config := { decide := true }) [Function.update_apply, hd1.val, zSE]
  have x5 := pairLoop_spec (cap := cap) (src := src) (dst := AS tK pe.tapeCount tH) (OP := opAS) (SC := scE) dsA
    (by decide) (emits_raw cap) (emits_raw cap) [] rfl (List.ofFn (P.code.enc Rv xp)) [] s4 hsrc4 hsrch4
    (by rw [hAS4, hASh4]) (by rw [hOP4, marks_len, flatMap_pair, marks_len]; simp; omega)
    (by rw [hSE4]; simp; omega)
  obtain ⟨s5, hs5, e5⟩ := named (WXExec.wm x5)
  rw [flatMap_pair] at hs5
  have hSC5 : s5.val scP2 = (marks (List.ofFn xp)).length := by
    rw [hs5, adv_val_other _ _ _ _ (by decide) (by decide), hs4]; simp only [WState.setv_val]
    rw [Function.update_of_ne (show scP2 ≠ rK by decide), adv_val_SC, hs3, hs2]
    simp (config := { decide := true }) [Function.update_apply, hd1.val, zSC]
  have x6 := wrewind_spec (cap := cap) (P2 tK pe.tapeCount tH) scP2 _ s5 hSC5 (by rw [hSC5, marks_len]; simp; omega)
  obtain ⟨s6, hs6, e6⟩ := named (WXExec.wm x6)
  have hAS6 : s6.st (AS tK pe.tapeCount tH) = marks (List.ofFn (sysEnc P.code Rv xp)) := by
    rw [hs6]; simp only [WState.seth_st, WState.setv_st]; rw [hs5, adv_st_dst, hAS4]
    rw [show sysEnc P.code Rv xp = Fin.addCases xp (P.code.enc Rv xp) from rfl, ofFn_addCases, marks_append']
  have hASh6 : s6.sh (AS tK pe.tapeCount tH) = 2 * (Rv + P.code.length Rv) := by
    rw [hs6]; simp only [WState.seth_sh, WState.setv_sh]
    rw [Function.update_of_ne (Ne.symm dPA), hs5, adv_sh_dst dsA, hASh4]; simp [marks_len]; ring
  have hR2 : s2.val rR = Rv := by
    simp (config := { decide := true }) [hs2, Function.update_apply, hd1.val, hR]
  refine ⟨s6, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))) ?_,
    hAS6, hASh6, ?_, ?_, ?_⟩
  · have hτR : τ1.val rR = Rv := by rw [hd1.val, hR]
    simp [List.length_ofFn, hτR, hR2]; omega
  · funext q
    have hτv : ∀ r, τ1.val r = σ.val r := fun r => by rw [hd1.val]
    by_cases q1 : q = scP2
    · subst q1; simp (config := { decide := true }) [hs6, zSC]
    · by_cases q2 : q = scE
      · subst q2; simp (config := { decide := true }) [hs6, hs5, adv, appendO, Function.update_apply, hSE4,
          List.length_ofFn]
      · by_cases q3 : q = opAS
        · subst q3; simp (config := { decide := true }) [hs6, hs5, adv, appendO, Function.update_apply, hOP4,
            marks_len, List.length_ofFn]; ring
        · by_cases q4 : q = rK
          · subst q4; simp (config := { decide := true }) [hs6, hs5, hs4, adv, appendO, Function.update_apply, zK]
          · by_cases q5 : q = rT
            · subst q5; simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, adv, appendO,
                Function.update_apply, hτv, zT]
            · simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, adv, appendO, Function.update_apply,
                hτv, q1, q2, q3, q4, q5]
  · rw [hs6, hs5, hs4, hs3, hs2]; simp [adv, appendO, hd1.cell]
  · intro y hy hyA
    have hyS : y ≠ src := fun e => hy pe.outputTape (e ▸ rfl)
    have st5 : s6.st y = τ1.st y := by
      rw [hs6]; simp only [WState.seth_st, WState.setv_st]
      rw [hs5, adv_st_other _ _ _ _ hyA, hs4]; simp only [WState.setv_st]
      rw [adv_st_other _ _ _ _ hyA, hs3, hs2]; rfl
    refine ⟨st5.trans (hd1.other y hy).1, ?_⟩
    by_cases hyP : y = P2 tK pe.tapeCount tH
    · subst hyP; rw [hs6]; simp only [WState.seth_sh, Function.update_self]
      rw [hs5, adv_sh_other _ _ _ _ dPA (Ne.symm dsP), hs4]; simp only [WState.setv_sh]
      rw [adv_sh_src, hs3, hs2]; simp only [WState.setv_sh]; rw [hP2h1, hP2h]; simp
    · rw [hs6]; simp only [WState.seth_sh, WState.setv_sh]; rw [Function.update_of_ne hyP]
      rw [hs5, adv_sh_other _ _ _ _ hyA hyS, hs4]; simp only [WState.setv_sh]
      rw [adv_sh_other _ _ _ _ hyA hyP, hs3, hs2]; simp only [WState.setv_sh]
      exact (hd1.other y hy).2

end NearCubicGates.Close.Recovery.HT
