import Proof.Gates.Recovery.HTRunB

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

section Images
variable (tK tE tH : ℕ)

theorem convMap_val (j : Fin 135) : (convMap tK tE tH j).val = if j.val < 5 then j.val else 10 + j.val := by
  unfold convMap; split_ifs <;> rfl

theorem compMap_val (hIn dIn j : Fin tK) :
    (compMap tK tE tH hIn dIn j).val = if j = hIn then 0 else if j = dIn then 5 else 145 + j.val := by
  unfold compMap; split_ifs <;> rfl

theorem encMap_val (j : Fin tE) : (encMap tK tE tH j).val = if j.val = 0 then 6 else 145 + tK + j.val := by
  unfold encMap; split_ifs <;> rfl

theorem honMap_val (j : Fin tH) : (honMap tK tE tH j).val = if j.val = 0 then 8 else 145 + tK + tE + j.val := by
  unfold honMap; split_ifs <;> rfl

end Images

macro "himg" : tactic => `(tactic| (
  intro j e
  have h := congrArg Fin.val e
  simp only [convMap_val, compMap_val, encMap_val, honMap_val, P0_val, P1_val, P2_val, P3_val, P4_val, DS_val, EI_val,
    AS_val, HI_val, OUT_val, bC_val, bK_val, bE_val, bH_val] at h
  split_ifs at h <;> omega))

open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicGates.Close NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.OuterPCPRecovery (canonicalBoundedCircuitDescription)

/-- **Head, part A**: converter, descriptor, composite, encoder input. -/
theorem headA_exec {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}
    (cx : Setup.CompFull s P g) (tE tH cap : ℕ) {N : ℕ} (x : BitInput N)
    (Bs c : BooleanCircuit (Outer.width s.mw (g.sv s) N)) (hq : 2 ≤ Outer.width s.mw (g.sv s) N)
    (Bv : ℕ) (hc : c.size ≤ Bv) (u v : List Bool) (hu : u.length = Outer.width s.mw (g.sv s) N)
    (σ : WState (NS cx.t tE tH) 64)
    (hst : ∀ j : Fin 135, σ.st (convMap cx.t tE tH j) = CloseoutCaseTwo.Cold.input (mwWord s g N Bs)
      (RepairOrdinary.frame (canonicalBoundedCircuitDescription Bv c)) (RepairOrdinary.frame (u ++ v))
      (Outer.width s.mw (g.sv s) N) Bv j)
    (hsh : ∀ j : Fin 135, σ.sh (convMap cx.t tE tH j) = 0)
    (hDS : σ.st (DS cx.t tE tH) = []) (hDSh : σ.sh (DS cx.t tE tH) = 0)
    (hbK : ∀ j, σ.st (bK cx.t tE tH j) = [] ∧ σ.sh (bK cx.t tE tH j) = 0)
    (hEI : σ.st (EI cx.t tE tH) = []) (hEIh : σ.sh (EI cx.t tE tH) = 0)
    (hR : σ.val rR = Outer.width s.mw (g.sv s) N)
    (hz : ∀ q ∈ [opDS, scC, rRc, rH, rB, rK, rT, opEI, scP2], σ.val q = 0)
    (hcap : 2 * (PCPPNative.descriptor c).length + 8 * Outer.width s.mw (g.sv s) N + 8 ≤ cap) :
    ∃ τ, WXExec cap (.seq (convW cx.t tE tH) (.seq (.mach cx.M (compMap cx.t tE tH cx.cIn cx.dIn))
        (eiW cx.t tE tH))) σ τ
        (CloseoutCaseTwo.Cold.budget Bv c + 30 * (PCPPNative.descriptor c).length + 10 + 1 +
          (cx.C * ((mwWord s g N Bs).length + (PCPPNative.descriptor c).length + Outer.width s.mw (g.sv s) N + 1) ^ cx.e + 1 +
            100 * (Outer.width s.mw (g.sv s) N + 1) * (Outer.width s.mw (g.sv s) N + 1)))
      ∧ τ.st (bK cx.t tE tH cx.cOut) = RepairOrdinary.frame (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).word
      ∧ τ.sh (bK cx.t tE tH cx.cOut) = 0
      ∧ τ.st (bK cx.t tE tH cx.wOut) = (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).word
      ∧ τ.sh (bK cx.t tE tH cx.wOut) = 0
      ∧ τ.st (EI cx.t tE tH) = eiWord (Outer.width s.mw (g.sv s) N) u ∧ τ.sh (EI cx.t tE tH) = 0
      ∧ τ.st (P2 cx.t tE tH) = RepairOrdinary.frame (u ++ v) ∧ τ.sh (P2 cx.t tE tH) = 0
      ∧ τ.val = Function.update σ.val scC (2 * (PCPPNative.descriptor c).length) ∧ τ.cell = σ.cell
      ∧ (∀ y, (∀ j, convMap cx.t tE tH j ≠ y) → (∀ j, compMap cx.t tE tH cx.cIn cx.dIn j ≠ y) → y ≠ DS cx.t tE tH →
          y ≠ EI cx.t tE tH → τ.st y = σ.st y ∧ τ.sh y = σ.sh y) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zOD, zSC, zRc, zH, zB, zK, zT, zOE, zP2⟩ := hz
  -- converter
  obtain ⟨τ1, e1, hDS1, hDSh1, hP01, hP0h1, hP21, hP2h1, hv1, hc1, hk1⟩ :=
    conv_exec cx.t tE tH cap σ c hc (mwWord s g N Bs) (RepairOrdinary.frame (u ++ v)) hst hsh hDS hDSh zOD
      zSC (by omega)
  have nbKc : ∀ j', ∀ j, convMap cx.t tE tH j ≠ bK cx.t tE tH j' := by intro j'; himg
  have nbKD : ∀ j, bK cx.t tE tH j ≠ DS cx.t tE tH := fun j => by hdst
  -- composite
  obtain ⟨τ2, e2, hc2, hw2, -, -, hsh2, hv2, hcl2, hk2⟩ := comp_exec cx tE tH cap x ⟨Bs, c⟩ hq τ1 hP01 hP0h1 hDS1 hDSh1
    (fun j => by rw [(hk1 _ (nbKc j) (nbKD j)).1, (hbK j).1]) (fun j => by rw [(hk1 _ (nbKc j) (nbKD j)).2, (hbK j).2])
  have nd := cx.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at nd
  obtain ⟨⟨_, hc1', hw1', _, _, _⟩, ⟨dc, dw, _, _, _⟩, ⟨cw, _, _, _⟩, -, -, -⟩ := nd
  have hcm : compMap cx.t tE tH cx.cIn cx.dIn cx.cOut = bK cx.t tE tH cx.cOut :=
    compMap_other cx.t tE tH cx.cIn cx.dIn cx.cOut (Ne.symm hc1') (Ne.symm dc)
  have hwm : compMap cx.t tE tH cx.cIn cx.dIn cx.wOut = bK cx.t tE tH cx.wOut :=
    compMap_other cx.t tE tH cx.cIn cx.dIn cx.wOut (Ne.symm hw1') (Ne.symm dw)
  -- encoder input
  have nP2 : ∀ j, compMap cx.t tE tH cx.cIn cx.dIn j ≠ P2 cx.t tE tH := by himg
  have nEIk : ∀ j, compMap cx.t tE tH cx.cIn cx.dIn j ≠ EI cx.t tE tH := by himg
  have nEIc : ∀ j, convMap cx.t tE tH j ≠ EI cx.t tE tH := by himg
  have dEID : EI cx.t tE tH ≠ DS cx.t tE tH := by hdst
  have xE := ei_exec cx.t tE tH cap τ2 (Outer.width s.mw (g.sv s) N) u v hu (by rw [hv2, hv1]; simp (config := { decide := true }) [hR])
    (by rw [(hk2 _ nP2).1, hP21]) (by rw [(hk2 _ nP2).2, hP2h1])
    (by rw [(hk2 _ nEIk).1, (hk1 _ nEIc dEID).1, hEI]) (by rw [(hk2 _ nEIk).2, (hk1 _ nEIc dEID).2, hEIh])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [hv2, hv1]; simp (config := { decide := true }) [zRc, zH, zB, zK, zT, zOE, zP2])
    (by omega)
  have dEIc : EI cx.t tE tH ≠ bK cx.t tE tH cx.cOut := by hdst
  have dEIw : EI cx.t tE tH ≠ bK cx.t tE tH cx.wOut := by hdst
  have dEIP : EI cx.t tE tH ≠ P2 cx.t tE tH := by hdst
  refine ⟨τ2.sets (EI cx.t tE tH) (eiWord (Outer.width s.mw (g.sv s) N) u), WXExec.seq e1 (WXExec.seq e2 xE), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Function.update_apply, Ne.symm dEIc]; rw [hc2]
  · simp; rw [← hcm, hsh2]
  · simp [Function.update_apply, Ne.symm dEIw]; rw [hw2]
  · simp; rw [← hwm, hsh2]
  · simp
  · simp; rw [(hk2 _ nEIk).2, (hk1 _ nEIc dEID).2, hEIh]
  · simp [Function.update_apply, Ne.symm dEIP]; rw [(hk2 _ nP2).1, hP21]
  · simp; rw [(hk2 _ nP2).2, hP2h1]
  · simp; rw [hv2, hv1]
  · simp; rw [hcl2, hc1]
  · intro y hy1 hy2 hyD hyE
    simp [Function.update_apply, hyE]
    rw [(hk2 y hy2).1, (hk2 y hy2).2]
    exact hk1 y hy1 hyD

/-- **Head, part B**: encoder, `AS = marks (sysEnc x)`, `HI`, honest prover, `AS = marks (sysEnc x ++ honest)`. -/
theorem headB_exec (tK cap : ℕ) (P : ThreeQueryPCPP) (pe ph : Program) (Ke ee Kh eh : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a)))
    (D : Circuit) (h2 : 2 ≤ D.n) (xp : BitInput D.n) (hacc : D.D.eval xp = true) (v : List Bool) (cO wO : Fin tK)
    (hcw : cO ≠ wO)
    (σ : WState (NS tK pe.tapeCount ph.tapeCount) 64)
    (hR : σ.val rR = D.n)
    (hEI : σ.st (EI tK pe.tapeCount ph.tapeCount) = eiWord D.n (List.ofFn xp))
    (hEIh : σ.sh (EI tK pe.tapeCount ph.tapeCount) = 0)
    (hbE : ∀ j, σ.st (bE tK pe.tapeCount ph.tapeCount j) = [] ∧ σ.sh (bE tK pe.tapeCount ph.tapeCount j) = 0)
    (hbH : ∀ j, σ.st (bH tK pe.tapeCount ph.tapeCount j) = [] ∧ σ.sh (bH tK pe.tapeCount ph.tapeCount j) = 0)
    (hP2 : σ.st (P2 tK pe.tapeCount ph.tapeCount) = RepairOrdinary.frame (List.ofFn xp ++ v))
    (hP2h : σ.sh (P2 tK pe.tapeCount ph.tapeCount) = 0)
    (hAS : σ.st (AS tK pe.tapeCount ph.tapeCount) = []) (hASh : σ.sh (AS tK pe.tapeCount ph.tapeCount) = 0)
    (hHI : σ.st (HI tK pe.tapeCount ph.tapeCount) = []) (hHIh : σ.sh (HI tK pe.tapeCount ph.tapeCount) = 0)
    (hC : σ.st (bK tK pe.tapeCount ph.tapeCount cO) = RepairOrdinary.frame (checkedCircuit P.code D).word)
    (hCh : σ.sh (bK tK pe.tapeCount ph.tapeCount cO) = 0)
    (hz : ∀ q ∈ [rK, rT, opAS, scP2, scE, scK, rT1, scAS, opHI, scH], σ.val q = 0)
    (hcap : 8 * (D.n + P.code.length D.n) + 4 * (checkedCircuit P.code D).word.length +
      2 * (P.output (checkedCircuit P.code D)).proofBits + 16 ≤ cap) :
    let a := acceptedInput P.code D xp hacc
    let asg := List.ofFn (sysEnc P.code D.n xp) ++ List.ofFn (P.honest a)
    ∃ τ, WXExec cap (.seq (.seq (.mach pe.machine (encMap tK pe.tapeCount ph.tapeCount))
        (asW tK pe.tapeCount ph.tapeCount (encMap tK pe.tapeCount ph.tapeCount pe.outputTape)))
        (.seq (hiW tK pe.tapeCount ph.tapeCount (bK tK pe.tapeCount ph.tapeCount cO))
          (.seq (.mach ph.machine (honMap tK pe.tapeCount ph.tapeCount))
            (as2W tK pe.tapeCount ph.tapeCount (honMap tK pe.tapeCount ph.tapeCount ph.outputTape))))) σ τ
        (Ke * ((messageWord ⟨D.n, ⟨xp, h2⟩⟩).length + 1) ^ ee + 100 * (D.n + P.code.length D.n + 1) + 1 +
          (100 * ((checkedCircuit P.code D).word.length + (D.n + P.code.length D.n) + 1) + 1 +
            (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh +
              40 * ((P.output (checkedCircuit P.code D)).proofBits + 1))))
      ∧ τ.st (AS tK pe.tapeCount ph.tapeCount) = marks asg
      ∧ τ.sh (AS tK pe.tapeCount ph.tapeCount) = (marks asg).length ∧ τ.val opAS = (marks asg).length
      ∧ τ.st (bK tK pe.tapeCount ph.tapeCount wO) = σ.st (bK tK pe.tapeCount ph.tapeCount wO)
      ∧ τ.sh (bK tK pe.tapeCount ph.tapeCount wO) = σ.sh (bK tK pe.tapeCount ph.tapeCount wO)
      ∧ τ.st (P2 tK pe.tapeCount ph.tapeCount) = σ.st (P2 tK pe.tapeCount ph.tapeCount)
      ∧ τ.sh (P2 tK pe.tapeCount ph.tapeCount) = 0
      ∧ τ.st (OUT tK pe.tapeCount ph.tapeCount) = σ.st (OUT tK pe.tapeCount ph.tapeCount)
      ∧ τ.sh (OUT tK pe.tapeCount ph.tapeCount) = σ.sh (OUT tK pe.tapeCount ph.tapeCount)
      ∧ (∀ q, q ∉ [opAS, scE, scK, scAS, scH] → τ.val q = σ.val q) := by
  intro a asg
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zK, zT, zOA, zP2, zSE, zSK, zT1, zSA, zOH, zSH⟩ := hz
  -- encoder and AS := marks sysEnc
  obtain ⟨τ1, e1, hAS1, hASh1, hv1, hc1, hk1⟩ := sysEnc_exec tK ph.tapeCount cap P pe Ke ee hpe σ D.n h2 xp v hR hEI
    hEIh hbE hP2 hP2h hAS hASh
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨zK, zT, zOA, zP2, zSE⟩) (by omega)
  set sl := List.ofFn (sysEnc P.code D.n xp) with hsl
  have hsll : sl.length = D.n + P.code.length D.n := by simp [hsl]
  have nC : ∀ j, encMap tK pe.tapeCount ph.tapeCount j ≠ bK tK pe.tapeCount ph.tapeCount cO := by himg
  have nW : ∀ j, encMap tK pe.tapeCount ph.tapeCount j ≠ bK tK pe.tapeCount ph.tapeCount wO := by himg
  have nH : ∀ j, encMap tK pe.tapeCount ph.tapeCount j ≠ HI tK pe.tapeCount ph.tapeCount := by himg
  have nP : ∀ j, encMap tK pe.tapeCount ph.tapeCount j ≠ P2 tK pe.tapeCount ph.tapeCount := by himg
  have nO : ∀ j, encMap tK pe.tapeCount ph.tapeCount j ≠ OUT tK pe.tapeCount ph.tapeCount := by himg
  have nbH : ∀ j' j, encMap tK pe.tapeCount ph.tapeCount j ≠ bH tK pe.tapeCount ph.tapeCount j' := by intro j'; himg
  have dCA : bK tK pe.tapeCount ph.tapeCount cO ≠ AS tK pe.tapeCount ph.tapeCount := by hdst
  have dCH : bK tK pe.tapeCount ph.tapeCount cO ≠ HI tK pe.tapeCount ph.tapeCount := by hdst
  have dWA : bK tK pe.tapeCount ph.tapeCount wO ≠ AS tK pe.tapeCount ph.tapeCount := by hdst
  have dHA : HI tK pe.tapeCount ph.tapeCount ≠ AS tK pe.tapeCount ph.tapeCount := by hdst
  have dPA : P2 tK pe.tapeCount ph.tapeCount ≠ AS tK pe.tapeCount ph.tapeCount := by hdst
  have dOA : OUT tK pe.tapeCount ph.tapeCount ≠ AS tK pe.tapeCount ph.tapeCount := by hdst
  have dbHA : ∀ j, bH tK pe.tapeCount ph.tapeCount j ≠ AS tK pe.tapeCount ph.tapeCount := fun j => by hdst
  -- HI := frame (C.word ++ sysEnc)
  have xH := hi_exec tK pe.tapeCount ph.tapeCount cap τ1 (bK tK pe.tapeCount ph.tapeCount cO) (checkedCircuit P.code D).word sl dCA dCH
    (by rw [(hk1 _ nC dCA).1, hC]) (by rw [(hk1 _ nC dCA).2, hCh]) hAS1 (by rw [hASh1, marks_len, hsll])
    (by rw [hv1]; simp (config := { decide := true }) [marks_len, hsll])
    (by rw [(hk1 _ nH dHA).1, hHI]) (by rw [(hk1 _ nH dHA).2, hHIh])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [hv1]; simp (config := { decide := true }) [zSK, zT1, zT, zSA, zOH])
    (by omega)
  set τ2 := (((τ1.sets (HI tK pe.tapeCount ph.tapeCount) (RepairOrdinary.frame ((checkedCircuit P.code D).word ++ sl))).seth
    (bK tK pe.tapeCount ph.tapeCount cO) (2 * (checkedCircuit P.code D).word.length)).setv scK
    (2 * (checkedCircuit P.code D).word.length)).setv scAS (2 * sl.length) with hτ2
  have hacw : acceptedCircuitInputWord a = (checkedCircuit P.code D).word ++ sl := rfl
  -- honest prover
  obtain ⟨τ3, e3, hAS3, hASh3, hv3, hc3, hk3⟩ := honest_exec tK pe.tapeCount cap P ph Kh eh hph τ2 a sl
    (by rw [hτ2, hacw]; simp) (by rw [hτ2]; simp [Function.update_apply, Ne.symm dCH, (hk1 _ nH dHA).2, hHIh])
    (fun j => by
      have h1 : bH tK pe.tapeCount ph.tapeCount j ≠ HI tK pe.tapeCount ph.tapeCount := by hdst
      have h2 : bH tK pe.tapeCount ph.tapeCount j ≠ bK tK pe.tapeCount ph.tapeCount cO := by hdst
      rw [hτ2]; simp [Function.update_apply, h1, h2]
      rw [(hk1 _ (fun i => nbH j i) (dbHA j)).1, (hk1 _ (fun i => nbH j i) (dbHA j)).2]; exact hbH j)
    (by rw [hτ2]; simp [Function.update_apply, Ne.symm dHA, hAS1])
    (by rw [hτ2]; simp [Function.update_apply, Ne.symm dCA, hASh1, marks_len, hsll])
    (by rw [hτ2]; simp (config := { decide := true }) [Function.update_apply]; rw [hv1]
        simp (config := { decide := true }) [marks_len, hsll])
    (by rw [hτ2]; simp (config := { decide := true }) [Function.update_apply]; rw [hv1]
        simp (config := { decide := true }) [zSH])
    (by rw [hsll]; show 2 * (D.n + P.code.length D.n) + 2 * (P.output (checkedCircuit P.code D)).proofBits + 2 ≤ cap
        omega)
  have hhl : (List.ofFn (P.honest a)).length = (P.output (checkedCircuit P.code D)).proofBits := List.length_ofFn
  have nW3 : ∀ j, honMap tK pe.tapeCount ph.tapeCount j ≠ bK tK pe.tapeCount ph.tapeCount wO := by himg
  have nP3 : ∀ j, honMap tK pe.tapeCount ph.tapeCount j ≠ P2 tK pe.tapeCount ph.tapeCount := by himg
  have nO3 : ∀ j, honMap tK pe.tapeCount ph.tapeCount j ≠ OUT tK pe.tapeCount ph.tapeCount := by himg
  have dWH : bK tK pe.tapeCount ph.tapeCount wO ≠ HI tK pe.tapeCount ph.tapeCount := by hdst
  have dWC : bK tK pe.tapeCount ph.tapeCount wO ≠ bK tK pe.tapeCount ph.tapeCount cO := by
    apply fin_ne; simp only [bK_val]; intro h; exact hcw (Fin.ext (by omega)).symm
  have dPH : P2 tK pe.tapeCount ph.tapeCount ≠ HI tK pe.tapeCount ph.tapeCount := by hdst
  have dPC : P2 tK pe.tapeCount ph.tapeCount ≠ bK tK pe.tapeCount ph.tapeCount cO := by hdst
  have dOH : OUT tK pe.tapeCount ph.tapeCount ≠ HI tK pe.tapeCount ph.tapeCount := by hdst
  have dOC : OUT tK pe.tapeCount ph.tapeCount ≠ bK tK pe.tapeCount ph.tapeCount cO := by hdst
  have hasgl : asg.length = D.n + P.code.length D.n + (P.output (checkedCircuit P.code D)).proofBits := by
    simp only [asg, List.length_append, hhl]; rw [← hsl, hsll]
  refine ⟨τ3, WXExec.mono (WXExec.seq e1 (WXExec.seq xH e3)) (by rw [hsll]; exact le_refl _), hAS3, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hASh3, marks_len, hasgl, hsll]; rfl
  · rw [hv3]; simp (config := { decide := true }) [marks_len, hasgl, hsll]; rfl
  · rw [(hk3 _ nW3 dWA).1, hτ2]; simp [Function.update_apply, dWH]; exact (hk1 _ nW dWA).1
  · rw [(hk3 _ nW3 dWA).2, hτ2]; simp [Function.update_apply, dWC]; exact (hk1 _ nW dWA).2
  · rw [(hk3 _ nP3 dPA).1, hτ2]; simp [Function.update_apply, dPH]; exact (hk1 _ nP dPA).1
  · rw [(hk3 _ nP3 dPA).2, hτ2]; simp [Function.update_apply, dPC]; rw [(hk1 _ nP dPA).2, hP2h]
  · rw [(hk3 _ nO3 dOA).1, hτ2]; simp [Function.update_apply, dOH]; exact (hk1 _ nO dOA).1
  · rw [(hk3 _ nO3 dOA).2, hτ2]; simp [Function.update_apply, dOC]; exact (hk1 _ nO dOA).2
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5⟩ := hq
    rw [hv3]; simp only [Function.update_apply, q1, q5, if_false]; rw [hτ2]
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, q3, q4, if_false]
    rw [hv1]; simp only [Function.update_apply, q1, q2, if_false]

end NearCubicGates.Close.Recovery.HT
