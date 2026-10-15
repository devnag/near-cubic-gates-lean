import Proof.Gates.Recovery.HTRunT

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named frontState frontCost frontW front_exec)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)
open NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces

theorem litNeg_le {k : ℕ} (l : Literal k) : litNeg l ≤ 1 := by cases l <;> simp [litNeg]

/-- The output value is the table bit. -/
theorem outBit_tableBit {m : ℕ} (raw : RawThreeQueryPCPP m) (asg : List Bool) (a j : ℕ) :
    let cl := raw.clause ⟨a % 2 ^ raw.randomBits, Nat.mod_lt _ (by positivity)⟩
    outBit (j % 5) (bitAt asg (litVar (cl 0))) (bitAt asg (litVar (cl 1))) (bitAt asg (litVar (cl 2)))
      (litNeg (cl 0)) (litNeg (cl 1)) (litNeg (cl 2)) = TableSem.tableBit raw asg a j := by
  intro cl
  unfold bitAt
  rw [outBit_eq]
  unfold TableSem.tableBit
  dsimp only
  split_ifs with h
  · have hl : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 := by omega
    rcases hl with e | e | e <;> simp [e] <;> rfl
  · rfl

/-- The tail program: address split, clause front end, coordinates, output. -/
noncomputable def tailW (tK tE tH pl : ℕ) (wO : Fin tK) : WMX (NS tK tE tH) 64 :=
  .seq (addrW tK tE tH pl) (.seq (frontW (bK tK tE tH wO) R) (.seq (rdW tK tE tH) (outPhase tK tE tH)))

theorem tail_exec (tK tE tH pl cap : ℕ) (σ : WState (NS tK tE tH) 64) (wO : Fin tK) {m : ℕ}
    (raw : RawThreeQueryPCPP m) (asg u wa wj r : List Bool) (Rv cl : ℕ)
    (hu : u.length = Rv) (ha : wa.length = cl) (hj : wj.length = pl)
    (hP2 : σ.st (P2 tK tE tH) = frame (u ++ wa ++ wj ++ r)) (hP2h : σ.sh (P2 tK tE tH) = 0)
    (hR : σ.val rR = Rv) (hCL : σ.val rCL = cl)
    (hW : σ.st (bK tK tE tH wO) = raw.word) (hWh : σ.sh (bK tK tE tH wO) = 0)
    (hAS : σ.st (AS tK tE tH) = marks asg) (hASh : σ.sh (AS tK tE tH) = (marks asg).length)
    (hOP : σ.val opAS = (marks asg).length)
    (hO : σ.st (OUT tK tE tH) = []) (hOh : σ.sh (OUT tK tE tH) = 0)
    (hz : ∀ q ∈ [rK, rT, scP2, rJ, rT1, rKr, rT3, b0, b1, b2, rM5, rJ5, rD5, rK5, opOUT], σ.val q = 0)
    (hzR : ∀ i : Fin 18, σ.val (R i) = 0)
    (hlit : ∀ c t, litVar (raw.clause c t) < m + raw.proofBits)
    (hcap : 2 * 2 ^ cl + 2 * 2 ^ pl + 4 * (Rv + cl + pl) + 4 + 16 * (raw.word.length + 2 ^ cl + m + raw.proofBits + 2)
      + 4 * (asg.length + 3 * (m + raw.proofBits)) + 2 ^ pl + 20 ≤ cap) :
    ∃ τ, WXExec cap (tailW tK tE tH pl wO) σ τ
        (200 * (Rv + 1) + 2 * LitDecode.binKCost cl + 2 * LitDecode.binKCost pl + 4 * pl + 100 + 1 +
          (frontCost (raw.word.length + value wa + m + raw.proofBits) + 1 +
            (100 * (asg.length + 3 * (m + raw.proofBits) + 2) + 1 + 300 * (value wj + 1)))) ∧
      τ.st (OUT tK tE tH) = outWord (TableSem.tableBit raw asg (value wa) (value wj)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zK, zT, zSC, zJ, zT1, zKr, zT3, z0, z1, z2, zM, zJ5, zD, zK5, zO⟩ := hz
  have hva : value wa < 2 ^ cl := ha ▸ RadixSemantics.value_lt wa
  have hvj : value wj < 2 ^ pl := hj ▸ RadixSemantics.value_lt wj
  -- address
  have xA := addr_exec tK tE tH pl cap σ u wa wj r Rv cl hu ha hj hP2 hP2h hR hCL
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨zK, zT, zSC, hzR 0, hzR 10, hzR 11, hzR 12, zJ⟩) (by omega)
  set σA := ((((σ.seth (P2 tK tE tH) (2 * (Rv + cl + pl))).setv (R 0) (value wa)).setv rJ (value wj)).setv scP2
    (2 * (Rv + cl + pl))) with hσA
  have dWP : bK tK tE tH wO ≠ P2 tK tE tH := by hdst
  -- front end
  have hWA : σA.st (bK tK tE tH wO) = raw.word := by rw [hσA]; simp [Function.update_apply, dWP, hW]
  have xF := front_exec (cap := cap) (bK tK tE tH wO) R raw (value wa) σA (by rw [hWA]; exact RdEq.refl _)
    (by rw [hσA]; simp [Function.update_apply, dWP, hWh])
    (by simp (config := { decide := true }) [hσA, Function.update_apply])
    (fun i hi => by
      have h1 : R i ≠ rJ := fin_ne (by simp; omega)
      have h2 : R i ≠ scP2 := fin_ne (by simp; omega)
      have h3 : R i ≠ R 0 := fun e => hi (R.injective e)
      simp [hσA, Function.update_apply, h1, h2, h3, hzR i])
    (by omega)
  set cls := raw.clause ⟨value wa % 2 ^ raw.randomBits, Nat.mod_lt _ (by positivity)⟩ with hcls
  set σF := frontState R σA raw (value wa) with hσF
  have dAP : AS tK tE tH ≠ P2 tK tE tH := by hdst
  have hFst : ∀ y, σF.st y = σA.st y := fun y => by simp [hσF, frontState]
  have hFsh : ∀ y, σF.sh y = σA.sh y := fun y => by simp [hσF, frontState]
  have hFv : ∀ q : Fin 64, 18 ≤ q.val → σF.val q = σA.val q := by
    intro q hq
    have : ∀ i : Fin 18, q ≠ R i := fun i e => by rw [e] at hq; simp at hq; omega
    simp [hσF, frontState, Function.update_apply, this]
  have hl0 : litVar (cls 0) < m + raw.proofBits := hlit _ 0
  have hl1 : litVar (cls 1) < m + raw.proofBits := hlit _ 1
  have hl2 : litVar (cls 2) < m + raw.proofBits := hlit _ 2
  have xR := rd_exec tK tE tH cap σF asg (litVar (cls 0)) (litVar (cls 1)) (litVar (cls 2))
    (by rw [hFst, hσA]; simp [Function.update_apply, dAP, hAS]; exact RdEq.refl _)
    (by rw [hFsh, hσA]; simp [Function.update_apply, dAP, hASh])
    (by rw [hFv _ (by decide), hσA]; simp (config := { decide := true }) [Function.update_apply, hOP])
    (by simp (config := { decide := true }) [hσF, frontState, hcls])
    (by simp (config := { decide := true }) [hσF, frontState, hcls])
    (by simp (config := { decide := true }) [hσF, frontState, hcls])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hFv _ (by decide), hσA] <;>
        simp (config := { decide := true }) [Function.update_apply, zT1, zT, zKr, zT3, z0, z1, z2])
    (by omega)
  set σR := (((σF.seth (AS tK tE tH) 0).setv b0 (bitAt asg (litVar (cls 0)))).setv b1
    (bitAt asg (litVar (cls 1)))).setv b2 (bitAt asg (litVar (cls 2))) with hσR
  have hbit : ∀ v, bitAt asg v ≤ 1 := fun v => Bool.toNat_le _
  have dOA : OUT tK tE tH ≠ AS tK tE tH := by hdst
  have dOP : OUT tK tE tH ≠ P2 tK tE tH := by hdst
  have xO := out_exec tK tE tH cap σR (value wj)
    (by rw [hσR]; simp (config := { decide := true }) [Function.update_apply]; rw [hFv _ (by decide), hσA]
        simp (config := { decide := true }) [Function.update_apply])
    (by simp (config := { decide := true }) [hσR, hbit])
    (by simp (config := { decide := true }) [hσR, hbit])
    (by simp (config := { decide := true }) [hσR, hbit])
    (by simp (config := { decide := true }) [hσR, hσF, frontState, Function.update_apply, litNeg_le])
    (by simp (config := { decide := true }) [hσR, hσF, frontState, Function.update_apply, litNeg_le])
    (by simp (config := { decide := true }) [hσR, hσF, frontState, Function.update_apply, litNeg_le])
    (by rw [hσR]; simp [Function.update_apply, dOA]; rw [hFst, hσA]; simp [Function.update_apply, dOP, hO])
    (by rw [hσR]; simp [Function.update_apply, dOA]; rw [hFsh, hσA]; simp [Function.update_apply, dOP, hOh])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hσR] <;> simp (config := { decide := true }) [Function.update_apply] <;>
        rw [hFv _ (by decide), hσA] <;> simp (config := { decide := true }) [Function.update_apply, zM, zJ5, zD, zK5,
          zT, zO])
    (by omega)
  obtain ⟨τ, eO, hτ⟩ := xO
  refine ⟨τ, WXExec.seq xA (WXExec.seq xF (WXExec.seq (WXExec.mono xR (by omega)) eO)), ?_⟩
  rw [hτ, ← outBit_tableBit]
  congr 2 <;> simp (config := { decide := true }) [hσR, hσF, frontState, Function.update_apply, hcls]

end NearCubicGates.Close.Recovery.HT
