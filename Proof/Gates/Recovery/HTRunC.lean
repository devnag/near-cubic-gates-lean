import Proof.Gates.Recovery.HTRunF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)
open NearCubicWires.OuterPCPRecovery (canonicalBoundedCircuitDescription)

theorem convMap_lo (tK tE tH : ℕ) (j : Fin 135) (h : j.val < 5) : (convMap tK tE tH j).val = j.val := by
  simp [convMap, h]

theorem convMap_hi (tK tE tH : ℕ) (j : Fin 135) (h : ¬ j.val < 5) : convMap tK tE tH j = bC tK tE tH j := by
  simp [convMap, h]

theorem flatMap_raw (u : List Bool) : (u.flatMap fun b => ([] : List Bool) ++ [b]) = u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [ih]

theorem frame_marks (u : List Bool) : frame u = marks u ++ [false] := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [frame, marks] at ih ⊢; exact ih

/-- **Phase C.** -/
theorem conv_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) {Rv Bv : ℕ} (c : BooleanCircuit Rv)
    (hc : c.size ≤ Bv) (h addr : List Bool)
    (hst : ∀ j : Fin 135, σ.st (convMap tK tE tH j) =
      CloseoutCaseTwo.Cold.input h (frame (canonicalBoundedCircuitDescription Bv c)) addr Rv Bv j)
    (hsh : ∀ j : Fin 135, σ.sh (convMap tK tE tH j) = 0)
    (hDS : σ.st (DS tK tE tH) = []) (hDSh : σ.sh (DS tK tE tH) = 0) (hop : σ.val opDS = 0) (hsc : σ.val scC = 0)
    (hcap : 2 * (PCPPNative.descriptor c).length + 2 ≤ cap) :
    ∃ τ, WXExec cap (convW tK tE tH) σ τ (CloseoutCaseTwo.Cold.budget Bv c + 30 * (PCPPNative.descriptor c).length + 10) ∧
      τ.st (DS tK tE tH) = PCPPNative.descriptor c ∧ τ.sh (DS tK tE tH) = 0 ∧
      τ.st (P0 tK tE tH) = h ∧ τ.sh (P0 tK tE tH) = 0 ∧ τ.st (P2 tK tE tH) = addr ∧ τ.sh (P2 tK tE tH) = 0 ∧
      τ.val = Function.update σ.val scC (2 * (PCPPNative.descriptor c).length) ∧ τ.cell = σ.cell ∧
      (∀ x, (∀ j, convMap tK tE tH j ≠ x) → x ≠ DS tK tE tH → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) := by
  set d := PCPPNative.descriptor c with hd
  obtain ⟨out, hrun, h132, h0, _, h2⟩ := CloseoutCaseTwo.Cold.converter_run c hc h addr
  obtain ⟨τ1, e1, hd1⟩ := Dock.ready_mach cap hrun (convMap_inj tK tE tH) σ hsh hst
  have hb132 : convMap tK tE tH 132 = bC tK tE tH 132 := convMap_hi tK tE tH 132 (by decide)
  have dDS : ∀ j, convMap tK tE tH j ≠ DS tK tE tH := by
    intro j e; have := congrArg Fin.val e; unfold convMap at this; split_ifs at this <;> simp at this <;> omega
  have hDS1 : τ1.st (DS tK tE tH) = [] := by rw [(hd1.other _ dDS).1, hDS]
  have hDSh1 : τ1.sh (DS tK tE tH) = 0 := by rw [(hd1.other _ dDS).2, hDSh]
  have hsrc : τ1.st (bC tK tE tH 132) = [] ++ marks d ++ [false] := by
    rw [← hb132, hd1.st, h132, frame_marks]; simp [hd]
  have hsrch : τ1.sh (bC tK tE tH 132) = ([] : List Bool).length := by rw [← hb132, hd1.sh]; rfl
  have dCD : bC tK tE tH 132 ≠ DS tK tE tH := by hdst
  have x2 := pairLoop_spec (cap := cap) (src := bC tK tE tH 132) (dst := DS tK tE tH) (OP := opDS) (SC := scC) dCD
    (by decide) (emits_none cap) (emits_raw cap) [false] rfl d [] τ1 hsrc hsrch (by rw [hDS1, hDSh1]; rfl)
    (by rw [hd1.val, hop]; simp [flatMap_raw] <;> omega) (by rw [hd1.val, hsc]; omega)
  obtain ⟨τ2, hτ2, e2⟩ := named (WXExec.wm x2)
  rw [flatMap_raw] at hτ2
  have hop2 : τ2.val opDS = d.length := by rw [hτ2, adv_val_OP (by decide), hd1.val, hop]; simp
  have x3 := wrewind_spec (cap := cap) (DS tK tE tH) opDS d.length τ2 hop2 (by omega)
  obtain ⟨τ3, hτ3, e3⟩ := named (WXExec.wm x3)
  have hP0m : convMap tK tE tH 0 = P0 tK tE tH := Fin.ext (by simp [convMap, P0])
  have hP2m : convMap tK tE tH 2 = P2 tK tE tH := Fin.ext (by simp [convMap, P2])
  have nP0 : P0 tK tE tH ≠ DS tK tE tH := by hdst
  have nP2 : P2 tK tE tH ≠ DS tK tE tH := by hdst
  have nP0b : P0 tK tE tH ≠ bC tK tE tH 132 := by hdst
  have nP2b : P2 tK tE tH ≠ bC tK tE tH 132 := by hdst
  have hτ3' : τ3 = (τ2.setv opDS 0).seth (DS tK tE tH) (τ2.sh (DS tK tE tH) - d.length) := by rw [hτ3]
  have st3 : ∀ x, x ≠ DS tK tE tH → τ3.st x = τ1.st x := by
    intro x hx; rw [hτ3', hτ2]; simp [adv, appendO, Function.update_apply, hx]
  have sh3 : ∀ x, x ≠ DS tK tE tH → x ≠ bC tK tE tH 132 → τ3.sh x = τ1.sh x := by
    intro x hx hb; rw [hτ3', hτ2]; simp [adv, appendO, Function.update_apply, hx, hb]
  refine ⟨τ3, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hτ3', hτ2]; simp [adv, appendO, hDS1]
  · rw [hτ3', hτ2]; simp [adv, appendO, hDSh1, Ne.symm dCD]
  · rw [st3 _ nP0, ← hP0m, hd1.st, h0]
  · rw [sh3 _ nP0 nP0b, ← hP0m, hd1.sh]
  · rw [st3 _ nP2, ← hP2m, hd1.st, h2]
  · rw [sh3 _ nP2 nP2b, ← hP2m, hd1.sh]
  · rw [hτ3', hτ2]
    funext q
    by_cases q1 : q = opDS
    · subst q1; simp (config := { decide := true }) [adv, appendO, Function.update_apply, hd1.val, hop]
    · by_cases q2 : q = scC
      · subst q2; simp (config := { decide := true }) [adv, appendO, Function.update_apply, hd1.val, hsc]
      · simp (config := { decide := true }) [adv, appendO, Function.update_apply, hd1.val, q1, q2]
  · rw [hτ3', hτ2]; simp [adv, appendO, hd1.cell]
  · intro x hx hxD
    have hxb : x ≠ bC tK tE tH 132 := fun e => hx 132 (hb132.trans e.symm)
    rw [st3 _ hxD, sh3 _ hxD hxb]
    exact hd1.other x hx

end NearCubicGates.Close.Recovery.HT
