import Proof.Wire_3_5.OutMachineP5
import Proof.Gates.WordPrograms.WMX

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WilliamsPublishedForm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires.WireExponent3_5.FinalPass.Out.P3 (fb)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

theorem printNat_spec' (X : Fin (nsO + 1)) (hX : X ≠ sO) (W x : ℕ) (σ : St) (hW : 1 ≤ W) (hx : x < 2 ^ W)
    (hXst : σ.st X = frame (binary W x)) (hXsh : σ.sh X = 0) (hO : σ.sh sO = (σ.st sO).length)
    (hw : σ.val rW = W) (hz : ∀ r, r ≠ rW → σ.val r = 0) :
    ∃ ρ : St, WExec (capO W) (printNat X) σ ρ (pnCost W) ∧ ρ.st sO = σ.st sO ++ natWord x ∧
      ρ.sh sO = (ρ.st sO).length ∧ (∀ i, i ≠ sO → ρ.st i = σ.st i) ∧ (∀ i, i ≠ sO → i ≠ X → ρ.sh i = σ.sh i) ∧
      ρ.val = σ.val ∧ ρ.cell = σ.cell ∧ ρ.sh X = 2 * natBitLength x + 1 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19⟩ := regs_ne
  have hcap : 8 * W + 8 = capO W := rfl
  -- 1. `rK := W`
  have s1 := UnionMachine.BinW.dupR_spec (capO W) rW rK rT n16 n18 (Ne.symm n19) σ W hw (hz rK (Ne.symm n16))
    (hz rT (Ne.symm n18)) (by omega)
  set σ1 := σ.setv rK W with hσ1
  -- 2. to the first bit
  have s2 : WExec (capO W) (.fwd X) σ1 (σ1.seth X 1) 1 := by
    have e := WExec.fwd (cap := capO W) X σ1
    rwa [show σ1.sh X = 0 by simp [hσ1, hXsh]] at e
  set σ2 := σ1.seth X 1 with hσ2
  -- 3. the scan
  have s3 := scanLoop_spec X W (binary W x) [] σ2 0 0 (by simp [hσ2, hσ1, hXst, frame_eq_frameP]) (by simp [hσ2])
    (by simp [hσ2, hσ1, Function.update_of_ne n3, hz rZ (Ne.symm n13)])
    (by simp [hσ2, hσ1, Function.update_of_ne n5, hz rL (Ne.symm n14)])
    (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm (show rK ≠ rR from Ne.symm n6)), hz rR (Ne.symm n15)])
    (by simp [hσ2, hσ1]) (by simp) (by simp)
  simp only [List.length_nil, SignedSortKey.binary_length, Nat.zero_add] at s3
  set zs := (scanL (binary W x) (0, 0)).1 with hzs
  set ls := (scanL (binary W x) (0, 0)).2 with hls
  have hsum := scanL_sum (binary W x) 0 0
  simp only [SignedSortKey.binary_length, Nat.zero_add] at hsum
  set σ3 := nfS σ2 X (2 * W + 1) zs ls (2 * W) with hσ3
  -- 4. back to the first bit
  have h3R : σ3.val rR = 2 * W := by simp [hσ3, nfS, Function.update_of_ne n6]
  have s4 := wrewind_spec (capO W) X rR (2 * W) σ3 h3R (by rw [h3R]; omega)
  have h3X : σ3.sh X = 2 * W + 1 := by simp [hσ3, nfS]
  rw [h3X, show 2 * W + 1 - 2 * W = 1 by omega] at s4
  set σ4 := (σ3.setv rR 0).seth X 1 with hσ4
  -- 5. `Z := 0`
  have s5 := wclear_spec (capO W) rZ zs σ4
    (by simp [hσ4, hσ3, nfS, Function.update_of_ne n2, Function.update_of_ne n3, Function.update_of_ne n1])
    (by rw [show σ4.val rZ = zs by simp [hσ4, hσ3, nfS, Function.update_of_ne n2, Function.update_of_ne n3,
      Function.update_of_ne n1]]; omega)
  set σ5 := σ4.setv rZ 0 with hσ5
  have h5L : σ5.val rL = ls := by
    simp [hσ5, hσ4, hσ3, nfS, Function.update_of_ne (Ne.symm n1), Function.update_of_ne n4, Function.update_of_ne n5]
  -- 6. `L := max 1 L`
  set Lx := natBitLength x with hLx
  have hLx' : (if ls = 0 then 1 else ls) = Lx := scanL_nbl W x hx
  have hLW : Lx ≤ W := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [hLx, h0]; unfold natBitLength; simp; omega
    · rw [hLx, natBitLength_eq x h0]; exact Nat.size_le.2 hx
  have s6 : WExec (capO W) (.ifr rL .skip (.inc rL)) σ5 (σ5.setv rL Lx) 4 := by
    by_cases h0 : ls = 0
    · rw [if_pos h0] at hLx'
      have i1 := WExec.inc (cap := capO W) rL σ5 (by rw [h5L, h0]; omega)
      rw [h5L, h0] at i1
      rw [← hLx']
      exact WExec.ifrF (by rw [h5L, h0]) i1
    · rw [if_neg h0] at hLx'
      rw [← hLx', ← h5L, wsetv_same]
      exact WExec.mono (WExec.ifrT (by rw [h5L]; exact h0) (WExec.skip σ5)) (by omega)
  set σ6 := σ5.setv rL Lx with hσ6
  -- 7. `C := L`
  have s7 := UnionMachine.BinW.dupR_spec (capO W) rL rC rT (Ne.symm n7) n9 n8 σ6 Lx (by simp [hσ6])
    (by simp [hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne n7, Function.update_of_ne n12,
      Function.update_of_ne n10, Function.update_of_ne n11, hz rC (Ne.symm n17)])
    (by simp [hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne (Ne.symm n9),
      Function.update_of_ne n19, Function.update_of_ne (show rT ≠ rR by decide),
      Function.update_of_ne (show rT ≠ rZ by decide), hz rT (Ne.symm n18)]) (by omega)
  set σ7 := σ6.setv rC Lx with hσ7
  have h7O : σ7.sh sO = (σ7.st sO).length := by
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne (Ne.symm hX), hO]
  -- 8. the ones
  have s8 := onesLoop_spec W Lx σ7 (by simp [hσ7]) (by omega) h7O
  set σ8 := ((σ7.sets sO (σ7.st sO ++ List.replicate Lx true)).seth sO ((σ7.st sO).length + Lx)).setv rC 0 with hσ8
  -- 9. the separator
  have s9 := emit_spec (capO W) sO false σ8 (by simp [hσ8])
  set σ9 := (σ8.sets sO (σ8.st sO ++ [false])).seth sO ((σ8.st sO).length + 1) with hσ9
  -- 10. the bits
  have s10 := bitsLoop_spec X hX W Lx (binary W x) [] σ9
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hX, hXst, frame_eq_frameP])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hX])
    (by simp [hσ9, hσ8, hσ7, hσ6, Function.update_of_ne (Ne.symm n7)]) (by simp; exact hLW) (by omega)
    (by simp [hσ9])
  refine ⟨_, WExec.cast (capO W) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 s10))))))))) rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pnCost
    have : zs ≤ W := by omega
    omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, List.nil_append]
    rw [natWord_binary W x hW hx, ← hLx]
    simp
  · simp only [WState.setv_sh, WState.setv_st, WState.seth_sh, WState.seth_st, WState.sets_st, WState.sets_sh,
      Function.update_of_ne (Ne.symm hX), Function.update_self]
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, List.length_append, List.length_replicate, List.length_take,
      SignedSortKey.binary_length, List.length_singleton]
    rw [Nat.min_eq_left hLW]
  · intro i hi
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hi]
  · intro i hi hiX
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hi, Function.update_of_ne hiX]
  · funext j
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_val, WState.seth_val, WState.sets_val,
      Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first
      | rfl
      | (symm; apply hz; decide)
  · rfl
  · simp [hLx]

end NearCubicWires.WireExponent3_5.FinalPass.Out.P5
