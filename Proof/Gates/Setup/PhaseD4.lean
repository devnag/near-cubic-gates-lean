import Proof.Gates.Setup.PhaseD3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

noncomputable section

/-- The register program of phase D. -/
def regsP {ns : ℕ} (pS rS cS : Fin (ns + 1)) (d : ℕ) : WMX ns nrW :=
  .seq (binRW pS rPB 60 61 62 63)
  (.seq (binRW rS rRB 60 61 62 63)
  (.seq (readRW cS)
  (.seq (clA d)
  (.seq clB
  (.wm (.seq (Codec.dupR rPB cA dS) (Codec.dupR rM cA dS)))))))

/-- The registers after `regsP`. -/
def regsSt {ns : ℕ} (σ : WState ns nrW) (pb rb sc cl : ℕ) : WState ns nrW :=
  ((((((σ.setv rPB pb).setv rRB rb).setv rSC sc).setv rCL cl).setv rM (2 ^ cl)).setv rLC (2 ^ cl)).setv cA
    (pb + 2 ^ cl)

/-- The cost of `regsP`. -/
def regsCost (pb rb sc cl q : ℕ) : ℕ :=
  LitDecode.binCost pb.bits.length + 1 + (5 * (2 * pb.bits.length + 1) + 1) + 1 +
  (LitDecode.binCost rb.bits.length + 1 + (5 * (2 * rb.bits.length + 1) + 1) + 1 +
  (200 * (sc + 2) ^ 2 + 40 * 2 ^ natBitLength sc * (sc + 3) + 1 +
  (1000 * (2 ^ cl + q + 2) ^ 3 + 1 + (100 * (2 ^ cl + 1) ^ 2 + 1 + (18 * pb + 3 + 1 + (18 * 2 ^ cl + 3))))))

theorem regs_exec {ns cap : ℕ} (pS rS cS : Fin (ns + 1)) (d q pb rb sc : ℕ) (rest : List Bool) (σ : WState ns nrW)
    (hp : σ.st pS = RepairOrdinary.frame pb.bits) (hph : σ.sh pS = 0)
    (hr : σ.st rS = RepairOrdinary.frame rb.bits) (hrh : σ.sh rS = 0)
    (hc : σ.st cS = marks (natWord sc) ++ rest) (hch : σ.sh cS = 0)
    (hq : σ.val (regE 6) = q)
    (hz : ∀ r : Fin nrW, 40 < r.val → r.val < 100 → r ≠ rN → σ.val r = 0)
    (hcap : 4 * (2 ^ clauseWidth d q + q + pb + rb + sc + 4) ^ 2 ≤ cap) :
    WXExec cap (regsP pS rS cS d) σ (regsSt σ pb rb sc (clauseWidth d q)) (regsCost pb rb sc (clauseWidth d q) q) := by
  have hM1 : 1 ≤ 2 ^ clauseWidth d q := Nat.one_le_two_pow
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ clauseWidth d q + q + pb + rb + sc + 4 := ⟨_, rfl⟩
  rw [← hX] at hcap
  have hXp : pb + 4 ≤ X := by omega
  have hXr : rb + 4 ≤ X := by omega
  have hXs : sc + 4 ≤ X := by omega
  have hXM : 2 ^ clauseWidth d q + q + 2 ≤ X := by omega
  have hXX : 16 * X ≤ cap := by nlinarith
  have hpb2 := LitDecode.two_pow_bits_le pb
  have hrb2 := LitDecode.two_pow_bits_le rb
  have hpbl := LitDecode.bits_len_le pb
  have hrbl := LitDecode.bits_len_le rb
  have hz' : ∀ r : Fin nrW, r ∈ ([60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, rPB, rRB,
      rSC, rCL, rM, rLC, cA, dS] : List (Fin nrW)) → σ.val r = 0 := fun r hr => by
    apply hz
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- proofBits
  have e1 := binRW_exec (cap := cap) pS (X := rPB) (P := 60) (Q := 61) (T := 62) (SC := 63) (by decide) pb.bits σ
    (by rw [hp]; exact RdEq.refl _) hph (hz' _ (by simp)) (hz' _ (by simp)) (hz' _ (by simp)) (hz' _ (by simp))
    (hz' _ (by simp)) (by omega)
  rw [LitDecode.value_bits] at e1
  -- rb
  have e2 := binRW_exec (cap := cap) rS (X := rRB) (P := 60) (Q := 61) (T := 62) (SC := 63) (by decide) rb.bits
    (σ.setv rPB pb) (by simp only [WState.setv_st]; rw [hr]; exact RdEq.refl _) (by simpa using hrh)
    (by simp (config := { decide := true }) [Function.update_apply]; exact hz' _ (by simp))
    (by simp (config := { decide := true }) [Function.update_apply]; exact hz' _ (by simp))
    (by simp (config := { decide := true }) [Function.update_apply]; exact hz' _ (by simp))
    (by simp (config := { decide := true }) [Function.update_apply]; exact hz' _ (by simp))
    (by simp (config := { decide := true }) [Function.update_apply]; exact hz' _ (by simp))
    (by omega)
  rw [LitDecode.value_bits] at e2
  -- sysCount
  have hsc2 : 2 ^ (natBitLength sc + 1) ≤ 4 * sc + 4 := by
    unfold natBitLength
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · subst h0; simp
    · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hpos)
      have e : 2 ^ (Nat.log 2 sc + 1 + 1) = 4 * 2 ^ Nat.log 2 sc := by rw [pow_succ, pow_succ]; ring
      omega
  have e3 := readRW_exec (cap := cap) cS sc rest ((σ.setv rPB pb).setv rRB rb) (by simpa using hc) (by simpa using hch)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [Function.update_apply] <;> exact hz' _ (by simp))
    (by omega)
  -- cl
  have e4 := clA_exec (cap := cap) d q (((σ.setv rPB pb).setv rRB rb).setv rSC sc)
    (by simp (config := { decide := true }) [Function.update_apply]; exact hq)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [Function.update_apply] <;> exact hz' _ (by simp))
    (by have := Nat.pow_le_pow_left hXM 2; omega)
  -- M
  have e5 := clB_exec (cap := cap) (clauseWidth d q) ((((σ.setv rPB pb).setv rRB rb).setv rSC sc).setv rCL
    (clauseWidth d q)) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [Function.update_apply] <;> exact hz' _ (by simp))
    (by omega)
  -- aux
  set τ := ((((((σ.setv rPB pb).setv rRB rb).setv rSC sc).setv rCL (clauseWidth d q)).setv rM
    (2 ^ clauseWidth d q)).setv rLC (2 ^ clauseWidth d q)) with hτ
  have zcA : σ.val cA = 0 := hz' _ (by simp)
  have zdS : σ.val dS = 0 := hz' _ (by simp)
  have e6 := Codec.dupR_spec cap rPB cA dS (by decide) (by decide) (by decide) τ
    (by simp (config := { decide := true }) [hτ, Function.update_apply, zdS])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, zcA]; omega)
  have e7 := Codec.dupR_spec cap rM cA dS (by decide) (by decide) (by decide) (τ.setv cA (τ.val cA + τ.val rPB))
    (by simp (config := { decide := true }) [hτ, Function.update_apply, zdS])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, zcA]; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.wm (WExec.seq e6 e7))))))) ?_ ?_
  · clear e1 e2 e3 e4 e5 e6 e7
    simp only [regsSt, hτ, LitDecode.setv_setv]
    simp (config := { decide := true }) [Function.update_apply, zcA]
  · simp (config := { decide := true }) [regsCost, hτ, Function.update_apply, zcA]

end

end NearCubicGates.Close.Setup
