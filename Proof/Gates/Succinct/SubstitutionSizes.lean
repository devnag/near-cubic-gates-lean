import Proof.Gates.Succinct.SubstitutionCount

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct
open RepairRepresentation (natWord)

variable {q : ℕ}

/-- The size of the fold (`|accI n_C|`). -/
def szv (o : OracleOutput) (B : BooleanCircuit q) : ℕ :=
  kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) + o.circuit.nodes.length + 1

theorem szv_eq (o : OracleOutput) (B : BooleanCircuit q) :
    (accI B o.circuit o.circuit.nodes.length).1.length = szv o B := by
  have h := accI_fst_len B o.circuit o.circuit.nodes.length le_rfl
  have hB : 1 ≤ B.nodes.length := by have := B.output.isLt; omega
  unfold szv
  obtain ⟨m, hm⟩ : ∃ m, B.nodes.length = m + 1 := ⟨B.nodes.length - 1, by omega⟩
  rw [hm] at h ⊢
  simp only [Nat.add_sub_cancel, Nat.mul_succ] at h ⊢
  omega

/-- The registers after the sizes. -/
def V3 (o : OracleOutput) (B : BooleanCircuit q) : HReg → ℕ := fun u =>
  if u = .sz then szv o B else if u = .pd then q - (szv o B + 1) else
  if u = .M then szv o B + 1 + (q - (szv o B + 1)) else V2 o B u

/-- The cost class of the sizes. -/
def sizesCost (S : ℕ) : ℕ := 1000 * (S + 2) ^ 2

theorem kOf_le (o : OracleOutput) : kOf o.circuit o.circuit.nodes.length ≤ o.circuit.nodes.length := by
  unfold kOf; exact (List.countP_le_length).trans (by simp)

set_option maxHeartbeats 1600000 in
/-- **The sizes** (paper §11.4: `D_B` padded to `q` inputs, `padToArity`). -/
theorem sizes_spec (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (σ : WState 4 nrH) (hC : CntPost o B σ)
    (hcap : 4 * (sizeS o B + 2) ^ 2 ≤ cap) :
    ∃ τ, WXExec cap sizes σ τ (sizesCost (sizeS o B)) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ RV τ (V3 o B) ∧
      τ.cell = σ.cell := by
  obtain ⟨_, hv, _⟩ := hC
  have hv' : ∀ u, σ.val (regH u) = V2 o B u := hv
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hk := kOf_le o
  have hsq : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hkn : kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) ≤ (sizeS o B + 2) ^ 2 := by
    calc kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1)
        ≤ (sizeS o B + 2) * (sizeS o B + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = (sizeS o B + 2) ^ 2 := by ring
  have hsz : szv o B = kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) + o.circuit.nodes.length + 1 := rfl
  have fk : σ.val (regH .k) = kOf o.circuit o.circuit.nodes.length := by rw [hv']; simp [V2]
  have fn1 : σ.val (regH .nB1) = B.nodes.length - 1 := by rw [hv']; simp [V2, V1]
  have fnC : σ.val (regH .nC) = o.circuit.nodes.length := by rw [hv']; simp [V2, V1]
  have fq : σ.val (regH .q) = q := by rw [hv']; simp [V2, V1]
  have z : ∀ u, u ∈ [HReg.sz, .gb, .t, .pd, .x, .M] → σ.val (regH u) = 0 := by
    intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hv'] <;> simp [V2, V1]
  have e1 := mulR_spec cap (A := regH .k) (A2 := regH .gb) (B := regH .nB1) (C := regH .sz) (T := regH .t)
    (by simp) σ (z _ (by simp)) (z _ (by simp)) (by rw [z _ (by simp), fk, fn1]; omega) (by rw [fk]; omega)
  rw [z _ (by simp), fk, fn1, Nat.zero_add] at e1
  set σ1 := σ.setv (regH .sz) (kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1)) with hσ1
  have e2 := addTo_spec cap (regH .nC) (regH .sz) (regH .t) (by simp) (by simp) (by simp) σ1
    (by simp [σ1, z _ (show HReg.t ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]) (by simp [σ1, fnC]; omega)
    (by simp [σ1, fnC]; omega)
  rw [show σ1.val (regH .sz) + σ1.val (regH .nC) = kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) +
    o.circuit.nodes.length by simp [σ1, fnC]] at e2
  set σ2 := σ1.setv (regH .sz) (kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1) + o.circuit.nodes.length)
    with hσ2
  have e3 := WExec.inc (cap := cap) (regH .sz) σ2 (by simp [σ2]; omega)
  rw [show σ2.val (regH .sz) + 1 = szv o B by simp [σ2, hsz]] at e3
  set σ3 := σ2.setv (regH .sz) (szv o B) with hσ3
  have e4 := addTo_spec cap (regH .q) (regH .pd) (regH .t) (by simp) (by simp) (by simp) σ3
    (by simp [σ3, σ2, σ1, z _ (show HReg.t ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]) (by simp [σ3, σ2, σ1, fq]; omega)
    (by simp [σ3, σ2, σ1, fq, z _ (show HReg.pd ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]; omega)
  rw [show σ3.val (regH .pd) + σ3.val (regH .q) = q by
    simp [σ3, σ2, σ1, fq, z _ (show HReg.pd ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]] at e4
  set σ4 := σ3.setv (regH .pd) q with hσ4
  have e5 := addTo_spec cap (regH .sz) (regH .x) (regH .t) (by simp) (by simp) (by simp) σ4
    (by simp [σ4, σ3, σ2, σ1, z _ (show HReg.t ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]) (by simp [σ4, σ3]; omega)
    (by simp [σ4, σ3, σ2, σ1, z _ (show HReg.x ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]; omega)
  rw [show σ4.val (regH .x) + σ4.val (regH .sz) = szv o B by
    simp [σ4, σ3, σ2, σ1, z _ (show HReg.x ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]] at e5
  set σ5 := σ4.setv (regH .x) (szv o B) with hσ5
  have e6 := WExec.inc (cap := cap) (regH .x) σ5 (by simp [σ5]; omega)
  set σ6 := σ5.setv (regH .x) (σ5.val (regH .x) + 1) with hσ6
  -- `pd := q − (sz + 1)`
  let S : ℕ → WState 4 nrH := fun j => (σ5.setv (regH .x) (szv o B + 1 - j)).setv (regH .pd) (q - j)
  have hS0 : S 0 = σ6 := by
    refine WState.eq rfl rfl ?_ rfl
    funext r; simp only [S, σ6, σ5, σ4, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all
  have e7 := UnionMachine.Round.wloop cap (regH .x) (.dec (regH .pd)) 1 (szv o B + 1) S
    (fun j _ => by simp [S, Function.update_apply]) (by omega)
    (fun j _ => by
      have := WExec.dec (cap := cap) (regH .pd) ((S j).setv (regH .x) (szv o B + 1 - j - 1)) (by simp [S]; omega)
      refine WExec.cast cap this ?_ le_rfl
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [S, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all <;> omega)
  rw [hS0] at e7
  set σ7 := S (szv o B + 1) with hσ7
  have f7 : ∀ u, σ7.val (regH u) = if u = .pd then q - (szv o B + 1) else if u = .x then 0 else
      if u = .sz then szv o B else σ.val (regH u) := by
    intro u; simp only [σ7, S, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply, regH_eq_iff]
    split_ifs <;> simp_all
  have e8 := addTo_spec cap (regH .sz) (regH .M) (regH .t) (by simp) (by simp) (by simp) σ7
    (by rw [f7]; simp [z _ (show HReg.t ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]) (by rw [f7]; simp; omega)
    (by rw [f7, f7]; simp [z _ (show HReg.M ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]; omega)
  rw [show σ7.val (regH .M) + σ7.val (regH .sz) = szv o B by
    rw [f7, f7]; simp [z _ (show HReg.M ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)]] at e8
  set σ8 := σ7.setv (regH .M) (szv o B) with hσ8
  have e9 := WExec.inc (cap := cap) (regH .M) σ8 (by simp [σ8]; omega)
  set σ9 := σ8.setv (regH .M) (σ8.val (regH .M) + 1) with hσ9
  have e10 := addTo_spec cap (regH .pd) (regH .M) (regH .t) (by simp) (by simp) (by simp) σ9
    (by simp [σ9, σ8, Function.update_apply, f7, z _ (show HReg.t ∈ [HReg.sz, .gb, .t, .pd, .x, .M] by simp)])
    (by simp [σ9, σ8, Function.update_apply, f7]; omega) (by simp [σ9, σ8, Function.update_apply, f7]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.wm (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10)))))))))) ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : σ1.val (regH .nC) = o.circuit.nodes.length := by simp [σ1, fnC]
    have c3 : σ3.val (regH .q) = q := by simp [σ3, σ2, σ1, fq]
    have c4 : σ4.val (regH .sz) = szv o B := by simp [σ4, σ3]
    have c7 : σ7.val (regH .sz) = szv o B := by rw [f7]; simp
    have c9 : σ9.val (regH .pd) = q - (szv o B + 1) := by simp [σ9, σ8, Function.update_apply, f7]
    rw [c1, c3, c4, c7, c9]
    have hm : kOf o.circuit o.circuit.nodes.length * (18 * (B.nodes.length - 1) + 3 + 8) ≤
        18 * (kOf o.circuit o.circuit.nodes.length * (B.nodes.length - 1)) + 11 * (sizeS o B + 2) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm _ (18 * _), Nat.mul_assoc]; nlinarith
    unfold sizesCost
    omega
  · simp [σ9, σ8, σ7, S, σ5, σ4, σ3, σ2, σ1]
  · simp [σ9, σ8, σ7, S, σ5, σ4, σ3, σ2, σ1]
  · intro u; simp only [σ9, σ8, WState.setv_val, Function.update_apply, regH_eq_iff, f7]
    unfold V3; rw [hv']; split_ifs <;> simp_all
  · simp [σ9, σ8, σ7, S, σ5, σ4, σ3, σ2, σ1]

end NearCubicGates.Close.Succinct.SubstMachine
