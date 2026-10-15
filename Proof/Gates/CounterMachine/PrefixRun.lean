import Proof.Gates.CounterMachine.PrefixMain
import Proof.Gates.Cells.InputLen
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.RepairOrdinary (frame)

/-! ## Sizes -/

section Sizes
variable {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT)

theorem cellInput_eq : cellInput r = (cellN r.c r.p r.wt).flatMap natWord := (cellN_word _ _ _).symm

theorem cellN_len_le : (cellN r.c r.p r.wt).length ≤ (cellInput r).length := by
  rw [cellInput_eq, List.length_flatMap]
  calc (cellN r.c r.p r.wt).length = ((cellN r.c r.p r.wt).map fun _ => 1).sum := by simp
    _ ≤ _ := by
      apply List.sum_le_sum; intro x _; rw [natWord_length]; omega

theorem nbl_cellN (x : ℕ) (hx : x ∈ cellN r.c r.p r.wt) : natBitLength x ≤ (cellInput r).length := by
  rw [cellInput_eq]; exact (nbl_le_word x).trans (len_le_flatMap _ _ x hx)

theorem mem_cellN_of_call {x : ℕ} (hx : x ∈ callN r.c) : x ∈ cellN r.c r.p r.wt := by
  unfold cellN; simp [hx]

theorem mem_cellN_of_params {x : ℕ} (hx : x ∈ paramsN r.p) : x ∈ cellN r.c r.p r.wt := by
  unfold cellN; simp [hx]

theorem mem_cellN_of_wit {x : ℕ} (hx : x ∈ witN r.c r.p r.wt) : x ∈ cellN r.c r.p r.wt := by
  unfold cellN; simp [hx]

theorem coords_sub (x : ℕ) (hx : x ∈ coordsOf r.wt.I) : x ∈ cellN r.c r.p r.wt :=
  mem_cellN_of_wit r (by unfold witN; simp [hx])

theorem blk1_sub (x : ℕ) (hx : x ∈ r.c.first.gates.flatMap gateN) : x ∈ cellN r.c r.p r.wt :=
  mem_cellN_of_call r (by unfold callN circN; simp only [List.mem_append]; tauto)

theorem blk2_sub (x : ℕ) (hx : x ∈ r.c.second.gates.flatMap gateN) : x ∈ cellN r.c r.p r.wt :=
  mem_cellN_of_call r (by unfold callN circN; simp only [List.mem_append]; tauto)

theorem split_len : (cellN r.c r.p r.wt).length = 2 + (circN r.c.first).length + (circN r.c.second).length + 1 +
    r.c.parity.length + (callTail r.c r.p r.wt).length := by
  rw [cellN_split]; simp; omega

theorem circ_len_ge {n : ℕ} (Cc : NCircuit n) : 1 + (Cc.gates.flatMap gateN).length ≤ (circN Cc).length := by
  rw [circN_eq]; simp; omega

theorem gates_le_circ {n : ℕ} (Cc : NCircuit n) : Cc.gates.length ≤ (circN Cc).length := by
  have h := circ_len_ge Cc
  rw [gates_flat_length] at h
  nlinarith

theorem tail_len : (coordsOf r.wt.I).length + 1 ≤ (callTail r.c r.p r.wt).length := by
  unfold callTail; simp; omega

theorem J_le_tail : r.p.J ≤ (callTail r.c r.p r.wt).length := by
  have h1 : r.p.J ≤ (srList r.c r.p).length := by
    rw [srList_len]; have := roleCount_pos r.c.kind; nlinarith
  have h2 : (srList r.c r.p).length ≤ (witRest r.c r.p r.wt).length := by
    unfold witRest; rw [List.length_flatMap]
    calc (srList r.c r.p).length = ((srList r.c r.p).map fun _ => 1).sum := by simp
      _ ≤ _ := by apply List.sum_le_sum; intro x _; simp
  unfold callTail; simp; omega

/-- A call with `W ≠ 0` has a gate, so `n` is at most the cell input's length. -/
theorem n_le_cellN : r.c.n ≤ (cellN r.c r.p r.wt).length := by
  have hW := r.hW
  unfold Call.W at hW
  have hne : r.c.first.gates ≠ [] ∨ r.c.second.gates ≠ [] := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    have h1 : r.c.first.coeffs = [] := by
      have := r.adm.2.1.1; rw [hcon.1] at this; exact List.eq_nil_of_length_eq_zero this.symm
    have h2 : r.c.second.coeffs = [] := by
      have := r.adm.2.2.1.1; rw [hcon.2] at this; exact List.eq_nil_of_length_eq_zero this.symm
    apply hW; simp [NCircuit.topWeight, h1, h2]
  have hlen := split_len r
  rcases hne with h | h
  · have := circ_len_ge r.c.first
    rw [gates_flat_length] at this
    have : 1 ≤ r.c.first.gates.length := List.length_pos_of_ne_nil h
    nlinarith
  · have := circ_len_ge r.c.second
    rw [gates_flat_length] at this
    have : 1 ≤ r.c.second.gates.length := List.length_pos_of_ne_nil h
    nlinarith

theorem leadOnes_rep (L : ℕ) (w : List Bool) : leadOnes (List.replicate L true ++ false :: w) = L := by
  induction L with
  | zero => simp [leadOnes]
  | succ L ih => simp only [List.replicate_succ, List.cons_append, leadOnes, ih]

theorem leadOnes_natWord (v : ℕ) (rest : List Bool) : leadOnes (natWord v ++ rest) = natBitLength v := by
  rw [natWord_eq, List.append_assoc, List.cons_append, leadOnes_rep]

theorem leadOnes_cellInput : leadOnes (cellInput r) = natBitLength r.c.n := by
  unfold cellInput callWord; simp only [List.append_assoc]; exact leadOnes_natWord _ _

end Sizes

/-! ## The program -/

def cstInit : St VV MM := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

/-- **The prefix program.** -/
def mainP : St VV MM := .seq cstInit (.seq loadP (.seq parseP (.seq setupG (.seq resBlock momBlock))))

theorem cstInit_spec (C : Ctx) (hW : 2 ≤ C.Wd) : Hs C cstInit (a0 : DS VV MM) 5 (fun d => Cst d ∧
    d.ram = (fun _ => []) ∧ d.rc = (fun _ => 0) ∧ d.ip = 0 ∧ d.out = [] ∧ d.kin = [] ∧ d.kout = [] ∧ d.kc = 0) := by
  have h4 : 4 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  unfold cstInit
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C v1 a0 (by simp [a0]; omega)) (fun d1 hd1 => ?_)
  subst hd1
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C v2 _ (by vsimp [a0]; omega)) (fun d2 hd2 => ?_)
  subst hd2
  refine Hs.mono (hs_inc C v2 _ (by vsimp [a0]; omega)) le_rfl ?_
  rintro d rfl
  exact ⟨⟨by vsimp [a0], by vsimp [a0], by vsimp [a0]⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NearCubicGates.Close.CounterMachine.PrefixProg
