import Proof.Gates.CounterMachine.CellTablesCls2
import Proof.Gates.CounterMachine.CellTablesPackSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem size_pred_le_clog (m : ℕ) : Nat.size (m - 1) ≤ Nat.clog 2 m := by
  rw [Nat.size_le]
  have := Nat.le_pow_clog (by norm_num : 1 < 2) m
  have := Nat.one_le_two_pow (n := Nat.clog 2 m)
  omega

theorem kLow_le (cT n : ℕ) : kLow cT (natBitLength n) ≤ Counter.inner cT n := by
  unfold kLow Counter.inner Jmax
  have h1 : natBitLength n - 1 ≤ Target.lambda n := by
    unfold natBitLength Target.lambda
    simp only [Nat.add_sub_cancel]
    exact Nat.log_le_clog 2 n
  have h2 : Nat.size (natBitLength n - 2) ≤ Target.mu n := by
    have e : natBitLength n - 2 = (natBitLength n - 1) - 1 := by omega
    rw [e]
    refine (size_pred_le_clog _).trans ?_
    unfold Target.mu
    exact Nat.clog_mono_right 2 h1
  have h3 : 2 + cT + 3 * Nat.size (natBitLength n - 2) ≤ 2 * (Target.mu n + 1) + cT + Target.mu n := by omega
  exact Nat.mul_le_mul h3 h1

/-- `leadOnes` of the cell input is `natBitLength n`. -/
theorem leadOnes_cellInput (r : CellReq B1 B2 cT) : leadOnes (cellInput r) = natBitLength r.c.n := by
  show leadOnes (callWord r.c ++ paramsWord r.p ++ witWord r.c r.p r.wt) = _
  unfold callWord
  simp only [List.append_assoc]
  exact leadOnes_natWord _ _

theorem cellInput_natWord (r : CellReq B1 B2 cT) : ∃ rest, cellInput r = natWord r.c.n ++ rest := by
  show ∃ rest, callWord r.c ++ paramsWord r.p ++ witWord r.c r.p r.wt = natWord r.c.n ++ rest
  unfold callWord
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

/-! ## Widths of RK's tables -/

theorem recStream_length (L : List ℕ) (f : ℕ → List Bool) (w : ℕ) (hf : ∀ i, (f i).length = w) :
    (WordPrograms.recStream (L.map f)).length = L.length * (2 * w + 1) + 1 := by
  unfold WordPrograms.recStream
  rw [List.length_append, WordPrograms.flatMap_frame_length w _ (by intro v hv; simp at hv; obtain ⟨i, _, rfl⟩ := hv; exact hf i)]
  simp

theorem width_le (RK : TabCallMachine B1 B2 cT PolyTab) (C0 e0 : ℕ)
    (hRK : ∀ x : TabCallReq B1 B2 cT, RK.budget x ≤ C0 * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e0)
    (x : TabCallReq B1 B2 cT) : PolyTab.width (tabCallTab x) ≤ C0 * (x.r.c.n + 1) ^ e0 := by
  have h1 := Cells.wf_out_len RK.wf x
  have h2 : (tabCallOutput PolyTab x).length = 2 ^ (x.r.c.n - x.r.p.k) * (2 * PolyTab.width (tabCallTab x) + 1) + 1 := by
    unfold tabCallOutput tableWord
    rw [recStream_length _ _ (PolyTab.width (tabCallTab x)) (fun i => RepairOrdinary.SignedSortKey.binary_length _ _),
      CellTables.printerOrder_length, tabCallTab_s]
  have h3 := hRK x
  rw [h2] at h1
  have h4 : 2 ^ (x.r.c.n - x.r.p.k) * (2 * PolyTab.width (tabCallTab x) + 1) ≤ 2 ^ (x.r.c.n - x.r.p.k) *
      (C0 * (x.r.c.n + 1) ^ e0) := by
    have : C0 * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e0 = 2 ^ (x.r.c.n - x.r.p.k) * (C0 * (x.r.c.n + 1) ^ e0) := by
      ring
    omega
  have h5 := Nat.le_of_mul_le_mul_left h4 (Nat.two_pow_pos _)
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
