import Proof.Gates.CounterMachine.CellTablesMain3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {B1 B2 cT : ℕ}

theorem cellInput_le (r : CellReq B1 B2 cT) :
    (cellInput r).length ≤ 2 ^ 19 * (r.c.n + 1) ^ (B1 + B2 + 13) := by
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  set c := r.c
  set N := c.n + 1 with hN
  have hN5 : 5 ≤ N := by have := hadm.1; omega
  have hN1 : 1 ≤ N := by omega
  set Q := N ^ (B1 + B2 + 8) with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have q1 : N ≤ Q := by simpa using Cells.pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have q2 : N ^ 2 ≤ Q := Cells.pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ Q := Cells.pw_le hN1 (by omega)
  have qB : N ^ B2 ≤ Q := Cells.pw_le hN1 (by omega)
  have hW := hadm.2.2.2.2.2.2.1
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hbits : ∀ x ∈ cellN c r.p r.wt, natBitLength x ≤ 2 ^ 10 * Q := by
    intro x hx
    simp only [cellN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · have := Cells.call_bits c hadm x hx; rw [← hN] at this; omega
    · have := Cells.params_bits c r.p hadm hs x hx; rw [← hN] at this; omega
    · have := Cells.wit_bits c r.p hadm hs r.wt w hw x hx; omega
  have hlen : (cellN c r.p r.wt).length ≤ 70 * N ^ 5 := by
    have h1 := Cells.call_len c hadm
    have h2 := Cells.params_len c r.p hadm hs
    have h3 := Cells.wit_len c r.p hadm hs r.wt w hw
    have hJ := (J_le_Jmax c r.p hs).trans (Cells.Jmax_le c r.p hadm hs)
    have e1 : (2 * c.W) ≤ 4 * N ^ 4 := by omega
    have e2 : r.p.J * 2 * (1 + 2 * c.W) ≤ 2 * N * (1 + 4 * N ^ 4) := by
      have := Nat.mul_le_mul (show r.p.J * 2 ≤ 2 * N by omega) (show 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 by omega)
      exact this
    rw [← hN] at h1 h2
    have e3 : N ^ 5 = N * N ^ 4 := by ring
    have e4 : 5 * N ^ 4 ≤ N ^ 5 := by rw [e3]; exact Nat.mul_le_mul_right _ hN5
    have e5 : N ≤ N ^ 4 := by simpa using Cells.pw_le hN1 (show 1 ≤ 4 by omega)
    have e6 : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
    have e7 : 2 * N * (1 + 4 * N ^ 4) = 2 * N + 8 * N ^ 5 := by ring
    simp only [cellN, List.length_append]
    omega
  have hcell : cellInput r = (cellN c r.p r.wt).flatMap natWord := by
    rw [cellN_word]; rfl
  rw [hcell]
  have h := Cells.flat_len_le _ _ hbits
  have h5 : N ^ 5 * Q = N ^ (B1 + B2 + 13) := by rw [hQ, ← pow_add]; ring_nf
  calc _ ≤ (cellN c r.p r.wt).length * (2 * (2 ^ 10 * Q) + 1) := h
    _ ≤ 70 * N ^ 5 * (2 ^ 12 * Q) := Nat.mul_le_mul hlen (by omega)
    _ ≤ 2 ^ 19 * N ^ (B1 + B2 + 13) := by rw [← h5]; nlinarith

end NearCubicGates.Close.CounterMachine.CellTablesProg
