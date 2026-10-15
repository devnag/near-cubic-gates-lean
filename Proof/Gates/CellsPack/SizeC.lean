import Proof.Gates.CellsPack.SizeB

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.SystemsPhase

noncomputable def kC (S : SolveMachine) : ℕ := S.cls.choose
noncomputable def kE (S : SolveMachine) : ℕ := S.cls.choose_spec.choose
theorem kC_spec (S : SolveMachine) (s : SysReq) : S.budget s ≤ kC S * ((sysWord s).length + 1) ^ kE S :=
  S.cls.choose_spec.choose_spec s

noncomputable def zOf (S : SolveMachine) (B1 B2 : ℕ) : Sz :=
  ⟨2 ^ 22, B1 + B2 + 10, 2 ^ 12, 9, kC S * 2 ^ (13 * kE S), 9 * kE S⟩

theorem pow_L_ge (n c : ℕ) : (n + 1) ^ c ≤ 2 ^ (c * natBitLength n) := by
  rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (CounterMachine.PrefixProg.pow_nbl n) c

theorem zOf_ok (S : SolveMachine) (B1 B2 : ℕ) : SzOK S B1 B2 (bigOf B1 B2) (zOf S B1 B2) := by
  intro cT r
  rw [leadOnes_pkIn]
  have hY1 : 1 ≤ r.c.n + 1 := by omega
  have hW : (zOf S B1 B2).W (natBitLength r.c.n) = 2 ^ ((B1 + B2 + 10) * natBitLength r.c.n) * 2 ^ 22 := rfl
  have hLk : (zOf S B1 B2).Lk (natBitLength r.c.n) = 2 ^ (9 * natBitLength r.c.n) * 2 ^ 12 := rfl
  have hBk : (zOf S B1 B2).Bk (natBitLength r.c.n) =
      2 ^ (9 * kE S * natBitLength r.c.n) * (kC S * 2 ^ (13 * kE S)) := rfl
  have p1 := pow_L_ge r.c.n (B1 + B2 + 10)
  have p2 := pow_L_ge r.c.n 9
  have p3 := pow_L_ge r.c.n (9 * kE S)
  refine ⟨?_, ?_, fun y part κ _ => ⟨?_, ?_⟩⟩
  · rw [hW]; have : 1 ≤ 2 ^ ((B1 + B2 + 10) * natBitLength r.c.n) := Nat.one_le_two_pow
    have : (3 : ℕ) ≤ 2 ^ 22 := by norm_num
    nlinarith
  · rw [hW]
    calc _ ≤ 2 ^ 22 * (r.c.n + 1) ^ (B1 + B2 + 10) := wdNeed_le r
      _ ≤ 2 ^ 22 * 2 ^ ((B1 + B2 + 10) * natBitLength r.c.n) := Nat.mul_le_mul_left _ p1
      _ = _ := by ring
  · rw [hLk]
    calc _ ≤ 2 ^ 12 * (r.c.n + 1) ^ 9 := sysWord_len r y part κ
      _ ≤ 2 ^ 12 * 2 ^ (9 * natBitLength r.c.n) := Nat.mul_le_mul_left _ p2
      _ = _ := by ring
  · rw [hBk]
    have hs := sysWord_len r y part κ
    have hY9 : 1 ≤ (r.c.n + 1) ^ 9 := Nat.one_le_pow _ _ hY1
    have h1 : (sysWord (sysOf r.c r.p r.wt y κ part)).length + 1 ≤ 2 ^ 13 * (r.c.n + 1) ^ 9 := by
      have : 2 ^ 13 * (r.c.n + 1) ^ 9 = 2 * (2 ^ 12 * (r.c.n + 1) ^ 9) := by ring
      omega
    calc S.budget (sysOf r.c r.p r.wt y κ part) ≤ kC S * ((sysWord (sysOf r.c r.p r.wt y κ part)).length + 1) ^ kE S :=
          kC_spec S _
      _ ≤ kC S * (2 ^ 13 * (r.c.n + 1) ^ 9) ^ kE S := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = kC S * 2 ^ (13 * kE S) * (r.c.n + 1) ^ (9 * kE S) := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ kC S * 2 ^ (13 * kE S) * 2 ^ (9 * kE S * natBitLength r.c.n) := Nat.mul_le_mul_left _ p3
      _ = _ := by ring

/-- The table word's length. -/
theorem cellWord_len {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    (cellWord r.c r.p r.wt).length = 2 ^ (r.c.n - r.p.k) * (reqIds r.c r.p).length *
      (2 * recWidth r.c r.p r.wt + 1) + 1 := by
  obtain ⟨w, hw⟩ := r.hw
  have hcard := decodeWitness_card r.c r.p w r.wt hw
  unfold cellWord
  rw [WordPrograms.recStream_length (recWidth r.c r.p r.wt) _ (fun x hx => by
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; exact NearCubicWires.RepairOrdinary.SignedSortKey.binary_length _ _)]
  rw [List.length_map, List.length_insertionSort, List.length_flatMap]
  simp only [List.length_map, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  unfold cellBits
  rw [CounterMachine.outerCoords_length r.wt.I hcard]

end NearCubicGates.Close.CellsPack
