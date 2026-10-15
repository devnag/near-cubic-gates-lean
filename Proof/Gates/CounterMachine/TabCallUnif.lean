import Proof.Gates.CounterMachine.TabCallNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter NearCubicGates.Close.CheckedPCPP

/-! ## The uniform cell-input bound -/

section Cin
open NearCubicGates.Close.Cells

/-- `|cellInput r| ≤ 2^19·(n+1)^{B₁+B₂+13}` for every `c_T` (the proof of `Cells.cellInput_length_le`). -/
theorem cellInput_unif {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
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
  have q1 : N ≤ Q := by simpa using pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have q2 : N ^ 2 ≤ Q := pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ Q := pw_le hN1 (by omega)
  have qB : N ^ B2 ≤ Q := pw_le hN1 (by omega)
  have hW := hadm.2.2.2.2.2.2.1
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hbits : ∀ x ∈ cellN c r.p r.wt, natBitLength x ≤ 2 ^ 10 * Q := by
    intro x hx
    simp only [cellN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · have := call_bits c hadm x hx; rw [← hN] at this; omega
    · have := params_bits c r.p hadm hs x hx; rw [← hN] at this; omega
    · have := wit_bits c r.p hadm hs r.wt w hw x hx; omega
  have hlen : (cellN c r.p r.wt).length ≤ 70 * N ^ 5 := by
    have h1 := call_len c hadm
    have h2 := params_len c r.p hadm hs
    have h3 := wit_len c r.p hadm hs r.wt w hw
    have hJ := (J_le_Jmax c r.p hs).trans (Jmax_le c r.p hadm hs)
    have e1 : (2 * c.W) ≤ 4 * N ^ 4 := by omega
    have e2 : r.p.J * 2 * (1 + 2 * c.W) ≤ 2 * N * (1 + 4 * N ^ 4) := by
      have := Nat.mul_le_mul (show r.p.J * 2 ≤ 2 * N by omega) (show 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 by omega)
      exact this
    rw [← hN] at h1 h2
    have e3 : N ^ 5 = N * N ^ 4 := by ring
    have e4 : 5 * N ^ 4 ≤ N ^ 5 := by rw [e3]; exact Nat.mul_le_mul_right _ hN5
    have e5 : N ≤ N ^ 4 := by simpa using pw_le hN1 (show 1 ≤ 4 by omega)
    have e6 : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
    have e7 : 2 * N * (1 + 4 * N ^ 4) = 2 * N + 8 * N ^ 5 := by ring
    simp only [cellN, List.length_append]
    omega
  have hcell : cellInput r = (cellN c r.p r.wt).flatMap natWord := by
    rw [cellN_word]; rfl
  rw [hcell]
  have h := flat_len_le _ _ hbits
  have h5 : N ^ 5 * Q = N ^ (B1 + B2 + 13) := by rw [hQ, ← pow_add]; ring_nf
  calc _ ≤ (cellN c r.p r.wt).length * (2 * (2 ^ 10 * Q) + 1) := h
    _ ≤ 70 * N ^ 5 * (2 ^ 12 * Q) := Nat.mul_le_mul hlen (by omega)
    _ ≤ 2 ^ 19 * N ^ (B1 + B2 + 13) := by rw [← h5]; nlinarith

end Cin

/-! ## The index and the classes -/

/-- Every request of every clock constant. -/
abbrev TabCallIndex (B1 B2 : ℕ) : Type := (cT : ℕ) × TabCallReq B1 B2 cT

variable {B1 B2 : ℕ}

/-- The size `n`. -/
def nI (i : TabCallIndex B1 B2) : ℕ := i.2.r.c.n

/-- The outer dimension `s = n − k`. -/
def sI (i : TabCallIndex B1 B2) : ℕ := i.2.r.c.n - i.2.r.p.k

/-- The tabulation-path class, uniform in `c_T`. -/
def TB (f : TabCallIndex B1 B2 → ℕ) : Prop := ∃ C e : ℕ, ∀ i, f i ≤ C * 2 ^ sI i * (nI i + 1) ^ e

theorem TB.of_le {f g : TabCallIndex B1 B2 → ℕ} (hg : PolyB nI g) (h : ∀ i, f i ≤ 2 ^ sI i * g i) : TB f := by
  obtain ⟨C, e, hC⟩ := hg
  refine ⟨C, e, fun i => (h i).trans ?_⟩
  calc 2 ^ sI i * g i ≤ 2 ^ sI i * (C * (nI i + 1) ^ e) := Nat.mul_le_mul_left _ (hC i)
    _ = C * 2 ^ sI i * (nI i + 1) ^ e := by ring

theorem TB.ofPoly {f : TabCallIndex B1 B2 → ℕ} (hf : PolyB nI f) : TB f :=
  TB.of_le hf fun i => by have := Nat.one_le_two_pow (n := sI i); nlinarith

theorem TB.mono {f g : TabCallIndex B1 B2 → ℕ} (hg : TB g) (h : ∀ i, f i ≤ g i) : TB f := by
  obtain ⟨C, e, hC⟩ := hg
  exact ⟨C, e, fun i => (h i).trans (hC i)⟩

theorem TB.add {f g : TabCallIndex B1 B2 → ℕ} (hf : TB f) (hg : TB g) : TB (fun i => f i + g i) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 + C2, e1 + e2, fun i => ?_⟩
  show f i + g i ≤ _
  have a1 : (nI i + 1) ^ e1 ≤ (nI i + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have a2 : (nI i + 1) ^ e2 ≤ (nI i + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have b1 : C1 * 2 ^ sI i * (nI i + 1) ^ e1 ≤ C1 * 2 ^ sI i * (nI i + 1) ^ (e1 + e2) := Nat.mul_le_mul_left _ a1
  have b2 : C2 * 2 ^ sI i * (nI i + 1) ^ e2 ≤ C2 * 2 ^ sI i * (nI i + 1) ^ (e1 + e2) := Nat.mul_le_mul_left _ a2
  have := h1 i
  have := h2 i
  have e : (C1 + C2) * 2 ^ sI i * (nI i + 1) ^ (e1 + e2) =
      C1 * 2 ^ sI i * (nI i + 1) ^ (e1 + e2) + C2 * 2 ^ sI i * (nI i + 1) ^ (e1 + e2) := by ring
  omega

theorem TB.cmul {f : TabCallIndex B1 B2 → ℕ} (c : ℕ) (hf : TB f) : TB (fun i => c * f i) := by
  obtain ⟨C, e, h⟩ := hf
  exact ⟨c * C, e, fun i => by
    calc c * f i ≤ c * (C * 2 ^ sI i * (nI i + 1) ^ e) := Nat.mul_le_mul_left _ (h i)
      _ = c * C * 2 ^ sI i * (nI i + 1) ^ e := by ring⟩

/-! ## Uniform polynomial sizes -/

theorem polyCin : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => (cellInput i.2.r).length) :=
  ⟨2 ^ 19, B1 + B2 + 13, fun i => cellInput_unif i.2.r⟩

theorem descN_len {cT : ℕ} (x : TabCallReq B1 B2 cT) : (descN x.id).length ≤ 2 * x.r.c.n + 8 := by
  have hmem := x.mem
  have hJ := J_le x
  have hrc := TabCallSizes.roleCount_le x.r.c.kind
  cases hid : x.id with
  | residue part q κ σ =>
    rw [hid] at hmem
    obtain ⟨-, hκ, hσ⟩ := TabCallSizes.mem_residue hmem
    rw [Cells.mem_vecs_iff] at hκ hσ
    have : roleCount x.r.c.kind * x.r.p.J ≤ 2 * (x.r.c.n + 1) := Nat.mul_le_mul hrc hJ
    simp only [descN, List.length_append, List.length_cons, List.length_nil, hκ.1, hσ.1]
    omega
  | digitMoment r j => simp [descN]
  | phiMoment r => simp [descN]

theorem polyL : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => (tabCallInput i.2).length) := by
  have hn : PolyB (nI (B1 := B1) (B2 := B2)) nI := PolyB.size
  have hd : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => (2 * nI i + 8) * (2 * (2 * nI i + 5) + 1)) :=
    PolyB.mul (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 8))
      (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 5)))
        (PolyB.const 1))
  refine (PolyB.add hd polyCin).mono fun i => ?_
  rw [tabCallInput, List.length_append]
  have h1 := Cells.flat_len_le (descN i.2.id) (2 * nI i + 5) (fun v hv => by
    have := desc_le i.2 v hv
    have := TabCallSizes.nbl_le_self' v
    unfold nI; omega)
  have h2 : (descN i.2.id).length * (2 * (2 * nI i + 5) + 1) ≤ (2 * nI i + 8) * (2 * (2 * nI i + 5) + 1) :=
    Nat.mul_le_mul_right _ (descN_len i.2)
  omega

theorem polyTab : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => tabSize (tabCallTab i.2)) := by
  open TabCallSizes in
  have hn : PolyB (nI (B1 := B1) (B2 := B2)) nI := PolyB.size
  have hΛ : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => (cellInput i.2.r).length) := polyCin
  have hLf : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => Lf (nI i) (cellInput i.2.r).length) :=
    (PolyB.add (PolyB.mul (PolyB.mul (PolyB.const 2) (PolyB.pow hn 4)) (PolyB.add hΛ (PolyB.const 6)))
      (PolyB.const 2)).mono fun x => le_refl _
  have hRes : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => ResB (nI i) (cellInput i.2.r).length) :=
    (PolyB.mul (PolyB.mul (PolyB.const 3) (PolyB.pow (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 3)) 2))
      (PolyB.add (PolyB.mul (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 4))
        (PolyB.add (PolyB.mul (PolyB.add hn (PolyB.const 1))
          (PolyB.add (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) hLf) hΛ) hn) (PolyB.const 12)))
          (PolyB.const 1))) (PolyB.const 6))).mono fun x => le_refl _
  have hMom : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => MomB (nI i) (cellInput i.2.r).length) :=
    (PolyB.add (PolyB.add (PolyB.mul (PolyB.add (PolyB.mul (PolyB.const 2) hn) (PolyB.const 1))
      (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 4) hLf) (PolyB.mul (PolyB.const 4) hΛ)) (PolyB.const 12)))
      (PolyB.mul (PolyB.const 2) hn)) (PolyB.const 1)).mono fun x => le_refl _
  have hW : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => Wb (nI i) (cellInput i.2.r).length) :=
    (PolyB.add hRes hMom).mono fun x => le_refl _
  have hn4 := PolyB.mul (PolyB.const 4) (PolyB.pow hn 4)
  have hT : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => Tb (nI i) (cellInput i.2.r).length) :=
    (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add hn hn4)
    (PolyB.mul (PolyB.mul (PolyB.const 4) hn) (PolyB.add hn (PolyB.const 1)))) hn4)
    (PolyB.add (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add hn4 (PolyB.const 1))) (PolyB.const 1))
      (PolyB.add (PolyB.mul (PolyB.const 2) hW) (PolyB.const 3)))
      (PolyB.mul hW (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 2) hW)
        (PolyB.mul (PolyB.const 2) (PolyB.add hn4 (PolyB.const 1)))) (PolyB.const 30))))) hW) hW)
    (PolyB.const 1)) (PolyB.const 0)).mono fun x => by unfold Tb; omega
  exact hT.mono fun i => TabCallSizes.tab_le i.2

/-! ## The exponential pieces -/

theorem k_le_s (i : TabCallIndex B1 B2) : 20 * i.2.r.p.k ≤ sI i := by
  have := k_small i.2; unfold sI; omega

theorem two_k_le (i : TabCallIndex B1 B2) : 2 ^ i.2.r.p.k ≤ 2 ^ sI i :=
  Nat.pow_le_pow_right (by norm_num) (by have := k_le_s i; omega)

theorem four_k_le (i : TabCallIndex B1 B2) : 4 ^ i.2.r.p.k ≤ 2 ^ sI i := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by have := k_le_s i; omega)

theorem tb_two_k {g : TabCallIndex B1 B2 → ℕ} (hg : PolyB nI g) : TB (fun i => 2 ^ i.2.r.p.k * g i) :=
  TB.of_le hg fun i => Nat.mul_le_mul_right _ (two_k_le i)

theorem tb_four_k {g : TabCallIndex B1 B2 → ℕ} (hg : PolyB nI g) : TB (fun i => 4 ^ i.2.r.p.k * g i) :=
  TB.of_le hg fun i => Nat.mul_le_mul_right _ (four_k_le i)

/-- The polynomial part of `Λf`. -/
def Apart (i : TabCallIndex B1 B2) : ℕ := 4 * (tabCallInput i.2).length + 40 * (nI i + 1) ^ 4 + 21

theorem Λ_le (i : TabCallIndex B1 B2) : Λf i.2 + 1 ≤ (Apart i + 1) * (4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2)) := by
  have h1 : 1 ≤ 4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2) := Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega)
  have e : (Apart i + 1) * (4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2)) =
      Apart i * (4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2)) + 4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2) := by ring
  have h2 : Apart i ≤ Apart i * (4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2)) := Nat.le_mul_of_pos_right _ h1
  unfold Λf Apart at *; unfold nI at *; omega

theorem tb_Λ5 : TB (fun i : TabCallIndex B1 B2 => (Λf i.2 + 1) ^ 5) := by
  have hA : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => 2 ^ 20 * (Apart i + 1) ^ 5 * (4 * nI i + 6) ^ 5) :=
    PolyB.mul (PolyB.mul (PolyB.const _) (PolyB.pow (PolyB.add (PolyB.add (PolyB.add
      (PolyB.mul (PolyB.const 4) polyL) (PolyB.mul (PolyB.const 40) (PolyB.pow (PolyB.add PolyB.size (PolyB.const 1)) 4)))
      (PolyB.const 21)) (PolyB.const 1)) 5))
      (PolyB.pow (PolyB.add (PolyB.mul (PolyB.const 4) PolyB.size) (PolyB.const 6)) 5)
  refine TB.of_le hA fun i => ?_
  have he := e_le_k i.2
  have hk := k_le i.2
  have hks := k_le_s i
  have h4e : (4 ^ i.2.r.p.e) ^ 5 ≤ 2 ^ 20 * 2 ^ sI i := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2e : (2 * i.2.r.p.e + 2) ^ 5 ≤ (4 * nI i + 6) ^ 5 := Nat.pow_le_pow_left (by unfold nI; omega) 5
  calc (Λf i.2 + 1) ^ 5 ≤ ((Apart i + 1) * (4 ^ i.2.r.p.e * (2 * i.2.r.p.e + 2))) ^ 5 :=
        Nat.pow_le_pow_left (Λ_le i) 5
    _ = (Apart i + 1) ^ 5 * (4 ^ i.2.r.p.e) ^ 5 * (2 * i.2.r.p.e + 2) ^ 5 := by ring
    _ ≤ (Apart i + 1) ^ 5 * (2 ^ 20 * 2 ^ sI i) * (4 * nI i + 6) ^ 5 := by
        gcongr
    _ = 2 ^ sI i * (2 ^ 20 * (Apart i + 1) ^ 5 * (4 * nI i + 6) ^ 5) := by ring

end NearCubicGates.Close.CounterMachine.TabCallProg
