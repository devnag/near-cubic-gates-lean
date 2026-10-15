import Proof.Gates.CounterMachine.CellTablesPack5

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

theorem setup_cost_le (V M : ℕ) (z : Sz) (cT n0 L : ℕ) :
    setupKCost V M z cT n0 L ≤ (costA (zK z cT n0 L) L + 1 + (costB V M (z.W L) (z.Lk L) ((zK z cT n0 L).Bk L) + 1 +
      costC L (z.W L) (z.Lk L) ((zK z cT n0 L).Bk L))) + bkCost z cT n0 L := by
  have hBk := zK_Bk z cT n0 L
  have ha3 : z.a3 ≤ (zK z cT n0 L).a3 := by
    show z.a3 ≤ 2 ^ (n0 - kLow cT L) * z.a3; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hBB : z.Bk L ≤ (zK z cT n0 L).Bk L := by rw [hBk]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hS : Nat.size (L - 2) ≤ L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hm : n0 - kLow cT L ≤ n0 := Nat.sub_le _ _
  have hD : (n0 - kLow cT L) * (60 * (2 ^ (n0 - kLow cT L) * z.Bk L) + 19) + 10 * (n0 - kLow cT L) + 5 + 1 ≤
      (n0 + 1) * (60 * (zK z cT n0 L).Bk L + 100) := by
    rw [hBk]
    generalize 2 ^ (n0 - kLow cT L) * z.Bk L = X
    have h1 := Nat.mul_le_mul_right (60 * X + 19) hm
    have e : (n0 + 1) * (60 * X + 100) = n0 * (60 * X + 19) + 81 * n0 + 60 * X + 100 := by ring
    omega
  have hf : bkCCost L (2 + cT + 3 * Nat.size (L - 2)) ≤ 23 * L * (2 + cT + 3 * L) + 25 * L + 3 * (2 + cT + 3 * L) + 20 :=
    by unfold bkCCost; gcongr
  have hBC : bkBCost L cT + 23 * L * (2 + cT + 3 * L) + 25 * L + 3 * (2 + cT + 3 * L) + 20 + 4 ≤
      1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) := by
    unfold bkBCost
    have h2 : 1 ≤ 2 ^ L + 2 := Nat.le_add_left 1 _ |>.trans (Nat.add_le_add_left (by norm_num) _)
    have : 1000 * (L + cT + 10) * (L + 2) ≤ 1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) := Nat.le_mul_of_pos_right _ h2
    nlinarith
  have hW : (zK z cT n0 L).W L = z.W L := rfl
  have hLk : (zK z cT n0 L).Lk L = z.Lk L := rfl
  have hc1 : (zK z cT n0 L).c1 = z.c1 := rfl
  have hc2 : (zK z cT n0 L).c2 = z.c2 := rfl
  have hc3 : (zK z cT n0 L).c3 = z.c3 := rfl
  have ha1 : (zK z cT n0 L).a1 = z.a1 := rfl
  have ha2 : (zK z cT n0 L).a2 = z.a2 := rfl
  have hLB : L * (60 * z.Bk L + 11 * z.c3 + 8) ≤ L * (60 * (zK z cT n0 L).Bk L + 11 * z.c3 + 8) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold setupKCost costA1 costA3 costA bkBlkCost bkCost
  rw [hW, hLk, hc1, hc2, hc3, ha1, ha2]
  omega

/-- **CellTables-SPLIT3** (with the register premise `5 ≤ M`). -/
noncomputable def packWF {V M : ℕ} (hM : 5 ≤ M) {Req : Type} (input output : Req → List Bool) (K : Callee) (z : Sz)
    (cT : ℕ) (n0 : Req → ℕ) (main : St V M) (N : Req → ℕ)
    (hin : ∀ r, ∃ rest, input r = natWord (n0 r) ++ rest)
    (hrun : ∀ r, ∃ b n, Ex (ctxOf K (zK z cT (n0 r) (leadOnes (input r))) (input r)) main a0 b n ∧ b.out = output r ∧
      n ≤ N r)
    (hW : ∀ r, 1 ≤ z.W (leadOnes (input r))) (hW2 : ∀ r, 2 ^ (leadOnes (input r) + 2) ≤ z.W (leadOnes (input r))) :
    WordFunction Req input output (fun r =>
      langBudget K (zK z cT (n0 r) (leadOnes (input r))) V M (input r) (N r) +
        bkCost z cT (n0 r) (leadOnes (input r))) :=
  Interfaces.wordFunction_of_wmx (progK K hM z cT main) sOUT (by simp)
    (fun r => langCap (zK z cT (n0 r) (leadOnes (input r))) M (input r) (N r) +
      ((leadOnes (input r) + 1) * (2 + cT + 3 * leadOnes (input r)) + cT + 2 * n0 r + 100)) (by
    intro r
    obtain ⟨rest, hrest⟩ := hin r
    obtain ⟨b, n, hex, hout, hn⟩ := hrun r
    set zr := zK z cT (n0 r) (leadOnes (input r)) with hzr
    set C := ctxOf K zr (input r) with hC
    set cap := langCap zr M (input r) (N r) +
      ((leadOnes (input r) + 1) * (2 + cT + 3 * leadOnes (input r)) + cT + 2 * n0 r + 100) with hcap
    have hcapv : cap = 2 * (input r).length + 8 * (zr.W (leadOnes (input r)) + zr.Lk (leadOnes (input r)) +
        zr.Bk (leadOnes (input r))) + 4 * (zr.a1 + zr.a2 + zr.a3) + 40 +
        (2 * zr.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) + N r +
        ((leadOnes (input r) + 1) * (2 + cT + 3 * leadOnes (input r)) + cT + 2 * n0 r + 100) := rfl
    have hLi : leadOnes (input r) ≤ (input r).length := leadOnes_le _
    have hzW : zr.W (leadOnes (input r)) = z.W (leadOnes (input r)) := rfl
    have hzLk : zr.Lk (leadOnes (input r)) = z.Lk (leadOnes (input r)) := rfl
    have hza1 : zr.a1 = z.a1 := rfl
    have hza2 : zr.a2 = z.a2 := rfl
    have hza3 : z.a3 ≤ zr.a3 := by
      show z.a3 ≤ 2 ^ (n0 r - kLow cT (leadOnes (input r))) * z.a3; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have hc1 : C.inp.length = (input r).length := rfl
    have hc2 : C.Lk = zr.Lk (leadOnes (input r)) := rfl
    have hc3 : C.Bk = zr.Bk (leadOnes (input r)) := rfl
    have hc4 : C.Wd = zr.W (leadOnes (input r)) := rfl
    have hWN : 2 * zr.W (leadOnes (input r)) + 1 ≤ (2 * zr.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    have hW2r := hW2 r
    have hLn : leadOnes (input r) = natBitLength (n0 r) := by rw [hrest]; exact leadOnes_natWord (n0 r) rest
    have hn0 : n0 r < 2 ^ leadOnes (input r) := by
      rw [hLn]; unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hL4 : 4 * leadOnes (input r) + 4 ≤ 2 ^ (leadOnes (input r) + 2) := by
      have := Nat.lt_two_pow_self (n := leadOnes (input r)); rw [pow_add]; omega
    have hn04 : 2 * n0 r ≤ 2 ^ (leadOnes (input r) + 2) := by rw [pow_add]; omega
    have s1 := setupK_spec (V := V) K hM z cT (n0 r) rest (input r) hrest cap
      (by rw [← hzr, hcapv, hzW, hzLk, hza1, hza2] at *; omega)
      (by rw [hcapv]; omega) (by rw [hcapv]; omega)
    have henc : Enc C (a0 : DS V M) (initSt (t := TS C) C.Wd C.Lk C.Bk C.inp) := initSt_enc C
    have hcapok : CapOK C cap (a0 : DS V M) n := by
      refine ⟨hW r, ?_, ?_, ?_, fun m => ?_, ?_⟩
      · show 2 * zr.W (leadOnes (input r)) + 2 ≤ cap
        rw [hcapv]; omega
      · show 2 * (input r).length + 2 ≤ cap
        rw [hcapv]; omega
      · show ([] : List Bool).length + n ≤ cap
        rw [hcapv]; simp only [List.length_nil]; omega
      · show (2 * zr.W (leadOnes (input r)) + 1) * (([] : List ℕ).length + n + 1) + 1 ≤ cap
        rw [hcapv]; simp only [List.length_nil, zero_add]
        have : (2 * zr.W (leadOnes (input r)) + 1) * (n + 1) ≤
            (2 * zr.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
          calc (2 * zr.W (leadOnes (input r)) + 1) * (n + 1) ≤ (2 * zr.W (leadOnes (input r)) + 1) * (N r + 1) :=
                Nat.mul_le_mul_left _ (by omega)
            _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
        omega
      · show 2 * zr.Lk (leadOnes (input r)) + zr.Bk (leadOnes (input r)) + 3 + 2 ≤ cap
        rw [hcapv]; omega
    obtain ⟨⟨τ, e1, r2⟩, _⟩ := comp_ok C cap (callee_hB C) hex (a0_valid C) _ henc hcapok
    have hval := hex.valid (hW r) (callee_hB C) (a0_valid C)
    have hol := hex.out_len
    have hrl := hex.ram_len
    have hrc : ∀ m, b.rc m ≤ n := fun m => by
      have := hval.rc_le m; have := hrl m; simp [a0] at this; omega
    obtain ⟨ρ, r3, hρo, hρs, hρv⟩ := tear_spec C b τ e1 cap (by
      have h1 := hval.ip_le
      have h2 := hval.kin_le
      have h3 := hval.kc_le
      have h4 := hval.kout_le
      have h5 := sum_rc_le n hrc
      have h6 : (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ (2 * zr.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
        calc (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ (2 * zr.W (leadOnes (input r)) + 1) * (M * n) :=
              Nat.mul_le_mul_left _ h5
          _ ≤ (2 * zr.W (leadOnes (input r)) + 1) * ((N r + 1) * (M + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = _ := by ring
      simp only [a0, List.length_nil, zero_add] at hol
      rw [hcapv]
      show 2 * b.ip + b.out.length + 2 * b.kin.length + b.kc + (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ _
      omega)
    have hst : initSt (V := V) (M := M) (t := TSK K) (z.W (leadOnes (input r))) (z.Lk (leadOnes (input r)))
        ((zK z cT (n0 r) (leadOnes (input r))).Bk (leadOnes (input r))) (input r) =
        initSt (V := V) (M := M) (t := TS C) C.Wd C.Lk C.Bk C.inp := rfl
    rw [hst] at s1
    refine ⟨ρ, WXExec.seq s1 (WXExec.seq r2 r3) |>.mono ?_, hρo.trans hout, hρs, hρv⟩
    -- the budget
    have h1 := hval.ip_le
    have h2 := hval.kin_le
    have h3 := hval.kc_le
    have h4 := hval.kout_le
    simp only [a0, List.length_nil, zero_add] at hol
    have htear : tearCost C b ≤ 10 * (input r).length + 5 * N r + 10 * zr.Lk (leadOnes (input r)) +
        5 * (zr.Bk (leadOnes (input r)) + 3) + M * (5 * ((2 * zr.W (leadOnes (input r)) + 1) * N r) + 2) + 10 := by
      unfold tearCost
      have hs : ((List.finRange M).map fun m => 5 * ((2 * C.Wd + 1) * b.rc m) + 2).sum ≤
          M * (5 * ((2 * zr.W (leadOnes (input r)) + 1) * N r) + 2) := by
        have := List.sum_le_card_nsmul ((List.finRange M).map fun m => 5 * ((2 * C.Wd + 1) * b.rc m) + 2)
          (5 * ((2 * zr.W (leadOnes (input r)) + 1) * N r) + 2) (fun x hx => by
            obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
            have := Nat.mul_le_mul_left (2 * zr.W (leadOnes (input r)) + 1) ((hrc m).trans hn)
            show 5 * ((2 * zr.W (leadOnes (input r)) + 1) * b.rc m) + 2 ≤ _
            omega)
        simpa using this
      omega
    have hKC : n * KC C ≤ N r * (500 * (zr.W (leadOnes (input r)) + 1) ^ 2 + 100 * (TSK K + 3)) :=
      Nat.mul_le_mul_right _ hn
    have hset := setup_cost_le V M z cT (n0 r) (leadOnes (input r))
    rw [← hzr] at hset
    simp only [langBudget]
    rw [hzW, hzLk] at *
    omega)

theorem packK_of {V M : ℕ} (hM : 5 ≤ M) {Req : Type} (input output : Req → List Bool) (K : Callee) (z : Sz)
    (cT : ℕ) (n0 : Req → ℕ) (main : St V M) (N : Req → ℕ)
    (hin : ∀ r, ∃ rest, input r = natWord (n0 r) ++ rest)
    (hrun : ∀ r, ∃ b n, Ex (ctxOf K (zK z cT (n0 r) (leadOnes (input r))) (input r)) main a0 b n ∧ b.out = output r ∧
      n ≤ N r)
    (hW : ∀ r, 1 ≤ z.W (leadOnes (input r))) (hW2 : ∀ r, 2 ^ (leadOnes (input r) + 2) ≤ z.W (leadOnes (input r))) :
    Nonempty (WordFunction Req input output (fun r =>
      langBudget K (zK z cT (n0 r) (leadOnes (input r))) V M (input r) (N r) +
        bkCost z cT (n0 r) (leadOnes (input r)))) :=
  ⟨packWF hM input output K z cT n0 main N hin hrun hW hW2⟩

end NearCubicGates.Close.CounterMachine.CellTablesProg

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (WordFunction)

def PackK5 : Prop :=
  ∀ {V M : ℕ} {Req : Type} (input output : Req → List Bool) (K : Callee) (z : Sz) (cT : ℕ) (n0 : Req → ℕ)
    (main : St V M) (N : Req → ℕ), 5 ≤ M →
    (∀ r, ∃ rest, input r = natWord (n0 r) ++ rest) →
    (∀ r, ∃ b n, Ex (ctxOf K (zK z cT (n0 r) (leadOnes (input r))) (input r)) main a0 b n ∧ b.out = output r ∧
      n ≤ N r) →
    (∀ r, 1 ≤ z.W (leadOnes (input r))) → (∀ r, 2 ^ (leadOnes (input r) + 2) ≤ z.W (leadOnes (input r))) →
    Nonempty (WordFunction Req input output (fun r =>
      langBudget K (zK z cT (n0 r) (leadOnes (input r))) V M (input r) (N r) +
        bkCost z cT (n0 r) (leadOnes (input r))))

/-- **CellTables-SPLIT3 (packaging).** -/
theorem packK5 : PackK5 := fun input output K z cT n0 main N hM hin hrun hW hW2 =>
  packK_of hM input output K z cT n0 main N hin hrun hW hW2

end NearCubicGates.Close.CounterMachine.CellTablesProg
