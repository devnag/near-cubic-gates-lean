import Proof.Gates.Recovery.AfterStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

/-- Stage 2's table tape is shared `3`, shared `18`, or in stage 2's block. -/
theorem tbl_cases : (tbl K).val = 3 ∨ (tbl K).val = 18 ∨ (off K 22 ≤ (tbl K).val ∧ (tbl K).val < off K 23) := by
  unfold tbl
  cases hp : portL (tBank K).l (cslot _ K.ts.tablePort) with
  | none =>
    right; right
    have hv : ((tBank K).slot (cslot _ K.ts.tablePort)).val = (tBank K).off + (cslot _ K.ts.tablePort).val :=
      bslot_priv hp
    have hoff : (tBank K).off = off K 22 := rfl
    have hlt := (cslot _ K.ts.tablePort).isLt
    have hsz : sz K 22 = (clocked K.ts.program).base.tapeCount := rfl
    have hfit : off K 23 = off K 22 + sz K 22 := rfl
    rw [hv, hoff]
    omega
  | some y =>
    have hy : (tBank K).slot (cslot _ K.ts.tablePort) = y := bslot_port hp
    have hm := portL_some hp
    simp only [tBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    rw [hy]
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · left; rfl
    · right; left; rfl

theorem tbl_lt : (tbl K).val < off K 23 := by
  have h22 := off_ge K 22
  have hm : off K 22 ≤ off K 23 := off_mono K (by omega)
  rcases tbl_cases K with h | h | h <;> omega

theorem tbl_ne (i : Fin 32) (h3 : i.val ≠ 3) (h18 : i.val ≠ 18) : tbl K ≠ sh K i := by
  intro he
  have hv := congrArg Fin.val he
  simp only [sh_val] at hv
  have := i.isLt
  have := off_ge K 22
  rcases tbl_cases K with h | h | h <;> omega

theorem blk_val (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) : (blk K k hk hs).val = off K k := rfl

theorem off_lt_succ (k : ℕ) (hs : 1 ≤ sz K k) : off K k < off K (k + 1) := by
  show off K k < off K k + sz K k; omega

theorem tslot_inj (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) (a b : Fin (T K)) (hab : a ≠ b)
    (ha : a.val < off K k) (hb : b.val < off K k) : Function.Injective (tslot K k hk hs a b) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;>
    simp [tslot, blk_val, Fin.ext_iff] at hv ⊢ <;> first | omega | exact hab (Fin.ext hv) | exact hab (Fin.ext hv.symm)

/-- **Piece 24**: `frame O*` from stage 2's table tape to shared `21`. -/
theorem ready24 (A : Fin (T K) → List Bool) (bits : List Bool) (hT : A (tbl K) = RepairOrdinary.frame bits)
    (h21 : A (sh K 21) = []) (hB : A (blk K 24 (by decide) le_rfl) = []) :
    Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 24)) (4 * bits.length + 4) A
      (Function.update (Function.update A (sh K 21) (RepairOrdinary.frame bits)) (blk K 24 (by decide) le_rfl)
        (List.replicate (2 * bits.length + 1) false)) := by
  have hT23 := tbl_lt K
  have h2324 : off K 23 ≤ off K 24 := off_mono K (by omega)
  have h32 := off_ge K 24
  have hi := tslot_inj K 24 (by decide) le_rfl (tbl K) (sh K 21) (tbl_ne K 21 (by decide) (by decide))
    (by omega) (by simp; omega)
  have h := copy_ready (tslot K 24 (by decide) le_rfl (tbl K) (sh K 21)) hi A bits []
    (by simpa [tslot] using hT) (by simpa [tslot] using h21) (by simpa [tslot] using hB)
  exact Ready.ordinary (ports K) h

/-- **Piece 25**: `frame O*` from stage 2's table tape to shared `22`. -/
theorem ready25 (A : Fin (T K) → List Bool) (bits : List Bool) (hT : A (tbl K) = RepairOrdinary.frame bits)
    (h22 : A (sh K 22) = []) (hB : A (blk K 25 (by decide) le_rfl) = []) :
    Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 25)) (4 * bits.length + 4) A
      (Function.update (Function.update A (sh K 22) (RepairOrdinary.frame bits)) (blk K 25 (by decide) le_rfl)
        (List.replicate (2 * bits.length + 1) false)) := by
  have hT23 := tbl_lt K
  have h2325 : off K 23 ≤ off K 25 := off_mono K (by omega)
  have h32 := off_ge K 25
  have hi := tslot_inj K 25 (by decide) le_rfl (tbl K) (sh K 22) (tbl_ne K 22 (by decide) (by decide))
    (by omega) (by simp; omega)
  have h := copy_ready (tslot K 25 (by decide) le_rfl (tbl K) (sh K 22)) hi A bits []
    (by simpa [tslot] using hT) (by simpa [tslot] using h22) (by simpa [tslot] using hB)
  exact Ready.ordinary (ports K) h

/-- **Piece 26**: the shared query tape erased with the driver `1^N` on shared `15`. -/
theorem ready26 (A : Fin (T K) → List Bool) (N : ℕ) (hQ : (A (sh K 3)).length ≤ N)
    (hD : A (sh K 15) = List.replicate N true) (hB : A (blk K 26 (by decide) le_rfl) = []) :
    Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 26)) (2 * N + 4) A
      (Function.update (Function.update A (sh K 3) (List.replicate N false)) (blk K 26 (by decide) le_rfl)
        (List.replicate (N + 1) false)) := by
  have h32 := off_ge K 26
  have hi := tslot_inj K 26 (by decide) le_rfl (sh K 3) (sh K 15) (by simp) (by simp; omega) (by simp; omega)
  have h := clear_ready (tslot K 26 (by decide) le_rfl (sh K 3) (sh K 15)) hi A N
    (by simpa [tslot] using hQ) (by simpa [tslot] using hD) (by simpa [tslot] using hB)
  exact Ready.ordinary (ports K) h

end

end NearCubicGates.Close.Recovery.After
