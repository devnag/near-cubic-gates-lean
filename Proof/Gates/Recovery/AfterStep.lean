import Proof.Gates.Recovery.AfterState

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

/-- **One step**: piece `k` runs, then the controller enters piece `l`. -/
theorem step_call {k l : Fin 31} {n : ℕ} {A A' : Fin (T K) → List Bool}
    (h : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c k)) n A A')
    (hn : ∀ q, next K c k q (fun i => readTapeBit (A' i) 0) = some l) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (n + 1) (start K c k A) (start K c l A') :=
  h.call (ports K) (pieces K c) 0 (next K c) k l hn

/-- **The last step**: piece `k` runs, then the controller stops. -/
theorem step_stop {k : Fin 31} {n : ℕ} {A A' : Fin (T K) → List Bool}
    (h : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c k)) n A A')
    (hn : ∀ q, next K c k q (fun i => readTapeBit (A' i) 0) = none) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (n + 1) (start K c k A) (stopAt K c A') :=
  h.stop (ports K) (pieces K c) 0 (next K c) k hn

/-- A fall-through piece. -/
theorem next_plain (k : ℕ) (hk : k + 1 < 31) (h16 : k ≠ 16) (h22 : k ≠ 22) (h27 : k ≠ 27) (h17 : k ≠ 17)
    (h23 : k ≠ 23) (h28 : k ≠ 28) (q : Fin (pieces K c ⟨k, by omega⟩).states) (read : Fin (T K) → Bool) :
    next K c ⟨k, by omega⟩ q read = some ⟨k + 1, hk⟩ := by
  unfold next
  simp only [h16, h22, h27, h17, h23, h28, false_or, if_false, dif_pos hk]
  rw [if_neg (by omega)]

theorem next_16 (q : Fin (pieces K c 16).states) (read : Fin (T K) → Bool) :
    next K c 16 q read = some (if read (sh K 19) then 18 else 17) := by
  unfold next; rfl

/-- Stage 2's branch (its flag tape `flag2`). -/
theorem next_22 (q : Fin (pieces K c 22).states) (read : Fin (T K) → Bool) :
    next K c 22 q read = some (if read (flag2 K) then 24 else 23) := by
  unfold next; rfl

theorem next_27 (q : Fin (pieces K c 27).states) (read : Fin (T K) → Bool) :
    next K c 27 q read = some (if read (sh K 31) then 29 else 28) := by
  unfold next; rfl

/-- The terminal pieces stop. -/
theorem next_17 (q : Fin (pieces K c 17).states) (read : Fin (T K) → Bool) : next K c 17 q read = none := by
  unfold next; rfl

theorem next_23 (q : Fin (pieces K c 23).states) (read : Fin (T K) → Bool) : next K c 23 q read = none := by
  unfold next; rfl

theorem next_28 (q : Fin (pieces K c 28).states) (read : Fin (T K) → Bool) : next K c 28 q read = none := by
  unfold next; rfl

theorem next_30 (q : Fin (pieces K c 30).states) (read : Fin (T K) → Bool) : next K c 30 q read = none := by
  unfold next; rfl

end

end NearCubicGates.Close.Recovery.After
