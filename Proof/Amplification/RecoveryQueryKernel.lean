import Proof.Amplification.RecoveryQueryPrepare
import Proof.Amplification.RecoveryQueryCore

/-! Whole reused compact-prefix query producer. The caller supplies three
actual framed canonical fields and its physically produced capacity driver;
all subsequent scratch preparation, field copies and encoding are executed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def kernel (flat : Bool) := Composition.machine (Prepare.machine flat) machine
def querySlot : Fin 357 := bank 8 26

theorem query_run (cap log : Nat) (flat : Bool) (payload committed count : Nat)
    (ambient : Fin 357→List Bool) (paddedPayload paddedCommitted paddedCount : List Bool)
    (hcap : capacity payload committed count ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1)
    (hp : ambient 0=frame payload.bits++paddedPayload)
    (ha : ambient 1=frame committed.bits++paddedCommitted)
    (hn : ambient 2=frame count.bits++paddedCount) :
    ∃ out : Fin 357→List Bool,
      ClockJoin.ReadyRun (kernel flat) (16*cap) ambient out ∧
      out querySlot=ZeroPadding.pad cap (frame (code flat payload committed count).bits) ∧
      (∀ i : Fin 357,i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧ Bounded cap out := by
  have hprepare := Prepare.prepare_run cap log flat payload committed count ambient
    paddedPayload paddedCommitted paddedCount hcap hb hd hl hz hp ha hn
  obtain ⟨out,hcore,hquery,hlow,hbound⟩ := core_run cap flat payload committed count
    (Prepare.cleared cap ambient) hcap
  have whole := ClockJoin.join _ _ _ _ _ _ _ hprepare hcore
  have hbase : bytes payload committed count+1 ≤ (bytes payload committed count+1)^2 := by nlinarith
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have htime : (2*cap+4*bytes payload committed count+40)+1+9*cap ≤ 16*cap := by
    unfold capacity at hcap
    omega
  refine ⟨out,ClockJoin.enlarge _ _ _ _ _ whole htime,hquery,?_,?_,?_,hbound⟩
  · intro i hi
    rw [hlow i (by omega)]
    simp [Prepare.cleared,hi]
  · exact hlow 3 (by decide)
  · exact hlow 4 (by decide)

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
