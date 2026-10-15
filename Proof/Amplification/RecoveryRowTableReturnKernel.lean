import Proof.Amplification.RecoveryRowTableLoop

/-! A small physical Boolean-return graph proved over an abstract source
state count, avoiding expansion of the enclosing table's finite controls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowTableReturn
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def writeResult (bit : Bool) : Machine 69 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun i=>if i=50 then some bit else none,fun _=>.stay⟩ else none

theorem write_result_run (heads : Fin 69→Nat) (tapes : Fin 69→List Bool) (old bit : Bool)
    (hh : heads 50=0) (ht : tapes 50=[old]) :
    ∃ r,runFrom (writeResult bit) 1 (⟨0,heads,tapes⟩ : Configuration 69 2)=some r ∧
      r.final=⟨1,heads,Function.update tapes 50 [bit]⟩ ∧ r.steps=1 := by
  have h : step (writeResult bit) (⟨0,heads,tapes⟩ : Configuration 69 2)=
      some (⟨1,heads,Function.update tapes 50 [bit]⟩ : Configuration 69 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=50
      · subst i; simp [applyAction,hh,ht,writeTapeBit]
      · simp [applyAction,hi]
  exact (Timed.single (by rfl) h).run (by rfl)

def sizes (s : Nat) : Fin 3→Nat := ![s,2,2]
def programs {s : Nat} (p : Machine 69 s) : (j : Fin 3)→Machine 69 (sizes s j)
  | ⟨0,_⟩=>p
  | ⟨1,_⟩=>writeResult false
  | ⟨2,_⟩=>writeResult true
  | ⟨n+3,h⟩=>False.elim (by omega)
def next {s : Nat} (result : Fin s→Bool) : (j : Fin 3)→Fin (sizes s j)→(Fin 69→Bool)→Option (Fin 3)
  | ⟨0,_⟩,q,_=>if result q then some 2 else some 1
  | ⟨1,_⟩,_,_=>none
  | ⟨2,_⟩,_,_=>none
  | ⟨n+3,h⟩,_,_=>False.elim (by omega)
noncomputable def machine {s : Nat} (p : Machine 69 s) (result : Fin s→Bool) :=
  RecoveryCalls.machine (sizes s) (programs p) 0 (next result)

theorem return_trace {s : Nat} (p : Machine 69 s) (result : Fin s→Bool) (fuel : Nat)
    (source : Configuration 69 s) (first : ExecutionReceipt 69 s)
    (hr : runFrom p fuel source=some first) (old : Bool)
    (hh : first.final.heads 50=0) (ht : first.final.tapes 50=[old]) :
    ∃ n,n ≤ fuel+3 ∧ Timed (machine p result) n
      (controlConfig (RecoveryCalls.code (sizes s) 0) source)
      (RecoveryCalls.stopped (sizes s) first.final.heads (Function.update first.final.tapes 50 [result first.final.control])) := by
  cases ha : result first.final.control
  · have hn : next result 0 first.final.control first.final.scanned=some 1 := by
      change (if result first.final.control then some (2 : Fin 3) else some 1)=some 1
      rw [ha]; rfl
    obtain ⟨n0,hn0,h0⟩ := call_receipt (sizes s) (programs p) 0 (next result) 0 1 fuel source first hr hn
    obtain ⟨last,hr1,hf1,_⟩ := write_result_run first.final.heads first.final.tapes old false hh ht
    obtain ⟨n1,hn1,h1⟩ := stop_receipt (sizes s) (programs p) 0 (next result) 1 1 _ last hr1 (by rfl)
    have h := h0.trans h1
    rw [hf1] at h
    exact ⟨n0+n1,by omega,h⟩
  · have hn : next result 0 first.final.control first.final.scanned=some 2 := by
      change (if result first.final.control then some (2 : Fin 3) else some 1)=some 2
      rw [ha]; rfl
    obtain ⟨n0,hn0,h0⟩ := call_receipt (sizes s) (programs p) 0 (next result) 0 2 fuel source first hr hn
    obtain ⟨last,hr1,hf1,_⟩ := write_result_run first.final.heads first.final.tapes old true hh ht
    obtain ⟨n1,hn1,h1⟩ := stop_receipt (sizes s) (programs p) 0 (next result) 2 1 _ last hr1 (by rfl)
    have h := h0.trans h1
    rw [hf1] at h
    exact ⟨n0+n1,by omega,h⟩

theorem return_run {s : Nat} (p : Machine 69 s) (result : Fin s→Bool) (fuel : Nat)
    (source : Configuration 69 s) (first : ExecutionReceipt 69 s)
    (hr : runFrom p fuel source=some first) (old : Bool)
    (hh : first.final.heads 50=0) (ht : first.final.tapes 50=[old]) :
    ∃ r,runFrom (machine p result) (fuel+3) (controlConfig (RecoveryCalls.code (sizes s) 0) source)=some r ∧
      r.steps ≤ fuel+3 ∧
      r.final=RecoveryCalls.stopped (sizes s) first.final.heads (Function.update first.final.tapes 50 [result first.final.control]) := by
  obtain ⟨n,hn,h⟩ := return_trace p result fuel source first hr old hh ht
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel (machine p result) n (fuel+3-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hs.le.trans hn,hf⟩

end NearCubicWires.RepairOrdinary.RecoveryRowTableReturn
