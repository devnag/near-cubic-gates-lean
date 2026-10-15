import Proof.CaseAnalysis.RowsGateCalls

/-! The two-node cold guard is defined and proved at symbolic state counts.
Its concrete use specializes this ONE machine-and-execution constructor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateColdPair
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {t a b : ℕ} (p : Machine t a) (q : Machine t b)
noncomputable def sizes : Fin 2 → ℕ := ![a,b]
noncomputable def programs : (j : Fin 2) → Machine t (sizes (a := a) (b := b) j)
  | ⟨0,_⟩ => p
  | ⟨1,_⟩ => q
  | ⟨j+2,hj⟩ => False.elim (by omega)
def next (test : (Fin t → Bool) → Bool) (j : Fin 2)
    (_ : Fin (sizes (a := a) (b := b) j)) (bits : Fin t → Bool) : Option (Fin 2) :=
  if j.val=0 && test bits then some 1 else none
noncomputable def machine (test : (Fin t → Bool) → Bool) :=
  RecoveryCalls.machine (sizes (a := a) (b := b)) (programs p q) 0 (next test)

theorem joined (test : (Fin t → Bool) → Bool) (fp fq : ℕ) (input middle output : Fin t → List Bool)
    (hp : ClockJoin.ReadyRun p fp input middle) (hq : ClockJoin.ReadyRun q fq middle output)
    (hn : test (fun i => readTapeBit (middle i) 0)=true) :
    ClockJoin.ReadyRun (machine p q test) (fp+1+fq+1) input output := by
  obtain ⟨u,hu,first⟩ := CloseoutRowsGateColdCalls.call (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 0 1 fp input middle hp (by
      intro state
      change (if test (fun i => readTapeBit (middle i) 0) then some (1 : Fin 2) else none)=some 1
      rw [hn];rfl)
  obtain ⟨v,hv,last⟩ := CloseoutRowsGateColdCalls.stop (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 1 fq middle output hq (by intro state;rfl)
  exact CloseoutRowsGateColdCalls.finish (sizes (a := a) (b := b)) (programs p q) 0 (next test)
    (fp+1+fq+1) (u+v) input output (first.trans last) (by omega)

theorem rejected (test : (Fin t → Bool) → Bool) (fp : ℕ) (input output : Fin t → List Bool)
    (hp : ClockJoin.ReadyRun p fp input output) (hn : test (fun i => readTapeBit (output i) 0)=false) :
    ClockJoin.ReadyRun (machine p q test) (fp+1) input output := by
  obtain ⟨u,hu,trace⟩ := CloseoutRowsGateColdCalls.stop (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 0 fp input output hp (by
      intro state
      change (if test (fun i => readTapeBit (output i) 0) then some (1 : Fin 2) else none)=none
      rw [hn];rfl)
  exact CloseoutRowsGateColdCalls.finish (sizes (a := a) (b := b)) (programs p q) 0 (next test)
    (fp+1) u input output trace hu

end NearCubicWires.RepairOrdinary.CloseoutRowsGateColdPair
