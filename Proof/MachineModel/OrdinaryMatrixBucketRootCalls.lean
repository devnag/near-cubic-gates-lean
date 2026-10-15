import Proof.MachineModel.OrdinaryMatrixBucketRootTest
import Proof.Circuits.MatrixBucketDimensionsIncrement

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootCalls
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBucketRootClear (tapes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def incrementSlots : Fin 1 → Fin 27 := fun _ => 0
noncomputable def increment := RecoveryFocus.machine incrementSlots MatrixBucketDimensions.Increment.machine
abbrev testStates := (4+(2+Fintype.card (RecoveryCalls.Control (WilliamsPower.sizes 10))))+(3+2)
def sizes : Fin 2 → ℕ := ![testStates,5]
noncomputable def programs : (j : Fin 2) → Machine 27 (sizes j)
  | ⟨0,_⟩ => MatrixBucketRootTest.machine
  | ⟨1,_⟩ => increment
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 27 → Bool) : Option (Fin 2) :=
  if j=0 then if bits 23 then none else some 1 else some 0
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (j : Fin 2) (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j)
    (RecoveryCalls.restarted (programs j) (fun _ => 0) (tapes r c cap work))
noncomputable def result (r : Request) (cap : ℕ) (work : Fin 23 → List Bool) :=
  RecoveryCalls.stopped sizes (fun _ => 0) (tapes r (MatrixBucketDimensions.capacity r.U) cap work)

theorem increment_run (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :
    ∃ actual,runFrom increment (2*c+5)
      (RecoveryCalls.restarted increment (fun _ => 0) (tapes r c cap work))=some actual ∧
      actual.final.heads=(fun _ => 0) ∧ actual.final.tapes=tapes r (c+1) cap work ∧ actual.steps=2*c+5 := by
  have inj : Function.Injective incrementSlots := by intro i j _; exact Subsingleton.elim _ _
  obtain ⟨actual,ha,ah,atapes,as⟩ := HierarchyBinary.focused_run incrementSlots inj MatrixBucketDimensions.Increment.machine
    _ _ (MatrixBucketDimensions.Increment.increment_run c) (fun _ => 0) (tapes r c cap work)
    (by intro i; rfl) (by intro i; rfl)
  refine ⟨actual,ha,ah,?_,as⟩
  rw [atapes]
  funext i
  by_cases hi : i=0
  · subst i
    exact install_slot incrementSlots inj _ _ 0
  · have hn : RecoveryFocus.pick incrementSlots i=none := by
      simp [RecoveryFocus.pick,incrementSlots]
      exact Ne.symm hi
    simp only [install,hn]
    fin_cases i <;> first | contradiction | rfl

theorem increment_call (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :
    ∃ time≤2*c+6,Timed machine time (boundary 1 r c cap work) (boundary 0 r (c+1) cap work) := by
  obtain ⟨actual,ha,ah,atapes,_⟩ := increment_run r c cap work
  obtain ⟨time,ht,hprefix⟩ := call_receipt sizes programs 0 next 1 0 (2*c+5)
    (RecoveryCalls.restarted (programs 1) (fun _ => 0) (tapes r c cap work)) actual ha (by rfl)
  refine ⟨time,ht,?_⟩
  simpa only [ah,atapes,machine,boundary] using hprefix

theorem stop_bit (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool)
    (hflag : work 21=ZeroPadding.pad (D r) [decide (r.U≤c^10)]) :
    readTapeBit (tapes r c cap work 23) 0=decide (r.U≤c^10) := by
  change readTapeBit (work 21) 0=_
  rw [hflag,ZeroPadding.read_pad]
  rfl

theorem test_continue (r : Request) (c cap : ℕ) (backing : Fin 23 → List Bool)
    (hb : ∀ i,(backing i).length≤D r) (hc : 1≤c) (hlt : c<MatrixBucketDimensions.capacity r.U) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      ∃ time≤MatrixBucketRootTest.budget r+1,Timed machine time
        (boundary 0 r c cap backing) (boundary 1 r c (max cap (D r+1)) work) := by
  obtain ⟨work,hw,hflag,actual,ha,ah,atapes,_⟩ := MatrixBucketRootTest.test_run r c cap backing hb hc hlt.le
  have hfalse : decide (r.U≤c^10)=false := by
    have hp := MatrixBucketDimensions.before_root r.U c hlt
    simp [show ¬r.U≤c^10 by omega]
  have hscan : actual.final.scanned 23=false := by
    simp only [Configuration.scanned,ah,atapes]
    rw [stop_bit r c _ work hflag,hfalse]
  obtain ⟨time,ht,hprefix⟩ := call_receipt sizes programs 0 next 0 1 (MatrixBucketRootTest.budget r)
    (RecoveryCalls.restarted (programs 0) (fun _ => 0) (tapes r c cap backing)) actual ha
    (by simp [next]; exact hscan)
  refine ⟨work,hw,time,ht,?_⟩
  simpa only [ah,atapes,machine,boundary] using hprefix

theorem test_finish (r : Request) (cap : ℕ) (backing : Fin 23 → List Bool)
    (hb : ∀ i,(backing i).length≤D r) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      ∃ time≤MatrixBucketRootTest.budget r+1,Timed machine time
        (boundary 0 r (MatrixBucketDimensions.capacity r.U) cap backing) (result r (max cap (D r+1)) work) := by
  obtain ⟨work,hw,hflag,actual,ha,ah,atapes,_⟩ := MatrixBucketRootTest.test_run r (MatrixBucketDimensions.capacity r.U)
    cap backing hb (MatrixBucketDimensions.capacity_positive r.U Nat.one_le_two_pow) (Nat.le_refl _)
  have htrue : decide (r.U≤(MatrixBucketDimensions.capacity r.U)^10)=true := by
    exact decide_eq_true ((MatrixBucketDimensions.root_stop _ _).2 (Nat.le_refl _))
  have hscan : actual.final.scanned 23=true := by
    simp only [Configuration.scanned,ah,atapes]
    rw [stop_bit r _ _ work hflag,htrue]
  obtain ⟨time,ht,hprefix⟩ := stop_receipt sizes programs 0 next 0 (MatrixBucketRootTest.budget r)
    (RecoveryCalls.restarted (programs 0) (fun _ => 0) (tapes r (MatrixBucketDimensions.capacity r.U) cap backing)) actual ha
    (by simp [next]; exact hscan)
  refine ⟨work,hw,time,ht,?_⟩
  simpa only [ah,atapes,machine,boundary,result] using hprefix

end NearCubicWires.RepairOrdinary.MatrixBucketRootCalls
