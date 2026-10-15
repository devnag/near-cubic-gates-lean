import Proof.Supplier.EquationScalarWiden
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.Amplification.RecoveryListPredecessor

/-! Cold-workspace adapters for the already checked framed arithmetic
kernels. No magnitude is expanded into unary; the carry is the actual
low-bit carry of the physically supplied widened field. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar
open LocalBitMultitape SignedSortKey RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem widen_binary (w n : ℕ) (hn : n<2^w) :
    binary w n++[false]=binary (w+1) n := by
  have hv : value (binary w n++[false])=n := by
    simp [value_append,binary_value w n hn,value]
  have h := BoundedCounter.binary_of_value (binary w n++[false])
  rw [hv] at h
  simpa using h.symm

theorem increment_cold (w n : ℕ) (hn : n+1<2^w) :
    ∃ cost scratch,cost ≤ 4*w+2 ∧ scratch ≤ 2*w ∧
      ReadyRun FramedIncrement.machine cost ![frame (binary w n),[]]
        ![frame (binary w (n+1)),List.replicate scratch false] := by
  have hn' : n<2^w := by omega
  obtain ⟨count,tail,he⟩ : ∃ count tail,binary w n=List.replicate count true++false::tail := by
    rcases BoundedCounter.carry_split (binary w n) with h|h
    · exact h
    · have hv := congrArg value h
      rw [binary_value _ _ hn',binary_length] at hv
      have ht := BoundedCounter.true_value w
      omega
  have hlen : count+1+tail.length=w := by
    have h := congrArg List.length he
    simp only [binary_length,List.length_append,List.length_replicate,List.length_cons] at h
    omega
  have ho : List.replicate count false++true::tail=binary w (n+1) := by
    have hv : value (List.replicate count false++true::tail)=n+1 := by
      rw [BinaryIncrement.increment_value,←he,binary_value _ _ hn']
    have h := BoundedCounter.binary_of_value (List.replicate count false++true::tail)
    have hl : (List.replicate count false++true::tail).length=w := by simp; omega
    rw [hl,hv] at h
    exact h.symm
  obtain ⟨base,hb,hf,hs,_hp⟩ := FramedIncrement.carry_run count tail
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace FramedIncrement.raw
    (2*count+2) _ base hb 0
  have hi : (Fin.addCases (motive:=fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame (List.replicate count true++false::tail))
      (fun _ : Fin 1 => List.replicate 0 false))=![frame (binary w n),[]] := by
    rw [←he]
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  have hout : r.final.tapes=![frame (binary w (n+1)),List.replicate base.steps false] := by
    funext i; fin_cases i
    · change r.final.tapes 0=frame (binary w (n+1))
      have hz : (0 : Fin 1).castAdd 1=(0 : Fin 2) := by decide
      simpa only [hf,FramedIncrement.config,ho,hz] using ht (0 : Fin 1)
    · simpa using hc
  refine ⟨2*base.steps+2,base.steps,by omega,by omega,r,hr,hout,hh,hsteps⟩

theorem predecessor_binary (w n : ℕ) (hn : n<2^w) (hp : 0<n) :
    RecoveryListPredecessor.result (binary w n) true=binary w (n-1) := by
  have hv : value (RecoveryListPredecessor.result (binary w n) true)=n-1 := by
    rw [RecoveryListPredecessor.predecessor_value _ (by rw [binary_value w n hn]; omega),binary_value w n hn]
  have h := BoundedCounter.binary_of_value (RecoveryListPredecessor.result (binary w n) true)
  rw [hv,RecoveryListPredecessor.result_length,binary_length] at h
  exact h.symm

theorem predecessor_cold (w n : ℕ) (hn : n<2^w) (hp : 0<n) :
    ReadyRun RecoveryListPredecessor.machine (4*w+4)
      ![frame (binary w n),[false],[]]
      ![frame (binary w (n-1)),[true],List.replicate (2*w+1) false] := by
  have h := RecoveryListPredecessor.predecessor_ready (binary w n) false 0
  simpa only [binary_length,List.replicate_zero,predecessor_binary w n hn hp,
    binary_value w n hn,ne_eq,Nat.ne_of_gt hp,decide_not,decide_false,Bool.not_false,Nat.zero_max] using h

end NearCubicWires.RepairOrdinary.EquationScalar
