import Proof.Supplier.EquationNaturalHeaderPositive
import Proof.Hierarchy.HierarchyFixedWord

/-! The whole canonical natural header producer, including the actual zero
branch. The only varying input is one raw unary value; all scratch is blank. -/
namespace NearCubicWires.RepairOrdinary.EquationNaturalHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def select : Machine 16 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
def zeroSlots : Fin 2 → Fin 16 := ![14,15]
def zero := RecoveryFocus.machine zeroSlots (HierarchyFixedWord.machine [true,false,false])
def sizes : Fin 3 → ℕ := ![1,45,6]
def programs : (i : Fin 3) → Machine 16 (sizes i) :=
  Fin.cases select (Fin.cases positive (Fin.cases zero (fun i => nomatch i)))
def next (j : Fin 3) (_ : Fin (sizes j)) (bs : Fin 16 → Bool) : Option (Fin 3) :=
  if j=0 then some (if bs 0 then 1 else 2) else none
def machine := RecoveryCalls.machine sizes programs 0 next
def entry (j : Fin 3) (a : Fin 16 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) a)

theorem enter (n : ℕ) :
    Timed machine 1 (initialConfiguration machine (input n))
      (entry (if n=0 then 2 else 1) (input n)) := by
  have hr : next 0 (0 : Fin 1) (initialConfiguration select (input n)).scanned=
      some (if n=0 then 2 else 1) := by
    cases n with
    | zero => rfl
    | succ n => simp [next,Configuration.scanned,initialConfiguration,input,readTapeBit]
  exact Timed.single (by simp [machine,RecoveryCalls.machine,RecoveryCalls.code,initialConfiguration])
    (RecoveryCalls.return_step sizes programs 0 next 0 _
      (initialConfiguration select (input n)) (by rfl) hr)

theorem stop_body (j : Fin 3) (hj : j≠0) (fuel : ℕ) (a out : Fin 16 → List Bool)
    (h : ClockJoin.ReadyRun (programs j) fuel a out) :
    ∃ time, time ≤ fuel+1 ∧ Timed machine time (entry j a)
      (RecoveryCalls.stopped sizes (fun _ => 0) out) := by
  obtain ⟨r,hr,rt,rh,_⟩ := h
  obtain ⟨time,ht,hs⟩ := stop_receipt sizes programs 0 next j fuel
    (initialConfiguration (programs j) a) r hr (by simp [next,hj])
  have he : r.final.heads=(fun _ => 0) := funext rh
  rw [he,rt] at hs
  exact ⟨time,ht,hs⟩

theorem zero_ready :
    ∃ out,ClockJoin.ReadyRun zero 8 (input 0) out ∧ out 1=[] ∧ out 14=natWord 0 := by
  have h := (HierarchyFixedWord.word_ready [true,false,false]).focus zeroSlots (by decide) (input 0)
    (by intro i; fin_cases i <;> rfl)
  let out := install zeroSlots (input 0) (![([true,false,false] : List Bool),List.replicate 3 false])
  obtain ⟨r,hr,rt,rh,rs⟩ := h
  refine ⟨out,⟨r,hr,rt,rh,rs.le⟩,?_,?_⟩
  · exact install_other zeroSlots _ _ 1 (by decide)
  · exact install_slot zeroSlots (by decide) _ _ 0

theorem header_ready (n : ℕ) :
    ∃ out,ClockJoin.ReadyRun machine (budget n+2) (input n) out ∧
      out 1=List.replicate n true ∧ out 14=natWord n := by
  have hbody : ∃ out time, time ≤ budget n+1 ∧
      Timed machine time (entry (if n=0 then 2 else 1) (input n))
        (RecoveryCalls.stopped sizes (fun _ => 0) out) ∧
      out 1=List.replicate n true ∧ out 14=natWord n := by
    by_cases hn : n=0
    · subst n
      obtain ⟨out,h,h1,h14⟩ := zero_ready
      obtain ⟨time,ht,hs⟩ := stop_body 2 (by decide) 8 (input 0) out h
      exact ⟨out,time,by unfold budget; omega,by simpa only [ite_true] using hs,h1,h14⟩
    · obtain ⟨out,h,h1,h14⟩ := positive_ready n (by omega)
      obtain ⟨time,ht,hs⟩ := stop_body 1 (by decide) (budget n) (input n) out h
      exact ⟨out,time,ht,by simpa only [hn,ite_false] using hs,h1,h14⟩
  obtain ⟨out,time,ht,h,h1,h14⟩ := hbody
  obtain ⟨r,hr,rf,rs⟩ := ((enter n).trans h).run (by
    simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have htime : 1+time ≤ budget n+2 := by omega
  have hm := runFrom_moreFuel machine (1+time) (budget n+2-(1+time)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨out,⟨r,hm,?_,?_,?_⟩,h1,h14⟩
  · rw [rf]; rfl
  · intro i; rw [rf]; rfl
  · omega

end
end NearCubicWires.RepairOrdinary.EquationNaturalHeader
