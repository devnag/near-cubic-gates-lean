import Proof.PCP.PCPPRequestNodeCodeBinary
import Proof.PCP.PCPPRequestNodeSchema

/-! One fixed node-code machine reads the physically prepared arity flag.
Its two branches return the literal canonical Boolean-node code. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeDispatch
open LocalBitMultitape RecoveryExecution RecoveryRootRound PCPPRequestNodeCode
open RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def select : Machine 234 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
private abbrev states {t s : ℕ} (_ : Machine t s) := s
def sizes : Fin 3 → ℕ := ![1,states unary,states binary]
def programs : (j : Fin 3) → Machine 234 (sizes j) :=
  Fin.cases select (Fin.cases unary (Fin.cases binary (fun j => nomatch j)))
def next (j : Fin 3) (_ : Fin (sizes j)) (bs : Fin 234 → Bool) : Option (Fin 3) :=
  if j=0 then some (if bs 5 then 2 else 1) else none
def machine := RecoveryCalls.machine sizes programs 0 next
def entry (j : Fin 3) (a : Fin 234 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) a)
def budget (a b c : ℕ) (flag : Bool) := (if flag then binaryBudget a b c else unaryBudget a b)+2

theorem enter (a b c pa pb pc : ℕ) (flag : Bool) :
    Timed machine 1 (initialConfiguration machine (input a b c flag pa pb pc))
      (entry (if flag then 2 else 1) (input a b c flag pa pb pc)) := by
  have hr : next 0 (0 : Fin 1) (initialConfiguration select (input a b c flag pa pb pc)).scanned=
      some (if flag then 2 else 1) := by
    cases flag <;> rfl
  exact Timed.single (by simp [machine,RecoveryCalls.machine,RecoveryCalls.code,initialConfiguration])
    (RecoveryCalls.return_step sizes programs 0 next 0 _
      (initialConfiguration select (input a b c flag pa pb pc)) (by rfl) hr)

theorem stop_body (j : Fin 3) (hj : j≠0) (fuel : ℕ) (a out : Fin 234 → List Bool)
    (h : ClockJoin.ReadyRun (programs j) fuel a out) :
    ∃ time,time≤fuel+1 ∧ Timed machine time (entry j a)
      (RecoveryCalls.stopped sizes (fun _ => 0) out) := by
  obtain ⟨r,hr,rt,rh,_⟩ := h
  obtain ⟨time,ht,hs⟩ := stop_receipt sizes programs 0 next j fuel
    (initialConfiguration (programs j) a) r hr (by simp [next,hj])
  have he : r.final.heads=(fun _ => 0) := funext rh
  rw [he,rt] at hs
  exact ⟨time,ht,hs⟩

theorem dispatch_run (a b c pa pb pc : ℕ) (flag : Bool) :
    ∃ out,ClockJoin.ReadyRun machine (budget a b c flag) (input a b c flag pa pb pc) out ∧
      (∃ padding,out 222=frame (result a b c flag).bits++List.replicate padding false) ∧
      out 232=(result a b c flag).bits := by
  have hb : ∃ out,ClockJoin.ReadyRun
      (programs (if flag then 2 else 1))
      (if flag then binaryBudget a b c else unaryBudget a b)
      (input a b c flag pa pb pc) out ∧
      (∃ padding,out 222=frame (result a b c flag).bits++List.replicate padding false) ∧
        out 232=(result a b c flag).bits := by
    cases flag
    · obtain ⟨out,h,hf,hr⟩ := unary_run a b c pa pb pc
      exact ⟨out,h,hf,hr⟩
    · obtain ⟨out,h,hf,hr⟩ := binary_run a b c pa pb pc
      exact ⟨out,h,hf,hr⟩
  obtain ⟨out,h,hf,hr⟩ := hb
  obtain ⟨time,ht,hstop⟩ := stop_body (if flag then 2 else 1)
    (by cases flag <;> decide) _ _ _ h
  obtain ⟨r,hrun,rf,rs⟩ := ((enter a b c pa pb pc flag).trans hstop).run
    (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have htime : 1+time≤budget a b c flag := by unfold budget; omega
  have hm := runFrom_moreFuel machine (1+time) (budget a b c flag-(1+time)) _ r hrun
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨out,⟨r,hm,?_,?_,?_⟩,hf,hr⟩
  · rw [rf]; rfl
  · intro i; rw [rf]; rfl
  · omega

theorem result_code {n : ℕ} (node : BooleanNode n) :
    result (CanonicalBinary.encodeNat (PCPPRequestNodeSchema.fields node 0))
      (CanonicalBinary.encodeNat (PCPPRequestNodeSchema.fields node 1))
      (CanonicalBinary.encodeNat (PCPPRequestNodeSchema.fields node 2))
      (PCPPRequestNodeSchema.binaryNode node)=encodeBooleanNode node := by
  cases node <;> rfl

end
end NearCubicWires.RepairOrdinary.PCPPRequestNodeDispatch
