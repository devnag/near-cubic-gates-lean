import Proof.PCP.PCPPRequestNodeCodeReady

/-! Reuse the checked two-element tagged-list encoder. Its two fixed false
input fields are physically written in one transition; only the two actual
canonical operands are present initially. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitTag
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (a b pa pb : ℕ) (i : Fin 234) : List Bool :=
  if i=0 then frame a.bits++List.replicate pa false
  else if i=1 then frame b.bits++List.replicate pb false else []
def mark : Machine 234 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=2 ∨ i=5 then some false else none,fun _ => .stay⟩ else none
noncomputable def machine := Composition.machine mark PCPPRequestNodeCode.unary
def budget (a b : ℕ) := 2+PCPPRequestNodeCode.unaryBudget a b

theorem mark_ready (a b pa pb : ℕ) : ReadyRun mark 1 (input a b pa pb)
    (PCPPRequestNodeCode.input a b 0 false pa pb 0) := by
  let c : Configuration 234 2 := ⟨1,fun _ => 0,PCPPRequestNodeCode.input a b 0 false pa pb 0⟩
  have hs : step mark (initialConfiguration mark (input a b pa pb))=some c := by
    simp [step,mark,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases h0 : i=0
      · subst i; rfl
      by_cases h1 : i=1
      · subst i; rfl
      by_cases h2 : i=2
      · subst i; rfl
      by_cases h5 : i=5
      · subst i; rfl
      simp only [applyAction,input,PCPPRequestNodeCode.input,h0,h1,h2,h5,
        false_or,ite_false,c]
  obtain ⟨r,hr,rf,rs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i; rw [rf],rs⟩

theorem tag_run (a b pa pb : ℕ) :
    ∃ out,ClockJoin.ReadyRun machine (budget a b) (input a b pa pb) out ∧
      (∃ padding,out 222=frame (CanonicalBinary.encodeTaggedList [a,b]).bits++List.replicate padding false) ∧
      out 232=(CanonicalBinary.encodeTaggedList [a,b]).bits := by
  obtain ⟨out,ho,hf,hr⟩ := PCPPRequestNodeCode.unary_run a b 0 pa pb 0
  obtain ⟨r,rr,rt,rh,rs⟩ := mark_ready a b pa pb
  exact ⟨out,ClockJoin.join _ _ _ _ _ _ _ ⟨r,rr,rt,rh,rs.le⟩ ho,hf,hr⟩

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitTag
