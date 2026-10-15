import Proof.CaseAnalysis.RecoveryAddressReverse

/-! One fixed machine executes the original address expression: the actual
address children, false seed, and reverse OR fold on their saved references. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def forwardBudget (count W : ℕ):=count*(stepBudget W+2)+count+3
def reverseBudget (count W : ℕ):=count*(24*RecoveryBoundedSelectorLoop.capacity W+66)+count+3
def budget (count W : ℕ):=forwardBudget count W+1+RecoveryBoundedSelectorFinish.falseBits.length+1+reverseBudget count W
noncomputable def machine:=Composition.machine (Composition.machine forwardMachine seed) reverseMachine
def initial (base : ℕ) (out skipped pre : List Bool) : State:=⟨base,0,out,skipped,pre⟩
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1)) (start limit W D base count : ℕ)
    (out skipped source pre : List Bool):=
  restart (configuration (n:=n) 0 row start limit W D (initial base out skipped pre) source count 1) machine.start

theorem join_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (bits out skipped tail pre : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hf : b.nodes.length+prefixSize (items row start limit hblock 0 bits)+bits.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (RecoveryBoundedSelectorLoop.capacity W) ≤ D) :
    let source:=skipped++bits++tail
    let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock bits
    let refs:=references b.nodes.length (items row start limit hblock 0 bits)
    ∃ r,runFrom machine (budget bits.length W)
      (entry (n:=n) row start limit W D b.nodes.length bits.length out skipped source pre)=some r ∧
      r.steps ≤ budget bits.length W ∧
      r.final.heads=(reverseOutput (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (RecoveryBoundedSelectorLoop.capacity W) D bits.length limit bits.length a.skipped.length
        (a.out++RecoveryBoundedSelectorFinish.falseBits) source pre refs).heads ∧
      r.final.tapes=(reverseOutput (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (RecoveryBoundedSelectorLoop.capacity W) D bits.length limit bits.length a.skipped.length
        (a.out++RecoveryBoundedSelectorFinish.falseBits) source pre refs).tapes := by
  let source:=skipped++bits++tail
  let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock bits
  let refs:=references b.nodes.length (items row start limit hblock 0 bits)
  have hs:=iterate_schedule row start limit hblock bits (initial b.nodes.length out skipped pre)
  dsimp only [initial] at hs
  have haPos : a.position=b.nodes.length+prefixSize (items row start limit hblock 0 bits):=hs.1
  have haValue : a.value=bits.length := by simpa only [a,initial,Nat.zero_add] using hs.2.1
  have haStack : a.stack=pre++RecoveryBoundedNativeUnaryLoop.stackWords refs:=hs.2.2.2.2
  have hrlen : refs.length=bits.length := by simp only [refs,RecoveryBoundedAddress.references_length,items_length]
  have hf' : a.position+bits.length ≤ W := by rw [haPos];exact hf
  obtain ⟨r0,hr0,rf0,rs0⟩:=forward_run W D bits.length row start limit hblock b
    (initial b.nodes.length out skipped pre) bits tail rfl (by simp [initial]) hi hp hc hD
  obtain ⟨r1,hr1,rs1,rh1,rt1⟩:=seed_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position (RecoveryBoundedSelectorLoop.capacity W) D a.value limit bits.length a.skipped.length a.out source a.stack
  have hr1' : runFrom seed RecoveryBoundedSelectorFinish.falseBits.length (restart r0.final seed.start)=some r1 := by
    rw [rf0]
    exact hr1
  have firstJoin:=Composition.run_join forwardMachine seed _ _ _ r0 r1 hr0 hr1'
  have href : ∀ ref∈refs,ref ≤ W := by
    intro ref hr
    have h:=saved_bound b.nodes.length (items row start limit hblock 0 bits) ref hr
    rw [←haPos] at h
    omega
  obtain ⟨r2,hr2,rs2,rf2⟩:=reverse_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position W D bits.length limit bits.length a.skipped.length (a.out++RecoveryBoundedSelectorFinish.falseBits) source pre refs
    hrlen href (by rw [hrlen];exact hf')
  rw [hrlen] at hr2 rs2
  have hr2' : runFrom reverseMachine (reverseBudget bits.length W)
      (restart (joinedReceipt r0 r1).final reverseMachine.start)=some r2 := by
    change runFrom reverseMachine _ ⟨reverseMachine.start,r1.final.heads,r1.final.tapes⟩=some r2
    rw [rh1,rt1,haStack,haValue]
    exact hr2
  have full:=Composition.run_join (Composition.machine forwardMachine seed) reverseMachine _ _ _
    (joinedReceipt r0 r1) r2 firstJoin hr2'
  refine ⟨joinedReceipt (joinedReceipt r0 r1) r2,full,?_,?_,?_⟩
  · change r0.steps+1+r1.steps+1+r2.steps ≤ budget bits.length W
    unfold budget forwardBudget reverseBudget
    omega
  · change r2.final.heads=_
    rw [rf2]
  · change r2.final.tapes=_
    rw [rf2]

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
