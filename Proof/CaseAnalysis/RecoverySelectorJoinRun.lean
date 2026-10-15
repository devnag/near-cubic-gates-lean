import Proof.CaseAnalysis.RecoverySelectorReverse
import Proof.CaseAnalysis.RecoverySelectorConsumerSchedule

/-! One fixed machine executes the whole original unary field selector:
forward guarded heads, the false seed, then the original reverse OR fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def endBank (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ) :=
  RecoveryFocus.config foldSlots (heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos)
    (data index base C D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    (foldOutput base C total out pre refs)

theorem reverse_full_run (index base W D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ)
    (htotal : refs.length=total) (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W) :
    ∃ r,runFrom reverseMachine (refs.length*(24*capacity W+66)+total+3)
      ⟨reverseMachine.start,heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos,
        data index base (capacity W) D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r ∧
      r.steps ≤ refs.length*(24*capacity W+66)+total+3 ∧
      r.final=endBank index base (capacity W) D value limit total pos out source pre refs := by
  have hc : 1 ≤ capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨p,hp,pf,ps⟩:=padded_reverse_run base W total out pre refs htotal href ha
  have he:=WilliamsSourceCrop.focus_same foldSlots
    (⟨reverseMachine.start,heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos,
      data index base (capacity W) D value limit total out source
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩ : Configuration 43 _)
    (foldInput base (capacity W) total out pre refs)
    (fold_input_heads base (capacity W) total pos out pre refs)
    (fold_input_tapes index base (capacity W) D value limit total out source pre refs hc)
  obtain ⟨r,hr,rf,rs⟩:=RecoveryFocus.run_config foldSlots fold_injective (RecoveryBoundedNativeFoldLoop.machine false)
    (heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos)
    (data index base (capacity W) D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    _ (foldInput base (capacity W) total out pre refs) p hp
  rw [he] at hr
  refine ⟨r,hr,rs.le.trans ps,?_⟩
  rw [rf,pf]
  rfl

def forwardBudget (count W : ℕ):=count*(stepBudget W+2)+count+3
def reverseBudget (count W : ℕ):=count*(24*capacity W+66)+count+3
def budget (count W : ℕ):=forwardBudget count W+1+falseBits.length+1+reverseBudget count W
noncomputable def machine:=Composition.machine (Composition.machine forwardMachine seed) reverseMachine
def initial (base : ℕ) (out skipped pre : List Bool) : RecoveryBoundedSelectorLoop.State:=⟨base,0,out,skipped,pre⟩
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1)) (start limit W D base count : ℕ)
    (out skipped source pre : List Bool) :=
  restart (configuration (n:=n) 0 row start limit W D (initial base out skipped pre) source count 1) machine.start

theorem join_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out skipped tail pre : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hf : b.nodes.length+RecoveryBoundedUniversal.prefixSize
      (fieldItems row start limit hblock 0 (wires.map (fun w=>w.output.val)))+wires.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) :
    let raw:=wires.map (fun w=>w.output.val)
    let source:=skipped++sourceWord raw++tail
    let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock raw
    let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
    ∃ r,runFrom machine (budget wires.length W)
      (entry (n:=n) row start limit W D b.nodes.length wires.length out skipped source pre)=some r ∧
      r.steps ≤ budget wires.length W ∧
      r.final.heads=(endBank (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (capacity W) D wires.length limit wires.length a.skipped.length (a.out++falseBits) source pre refs).heads ∧
      r.final.tapes=(endBank (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (capacity W) D wires.length limit wires.length a.skipped.length (a.out++falseBits) source pre refs).tapes := by
  let raw:=wires.map (fun w=>w.output.val)
  let source:=skipped++sourceWord raw++tail
  let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock raw
  let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
  have hs:=iterate_schedule row start limit hblock raw (initial b.nodes.length out skipped pre)
  dsimp only [initial] at hs
  have haPos : a.position=b.nodes.length+RecoveryBoundedUniversal.prefixSize (fieldItems row start limit hblock 0 raw) := hs.1
  have haValue : a.value=wires.length := by simpa only [a,initial,raw,List.length_map,Nat.zero_add] using hs.2.1
  have haStack : a.stack=pre++RecoveryBoundedNativeUnaryLoop.stackWords refs := hs.2.2.2.2
  have hrlen : refs.length=wires.length := by
    simp only [refs,RecoveryBoundedUniversal.references_length,fieldItems_length,raw,List.length_map]
  have hf' : a.position+wires.length ≤ W := by rw [haPos]; exact hf
  obtain ⟨r0,hr0,rf0,rs0⟩:=forward_run wires.length W D wires.length row start limit hblock b
    (initial b.nodes.length out skipped pre) wires tail rfl rfl (by simp [initial]) hi hp hc hD
  obtain ⟨r1,hr1,rs1,rh1,rt1⟩:=seed_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position (capacity W) D a.value limit wires.length a.skipped.length a.out source a.stack
  have hr1' : runFrom seed falseBits.length (restart r0.final seed.start)=some r1 := by
    rw [rf0]
    change runFrom seed _ ⟨seed.start,
      (configuration (n:=n) 3 row start limit W D a source wires.length 1).heads,
      (configuration (n:=n) 3 row start limit W D a source wires.length 1).tapes⟩=some r1
    rw [forward_heads,forward_tapes]
    exact hr1
  have firstJoin:=Composition.run_join forwardMachine seed _ _ _ r0 r1 hr0 hr1'
  have href : ∀ ref∈refs,ref ≤ W := by
    intro ref hr
    have h:=saved_bound b.nodes.length (fieldItems row start limit hblock 0 raw) ref hr
    rw [←haPos] at h
    omega
  obtain ⟨r2,hr2,rs2,rf2⟩:=reverse_full_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position W D wires.length limit wires.length a.skipped.length (a.out++falseBits) source pre refs
    hrlen href (by rw [haPos,hrlen]; exact hf)
  rw [hrlen] at hr2 rs2
  have hr2' : runFrom reverseMachine (reverseBudget wires.length W)
      (restart (joinedReceipt r0 r1).final reverseMachine.start)=some r2 := by
    change runFrom reverseMachine _ ⟨reverseMachine.start,r1.final.heads,r1.final.tapes⟩=some r2
    rw [rh1,rt1,haStack,haValue]
    exact hr2
  have full:=Composition.run_join (Composition.machine forwardMachine seed) reverseMachine _ _ _
    (joinedReceipt r0 r1) r2 firstJoin hr2'
  refine ⟨joinedReceipt (joinedReceipt r0 r1) r2,full,?_,?_,?_⟩
  · change r0.steps+1+r1.steps+1+r2.steps ≤ budget wires.length W
    unfold budget forwardBudget reverseBudget
    omega
  · change r2.final.heads=_
    rw [rf2]
  · change r2.final.tapes=_
    rw [rf2]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
