import Proof.SourceAssembly.SourceParityGate
import Proof.CaseAnalysis.RowsEstimatorSubstitutionRepeat

/-! The original bitmap bit alone decides whether its identity gate is appended; the original coordinate always advances. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.SymmetricBody
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
open CloseoutRowsEstimator RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle:=SubstitutionRepeat.idle 7
noncomputable def writer:=TapeEmbedding.machine 1 Gate.machine
def test (bs : Fin 7→Bool):=bs 6
noncomputable def guarded:=CloseoutRowsGateColdPair.machine idle writer test
def counterSlot : Fin 1→Fin 7:=![1]
noncomputable def counter:=RecoveryFocus.machine counterSlot Counter.machine
def directions : Fin 7→HeadMove:=![.stay,.stay,.stay,.stay,.stay,.stay,.right]
noncomputable def move:=DecompositionCountPosition.move directions
noncomputable def machine:=Composition.machine (Composition.machine guarded counter) move

def H (pos : ℕ) (out : Fin 2→List Bool) : Fin 7→ℕ:=Fin.addCases (m:=6) (n:=1) (motive:=fun _=>ℕ) (Gate.H out) (fun _ : Fin 1=>pos)
def A (q j C : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool) : Fin 7→List Bool:=
  Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool) (Gate.A q j C cacheTail out) (fun _ : Fin 1=>bits)
def emitted (q j : ℕ) : Fin 2→List Bool:=![frame (bottomWord (Identity.onehot q j) 0),frame (Identity.onehot q j)]
def append (b : Bool) (q j : ℕ) (out : Fin 2→List Bool):=fun i=>out i++if b then emitted q j i else []
def cost (q : ℕ):=4*(natWord q).length+42*q+70

theorem writer_run (q j C pos : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool)
    (hj:j<q) (hC:2*(natWord q).length+1≤C) :
    Step writer (4*(natWord q).length+40*q+64) (H pos out) (A q j C cacheTail bits out)
      (H pos (append true q j out)) (A q j C cacheTail bits (append true q j out)) := by
  have actual:=(Gate.gate_run q C ⟨j,hj⟩ cacheTail out hC).embed (fun _ : Fin 1=>pos) (fun _ : Fin 1=>bits)
  have he : (![out 0++frame (CloseoutRowsCircuitBottom.nativeWord (inputBitSupportedGate ⟨j,hj⟩)),
      out 1++frame (CloseoutRowsGateSupport.gateMembers (inputBitSupportedGate ⟨j,hj⟩).support)])=append true q j out := by
    rw [identity_native,identity_support,Identity.identityMask_eq]
    funext i;fin_cases i <;>rfl
  rw [he] at actual
  exact actual

theorem guard_run (b : Bool) (q j C pos : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool)
    (hj:j<q) (hC:2*(natWord q).length+1≤C) (hb:readTapeBit bits pos=b) :
    Step guarded (4*(natWord q).length+40*q+66) (H pos out) (A q j C cacheTail bits out)
      (H pos (append b q j out)) (A q j C cacheTail bits (append b q j out)) := by
  let base : ExecutionReceipt 7 1:=⟨⟨0,H pos out,A q j C cacheTail bits out⟩,0,
    (⟨0,H pos out,A q j C cacheTail bits out⟩ : Configuration 7 1).tapeCells⟩
  have idleRun : runFrom idle 0 (RecoveryCalls.restarted idle (H pos out) (A q j C cacheTail bits out))=some base := by rfl
  cases b with
  | false=>
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.rejected idle writer test 0 _ _ base idleRun hb
    have actual:Step guarded 1 (H pos out) (A q j C cacheTail bits out) (H pos out) (A q j C cacheTail bits out):=
      ⟨r,hr,rh,rt,rs⟩
    have he:append false q j out=out:=by funext i;simp [append]
    rw [he]
    exact actual.enlarge (by omega)
  | true=>
    obtain ⟨last,hl,lh,lt,ls⟩:=writer_run q j C pos cacheTail bits out hj hC
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted idle writer test 0 _ _ _ base last idleRun hl hb
    have hcost : 0+1+(4*(natWord q).length+40*q+64)+1=4*(natWord q).length+40*q+66:=by omega
    rw [hcost] at hr rs
    exact ⟨r,hr,rh.trans lh,rt.trans lt,rs⟩

theorem counter_run (q j C pos : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool) :
    Step counter (2*j+2) (H pos out) (A q j C cacheTail bits out)
      (H pos out) (A q (j+1) C cacheTail bits out) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (Counter.increment_run j)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl))

theorem move_run (q j C pos : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool) :
    Step move 1 (H pos out) (A q j C cacheTail bits out)
      (H (pos+1) out) (A q j C cacheTail bits out) := by
  obtain ⟨r,hr,rf,_⟩:=DecompositionCountPosition.move_run directions (H pos out) (A q j C cacheTail bits out)
  refine Step.of_run hr ?_ (by rw [rf])
  rw [rf]
  funext i;fin_cases i <;>rfl

theorem body_run (b : Bool) (q j C pos : ℕ) (cacheTail bits : List Bool) (out : Fin 2→List Bool)
    (hj:j<q) (hC:2*(natWord q).length+1≤C) (hb:readTapeBit bits pos=b) :
    Step machine (cost q) (H pos out) (A q j C cacheTail bits out)
      (H (pos+1) (append b q j out)) (A q (j+1) C cacheTail bits (append b q j out)) := by
  have actual:=((guard_run b q j C pos cacheTail bits out hj hC hb).seq
    (counter_run q j C pos cacheTail bits (append b q j out))).seq
    (move_run q (j+1) C pos cacheTail bits (append b q j out))
  exact actual.enlarge (by unfold cost;omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.SymmetricBody
