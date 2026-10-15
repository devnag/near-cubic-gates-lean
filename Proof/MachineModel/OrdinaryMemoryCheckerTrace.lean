import Proof.MachineModel.OrdinaryMemoryCheckerList

/-! The existing memory checker consumes the same verifier's initialized
claimed trace. An accepted arbitrary bit prefix yields an actual run;
an actual run supplies a prefix whose chronological request checks true. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog ClaimedTrace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initialized_sound (v : Verifier) (input witness : List Bool)
    (claims : List (Fin v.tapeCount → Bool)) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event) {I W : ℕ}
    (hready : ListReady I W (MemoryInitialization.events input witness ++ trace))
    (hcheck : ClaimedTrace.check v.machine
      (view (initialConfiguration v.machine (v.inputTapes input witness))) claims =
        some (finalView,trace))
    (hresult : (listRequest hready).result = true)
    (hhalt : v.machine.halted finalView.control = true)
    (haccept : v.accepting finalView.control = true) :
    v.acceptsAt claims.length input witness := by
  rw [list_result] at hresult
  exact InitializedTrace.sound v input witness claims finalView trace hcheck hresult hhalt haccept

theorem evaluation_sound (v : Verifier) (input witness : List Bool)
    (n : ℕ) (bits : List Bool) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event) {I W : ℕ}
    (hready : ListReady I W (MemoryInitialization.events input witness ++ trace))
    (heval : TransitionWalk.evaluate v
      (view (initialConfiguration v.machine (v.inputTapes input witness))) n bits =
        some (finalView,trace))
    (hresult : (listRequest hready).result = true)
    (hhalt : v.machine.halted finalView.control = true)
    (haccept : v.accepting finalView.control = true) :
    v.acceptsAt n input witness := by
  obtain ⟨claims,_,hlen,_,hcheck⟩ := TransitionWalk.evaluate_implies_trace v n _ bits finalView trace heval
  have hs := initialized_sound v input witness claims finalView trace hready hcheck hresult hhalt haccept
  rw [hlen] at hs
  exact hs

theorem checked_evaluation_sound (v : Verifier) (input witness : List Bool)
    (n : ℕ) (bits : List Bool) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event) {I W : ℕ}
    (hready : ListReady I W (MemoryInitialization.events input witness ++ trace))
    (heval : TransitionWalk.evaluate v
      (view (initialConfiguration v.machine (v.inputTapes input witness))) n bits =
        some (finalView,trace))
    (hresult : (listRequest hready).result = true)
    (hdecision : TransitionWalk.accepted v
      (view (initialConfiguration v.machine (v.inputTapes input witness))) n bits = true) :
    v.acceptsAt n input witness := by
  have hflags : v.machine.halted finalView.control = true ∧ v.accepting finalView.control = true := by
    simpa only [TransitionWalk.accepted, heval, Bool.and_eq_true] using hdecision
  exact evaluation_sound v input witness n bits finalView trace hready heval hresult hflags.1 hflags.2

theorem evaluation_complete (v : Verifier) (input witness : List Bool) (fuel : ℕ)
    (r : ExecutionReceipt v.tapeCount v.stateCount)
    (hrun : LocalBitMultitape.run v.machine fuel (v.inputTapes input witness) = some r)
    (haccept : v.accepting r.final.control = true) :
    ∃ claims trace,
      claims.length = r.steps ∧ trace.length = v.tapeCount*r.steps ∧
      (MemoryInitialization.events input witness ++ trace).length =
        2*input.length+2*witness.length+2+v.tapeCount*r.steps ∧
      ClaimedTrace.check v.machine
        (view (initialConfiguration v.machine (v.inputTapes input witness))) claims =
          some (view r.final,trace) ∧
      (∀ padding,
        TransitionWalk.evaluate v
          (view (initialConfiguration v.machine (v.inputTapes input witness))) r.steps
          (TransitionWalk.traceBits claims ++ padding) = some (view r.final,trace) ∧
        TransitionWalk.accepted v
          (view (initialConfiguration v.machine (v.inputTapes input witness))) r.steps
          (TransitionWalk.traceBits claims ++ padding) = true) ∧
      (∀ (I W : ℕ) (hready : ListReady I W (MemoryInitialization.events input witness ++ trace)),
        (listRequest hready).result = true) := by
  obtain ⟨claims,trace,hlen,htlen,hcheck,hmemory,hhalt,helen⟩ :=
    InitializedTrace.complete v input witness fuel r hrun
  refine ⟨claims,trace,hlen,htlen,helen,hcheck,?_,?_⟩
  · intro padding
    have heval : TransitionWalk.evaluate v
        (view (initialConfiguration v.machine (v.inputTapes input witness))) r.steps
        (TransitionWalk.traceBits claims ++ padding) = some (view r.final,trace) := by
      rw [← hlen, TransitionWalk.evaluate_trace]
      exact hcheck
    refine ⟨heval,?_⟩
    apply (TransitionWalk.accepted_iff v _ _ _).mpr
    exact ⟨view r.final,trace,heval,hhalt,haccept⟩
  · intro I W hready
    rw [list_result, hmemory]
    rfl

end NearCubicWires.RepairOrdinary.MemoryChecker
