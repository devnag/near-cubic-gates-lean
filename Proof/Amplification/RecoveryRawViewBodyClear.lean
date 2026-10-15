import Proof.Amplification.RecoveryRawViewBodyCount

/-! The actual reset supplies the blank padded literal counter needed by
the count reader, retaining the witness cursor and extracted clause field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clear_trace (x : State) (word : List Bool) (k : Nat) (bits : List Bool)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word)
    (hp : x.inner.stream.pos=2*k) (hw : bits.length=x.width)
    (hf : x.outer.fields 0=frame bits) (hfalse : x.inner.stream.data.present=false) :
    ∃ n e,n ≤ clearBudget x ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 2) (x.cfg RecoveryRawView.clearMachine.start))
        (RecoveryCalls.stopped sizes e.heads e.tapes) ∧
      Result (countAnswer (cleared x) word k bits) (countOutput (cleared x) word k bits) e := by
  obtain ⟨first,hr,he,_⟩ := RecoveryRawView.clear_run x hx
  have htrace := call_receipt sizes programs 0 next 2 3 (clearCost x) _ first hr (by rfl)
  obtain ⟨n0,hn0,h0⟩ := htrace
  have htail := count_trace (cleared x) word k bits (cleared_valid x hx) rfl hs hp hw hf hfalse
  obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
  rw [he] at h0
  have h := h0.trans h1
  refine ⟨n0+n1,e,?_,h,hresult⟩
  change n1 ≤ countBudget x.width x.limit at hn1
  unfold clearBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
