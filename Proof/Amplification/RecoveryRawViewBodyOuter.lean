import Proof.Amplification.RecoveryRawViewBodyClear

/-! The outer raw-list extraction gates all clause work using its actual
presence bit. Missing cells halt with the result cell already false. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerAnswer (x : State) (word : List Bool) (k : Nat) :=
  if RadixSemantics.value x.outer.bits=0 then false else
    countAnswer (cleared (outerStep x)) word k (headWord x)
def outerOutput (x : State) (word : List Bool) (k : Nat) :=
  countOutput (cleared (outerStep x)) word k (headWord x)

theorem outer_scan {s : Nat} (x : State) (q : Fin s) :
    ((outerStep x).cfg q).scanned 59=decide (RadixSemantics.value x.outer.bits≠0) := by
  change (x.outer.after 0).flag=_
  exact RecoveryThreeCellReader.after_flag x.outer 0

theorem outer_trace (x : State) (word : List Bool) (k : Nat)
    (hx : x.Valid) (hs : x.inner.stream.source=frame word)
    (hp : x.inner.stream.pos=2*k) (hfalse : x.inner.stream.data.present=false) :
    ∃ n e,n ≤ outerBudget x ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (x.cfg outerMachine.start))
        (RecoveryCalls.stopped sizes e.heads e.tapes) ∧
      Result (outerAnswer x word k) (outerOutput x word k) e := by
  obtain ⟨first,hr,he,_⟩ := RecoveryRawView.outer_run x hx.2.1
  have hbit : first.final.scanned 59=decide (RadixSemantics.value x.outer.bits≠0) := by
    rw [he]
    exact outer_scan x _
  by_cases hz : RadixSemantics.value x.outer.bits=0
  · have hn : next 1 first.final.control first.final.scanned=none := by
      change (if first.final.scanned 59 then some (2 : Fin 6) else none)=none
      rw [hbit]
      simp [hz]
    have htrace := stop_receipt sizes programs 0 next 1 (RecoveryStoredListCell.time x.outer.bits) _ first hr hn
    obtain ⟨n,hn,h⟩ := htrace
    refine ⟨n,⟨0,first.final.heads,first.final.tapes⟩,?_,h,?_,?_,?_⟩
    · unfold outerBudget
      omega
    · change first.final.heads 28=0
      rw [he]
      rfl
    · change first.final.tapes 28=_
      rw [he]
      change [x.inner.stream.data.present]=[outerAnswer x word k]
      rw [hfalse]
      simp only [outerAnswer,hz,ite_true]
    · simp only [outerAnswer,hz,ite_true,Bool.false_eq_true,IsEmpty.forall_iff]
  · have hn : next 1 first.final.control first.final.scanned=some 2 := by
      change (if first.final.scanned 59 then some (2 : Fin 6) else none)=some 2
      rw [hbit]
      simp [hz]
    have htrace := call_receipt sizes programs 0 next 1 2 (RecoveryStoredListCell.time x.outer.bits) _ first hr hn
    obtain ⟨n0,hn0,h0⟩ := htrace
    have hfield : (outerStep x).outer.fields 0=frame (headWord x) := by
      change (x.outer.after 0).fields 0=_
      simp only [RecoveryClauseState.State.after,hz,ite_false,Function.update_self]
      rfl
    have htail := clear_trace (outerStep x) word k (headWord x) (outer_step_valid x hx)
      hs hp (head_width x hx) hfield hfalse
    obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
    rw [he] at h0
    have h := h0.trans h1
    refine ⟨n0+n1,e,?_,h,?_⟩
    · change n1 ≤ clearBudget x at hn1
      unfold outerBudget
      omega
    · simpa only [outerAnswer,outerOutput,if_neg hz] using hresult

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
