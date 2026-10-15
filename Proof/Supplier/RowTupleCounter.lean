import Proof.Supplier.RowCommonBounds
import Proof.MachineModel.OrdinaryWitnessCounterAdvance

/-! The tuple enumerator advances a bounded binary cursor on four retained
tapes. A real transition clears the previous continuation flag before the
checked increment/comparison call. The enumeration count is never unary. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCounter
open LocalBitMultitape RecoveryExecution SignedSortKey
open WitnessCounterCheck (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clear : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,![none,none,some false,none],fun _=>.stay⟩ else none
def machine := Composition.machine clear WitnessCounterAdvance.machine

theorem clear_run (w counter limit cap : ℕ) (flag : Bool) :
    ∃ r,runFrom clear 1 (config clear.start w counter limit cap flag)=some r ∧
      r.final=config 1 w counter limit cap false ∧ r.steps=1 := by
  have hs : step clear (config clear.start w counter limit cap flag)=
      some (config 1 w counter limit cap false) := by
    simp [step,clear,config]
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem next_run (w counter limit cap : ℕ) (flag : Bool)
    (hn : counter+1<2^w) (hb : limit<2^w) (hc : 2*w+1 ≤ cap) :
    ∃ r,runFrom machine (8*w+9) (config machine.start w counter limit cap flag)=some r ∧
      r.final=config 13 w (counter+1) limit cap (decide (counter+1 ≤ limit)) := by
  obtain ⟨a,ha,af,_⟩ := clear_run w counter limit cap flag
  obtain ⟨b,hb,bf⟩ := WitnessCounterAdvance.check_run w counter limit cap hn hb hc
  have hi : config WitnessCounterAdvance.machine.start w counter limit cap false=
      Composition.restart a.final WitnessCounterAdvance.machine.start := by rw [af]; rfl
  rw [hi] at hb
  have h := Composition.run_join clear WitnessCounterAdvance.machine _ _ _ a b ha hb
  have ht : 1+1+(8*w+7)=8*w+9 := by omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_⟩
  change Composition.rightConfig 2 b.final=_
  rw [bf]
  rfl

theorem binary_next_run (k counter : ℕ) (flag : Bool) (hc : counter<2^k) :
    ∃ r,runFrom machine (8*k+17)
      (config machine.start (k+1) counter (2^k-1) (2*k+3) flag)=some r ∧
      r.final=config 13 (k+1) (counter+1) (2^k-1) (2*k+3)
        (decide (counter+1<2^k)) := by
  have hp : 0<2^k := by positivity
  obtain ⟨r,hr,hf⟩ := next_run (k+1) counter (2^k-1) (2*k+3) flag
    (by rw [pow_succ]; omega) (by rw [pow_succ]; omega) (by omega)
  have ht : 8*(k+1)+9=8*k+17 := by omega
  rw [ht] at hr
  refine ⟨r,hr,?_⟩
  have he : (counter+1 ≤ 2^k-1) ↔ counter+1<2^k := by omega
  simpa only [he] using hf

end NearCubicWires.RepairOrdinary.RowTupleCounter
