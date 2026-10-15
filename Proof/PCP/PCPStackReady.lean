import Proof.PCP.PCPStackPop
import Proof.MachineModel.OrdinaryMaskedReset

/-! Stack calls with actual reusable zero storage and a paid local-output
reset. The stack cursor remains at its streamed boundary throughout. -/
namespace NearCubicWires.RepairOrdinary.PCPStackReady
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pushInput (bits stack : List Bool) (stackCap counterCap : ℕ) : Configuration 3 4 :=
  ⟨0,![0,stack.length,0],![frame bits,ZeroPadding.pad stackCap stack,List.replicate counterCap false]⟩
def pushOutput (bits stack : List Bool) (stackCap counterCap : ℕ) : Configuration 3 4 :=
  ⟨3,![0,(stack++(frame bits).reverse).length,0],
    ![frame bits,ZeroPadding.pad stackCap (stack++(frame bits).reverse),
      List.replicate (max counterCap (2*bits.length+1)) false]⟩

theorem push_run (bits stack : List Bool) (stackCap counterCap : ℕ) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom PCPStackPush.machine (4*bits.length+3) (pushInput bits stack stackCap counterCap)=some r ∧
      r.final=pushOutput bits stack stackCap counterCap ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := PCPStackPush.push_run bits stack
  let caps : Fin 3 → ℕ := ![0,stackCap,counterCap]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config PCPStackPush.machine caps _ _ base hr
  have hi : ZeroPadding.config caps (PCPStackPush.forward 0 (frame bits) stack 0)=
      pushInput bits stack stackCap counterCap := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,PCPStackPush.forward,pushInput,ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad counterCap ([]++List.replicate (2*bits.length+1) false)=_
      simp only [List.nil_append,ZeroPadding.pad,List.length_replicate]
      rw [←List.replicate_add]
      congr 1
      omega

def selected (i : Fin 2) : Bool := decide (i=1)
def machine : Machine 3 6 := MaskedReset.machine PCPStackPop.machine selected
def popInput (bits pre : List Bool) (z : ℕ) : Configuration 3 6 :=
  Rewind.recording (PCPStackPop.cfg 0 (pre++(frame bits).reverse++List.replicate z false)
    (pre.length+(frame bits).length) []) 0

theorem pop_run (bits pre : List Bool) (z : ℕ) :
    ∃ r : ExecutionReceipt 3 6,
      runFrom machine (4*bits.length+6) (popInput bits pre z)=some r ∧
      r.final.tapes=![pre++List.replicate (2*bits.length+1+z) false,frame bits,
        List.replicate (2*bits.length+2) false] ∧
      r.final.heads=![pre.length,0,0] ∧ r.steps=4*bits.length+6 := by
  obtain ⟨base,hr,hf,hs⟩ := PCPStackPop.pop_run bits pre [] z
  have hhead : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=1 := by simpa [selected] using hi
    subst i
    rw [hf,hs]
    change ([]++frame bits).length ≤ 2*bits.length+2
    simp [frame_length]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := MaskedReset.reset_run PCPStackPop.machine selected _ _ base hr hhead
  have he : 2*base.steps+2=4*bits.length+6 := by omega
  rw [he] at hrun hsteps
  refine ⟨r,hrun,?_,?_,hsteps⟩
  · rw [hfinal,hf,hs]
    funext i
    fin_cases i <;> rfl
  · rw [hfinal,hf]
    funext i
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPStackReady
