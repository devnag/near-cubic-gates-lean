import Proof.Amplification.RecoveryScannerReadNative

/-! Execute the grammar reader on its scanner copy and retain all final
checker banks. Successful syntax gives a real source cursor for table counts. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdScanner
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots (j : Fin 66) : Fin 270 := slots (viewSlots j)
theorem readSlots_injective : Function.Injective readSlots := slots_injective.comp viewSlots_injective
noncomputable def readProgram := RecoveryFocus.machine readSlots RecoveryRawViewEntry.machine
def flag : Fin 270 := readSlots 28
def source : Fin 270 := readSlots 29

theorem read_other (i : Fin 172) : ∀ j,readSlots j≠i.castAdd 98 := by
  intro j he
  have hv : (readSlots j).val=i.val := congrArg (fun k : Fin 270=>k.val) he
  have hb : 2≤(viewSlots j).val := by
    unfold viewSlots
    split <;> dsimp <;> omega
  change (slots (viewSlots j)).val=i.val at hv
  rw [slot_val,if_neg (by omega)] at hv
  have hi := i.isLt
  omega

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem read_input {s : Nat} (g : Fin 270→Nat) (a : Fin 270→List Bool) (q : Fin s) :
    RecoveryFocus.config readSlots g a ⟨q,(fun j=>g (readSlots j)),(fun j=>a (readSlots j))⟩=
      (⟨q,g,a⟩ : Configuration 270 s) := by
  apply focus_configuration readSlots readSlots_injective
  · rfl
  · intro j; rfl
  · intro j; rfl
  · intro i _; rfl
  · intro i _; rfl

theorem read_retained {s : Nat} (g : Fin 270→Nat) (a : Fin 270→List Bool) (c : Configuration 66 s) :
    (fun i : Fin 172=>(RecoveryFocus.config readSlots g a c).heads (i.castAdd 98))=
      (fun i=>g (i.castAdd 98)) ∧
    (fun i : Fin 172=>(RecoveryFocus.config readSlots g a c).tapes (i.castAdd 98))=
      (fun i=>a (i.castAdd 98)) := by
  constructor
  all_goals
    funext i
    have hn : ¬∃ j,readSlots j=i.castAdd 98 := by rintro ⟨j,hj⟩; exact read_other i j hj
    simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]

theorem read_run (bits word : List Bool) (g : Fin 270→Nat) (a : Fin 270→List Bool)
    (hready : RecoveryColdView.Ready bits word (fun j=>g (slots j)) (fun j=>a (slots j))) :
    ∃ count r,count≤limit bits ∧
      runFrom readProgram (RecoveryRawViewEntry.budget (view bits word (2*(count*(width bits+2)+1))))
        ⟨readProgram.start,g,a⟩=some r ∧
      r.steps≤536870912*(width bits+1)^4 ∧ r.final.heads flag=0 ∧
      r.final.tapes flag=[RecoveryRawViewEntry.answer
        (view bits word (2*(count*(width bits+2)+1))) word (count*(width bits+2)+1)] ∧
      (fun i : Fin 172=>r.final.heads (i.castAdd 98))=(fun i=>g (i.castAdd 98)) ∧
      (fun i : Fin 172=>r.final.tapes (i.castAdd 98))=(fun i=>a (i.castAdd 98)) ∧
      (r.final.tapes flag=[true] → ∃ pos,r.final.heads source=2*pos ∧ r.final.tapes source=frame word) := by
  obtain ⟨count,hc,_,_,hn⟩ := ready_native bits word (fun j=>g (slots j)) (fun j=>a (slots j))
    hready RecoveryRawViewEntry.machine.start
  obtain ⟨base,hbase,hbound,hh,ht,hgood⟩ := native_run bits word (count*(width bits+2)+1)
    (fun j=>g (readSlots j)) (fun j=>a (readSlots j)) hn
  obtain ⟨r,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config readSlots readSlots_injective
    RecoveryRawViewEntry.machine g a _ _ base hbase
  rw [read_input] at hr
  have hk := read_retained g a base.final
  have heh (j : Fin 66) : r.final.heads (readSlots j)=base.final.heads j := by
    rw [hfinal]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot readSlots readSlots_injective]
  have het (j : Fin 66) : r.final.tapes (readSlots j)=base.final.tapes j := by
    rw [hfinal]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot readSlots readSlots_injective]
  refine ⟨count,r,hc,hr,hsteps.le.trans hbound,(heh 28).trans hh,(het 28).trans ht,?_,?_,?_⟩
  · rw [hfinal]
    exact hk.1
  · rw [hfinal]
    exact hk.2
  · intro ha
    have hb : RecoveryRawViewEntry.answer (view bits word (2*(count*(width bits+2)+1)))
        word (count*(width bits+2)+1)=true := by
      have he := ((het 28).trans ht).symm.trans ha
      exact List.cons.inj he |>.1
    obtain ⟨pos,hpos,hsource⟩ := hgood hb
    exact ⟨pos,(heh 29).trans hpos,(het 29).trans hsource⟩

end NearCubicWires.RepairOrdinary.RecoveryColdScanner
