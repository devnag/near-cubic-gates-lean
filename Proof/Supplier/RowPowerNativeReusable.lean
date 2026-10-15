import Proof.Supplier.RowPowerNativeReset
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryReadyCalls

/-! A native signed field with physically reusable scratch. The source and
two append cursors survive; the capacity driver pays for every erased cell. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 9 → Fin 15 := ![1,2,3,4,5,6,7,8,12]
def eraseSlots : Fin 11 → Fin 15 :=
  Fin.addCases (m := 10) (n := 1) (motive := fun _ => Fin 15)
    (Fin.addCases (m := 9) (n := 1) (motive := fun _ => Fin 15)
      workSlots (fun _ : Fin 1 => 13)) (fun _ : Fin 1 => 14)
theorem erase_injective : Function.Injective eraseSlots := by decide
def extra (C : ℕ) : Fin 2 → List Bool :=
  ![List.replicate C true,List.replicate (C+1) false]
def erasedInput (C : ℕ) (backing : Fin 9 → List Bool) : Fin 11 → List Bool :=
  Fin.addCases (m := 10) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 9) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ : Fin 1 => List.replicate C true))
    (fun _ : Fin 1 => List.replicate (C+1) false)
noncomputable def cleared (C : ℕ) (a : Fin 15 → List Bool) :=
  install eraseSlots a (erasedInput C (fun _ => List.replicate C false))
noncomputable def first := TapeEmbedding.machine 2 RowPowerNativeReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 9)
noncomputable def machine := Composition.machine first last
def budget (z : ℤ) (w C : ℕ) := 12*natBitLength z.natAbs+4*w+2*C+29
def entry (source : List Bool) (pos w C : ℕ) (positive negative : List Bool) : Configuration 15 20 :=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ => 0) (extra C)
    (RowPowerNativeReset.entry source pos w C positive negative))
noncomputable def resetOutput (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) : Configuration 15 16 :=
  TapeEmbedding.config (fun _ => 0) (extra C)
    (RowPowerNativeReset.output source pos w C z positive negative)

theorem clear_run (C : ℕ) (heads : Fin 15 → ℕ) (a : Fin 15 → List Bool)
    (hh : ∀ j,heads (eraseSlots j)=0)
    (hb : ∀ j,(a (workSlots j)).length≤C)
    (hd : a 13=List.replicate C true) (hl : a 14=List.replicate (C+1) false) :
    ∃ r,runFrom last (2*C+4) ⟨last.start,heads,a⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared C a ∧ r.steps=2*C+4 := by
  obtain ⟨base,hbase,bt,bh,bs⟩ := RecoveryScratchErase.erase_ready C (C+1)
    (fun j => a (workSlots j)) hb
  have ht : ∀ j,a (eraseSlots j)=erasedInput C (fun j => a (workSlots j)) j := by
    intro j
    refine Fin.addCases (m := 10) (n := 1) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m := 9) (n := 1) (fun i => ?_) (fun i => ?_) i
      · simp only [eraseSlots,erasedInput,Fin.addCases_left]
      · simpa only [eraseSlots,erasedInput,Fin.addCases_left,Fin.addCases_right] using hd
    · simpa only [eraseSlots,erasedInput,Fin.addCases_right] using hl
  have hi : RecoveryFocus.config eraseSlots heads a
      (initialConfiguration (RecoveryScratchErase.resetMachine 9)
        (erasedInput C (fun j => a (workSlots j))))=⟨last.start,heads,a⟩ := by
    exact WilliamsSourceCrop.focus_same eraseSlots
      (⟨last.start,heads,a⟩ : Configuration 15 4) _ hh ht
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config eraseSlots erase_injective
    (RecoveryScratchErase.resetMachine 9) heads a _ _ base hbase
  unfold erasedInput at hi
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf]
    funext i
    cases hp : RecoveryFocus.pick eraseSlots i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick eraseSlots hp
      simpa only [RecoveryFocus.config,hp] using
        (bh j).trans ((hh j).symm.trans (congrArg heads he))
  · rw [rf]
    change install eraseSlots a base.final.tapes=cleared C a
    simp only [bt,max_self]
    rfl

theorem reset_heads (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) (j : Fin 11) :
    (resetOutput source pos w C z positive negative).heads (eraseSlots j)=0 := by
  have hh := RowPowerNativeReset.output_heads source pos w C z positive negative
  fin_cases j <;> simp [resetOutput,TapeEmbedding.config,eraseSlots,workSlots,Fin.addCases,hh]

theorem field_run (pre suffix positive negative : List Bool) (z : ℤ) (w C : ℕ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) :
    ∃ r,runFrom machine (budget z w C)
      (entry (pre++intWord z++suffix) pre.length w C positive negative)=some r ∧
      r.final.heads=(resetOutput (pre++intWord z++suffix)
        (pre.length+(intWord z).length) w C z positive negative).heads ∧
      r.final.tapes=cleared C (resetOutput (pre++intWord z++suffix)
        (pre.length+(intWord z).length) w C z positive negative).tapes ∧
      r.steps=budget z w C := by
  obtain ⟨raw,hr,rf,rs,support⟩ := RowPowerNativeReset.field_run pre suffix positive negative z w C hC
  let firstRun := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra C) raw
  have firstCall := TapeEmbedding.run_embed RowPowerNativeReset.machine
    (fun _ : Fin 2 => 0) (extra C) _ _ raw hr
  have outEq : firstRun.final=resetOutput (pre++intWord z++suffix)
      (pre.length+(intWord z).length) w C z positive negative := by
    change TapeEmbedding.config _ _ raw.final=_
    rw [rf]
    rfl
  have hb : ∀ j,(firstRun.final.tapes (workSlots j)).length≤C := by
    intro j
    fin_cases j <;> apply support <;> decide
  obtain ⟨lastRun,lastCall,lh,lt,ls⟩ := clear_run C firstRun.final.heads firstRun.final.tapes
    (by rw [outEq]; exact reset_heads _ _ _ _ _ _ _)
    hb rfl rfl
  have joined := Composition.run_join first last (2*RowPowerNativeReset.rawTime z w+2)
    (2*C+4) _ firstRun lastRun firstCall lastCall
  have hbgt : (2*RowPowerNativeReset.rawTime z w+2)+1+(2*C+4)=budget z w C := by
    unfold RowPowerNativeReset.rawTime budget
    omega
  rw [hbgt] at joined
  refine ⟨Composition.joinedReceipt firstRun lastRun,joined,?_,?_,?_⟩
  · exact lh.trans (congrArg Configuration.heads outEq)
  · exact lt.trans (congrArg (fun c => cleared C c.tapes) outEq)
  · change raw.steps+1+lastRun.steps=budget z w C
    rw [rs,ls,hbgt]

theorem cleared_work (C : ℕ) (a : Fin 15 → List Bool) (j : Fin 9) :
    cleared C a (workSlots j)=List.replicate C false := by
  have h := install_slot eraseSlots erase_injective a
    (erasedInput C (fun _ => List.replicate C false)) ((j.castAdd 1).castAdd 1)
  simpa only [cleared,eraseSlots,erasedInput,Fin.addCases_left] using h
theorem cleared_live (C : ℕ) (a : Fin 15 → List Bool) (i : Fin 15)
    (hi : i=0 ∨ i=9 ∨ i=10 ∨ i=11) : cleared C a i=a i := by
  apply install_other
  rcases hi with rfl|rfl|rfl|rfl
  all_goals intro j; fin_cases j <;> decide

end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
