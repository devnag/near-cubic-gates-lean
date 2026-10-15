import Proof.Assembly.RowsPoolMinimumAdd

/-! The live-negative sum keeps only its source, mask, width and accumulator
outside the one paid scratch erase. The same C driver survives every weight. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos mpos : ℕ) : Fin 20→ℕ:=fun i=>if i=0 then pos else if i=13 then mpos else 0
def extra (mask : List Bool) (w C a : ℕ) : Fin 7→List Bool:=
  ![mask,MatrixScoreWeight.scalar C w a,MatrixScoreWeight.zeros C,
    MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,List.replicate C true,List.replicate (C+1) false]
def data (source mask : List Bool) (w C a : ℕ) : Fin 20→List Bool:=
  Fin.addCases (m:=13) (n:=7) (motive:=fun _=>List Bool)
    (CloseoutRowsPoolMagnitude.input source w C) (extra mask w C a)
noncomputable def parsed (source mask : List Bool) (pos w C a : ℕ) (z : ℤ) : Fin 20→List Bool:=
  Fin.addCases (m:=13) (n:=7) (motive:=fun _=>List Bool)
    (CloseoutRowsPoolMagnitude.output source pos w C z) (extra mask w C a)
noncomputable def reader:=TapeEmbedding.machine 7 CloseoutRowsPoolMagnitude.machine

theorem read_run (pre tail mask : List Bool) (mpos w C a : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) :
    Step reader (CloseoutRowsPoolMagnitude.budget z w) (heads pre.length mpos)
      (data (pre++RepairRepresentation.intWord z++tail) mask w C a)
      (heads (pre.length+(RepairRepresentation.intWord z).length) mpos)
      (parsed (pre++RepairRepresentation.intWord z++tail) mask
        (pre.length+(RepairRepresentation.intWord z).length) w C a z):=by
  have h:=(CloseoutRowsPoolMagnitude.native_run pre tail w C z hC).embed
    (![mpos,0,0,0,0,0,0] : Fin 7→ℕ) (extra mask w C a)
  apply h.congr_in ?_ rfl |>.congr ?_ rfl
  all_goals funext i;fin_cases i <;> rfl

def workSlots : Fin 14→Fin 20:=![1,2,3,4,5,6,7,8,10,11,12,15,16,17]
def eraseSlots : Fin 16→Fin 20:=
  Fin.addCases (m:=15) (n:=1) (motive:=fun _=>Fin 20)
    (Fin.addCases (m:=14) (n:=1) (motive:=fun _=>Fin 20) workSlots (fun _ : Fin 1=>18))
    (fun _ : Fin 1=>19)
theorem erase_injective : Function.Injective eraseSlots:=by decide
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 14)
def eraseInput (C : ℕ) (A : Fin 14→List Bool) : Fin 16→List Bool:=
  Fin.addCases (m:=15) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=14) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>List.replicate C true))
    (fun _ : Fin 1=>List.replicate (C+1) false)
noncomputable def cleared (C : ℕ) (A : Fin 20→List Bool):=
  install eraseSlots A (eraseInput C (fun _=>List.replicate C false))

theorem clear_run (C : ℕ) (H : Fin 20→ℕ) (A : Fin 20→List Bool)
    (hh : ∀ j,H (eraseSlots j)=0) (hb : ∀ j,(A (workSlots j)).length≤C)
    (hd : A 18=List.replicate C true) (hl : A 19=List.replicate (C+1) false) :
    Step erase (2*C+4) H A H (cleared C A):=by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready C (C+1)
    (fun j=>A (workSlots j)) hb)
  have actual:=h.focus eraseSlots erase_injective H A
  have he:dockH eraseSlots H (fun _=>0)=H:=by
    funext i
    cases hp:RecoveryFocus.pick eraseSlots i with
    | none=>simp [dockH,hp]
    | some j=>
      have hij:=RecoveryFocus.slot_of_pick eraseSlots hp
      simp only [dockH,hp]
      exact (hh j).symm.trans (congrArg H hij)
  have ht:∀ j,A (eraseSlots j)=eraseInput C (fun j=>A (workSlots j)) j:=by
    intro j
    fin_cases j <;> first | rfl | exact hd | exact hl
  have out:install eraseSlots A
      (Fin.addCases (m:=15) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=14) (n:=1) (motive:=fun _=>List Bool) (fun _ : Fin 14=>List.replicate C false)
        (fun _ : Fin 1=>List.replicate C true))
        (fun _ : Fin 1=>List.replicate (max (C+1) (C+1)) false))=cleared C A:=by
    simp only [max_self]
    rfl
  exact actual.congr_in he (install_existing _ _ _ ht) |>.congr he out

theorem cleared_work (C : ℕ) (A : Fin 20→List Bool) (j : Fin 14) :
    cleared C A (workSlots j)=List.replicate C false := by
  have h:=install_slot eraseSlots erase_injective A
    (eraseInput C (fun _=>List.replicate C false)) ((j.castAdd 1).castAdd 1)
  simpa only [cleared,eraseSlots,eraseInput,Fin.addCases_left] using h

theorem cleared_live (C : ℕ) (A : Fin 20→List Bool) (i : Fin 20)
    (hi : i=0 ∨ i=9 ∨ i=13 ∨ i=14) : cleared C A i=A i:=by
  apply install_other
  rcases hi with rfl|rfl|rfl|rfl
  all_goals intro j;fin_cases j <;> decide

theorem cleared_driver (C : ℕ) (A : Fin 20→List Bool) :
    cleared C A 18=List.replicate C true ∧ cleared C A 19=List.replicate (C+1) false:=by
  constructor
  · exact install_slot eraseSlots erase_injective A _ (((0 : Fin 1).natAdd 14).castAdd 1)
  · exact install_slot eraseSlots erase_injective A _ ((0 : Fin 1).natAdd 15)

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
