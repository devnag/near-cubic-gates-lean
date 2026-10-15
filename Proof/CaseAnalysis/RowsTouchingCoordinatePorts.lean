import Proof.CaseAnalysis.RowsTouchingCoordinateVectors

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def low (i : Fin 9):Fin 35:=(((i.castAdd 15).castAdd 1).castAdd 1).castAdd 9
def middle (i : Fin 15):Fin 35:=(((i.natAdd 9).castAdd 1).castAdd 1).castAdd 9
def last (i : Fin 9):Fin 35:=i.natAdd 26

theorem cases35 {p : Fin 35→Prop} (h0:∀ i,p (low i)) (h1:∀ i,p (middle i))
    (h24:p 24) (h25:p 25) (h2:∀ i,p (last i)) (i : Fin 35):p i:=by
  refine Fin.addCases (m:=26) (n:=9) ?_ h2 i
  intro j
  refine Fin.addCases (m:=25) (n:=1) ?_ ?_ j
  · intro k
    refine Fin.addCases (m:=24) (n:=1) ?_ ?_ k
    · intro l
      exact Fin.addCases (m:=9) (n:=15) h0 h1 l
    · intro l;fin_cases l;exact h24
  · intro k;fin_cases k;exact h25

theorem data_low (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 9):
    data q G K k h w P C D E source mask st (low i)=
      GateSummary.data P C source (supportCells mask) st.gate.summary i:=by
  simp only [data,low,GateFoldReady.data,Gate.data,Fin.addCases_left]

theorem data_middle (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 15):
    data q G K k h w P C D E source mask st (middle i)=Gate.extra q k w P st.gate i:=by
  simp only [data,middle,GateFoldReady.data,Gate.data,Fin.addCases_left,Fin.addCases_right]

theorem data_last (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 9):
    data q G K k h w P C D E source mask st (last i)=extra q K h w P E st i:=by
  simp only [data,last,Fin.addCases_right]

theorem data_count (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    data q G K k h w P C D E source mask st 24=RepairSource.VerifierDecoding.CompareMachine.word G:=rfl
theorem data_log (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    data q G K k h w P C D E source mask st 25=List.replicate D false:=rfl
theorem chosen_excluded (w k h : ℕ) (st : Store):(chosen w k h st).gate.excluded=st.gate.excluded:=rfl
theorem chosen_included (w k h : ℕ) (st : Store):(chosen w k h st).gate.included=st.gate.included:=rfl
theorem chosen_store (w k h : ℕ) (st : Store):
    choiceStore (chosen w k h st)=Choice.after w st.gate.excluded st.gate.included k h (choiceStore st):=rfl

theorem choice_fields (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (j : Fin 12):
    data q G K k h w P C D E source mask st (choiceSlots j)=
      Choice.data w st.gate.excluded st.gate.included k h P (choiceStore st) j:=by
  fin_cases j <;> rfl

theorem choice_outside (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 35) (hi:∀ j,choiceSlots j≠i):
    data q G K k h w P C D E source mask (chosen w k h st) i=
      data q G K k h w P C D E source mask st i:=by
  revert hi
  refine cases35 (p:=fun i=>(∀ j,choiceSlots j≠i)→
    data q G K k h w P C D E source mask (chosen w k h st) i=
      data q G K k h w P C D E source mask st i) ?_ ?_ ?_ ?_ ?_ i
  · intro j hj;rw [data_low,data_low];rfl
  · intro j hj;rw [data_middle,data_middle]
    apply vector15
    · intro _;rfl
    · intro _;rfl
    · intro _;rfl
    · intro he;subst j;exact False.elim (hj 6 rfl)
    · intro _;rfl
  · intro _;rw [data_count,data_count]
  · intro _;rw [data_log,data_log]
  · intro j hj;rw [data_last,data_last]
    apply vector9
    · intro _;rfl
    · intro he;subst j;exact False.elim (hj 4 rfl)
    · intro he;subst j;exact False.elim (hj 5 rfl)
    · intro he;subst j;exact False.elim (hj 9 rfl)
    · intro _;rfl

theorem choice_installed (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell) (st : Store):
    install choiceSlots (data q G K k h w P C D E source mask st)
      (Choice.data w st.gate.excluded st.gate.included k h P
        (Choice.after w st.gate.excluded st.gate.included k h (choiceStore st)))=
      data q G K k h w P C D E source mask (chosen w k h st):=by
  apply HierarchyWidth.install_eq _ (by decide)
  · intro j
    simpa only [chosen_excluded,chosen_included,chosen_store] using
      choice_fields q G K k h w P C D E source mask (chosen w k h st) j
  · exact choice_outside q G K k h w P C D E source mask st

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
