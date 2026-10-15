import Proof.CaseAnalysis.RowsDegreeCoefficient
import Proof.CaseAnalysis.RowsEnumeratedCuts

/-! A complete fixed-degree row call starts with a blank coefficient cache.
Unary j and p produce (-2)^j once, then the actual positional enumeration
and signed-cut writer run at their retained native cache and output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsComputedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientSlots (i : Fin 14) : Fin 103 :=
  if i.val=12 then 48 else i.natAdd 89
def old (i : Fin 89) : Fin 103 := i.castAdd 14
theorem coefficient_injective : Function.Injective coefficientSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [coefficientSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega
theorem outside (i : Fin 89) (hi : i≠48) : ∀ j,coefficientSlots j≠old i := by
  intro j h
  have hv := congrArg Fin.val h
  simp only [coefficientSlots,old,Fin.val_castAdd] at hv
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · simp only [Fin.val_natAdd] at hv
    have hb := i.isLt
    omega

noncomputable def first := RecoveryFocus.machine coefficientSlots CloseoutRowsDegreeCoefficient.machine
noncomputable def last := TapeEmbedding.machine 14 CloseoutRowsEnumeratedCuts.machine
noncomputable def machine := Composition.machine first last
noncomputable def body {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsEnumeratedCuts.input state gs p F w (j+1) rows out ((-2 : ℤ)^j)
noncomputable def input {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Configuration 103 s :=
  ⟨state,Fin.addCases (m := 89) (n := 14) (motive := fun _ => ℕ)
      (body state gs p F w j rows out).heads (fun _ => 0),
    Fin.addCases (m := 89) (n := 14) (motive := fun _ => List Bool)
      (Function.update (body state gs p F w j rows out).tapes 48 [])
      (CloseoutRowsDegreeCoefficient.input j p)⟩
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w j : ℕ) (rows : List (List Bool)) :=
  CloseoutRowsDegreeCoefficient.budget j p+1+CloseoutRowsEnumeratedCuts.budget gs p F w (j+1) rows

theorem body_coefficient {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (body state gs p F w j rows out).heads 48=0 ∧
    (body state gs p F w j rows out).tapes 48=
      frame (MatrixScoreBatch.signMagnitude p ((-2 : ℤ)^j)) := by
  constructor
  · change (body state gs p F w j rows out).heads ((48 : Fin 49).castAdd 40)=0
    simp only [body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
    change (CloseoutRowsEnumeratedCuts.core state gs p F w (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)).heads
      ((0 : Fin 1).natAdd 48)=0
    simp only [CloseoutRowsEnumeratedCuts.core,Fin.addCases_right]
  · change (body state gs p F w j rows out).tapes ((48 : Fin 49).castAdd 40)=_
    simp only [body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
    change (CloseoutRowsEnumeratedCuts.core state gs p F w (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)).tapes
      ((0 : Fin 1).natAdd 48)=_
    simp only [CloseoutRowsEnumeratedCuts.core,Fin.addCases_right]

theorem cuts_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w j : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ actual,runFrom machine (budget gs p F w j rows)
      (input machine.start gs p F w j rows out)=some actual ∧
      (∀ i,actual.final.heads (old (CloseoutRowsEnumeratedCuts.rowSlots i))=
        (CloseoutRowsEnumeratedCuts.finished machine.start gs p F w (j+1) rows out ((-2 : ℤ)^j)).heads i) ∧
      (∀ i,actual.final.tapes (old (CloseoutRowsEnumeratedCuts.rowSlots i))=
        (CloseoutRowsEnumeratedCuts.finished machine.start gs p F w (j+1) rows out ((-2 : ℤ)^j)).tapes i) ∧
      actual.steps≤budget gs p F w j rows := by
  obtain ⟨⟨cof,hcof,ct,ch,_⟩,cw⟩ := CloseoutRowsDegreeCoefficient.coefficient_ready j p (hj.trans_le hQp)
  let start := input first.start gs p F w j rows out
  have hh : ∀ i,start.heads (coefficientSlots i)=0 := by
    intro i
    by_cases hz : i.val=12
    · have he : i=12 := Fin.ext hz
      subst i
      change (body first.start gs p F w j rows out).heads 48=0
      exact (body_coefficient first.start gs p F w j rows out).1
    · simp only [coefficientSlots,hz,↓reduceIte,start,input,Fin.addCases_right]
  have ht : ∀ i,start.tapes (coefficientSlots i)=CloseoutRowsDegreeCoefficient.input j p i := by
    intro i
    by_cases hz : i.val=12
    · have he : i=12 := Fin.ext hz
      subst i
      change Function.update (body first.start gs p F w j rows out).tapes 48 [] 48=[]
      exact Function.update_self _ _ _
    · simp only [coefficientSlots,hz,↓reduceIte,start,input,Fin.addCases_right]
  obtain ⟨a,ha,_,_,ah,atapeC,ak⟩ := RecoveryFocus.dock coefficientSlots coefficient_injective
    CloseoutRowsDegreeCoefficient.machine _ start.heads start.tapes _ hh ht cof hcof
  have ahead : ∀ i,a.final.heads (old i)=(body CloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out).heads i := by
    intro i
    by_cases hz : i=48
    · subst i
      change a.final.heads (coefficientSlots 12)=_
      rw [ah,ch]
      exact (body_coefficient _ gs p F w j rows out).1.symm
    · rw [(ak (old i) (outside i hz)).1]
      simp only [start,input,old,Fin.addCases_left,body,CloseoutRowsEnumeratedCuts.input,
        TapeEmbedding.config,CloseoutRowsEnumeratedCuts.core]
  have atape : ∀ i,a.final.tapes (old i)=(body CloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out).tapes i := by
    intro i
    by_cases hz : i=48
    · subst i
      change a.final.tapes (coefficientSlots 12)=_
      rw [atapeC,ct,cw]
      exact (body_coefficient _ gs p F w j rows out).2.symm
    · rw [(ak (old i) (outside i hz)).2]
      simp only [start,input,old,Fin.addCases_left,Function.update_of_ne hz,
        body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,CloseoutRowsEnumeratedCuts.core]
  obtain ⟨child,hchild,childH,childT,_⟩ := CloseoutRowsEnumeratedCuts.cuts_run gs p F Q w (j+1)
    rows out ((-2 : ℤ)^j) hl hM hw hj hp hF
  let tail := TapeEmbedding.receipt (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89)) child
  have htail := TapeEmbedding.run_embed CloseoutRowsEnumeratedCuts.machine
    (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89)) _ _ child hchild
  have hi : TapeEmbedding.config (fun i : Fin 14 => a.final.heads (i.natAdd 89))
      (fun i : Fin 14 => a.final.tapes (i.natAdd 89))
      (body CloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out)=
      Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 89) (n := 14) ?_ ?_ i <;> intro k
      · simpa only [TapeEmbedding.config,Composition.restart,Fin.addCases_left,old] using (ahead k).symm
      · simp only [TapeEmbedding.config,Composition.restart,Fin.addCases_right]
    · funext i
      refine Fin.addCases (m := 89) (n := 14) ?_ ?_ i <;> intro k
      · simpa only [TapeEmbedding.config,Composition.restart,Fin.addCases_left,old] using (atape k).symm
      · simp only [TapeEmbedding.config,Composition.restart,Fin.addCases_right]
  change runFrom last _ (TapeEmbedding.config
    (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89))
    (body CloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out))=some tail at htail
  rw [hi] at htail
  have hfirst : runFrom first (CloseoutRowsDegreeCoefficient.budget j p)
      (input first.start gs p F w j rows out)=some a := ha
  have whole := Composition.run_join first last _ _ _ a tail hfirst htail
  refine ⟨Composition.joinedReceipt a tail,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · intro i
    change tail.final.heads ((CloseoutRowsEnumeratedCuts.rowSlots i).castAdd 14)=_
    rw [TapeEmbedding.receipt_heads_old]
    exact childH i
  · intro i
    change tail.final.tapes ((CloseoutRowsEnumeratedCuts.rowSlots i).castAdd 14)=_
    rw [TapeEmbedding.receipt_tapes_old]
    exact childT i

end NearCubicWires.RepairOrdinary.CloseoutRowsComputedCuts
