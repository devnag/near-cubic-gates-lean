import Proof.Supplier.RowCommonCoordinateBody

/-! All weights and the target are emitted at the one common cut width.
The native arity driver executes the coordinate loop and restores itself. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowCommonCoordinateBody.machine (fun _ _=>true)
def field {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) (p j : ℕ) :=
  if hj : j≤n then MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices) else []
def word {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) (p : ℕ) : ℕ→ℕ→List Bool
  | _,0=>[]
  | j,k+1=>frame (field gs indices p j)++word gs indices p (j+1) k
def bodyBudget {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (indices : List (Fin gs.length)) :=
  RowCommonBounds.bound gs indices.length p+2*n+10
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (indices : List (Fin gs.length)) :=
  (n+1)*(bodyBudget gs p indices+3)+3
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (RowCommonCoordinateBody.entry gs j p tail out indices) (n+1) driver

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool)
    (hp : RowCoordinateLoop.width gs indices≤p) :
    ∃ time,time≤count*(bodyBudget gs p indices+2)+(n+1)+3 ∧
      Timed machine time (cfg gs p indices 0 j (j+1) tail out)
        (cfg gs p indices 3 (n+1) 1 tail (out++word gs indices p j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [machine,cfg,word,List.append_nil] using
      RepeatMachine.exhaust RowCommonCoordinateBody.machine (fun _ _=>true)
        (RowCommonCoordinateBody.entry gs (n+1) p tail out indices) (n+1)
  | succ count ih =>
    have hjn : j≤n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := RowCommonCoordinateBody.body_run gs j hjn p tail out indices hp
    have hs : r.steps≤bodyBudget gs p indices := by
      unfold bodyBudget RowCommonCoordinateBody.budget at *
      omega
    have ht := RepeatMachine.iteration RowCommonCoordinateBody.machine (fun _ _=>true)
      (RowCommonCoordinateBody.entry gs j p tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (RowCommonCoordinateBody.entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hjn indices))) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hjn indices)))
    have hdriver : j+1+1=j+2 := by omega
    rw [hdriver] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [machine,cfg,word,field,dif_pos hjn,List.append_assoc] using whole

theorem row_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (indices : List (Fin gs.length))
    (tail out : List Bool) (hp : RowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs p indices) (cfg gs p indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p indices 3 (n+1) 1 tail (out++word gs indices p 0 (n+1)) ∧
      r.steps≤budget gs p indices := by
  obtain ⟨time,hb,ht⟩ := remaining gs p indices 0 (n+1) (by omega) tail out hp
  have hbudget : time≤budget gs p indices := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have hmore := runFrom_moreFuel machine time (budget gs p indices-time) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  exact ⟨r,hmore,rf,rs.le.trans hbudget⟩

theorem field_weight {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) (p : ℕ) (j : Fin n) :
    field gs indices p j.val=MatrixScoreBatch.signMagnitude p ((RowCoordinateLoop.equation gs indices).weights j) := by
  simp only [field,dif_pos j.isLt.le,RowCommonCoefficient.value,RowCoordinateLoop.equation,
    RowCachedEquation.stack_weight]

theorem field_target {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) (p : ℕ) :
    field gs indices p n=MatrixScoreBatch.signMagnitude p (RowCoordinateLoop.equation gs indices).target := by
  simp only [field,dif_pos le_rfl,RowCommonCoefficient.value,RowCoordinateLoop.equation,
    RowCachedEquation.stack_target]

theorem word_add {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (p j a b : ℕ) : word gs indices p j (a+b)=word gs indices p j a++word gs indices p (j+a) b := by
  induction a generalizing j with
  | zero => simp [word]
  | succ a ih =>
    rw [Nat.succ_add,word,word,ih,List.append_assoc]
    rw [show j+1+a=j+(a+1) by omega]

theorem word_ofFn {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (p j count : ℕ) : word gs indices p j count=
      (List.ofFn (fun i : Fin count=>frame (field gs indices p (j+i.val)))).flatten := by
  induction count generalizing j with
  | zero => simp [word]
  | succ count ih =>
    rw [word,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have h : (fun i : Fin count=>frame (field gs indices p (j+1+i.val)))=
        (fun i : Fin count=>frame (field gs indices p (j+(i.val+1)))) := by
      funext i
      rw [show j+1+i.val=j+(i.val+1) by omega]
    rw [h]

theorem word_equation {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) (p : ℕ) :
    word gs indices p 0 (n+1)=RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs indices) := by
  rw [word_add,word_ofFn]
  simp only [Nat.zero_add,word,List.append_nil,field_target]
  simp only [RowCoordinateLoop.equationWord,EquationWidenLoop.stream,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,field_weight]
  congr 1
  rw [List.flatMap]
  simp only [List.map_ofFn,Function.comp_def]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ)
    (indices : List (Fin gs.length)) (tail out : List Bool) (hp : RowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs p indices) (cfg gs p indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p indices 3 (n+1) 1 tail
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs indices)) ∧
      r.steps≤budget gs p indices := by
  simpa only [word_equation] using row_run gs p indices tail out hp

end NearCubicWires.RepairOrdinary.RowCommonCoordinateLoop
