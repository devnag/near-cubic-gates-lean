import Proof.Supplier.RowCoordinateBody

/-! A literal native-arity driver executes all weight coordinates and the
target. Each body restores its coefficient bank and increments its actual
coordinate template. The resulting row is an ordered stream of fields. -/
namespace NearCubicWires.RepairOrdinary.RowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowCoordinateBody.machine (fun _ _=>true)
def field {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) (j : ℕ) :=
  if hj : j ≤ n then RowCoefficientStream.field gs j hj indices else []
def word {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) : ℕ → ℕ → List Bool
  | _,0=>[]
  | j,k+1=>frame (field gs indices j)++word gs indices (j+1) k
def bodyBudget {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :=
  65536*(indices.length+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+2*n+175
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :=
  (n+1)*(bodyBudget gs indices+3)+3
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (RowCoordinateBody.entry gs j tail out indices) (n+1) driver

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool) :
    ∃ time,time ≤ count*(bodyBudget gs indices+2)+(n+1)+3 ∧
      Timed machine time (cfg gs indices 0 j (j+1) tail out)
        (cfg gs indices 3 (n+1) 1 tail (out++word gs indices j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [machine,cfg,word,List.append_nil] using
      RepeatMachine.exhaust RowCoordinateBody.machine (fun _ _=>true)
        (RowCoordinateBody.entry gs (n+1) tail out indices) (n+1)
  | succ count ih =>
    have hjn : j ≤ n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := RowCoordinateBody.body_run gs j hjn tail out indices
    have hbudget := RowCoordinateBody.budget_bound gs j hjn indices
    have hs : r.steps ≤ bodyBudget gs indices := rs.trans hbudget
    have ht := RepeatMachine.iteration RowCoordinateBody.machine (fun _ _=>true)
      (RowCoordinateBody.entry gs j tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (RowCoordinateBody.entry gs (j+1) tail (out++frame (RowCoefficientStream.field gs j hjn indices)) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (RowCoefficientStream.field gs j hjn indices))
    have hdriver : j+1+1=j+2 := by omega
    rw [hdriver] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [machine,cfg,word,field,dif_pos hjn,List.append_assoc] using whole

theorem row_run {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (tail out : List Bool) :
    ∃ r,runFrom machine (budget gs indices) (cfg gs indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs indices 3 (n+1) 1 tail (out++word gs indices 0 (n+1)) ∧
      r.steps ≤ budget gs indices := by
  obtain ⟨time,hb,ht⟩ := remaining gs indices 0 (n+1) (by omega) tail out
  have hbudget : time ≤ budget gs indices := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have hmore := runFrom_moreFuel machine time (budget gs indices-time) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  exact ⟨r,hmore,rf,rs.le.trans hbudget⟩

end NearCubicWires.RepairOrdinary.RowCoordinateLoop
