import Proof.Supplier.RowTupleEquationBounds

/-! The complete equation emitter accepts any sufficiently large fixed
allocation. One source-size allocation can therefore serve every selected
tuple; its size need not depend on the runtime selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.RowCommonFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_mono {n : ℕ} (gs : List (ExactThresholdGate n)) (p a b : ℕ) (h : a≤b) :
    RowCommonBounds.capacity gs a p≤RowCommonBounds.capacity gs b p := by
  have hm := Nat.mul_le_mul_right (RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs))
    (Nat.mul_le_mul_left 16384 (Nat.add_le_add_right h 1))
  unfold RowCommonBounds.capacity
  omega

theorem coefficient_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices≤p) (hF : RowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom RowCommonClear.machine (4*F+7) (RowCommonClear.entry gs j p F tail out indices)=some r ∧
      r.final.heads=(RowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(RowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤4*F+7 := by
  have hcall := (RowCommonBounds.call_fits gs j hj p indices).trans hF
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCommonReusable.reusable_run gs j hj p F tail out indices hp hcall
    ((RowCommonBounds.padding_fits gs indices.length p).trans hF)
    ((RowCommonBounds.inner_fits gs indices.length p).trans hF)
  have hb : 2*RowCommonCoefficient.budget gs j hj p indices+2*F+7≤4*F+7 := by omega
  have more := runFrom_moreFuel RowCommonClear.machine _
    (4*F+7-(2*RowCommonCoefficient.budget gs j hj p indices+2*F+7)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rh,rt,rs.trans hb⟩

noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (RowCommonClear.entry gs j p F tail out indices) RowCommonCoordinateBody.machine.start

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : RowCommonBounds.capacity gs indices.length p≤F) :
    Function.update (RowCommonClear.entry gs j p F tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (RowCommonClear.entry gs (j+1) p F tail out indices).tapes := by
  have hpos : 1≤F := by have := RowCommonBounds.padding_fits gs indices.length p; omega
  have hinner := (RowCommonBounds.inner_fits gs indices.length p).trans hF
  rw [RowCommonReusable.entry_tapes gs j p F tail out indices hpos hinner,
    RowCommonReusable.entry_tapes gs (j+1) p F tail out indices hpos hinner]
  funext i; fin_cases i <;> simp [RowCommonReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices≤p) (hF : RowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom RowCommonCoordinateBody.machine (4*F+2*j+17) (entry gs j p F tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤4*F+2*j+17 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := coefficient_run gs j hj p F tail out indices hp hF
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,RowCommonReusable.entry_tapes gs j p F tail _ indices
      (by have := RowCommonBounds.padding_fits gs indices.length p; omega)
      ((RowCommonBounds.inner_fits gs indices.length p).trans hF)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := RowCommonCoordinateBody.increment_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join RowCommonClear.machine RowCommonCoordinateBody.increment _ _ _ a b ha hb
  rw [show 4*F+7+1+(2*j+9)=4*F+2*j+17 by omega] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,ah]
    exact RowCommonCoordinateBody.coordinate_heads gs j (j+1) p F tail _ indices
  · change b.final.tapes=_
    rw [bt,atapes]
    exact coordinate_tapes gs j p F tail _ indices hF
  · change a.steps+1+b.steps≤_
    omega

noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ) (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (entry gs j p F tail out indices) (n+1) driver
def budget (n F : ℕ) := (n+1)*(4*F+2*n+20)+3

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ) (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool)
    (hp : RowCoordinateLoop.width gs indices≤p) (hF : RowCommonBounds.capacity gs indices.length p≤F) :
    ∃ time,time≤count*(4*F+2*n+19)+(n+1)+3 ∧
      Timed RowCommonCoordinateLoop.machine time (cfg gs p F indices 0 j (j+1) tail out)
        (cfg gs p F indices 3 (n+1) 1 tail (out++RowCommonCoordinateLoop.word gs indices p j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [cfg,RowCommonCoordinateLoop.machine,RowCommonCoordinateLoop.word,List.append_nil] using
      RepeatMachine.exhaust RowCommonCoordinateBody.machine (fun _ _=>true) (entry gs (n+1) p F tail out indices) (n+1)
  | succ count ih =>
    have hjn : j≤n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := body_run gs j hjn p F tail out indices hp hF
    have hs : r.steps≤4*F+2*n+17 := by omega
    have ht := RepeatMachine.iteration RowCommonCoordinateBody.machine (fun _ _=>true)
      (entry gs j p F tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hjn indices))) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hjn indices)))
    rw [show j+1+1=j+2 by omega] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [cfg,RowCommonCoordinateLoop.machine,RowCommonCoordinateLoop.word,
        RowCommonCoordinateLoop.field,dif_pos hjn,List.append_assoc] using whole

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ) (indices : List (Fin gs.length))
    (tail out : List Bool) (hp : RowCoordinateLoop.width gs indices≤p)
    (hF : RowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom RowCommonCoordinateLoop.machine (budget n F) (cfg gs p F indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p F indices 3 (n+1) 1 tail
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs indices)) ∧ r.steps≤budget n F := by
  obtain ⟨time,hbound,ht⟩ := remaining gs p F indices 0 (n+1) (by omega) tail out hp hF
  have hb : time≤budget n F := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [RowCommonCoordinateLoop.machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel RowCommonCoordinateLoop.machine time (budget n F-time) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  rw [RowCommonCoordinateLoop.word_equation] at rf
  exact ⟨r,more,rf,rs.le.trans hb⟩

theorem tuple_capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (hrows : ∀ row∈rows,row.length=gs.length)
    (hd : ∀ d∈ds,d<rows.length) (hQ : ds.length≤Q)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    RowCommonBounds.capacity gs (RowTupleCommonEquation.indices gs.length rows ds).length p≤F := by
  have hc := RowTupleEquationBounds.count_le gs.length rows ds hrows hd
  rw [(RowTupleCommonEquation.index_fields gs.length rows ds hrows hd).2]
  apply (capacity_mono gs p _ _ (hc.trans (Nat.mul_le_mul_left gs.length hQ))).trans hF

end NearCubicWires.RepairOrdinary.RowCommonFixedCapacity
