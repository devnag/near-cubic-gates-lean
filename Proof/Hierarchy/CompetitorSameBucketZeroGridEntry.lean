import Proof.Hierarchy.CompetitorSameBucketZeroGridCold
import Proof.Amplification.RecoveryFocusDock

/-! The literal cold Request producer runs every gate, then appends one
zero key for every cell using the reference tapes retained by that same run.
No rank/coefficient replay or supplied zero bank is used. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldSlots : Fin 6 → Fin 442 := ![41,34,301,395,358,2]
def slots (j : Fin 19) : Fin 455 :=
  if h : j.val<6 then (oldSlots ⟨j.val,h⟩).castAdd 13 else ⟨442+j.val-6,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first:=TapeEmbedding.machine 13 CompetitorSameBucketColdGate.machine
noncomputable def grid:=RecoveryFocus.machine slots CompetitorSameBucketZeroGridCold.machine
noncomputable def machine:=Composition.machine first grid
def input (r : Request) (w : ℕ) : Fin 455 → List Bool :=
  Fin.addCases (m := 442) (n := 13) (motive := fun _=>List Bool) (CompetitorSameBucketColdGate.input r w) (fun _=>[])
noncomputable def output (r : Request):=CompetitorSameBucketGateNative.output r++CompetitorSameBucketZeroGrid.bits r.p r.M r.U 0 r.U
noncomputable def budget (r : Request):=CompetitorSameBucketColdGate.budget r+1+
  CompetitorSameBucketZeroGridCold.budget r.p r.M r.U (CompetitorSameBucketBucketBody.scalarCapacity r)
def retainedSlots : Fin 4 → Fin 455 := ![0,1,42,227]
def retainedValues (r : Request) (w : ℕ) : Fin 4 → List Bool :=
  ![MatrixScoreBatch.physicalInput r,List.replicate w true,List.replicate r.p true,List.replicate r.M true]
theorem retained_avoids (j : Fin 4) : ∀ k,slots k≠retainedSlots j := by
  intro k; fin_cases j <;> fin_cases k <;> decide

theorem count_fit (r : Request) : r.U+r.U<2^r.M := by
  rw [MatrixScoreBatch.common_width,Request.U]
  calc
    2^r.d+2^r.d=2^(r.d+1) := by rw [Nat.pow_succ]; omega
    _ < 2^(r.d+3) := Nat.pow_lt_pow_right (by decide) (by omega)

private theorem initial_embed {t e s : ℕ} (p : Machine t s) (xs : Fin t → List Bool) :
    TapeEmbedding.config (fun _ : Fin e=>0) (fun _ : Fin e=>[]) (initialConfiguration p xs)=
      initialConfiguration (TapeEmbedding.machine e p)
        (Fin.addCases (m := t) (n := e) (motive := fun _=>List Bool) xs (fun _=>[])) := by
  apply configuration_ext
  · rfl
  · funext i
    change (Fin.addCases (m := t) (n := e) (motive := fun _=>ℕ) (fun _=>0) (fun _=>0)) i=0
    refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
  · rfl

theorem first_run (r : Request) (w : ℕ) : ∃ actual,
    run first (CompetitorSameBucketColdGate.budget r) (input r w)=some actual ∧
    (∀ j,actual.final.heads (slots j)=CompetitorSameBucketZeroPrepareSpace.heads (CompetitorSameBucketGateNative.output r) j) ∧
    (∀ j,actual.final.tapes (slots j)=CompetitorSameBucketZeroPrepareSpace.input r.p r.M r.U
      (CompetitorSameBucketBucketBody.scalarCapacity r) (CompetitorSameBucketGateNative.output r) j) ∧
    (∀ j,actual.final.tapes (retainedSlots j)=retainedValues r w j) ∧
    (∀ j,actual.final.heads (retainedSlots j)=0) ∧ actual.steps≤CompetitorSameBucketColdGate.budget r := by
  obtain ⟨base,hb,t0,h0,t1,h1,t2,h2,rt,rh,bs⟩:=CompetitorSameBucketColdGate.reference_run r w
  let embedded:=TapeEmbedding.receipt (fun _ : Fin 13=>0) (fun _=>[]) base
  have he:=TapeEmbedding.run_embed CompetitorSameBucketColdGate.machine (fun _ : Fin 13=>0) (fun _=>[])
    _ _ base hb
  rw [initial_embed] at he
  have hfirst : run first (CompetitorSameBucketColdGate.budget r) (input r w)=some embedded := he
  have keptT (j : Fin 4) : embedded.final.tapes (retainedSlots j)=retainedValues r w j := by
    fin_cases j
    · exact t0
    · exact t1
    · exact rt 1
    · exact rt 2
  have keptH (j : Fin 4) : embedded.final.heads (retainedSlots j)=0 := by
    fin_cases j
    · exact h0
    · exact h1
    · exact rh 1
    · exact rh 2
  have selectedH : ∀ j,embedded.final.heads (slots j)=
      CompetitorSameBucketZeroPrepareSpace.heads (CompetitorSameBucketGateNative.output r) j := by
    intro j
    fin_cases j
    · exact rh 0
    · exact rh 4
    · exact rh 3
    · exact rh 5
    · exact rh 6
    · exact h2
    all_goals rfl
  have selectedT : ∀ j,embedded.final.tapes (slots j)=
      CompetitorSameBucketZeroPrepareSpace.input r.p r.M r.U (CompetitorSameBucketBucketBody.scalarCapacity r)
        (CompetitorSameBucketGateNative.output r) j := by
    intro j
    fin_cases j
    · exact rt 0
    · exact rt 4
    · exact rt 3
    · exact rt 5
    · exact rt 6
    · exact t2
    all_goals rfl
  exact ⟨embedded,hfirst,selectedH,selectedT,keptT,keptH,bs⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid
