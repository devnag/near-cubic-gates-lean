import Proof.Hierarchy.CompetitorSameBucketFields
import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! Produce the actual scalar capacity from the H field retained by the
cold rank producer. The original Request/W, both streams, all 342 previous
fields and their cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCapacity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 19) : Fin 360 := if i=0 then 304 else ⟨341+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by decide

theorem pick_old (i : Fin 342) (hi : i≠304) : RecoveryFocus.pick slots (i.castAdd 18)=none := by
  classical
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  have hv:=congrArg Fin.val hj
  by_cases h0 : j=0
  · subst j
    have he : i=304 := Fin.ext (by simpa [slots] using hv.symm)
    exact hi he
  · have hj0 : j.val≠0 := by simpa using h0
    simp only [slots,h0,ite_false] at hv
    change 341+j.val=i.val at hv
    omega

def input (r : Request) (w : ℕ) : Fin 360 → List Bool :=
  Fin.addCases (m := 342) (n := 18) (motive := fun _ => List Bool) (CompetitorSameBucketCold.input r w) (fun _ => [])
noncomputable def first := TapeEmbedding.machine 18 CompetitorSameBucketCold.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorDimensions.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) := CompetitorSameBucketCold.budget r+1+CompetitorDimensions.budget (H r)

theorem selected_heads {s : ℕ} (cold : Configuration 342 s) (hh : cold.heads 304=0) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) cold).heads (slots j)=0 := by
  intro j
  fin_cases j
  · exact hh
  all_goals rfl

theorem selected_tapes {s : ℕ} (r : Request) (cold : Configuration 342 s) (ht : cold.tapes 304=List.replicate (H r) true) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) cold).tapes (slots j)=CompetitorDimensions.input (H r) j := by
  intro j
  fin_cases j
  · exact ht
  all_goals rfl

theorem capacity_run (r : Request) (w : ℕ) : ∃ cold : ExecutionReceipt 342 _,∃ actual,
    run CompetitorSameBucketCold.machine (CompetitorSameBucketCold.budget r) (CompetitorSameBucketCold.input r w)=some cold ∧
    run machine (budget r) (input r w)=some actual ∧
    (∀ i : Fin 342,actual.final.tapes (i.castAdd 18)=cold.final.tapes i) ∧
    (∀ i : Fin 342,actual.final.heads (i.castAdd 18)=cold.final.heads i) ∧
    actual.final.tapes 358=List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) true ∧
    actual.final.heads 358=0 ∧ actual.steps≤budget r := by
  obtain ⟨ranked,cold,hr,hc,ct,ch,_,_,_,_,_,_,cs⟩:=CompetitorSameBucketCold.cold_run r w
  obtain ⟨_,same,_,hsame,_,_,_,_,_,_,_,_,sH,hH,_,_,_,_,_⟩:=MatrixBatchRankReverse.raw_run r
  have heq : same=ranked := Option.some.inj (hsame.symm.trans hr)
  subst same
  have cH : cold.final.tapes 304=List.replicate (H r) true := (ct 302).trans sH
  have cHhead : cold.final.heads 304=0 := (ch 302).trans hH
  have embedded:=TapeEmbedding.run_embed CompetitorSameBucketCold.machine (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) _ _ cold hc
  let prepared:=TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) cold
  obtain ⟨dimOut,dimReady,d0,_,d17⟩:=CompetitorDimensions.dimensions_run (H r)
  obtain ⟨dim,hd,dt,dh,ds⟩:=dimReady
  let entry:=initialConfiguration CompetitorDimensions.machine (CompetitorDimensions.input (H r))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact selected_heads cold.final cHhead
    · exact selected_tapes r cold.final cH
  obtain ⟨focused,hf,ff,fs⟩:=RecoveryFocus.run_config slots slots_injective CompetitorDimensions.machine
    prepared.final.heads prepared.final.tapes _ entry dim hd
  rw [hi] at hf
  have joined:=Composition.run_join first last _ _ _ prepared focused embedded hf
  have hin:=MatrixWilliamsProduct.initial_join (e := 18) CompetitorSameBucketCold.machine last (CompetitorSameBucketCold.input r w)
  rw [hin] at joined
  have localT (j : Fin 19) : focused.final.tapes (slots j)=dimOut j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dt]
  have localH (j : Fin 19) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dh]
  refine ⟨cold,Composition.joinedReceipt prepared focused,hc,joined,?_,?_,(localT 17).trans d17,localH 17,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 18)=_
    by_cases hi : i=304
    · subst i; exact ((localT 0).trans d0).trans cH.symm
    · rw [ff]
      simp only [RecoveryFocus.config,pick_old i hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · intro i
    change focused.final.heads (i.castAdd 18)=_
    by_cases hi : i=304
    · subst i; exact (localH 0).trans cHhead.symm
    · rw [ff]
      simp only [RecoveryFocus.config,pick_old i hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change cold.steps+1+dim.steps≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCapacity
