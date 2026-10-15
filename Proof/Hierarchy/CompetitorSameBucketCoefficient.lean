import Proof.Hierarchy.CompetitorSameBucketScalars
import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! The actual cold raw-p field produces the sign/magnitude zero template.
All previous streams, dimensions and cursors are preserved. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCoefficient
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 17) : Fin 398 := if i=0 then 42 else ⟨381+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by decide

theorem pick_old (i : Fin 382) (hi : i≠42) : RecoveryFocus.pick slots (i.castAdd 16)=none := by
  classical
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  have hv:=congrArg Fin.val hj
  by_cases h0 : j=0
  · subst j
    have he : i=42 := Fin.ext (by simpa [slots] using hv.symm)
    exact hi he
  · have hj0 : j.val≠0 := by simpa using h0
    simp only [slots,h0,ite_false] at hv
    change 381+j.val=i.val at hv
    omega

def input (r : Request) (w : ℕ) : Fin 398 → List Bool :=
  Fin.addCases (m := 382) (n := 16) (motive := fun _ => List Bool) (CompetitorSameBucketColdBlocks.input r w) (fun _ => [])
noncomputable def first := TapeEmbedding.machine 16 CompetitorSameBucketColdBlocks.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorSameBucketCoefficientTemplate.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) := CompetitorSameBucketColdBlocks.budget r+1+CompetitorSameBucketCoefficientTemplate.budget r.p

theorem selected_heads {s : ℕ} (cold : Configuration 382 s) (hh : cold.heads 42=0) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) cold).heads (slots j)=0 := by
  intro j
  fin_cases j
  · exact hh
  all_goals rfl

theorem selected_tapes {s : ℕ} (r : Request) (cold : Configuration 382 s) (ht : cold.tapes 42=List.replicate r.p true) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) cold).tapes (slots j)=CompetitorSameBucketCoefficientTemplate.input r.p j := by
  intro j
  fin_cases j
  · exact ht
  all_goals rfl

theorem coefficient_run (r : Request) (w : ℕ) : ∃ cold : ExecutionReceipt 382 _,∃ actual,
    run CompetitorSameBucketColdBlocks.machine (CompetitorSameBucketColdBlocks.budget r) (CompetitorSameBucketColdBlocks.input r w)=some cold ∧
    run machine (budget r) (input r w)=some actual ∧
    (∀ i : Fin 382,actual.final.tapes (i.castAdd 16)=cold.final.tapes i) ∧
    (∀ i : Fin 382,actual.final.heads (i.castAdd 16)=cold.final.heads i) ∧
    actual.final.tapes 395=frame (List.replicate (r.p+1) false) ∧
    actual.final.heads 395=0 ∧ actual.steps≤budget r := by
  obtain ⟨capacity,cold,hcapacity,hc,ct,ch,_,_,_,_,_,_,cs⟩:=CompetitorSameBucketColdBlocks.blocks_run r w
  obtain ⟨original,same,ho,hs,ot,oh,_,_,_⟩:=CompetitorSameBucketColdCapacity.capacity_run r w
  have heq : same=capacity := Option.some.inj (hs.symm.trans hcapacity)
  subst same
  obtain ⟨p,hp,_,_,_,_,_,_,_,_⟩:=CompetitorSameBucketColdScalars.cold_scalars r w original ho
  have cH : cold.final.tapes 42=List.replicate r.p true := (ct 42).trans ((ot 42).trans p)
  have cHhead : cold.final.heads 42=0 := (ch 42).trans ((oh 42).trans hp)
  have embedded:=TapeEmbedding.run_embed CompetitorSameBucketColdBlocks.machine (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) _ _ cold hc
  let prepared:=TapeEmbedding.receipt (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) cold
  obtain ⟨dimOut,dimReady,d0,d14⟩:=CompetitorSameBucketCoefficientTemplate.template_run r.p
  obtain ⟨dim,hd,dt,dh,ds⟩:=dimReady
  let entry:=initialConfiguration CompetitorSameBucketCoefficientTemplate.machine (CompetitorSameBucketCoefficientTemplate.input r.p)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact selected_heads cold.final cHhead
    · exact selected_tapes r cold.final cH
  obtain ⟨focused,hf,ff,fs⟩:=RecoveryFocus.run_config slots slots_injective CompetitorSameBucketCoefficientTemplate.machine
    prepared.final.heads prepared.final.tapes _ entry dim hd
  rw [hi] at hf
  have joined:=Composition.run_join first last _ _ _ prepared focused embedded hf
  have hin:=MatrixWilliamsProduct.initial_join (e := 16) CompetitorSameBucketColdBlocks.machine last (CompetitorSameBucketColdBlocks.input r w)
  rw [hin] at joined
  have localT (j : Fin 17) : focused.final.tapes (slots j)=dimOut j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dt]
  have localH (j : Fin 17) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dh]
  refine ⟨cold,Composition.joinedReceipt prepared focused,hc,joined,?_,?_,(localT 14).trans d14,localH 14,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 16)=_
    by_cases hi : i=42
    · subst i; exact ((localT 0).trans d0).trans cH.symm
    · rw [ff]
      simp only [RecoveryFocus.config,pick_old i hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · intro i
    change focused.final.heads (i.castAdd 16)=_
    by_cases hi : i=42
    · subst i; exact (localH 0).trans cHhead.symm
    · rw [ff]
      simp only [RecoveryFocus.config,pick_old i hi,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change cold.steps+1+dim.steps≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCoefficient
