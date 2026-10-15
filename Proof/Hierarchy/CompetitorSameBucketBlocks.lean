import Proof.Hierarchy.CompetitorSameBucketCapacity

/-! Execute all record/block drivers from the H/B fields of the actual
cold producer, retaining its capacity and every previous tape/cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdBlocks
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 24) : Fin 382 := if i=0 then 304 else if i=1 then 218 else ⟨358+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by decide

theorem pick_old (i : Fin 360) (h304 : i≠304) (h218 : i≠218) : RecoveryFocus.pick slots (i.castAdd 22)=none := by
  classical
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  have hv:=congrArg Fin.val hj
  by_cases h0 : j=0
  · subst j
    exact h304 (Fin.ext (by simpa [slots] using hv.symm))
  by_cases h1 : j=1
  · subst j
    exact h218 (Fin.ext (by simpa [slots] using hv.symm))
  have hj0 : j.val≠0 := by simpa using h0
  have hj1 : j.val≠1 := fun he => h1 (Fin.ext he)
  simp only [slots,h0,h1,ite_false] at hv
  change 358+j.val=i.val at hv
  omega

theorem cold_fields (r : Request) (w : ℕ) (cold : ExecutionReceipt 342 _)
    (hc : run CompetitorSameBucketCold.machine (CompetitorSameBucketCold.budget r) (CompetitorSameBucketCold.input r w)=some cold) :
    cold.final.tapes 304=List.replicate (H r) true ∧ cold.final.heads 304=0 ∧
    cold.final.tapes 218=UnaryTemplate.tape (r.bucketSize+1) ∧ cold.final.heads 218=0 := by
  obtain ⟨ranked,same,hr,hs,ct,ch,_,_,_,_,_,_,_⟩:=CompetitorSameBucketCold.cold_run r w
  have heq : same=cold := Option.some.inj (hs.symm.trans hc)
  subst same
  obtain ⟨b216,h216,_,_,_,_,_,_⟩:=CompetitorSameBucketColdFields.dimensions r ranked hr
  obtain ⟨_,same,_,hs,_,_,_,_,_,_,_,_,rH,hH,_,_,_,_,_⟩:=MatrixBatchRankReverse.raw_run r
  have heq : same=ranked := Option.some.inj (hs.symm.trans hr)
  subst same
  exact ⟨(ct 302).trans rH,(ch 302).trans hH,(ct 216).trans b216,(ch 216).trans h216⟩

def input (r : Request) (w : ℕ) : Fin 382 → List Bool :=
  Fin.addCases (m := 360) (n := 22) (motive := fun _ => List Bool) (CompetitorSameBucketColdCapacity.input r w) (fun _ => [])
noncomputable def first := TapeEmbedding.machine 22 CompetitorSameBucketColdCapacity.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorSameBucketBlockDrivers.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) := CompetitorSameBucketColdCapacity.budget r+1+CompetitorSameBucketBlockDrivers.budget (H r) (r.bucketSize+1)

theorem selected_heads {s : ℕ} (c : Configuration 360 s) (hH : c.heads 304=0) (hB : c.heads 218=0) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) c).heads (slots j)=0 := by
  intro j
  fin_cases j
  · exact hH
  · exact hB
  all_goals rfl

theorem selected_tapes {s : ℕ} (r : Request) (c : Configuration 360 s)
    (tH : c.tapes 304=List.replicate (H r) true) (tB : c.tapes 218=UnaryTemplate.tape (r.bucketSize+1)) :
    ∀ j,(TapeEmbedding.config (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) c).tapes (slots j)=
      CompetitorSameBucketBlockDrivers.input (H r) (r.bucketSize+1) j := by
  intro j
  fin_cases j
  · exact tH
  · exact tB
  all_goals rfl

theorem blocks_run (r : Request) (w : ℕ) : ∃ base : ExecutionReceipt 360 _,∃ actual,
    run CompetitorSameBucketColdCapacity.machine (CompetitorSameBucketColdCapacity.budget r) (CompetitorSameBucketColdCapacity.input r w)=some base ∧
    run machine (budget r) (input r w)=some actual ∧
    (∀ i : Fin 360,actual.final.tapes (i.castAdd 22)=base.final.tapes i) ∧
    (∀ i : Fin 360,actual.final.heads (i.castAdd 22)=base.final.heads i) ∧
    actual.final.tapes 370=UnaryTemplate.tape (4*H r+1) ∧ actual.final.heads 370=0 ∧
    actual.final.tapes 376=UnaryTemplate.tape ((4*H r+1)*(r.bucketSize+1)) ∧ actual.final.heads 376=0 ∧
    actual.final.tapes 380=UnaryTemplate.tape (r.bucketSize+1) ∧ actual.final.heads 380=0 ∧
    actual.steps≤budget r := by
  obtain ⟨cold,base,hc,hb,bt,bh,_,_,bs⟩:=CompetitorSameBucketColdCapacity.capacity_run r w
  obtain ⟨cH,hH,cB,hB⟩:=cold_fields r w cold hc
  have bH : base.final.tapes 304=List.replicate (H r) true := (bt 304).trans cH
  have bHhead : base.final.heads 304=0 := (bh 304).trans hH
  have bB : base.final.tapes 218=UnaryTemplate.tape (r.bucketSize+1) := (bt 218).trans cB
  have bBhead : base.final.heads 218=0 := (bh 218).trans hB
  have embedded:=TapeEmbedding.run_embed CompetitorSameBucketColdCapacity.machine (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) _ _ base hb
  let prepared:=TapeEmbedding.receipt (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) base
  obtain ⟨driverOut,ready,d0,d1,_,_,d12,_,_,d18,_,_,d22⟩:=CompetitorSameBucketBlockDrivers.drivers_ready (H r) (r.bucketSize+1)
  obtain ⟨driver,hd,dt,dh,ds⟩:=ready
  let entry:=initialConfiguration CompetitorSameBucketBlockDrivers.machine (CompetitorSameBucketBlockDrivers.input (H r) (r.bucketSize+1))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact selected_heads base.final bHhead bBhead
    · exact selected_tapes r base.final bH bB
  obtain ⟨focused,hf,ff,fs⟩:=RecoveryFocus.run_config slots slots_injective CompetitorSameBucketBlockDrivers.machine
    prepared.final.heads prepared.final.tapes _ entry driver hd
  rw [hi] at hf
  have joined:=Composition.run_join first last _ _ _ prepared focused embedded hf
  have hin:=MatrixWilliamsProduct.initial_join (e := 22) CompetitorSameBucketColdCapacity.machine last (CompetitorSameBucketColdCapacity.input r w)
  rw [hin] at joined
  have localT (j : Fin 24) : focused.final.tapes (slots j)=driverOut j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dt]
  have localH (j : Fin 24) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,dh]
  refine ⟨base,Composition.joinedReceipt prepared focused,hb,joined,?_,?_,
    (localT 12).trans d12,localH 12,(localT 18).trans d18,localH 18,(localT 22).trans d22,localH 22,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 22)=_
    by_cases h304 : i=304
    · subst i; exact ((localT 0).trans d0).trans bH.symm
    by_cases h218 : i=218
    · subst i; exact ((localT 1).trans d1).trans bB.symm
    rw [ff]
    simp only [RecoveryFocus.config,pick_old i h304 h218,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · intro i
    change focused.final.heads (i.castAdd 22)=_
    by_cases h304 : i=304
    · subst i; exact (localH 0).trans bHhead.symm
    by_cases h218 : i=218
    · subst i; exact (localH 1).trans bBhead.symm
    rw [ff]
    simp only [RecoveryFocus.config,pick_old i h304 h218,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+driver.steps≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdBlocks
