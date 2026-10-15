import Proof.MachineModel.OrdinaryMatrixScorePower
import Proof.MachineModel.OrdinaryMatrixScoreTemplateEntry

/-! One cold execution from the raw cut headers supplies d, p and the actual
assignment count U=2^d. Every copy, head retreat and unary expansion is paid. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreDimensions
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev H := (5+MatrixScoreHeaders.D)+MatrixScoreHeaders.D
abbrev P := 20+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))
def copySlots : Fin 5 → Fin 40 := ![12,23,24,25,26]
def powerSlots : Fin 14 → Fin 40 := ![23,27,28,29,30,31,32,33,34,35,36,37,38,39]
noncomputable def headers : Machine 40 H := TapeEmbedding.machine 17 MatrixScoreHeaders.machine
noncomputable def copy : Machine 40 10 := RecoveryFocus.machine copySlots MatrixScoreTemplateEntry.machine
noncomputable def prepare : Machine 40 (H+10) := Composition.machine headers copy
noncomputable def power : Machine 40 P := RecoveryFocus.machine powerSlots MatrixScorePower.machine
noncomputable def machine : Machine 40 ((H+10)+P) := Composition.machine prepare power
def input (bs : List Bool) : Fin 40 → List Bool := fun i => if i.val=0 then frame bs else []
def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreHeaders.budget d p suffix+4*d+16+MatrixScorePower.budget d

theorem dimensions_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 40 ((H+10)+P),
      run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧
      actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 3=List.replicate (natBitLength d) true ∧ actual.final.heads 3=0 ∧
      actual.final.tapes 6=frame (binary (natBitLength d) d) ∧ actual.final.heads 6=0 ∧
      actual.final.tapes 13=List.replicate (natBitLength p) true ∧ actual.final.heads 13=0 ∧
      actual.final.tapes 16=frame (binary (natBitLength p) p) ∧ actual.final.heads 16=0 ∧
      actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=1 ∧
      actual.final.tapes 23=List.replicate d true ∧ actual.final.heads 23=0 ∧
      actual.final.tapes 28=List.replicate (d+3) true ∧ actual.final.heads 28=0 ∧
      actual.final.tapes 32=frame (binary (d+3) (2^d)) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape (2^d) ∧ actual.final.heads 39=1 ∧
      actual.steps≤budget d p suffix := by
  let source := natWord d++natWord p++suffix
  obtain ⟨base,hb,ht0,hh0,ht1,hh1,ht3,hh3,ht6,hh6,ht12,hh12,ht13,hh13,ht16,hh16,ht22,hh22,hbs⟩ :=
    MatrixScoreHeaders.headers_run d p suffix
  have he := TapeEmbedding.run_embed MatrixScoreHeaders.machine (fun _ : Fin 17 => 0)
    (fun _ : Fin 17 => []) _ _ base hb
  let first := TapeEmbedding.receipt (fun _ : Fin 17 => 0) (fun _ : Fin 17 => []) base
  obtain ⟨copied,hc,_,hc1,_,_,hch,hcs⟩ := MatrixScoreTemplateEntry.entry_run d
  have ci : RecoveryFocus.config copySlots first.final.heads first.final.tapes (MatrixScoreTemplateEntry.input d)=
      Composition.restart first.final copy.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact hh12
      all_goals rfl
    · intro i
      fin_cases i
      · exact ht12
      all_goals rfl
  obtain ⟨middle,hm,hmf,hms⟩ := RecoveryFocus.run_config copySlots (by decide) MatrixScoreTemplateEntry.machine
    first.final.heads first.final.tapes _ (MatrixScoreTemplateEntry.input d) copied hc
  rw [ci] at hm
  have hj := Composition.run_join headers copy (MatrixScoreHeaders.budget d p suffix) (4*d+14)
    _ first middle he hm
  let prepared := Composition.joinedReceipt first middle
  have pickC (i : Fin 5) : RecoveryFocus.pick copySlots (copySlots i)=some i :=
    RecoveryFocus.pick_slot copySlots (by decide) i
  obtain ⟨last,hl,hl0,hl2,hl6,hl13,hlh,hlheads,hls⟩ := MatrixScorePower.power_run d
  let entry := initialConfiguration MatrixScorePower.machine (MatrixScorePower.input d)
  have powerPick (i : Fin 14) : RecoveryFocus.pick copySlots (powerSlots i)=
      (if i=0 then some 1 else none) := by
    fin_cases i
    · exact pickC 1
    all_goals decide
  have firstH (i : Fin 14) : first.final.heads (powerSlots i)=0 := by
    fin_cases i <;> simp [first,powerSlots,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  have firstT (i : Fin 14) : first.final.tapes (powerSlots i)=[] := by
    fin_cases i <;> simp [first,powerSlots,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  have pi : RecoveryFocus.config powerSlots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final power.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      change middle.final.heads (powerSlots i)=_
      rw [hmf]
      simp only [RecoveryFocus.config,powerPick]
      by_cases hi : i=0
      · simp [hi,hch,entry,initialConfiguration]
      · simp [hi,firstH,entry,initialConfiguration]
    · intro i
      change middle.final.tapes (powerSlots i)=_
      rw [hmf]
      simp only [RecoveryFocus.config,powerPick]
      by_cases hi : i=0
      · simpa [hi,entry,initialConfiguration,MatrixScorePower.input] using hc1
      · have hv : i.val≠0 := fun h => hi (Fin.ext h)
        simp [hi,firstT,entry,initialConfiguration,MatrixScorePower.input,hv]
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config powerSlots (by decide) MatrixScorePower.machine
    prepared.final.heads prepared.final.tapes _ entry last hl
  rw [pi] at hf
  have hall := Composition.run_join prepare power (MatrixScoreHeaders.budget d p suffix+1+(4*d+14))
    (MatrixScorePower.budget d) _ prepared focused hj hf
  have hin : Composition.leftConfig P (Composition.leftConfig 10
      (TapeEmbedding.config (fun _ : Fin 17 => 0) (fun _ : Fin 17 => [])
        (initialConfiguration MatrixScoreHeaders.machine (MatrixScoreHeaders.input source))))=
      initialConfiguration machine (input source) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,initialConfiguration]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,MatrixScoreHeaders.input]
  rw [hin] at hall
  have htime : MatrixScoreHeaders.budget d p suffix+1+(4*d+14)+1+MatrixScorePower.budget d=budget d p suffix := by
    unfold budget; omega
  rw [htime] at hall
  have pickP (i : Fin 14) : RecoveryFocus.pick powerSlots (powerSlots i)=some i :=
    RecoveryFocus.pick_slot powerSlots (by decide) i
  have otherT (i : Fin 23) (hc' : RecoveryFocus.pick copySlots (i.castAdd 17)=none)
      (hp' : RecoveryFocus.pick powerSlots (i.castAdd 17)=none) :
      focused.final.tapes (i.castAdd 17)=base.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hp']
    change middle.final.tapes (i.castAdd 17)=_
    rw [hmf]
    simp [RecoveryFocus.config,hc',first,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 23) (hc' : RecoveryFocus.pick copySlots (i.castAdd 17)=none)
      (hp' : RecoveryFocus.pick powerSlots (i.castAdd 17)=none) :
      focused.final.heads (i.castAdd 17)=base.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,hp']
    change middle.final.heads (i.castAdd 17)=_
    rw [hmf]
    simp [RecoveryFocus.config,hc',first,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hall,
    (otherT 0 (by decide) (by decide)).trans ht0,(otherH 0 (by decide) (by decide)).trans hh0,
    (otherT 1 (by decide) (by decide)).trans ht1,(otherH 1 (by decide) (by decide)).trans hh1,
    (otherT 3 (by decide) (by decide)).trans ht3,(otherH 3 (by decide) (by decide)).trans hh3,
    (otherT 6 (by decide) (by decide)).trans ht6,(otherH 6 (by decide) (by decide)).trans hh6,
    (otherT 13 (by decide) (by decide)).trans ht13,(otherH 13 (by decide) (by decide)).trans hh13,
    (otherT 16 (by decide) (by decide)).trans ht16,(otherH 16 (by decide) (by decide)).trans hh16,
    (otherT 22 (by decide) (by decide)).trans ht22,(otherH 22 (by decide) (by decide)).trans hh22,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (powerSlots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hl0
  · change focused.final.heads (powerSlots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hlheads 0 (by decide)
  · change focused.final.tapes (powerSlots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hl2
  · change focused.final.heads (powerSlots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hlheads 2 (by decide)
  · change focused.final.tapes (powerSlots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hl6
  · change focused.final.heads (powerSlots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hlheads 6 (by decide)
  · change focused.final.tapes (powerSlots 13)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hl13
  · change focused.final.heads (powerSlots 13)=_
    rw [hff]; simpa only [RecoveryFocus.config,pickP] using hlh
  · change base.steps+1+middle.steps+1+focused.steps≤_
    rw [hms,hfs,hcs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreDimensions
