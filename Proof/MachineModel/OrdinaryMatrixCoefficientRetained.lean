import Proof.MachineModel.OrdinaryMatrixCoefficientRetainedHeaders
import Proof.MachineModel.OrdinaryMatrixSignedPlane

/-! Retained finite dimensions from the same cold coefficient extraction.
The existing rewind supplies head zero for d, p and Gates without executing
another parse or adding a prepared dimension assumption. The unary `d` (tape 12)
is the header parse's column counter; the gate pass reads the unary width (tape 8). -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedCold
open LocalBitMultitape MatrixScoreBatch
open MatrixCoefficientCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem forward_fields (r : Request) : ∃ actual,
    run forward (forwardBudget r) (forwardInput r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 33=MatrixCoefficientLoop.output r.p r.cuts ∧
    actual.final.heads 33=(MatrixCoefficientLoop.output r.p r.cuts).length ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧
    actual.steps≤forwardBudget r := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,bw,bwh,bd,_,bg,bgh,bp,bph,bs⟩ := MatrixCoefficientRetainedHeaders.headers_fields r
  have he := TapeEmbedding.run_embed MatrixCoefficientHeaders.full (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base
  obtain ⟨body,hbody,bf,bodyS⟩ := MatrixCoefficientNative.all_run r []
  let entry := MatrixCoefficientNative.cfg r 0 (header r).length []
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      change prepared.final.heads (slots j)=entry.heads j
      simp only [entry,MatrixCoefficientNative.cfg_heads]
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bh1
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bwh
      · rfl
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bgh
    · intro j
      change prepared.final.tapes (slots j)=entry.tapes j
      simp only [entry,MatrixCoefficientNative.cfg_tapes]
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bt1
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bw
      · rfl
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,Fin.addCases] using bg
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixCoefficientLoop.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (initialConfiguration MatrixCoefficientHeaders.full (MatrixCoefficientHeaders.input r)))=
      initialConfiguration forward (forwardInput r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hn : RecoveryFocus.pick slots (0 : Fin 34)=none := by decide
  have hp : RecoveryFocus.pick slots (33 : Fin 34)=some 2 := RecoveryFocus.pick_slot slots slots_injective 2
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [ff]
    simpa [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bt0
  · change focused.final.heads 0=_
    rw [ff]
    simpa [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bh0
  · change focused.final.tapes 33=_
    rw [ff]
    simp only [RecoveryFocus.config,hp]
    rw [bf,MatrixCoefficientNative.cfg_tapes]
    simp
  · change focused.final.heads 33=_
    rw [ff]
    simp only [RecoveryFocus.config,hp]
    rw [bf,MatrixCoefficientNative.cfg_heads]
    simp
  · change focused.final.tapes 12=_
    rw [ff]
    have hp12 : RecoveryFocus.pick slots (12 : Fin 34)=none := by decide
    simpa [RecoveryFocus.config,hp12,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bd
  · change focused.final.tapes 22=_
    rw [ff]
    have hp22 : RecoveryFocus.pick slots (22 : Fin 34)=none := by decide
    simpa [RecoveryFocus.config,hp22,prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bp
  · change focused.final.tapes (slots 3)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    rw [bf,MatrixCoefficientNative.cfg_tapes]
    rfl
  · change base.steps+1+focused.steps≤forwardBudget r
    rw [fs]
    unfold forwardBudget
    omega

theorem cold_fields (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧
    actual.final.tapes 33=MatrixCoefficientLoop.output r.p r.cuts ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,_,outT,_,dt,pt,gt,bs⟩ := forward_fields r
  obtain ⟨actual,ha,atapes,ah,as,_⟩ := Rewind.reset_run forward _ _ base hb
  have hs : 2*base.steps+2≤budget r := by unfold budget; omega
  have he := run_moreFuel machine _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hs] at he
  have hi : Fin.addCases (m := 34) (n := 1) (motive := fun _ => List Bool) (forwardInput r) (fun _ => [])=input r := by
    funext i; fin_cases i <;> rfl
  rw [hi] at he
  exact ⟨actual,he,(atapes 0).trans bt,(atapes 33).trans outT,
    (atapes 12).trans dt,(atapes 22).trans pt,(atapes 32).trans gt,ah,as.trans_le hs⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedCold
