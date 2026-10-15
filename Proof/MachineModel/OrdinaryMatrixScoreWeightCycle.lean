import Proof.MachineModel.OrdinaryMatrixScoreWeightClear

/-! Reusable whole weight cycle: first physically erase work storage, then
load, widen and add the selected magnitude. Cold blank work is included. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightCycle
open LocalBitMultitape MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := TapeEmbedding.machine 2 MatrixScoreWeight.machine
noncomputable def machine := Composition.machine MatrixScoreWeightClear.machine body
def scratchIndex : Fin 10 → Fin 15 := ![2,3,4,5,7,8,9,12,13,14]
def harvest (data : Fin 15 → List Bool) : Fin 10 → List Bool := fun i => data (scratchIndex i)
def extra (c : ℕ) : Fin 2 → List Bool := ![List.replicate c true,zeros (c+1)]
noncomputable def input (source assignment : List Bool) (pos apos c w p n : ℕ) (scratch : Fin 10 → List Bool) :
    Configuration 17 (4+Fintype.card (RecoveryCalls.Control MatrixScoreWeight.sizes)) :=
  ⟨machine.start,MatrixScoreWeightClear.heads pos apos,MatrixScoreWeightClear.tapes source assignment c w p n scratch⟩

theorem endpoint (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    Fin.addCases (m := 15) (n := 2) (motive := fun _ => List Bool) (after source assignment bits c w p n sign bit) (extra c)=
      MatrixScoreWeightClear.tapes source assignment c w
        (nextPositive p (RadixSemantics.value bits) sign bit)
        (nextNegative n (RadixSemantics.value bits) sign bit)
        (harvest (after source assignment bits c w p n sign bit)) := by
  funext i
  fin_cases i
  · exact after_source _ _ _ _ _ _ _ _ _
  · exact after_assignment _ _ _ _ _ _ _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · exact after_width _ _ _ _ _ _ _ _ _
  · rfl
  · rfl
  · rfl
  · exact after_positive _ _ _ _ _ _ _ _ _
  · exact after_negative _ _ _ _ _ _ _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem cycle_run (pre suffix apre asuffix bits : List Bool) (c w p n : ℕ) (sign bit : Bool)
    (scratch : Fin 10 → List Bool) (hb : ∀ i,(scratch i).length≤c)
    (hw : bits.length≤w) (hc : 4*w+3≤c)
    (hfit : bit=true → RadixSemantics.value bits+(if sign then n else p)<2^w) :
    ∃ finalScratch : Fin 10 → List Bool,(∀ i,(finalScratch i).length≤c) ∧
      ∃ actual,runFrom machine (2*c+4*bits.length+16*w+31)
        (input (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
          pre.length apre.length c w p n scratch)=some actual ∧
        actual.final.heads=MatrixScoreWeightClear.heads (pre.length+2*bits.length+3) (apre.length+2) ∧
        actual.final.tapes=MatrixScoreWeightClear.tapes
          (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix) c w
          (nextPositive p (RadixSemantics.value bits) sign bit)
          (nextNegative n (RadixSemantics.value bits) sign bit) finalScratch ∧
        actual.steps≤2*c+4*bits.length+16*w+31 := by
  let source := pre++frame (sign::bits)++suffix
  let assignment := apre++[true,bit]++asuffix
  obtain ⟨cleared,hcRun,hch,hct,hcs⟩ := MatrixScoreWeightClear.clear_run source assignment
    pre.length apre.length c w p n scratch hb
  obtain ⟨base,hbRun,hbh,hbt,hbs⟩ := body_run pre suffix apre asuffix bits c w p n sign bit hw hc hfit
  have he := TapeEmbedding.run_embed MatrixScoreWeight.machine (fun _ : Fin 2 => 0) (extra c) _ _ base hbRun
  let last := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra c) base
  have hi : TapeEmbedding.config (fun _ : Fin 2 => 0) (extra c)
      (entry source assignment pre.length apre.length c w p n)=
      Composition.restart cleared.final body.start := by
    apply configuration_ext
    · rfl
    · funext i
      change _=cleared.final.heads i
      rw [hch]
      fin_cases i <;> rfl
    · funext i
      change _=cleared.final.tapes i
      rw [hct]
      fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,entry,controlConfig,tapes,
        extra,MatrixScoreWeightClear.tapes,zeros,ZeroPadding.pad]
  rw [hi] at he
  have joined := Composition.run_join MatrixScoreWeightClear.machine body (2*c+4)
    (4*bits.length+16*w+26) _ cleared last hcRun he
  have hin : Composition.leftConfig _ (RecoveryCalls.restarted MatrixScoreWeightClear.machine
      (MatrixScoreWeightClear.heads pre.length apre.length)
      (MatrixScoreWeightClear.tapes source assignment c w p n scratch))=
      input source assignment pre.length apre.length c w p n scratch := rfl
  rw [hin] at joined
  have htime : (2*c+4)+1+(4*bits.length+16*w+26)=2*c+4*bits.length+16*w+31 := by omega
  rw [htime] at joined
  refine ⟨harvest (after source assignment bits c w p n sign bit),?_,
    Composition.joinedReceipt cleared last,joined,?_,?_,?_⟩
  · intro i
    exact after_support source assignment bits c w p n sign bit hw (by omega) (scratchIndex i)
      (by fin_cases i <;> decide)
  · change (TapeEmbedding.config (fun _ : Fin 2 => 0) (extra c) base.final).heads=_
    change Fin.addCases (m := 15) (n := 2) (motive := fun _ => ℕ) base.final.heads (fun _ : Fin 2 => 0)=_
    rw [hbh]
    funext i; fin_cases i <;> rfl
  · change (TapeEmbedding.config (fun _ : Fin 2 => 0) (extra c) base.final).tapes=_
    change Fin.addCases (m := 15) (n := 2) (motive := fun _ => List Bool) base.final.tapes (extra c)=_
    rw [hbt]
    exact endpoint source assignment bits c w p n sign bit
  · change cleared.steps+1+base.steps≤_
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreWeightCycle
