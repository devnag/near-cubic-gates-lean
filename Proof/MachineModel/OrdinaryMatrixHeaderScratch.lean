import Proof.MachineModel.OrdinaryMatrixScoreHeaders
import Proof.MachineModel.OrdinaryZeroPadding

/-! Scratch fields of the existing header parsers. The same executed runs as `template_run`,
`prepare_run`, `header_run` and `headers_run`, with the tapes they leave all-`false` (the dimension
field's zero run, the normalizer's spare cell, the input copy's counter) and the second unary copy exposed.
Nothing is re-executed: these are stronger receipts of the same machines and budgets. The coefficient pass
reuses exactly these cells (by `ZeroPadding`) for its weight-count parse, so no tape count changes. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnaryTemplate
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `template_run`, also exposing the normalizer's spare cell (tape 1): it is `[]` or `[false]`. -/
theorem scratch_run (w n : ℕ) (hn : n<2^w) :
    ∃ r : ExecutionReceipt 7 (8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes)),
      run machine (budget w n) (input w n)=some r ∧
      r.final.tapes 0=List.replicate w true ∧
      ZeroPadding.pad 1 (r.final.tapes 1)=[false] ∧
      r.final.tapes 5=frame (binary w n) ∧
      r.final.tapes 6=UnaryTemplate.tape n ∧ r.final.heads 6=1 ∧
      (∀ i, i≠6 → r.final.heads i=0) ∧ r.steps≤budget w n := by
  obtain ⟨base,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.zero_run w
  let extras : Fin 2 → List Bool := ![frame (binary w n),[]]
  let z := TapeEmbedding.receipt (fun _ : Fin 2 => 0) extras base
  have hz := TapeEmbedding.run_embed ClockNormalize.machine (fun _ : Fin 2 => 0) extras _ _ base hr
  have hzhead : ∀ i, z.final.heads i=0 := by
    intro i; fin_cases i <;> simp [z,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hh]
  have hz0 : z.final.tapes 0=List.replicate w true := h0
  have hz1 : ZeroPadding.pad 1 (z.final.tapes 1)=[false] := h1
  have hz2 : z.final.tapes 2=frame (binary w 0) := h2
  have hz3 : z.final.tapes 3=[true] := h3
  have hz4 : z.final.tapes 4=List.replicate (2*w+1) false := h4
  have hz5 : z.final.tapes 5=frame (binary w n) := rfl
  have hz6 : z.final.tapes 6=[] := rfl
  obtain ⟨b,hb,hbf,hbs⟩ := boot_run z.final.tapes hz3 hz6
  have hbridge : Composition.restart z.final boot.start=initialConfiguration boot z.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext hzhead
    · rfl
  have hb' : runFrom boot 1 (Composition.restart z.final boot.start)=some b := by rw [hbridge]; exact hb
  have hp := Composition.run_join zero boot (4*w+4) 1 _ z b hz hb'
  let p := Composition.joinedReceipt z b
  have hphead : p.final.heads=fun i => if i=6 then 1 else 0 := by change b.final.heads=_; rw [hbf]; rfl
  have hptape : p.final.tapes=fun i => if i=3 ∨ i=6 then [false] else z.final.tapes i := by
    change b.final.tapes=_; rw [hbf]; rfl
  obtain ⟨localRun,hl,hlf,hls⟩ := MatrixUnary.loop_run w n hn
  let entry := MatrixUnary.boundary 0 w n 0 0 false
  have hi : RecoveryFocus.config slots p.final.heads p.final.tapes entry =
      Composition.restart p.final loop.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [hphead]
      fin_cases i <;> simp [slots,entry,MatrixUnary.boundary,controlConfig,MatrixUnary.config]
    · intro i
      rw [hptape]
      fin_cases i <;> simp [slots,entry,MatrixUnary.boundary,controlConfig,MatrixUnary.config,hz2,hz4,hz5]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixUnary.machine
    p.final.heads p.final.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join prepare loop (4*w+4+1+1)
    (n*(8*w+10)+4*w+n+10) _ p focused hp hfocus
  have htime : 4*w+4+1+1+1+(n*(8*w+10)+4*w+n+10)=budget w n := by unfold budget; omega
  rw [htime] at hj
  have hinput : Composition.leftConfig _
      (Composition.leftConfig 2 (TapeEmbedding.config (fun _ : Fin 2 => 0) extras
        (initialConfiguration ClockNormalize.machine (ClockScalarFields.zeroInput w)))) =
      initialConfiguration machine (input w n) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hinput] at hj
  have hpick : ∀ i : Fin 7, RecoveryFocus.pick slots i =
      (![none,none,some 1,some 2,some 3,some 0,some 4] : Fin 7 → Option (Fin 5)) i := by
    intro i; fin_cases i
    · decide
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 1
    · exact RecoveryFocus.pick_slot slots (by decide) 2
    · exact RecoveryFocus.pick_slot slots (by decide) 3
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · exact RecoveryFocus.pick_slot slots (by decide) 4
  refine ⟨Composition.joinedReceipt p focused,hj,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,hptape,hz0]
  · have e1 : focused.final.tapes 1=z.final.tapes 1 := by
      rw [hff,hlf]
      simp [RecoveryFocus.config,hpick,hptape]
    change ZeroPadding.pad 1 (focused.final.tapes 1)=_
    rw [e1]
    exact hz1
  · change focused.final.tapes 5=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · change focused.final.tapes 6=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · change focused.final.heads 6=1
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · intro i hi6
    change focused.final.heads i=0
    rw [hff,hlf]
    fin_cases i <;> simp [RecoveryFocus.config,hpick,hphead,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished] at *
  · change z.steps+1+b.steps+1+focused.steps≤_
    rw [hbs,hfs]
    have hzsteps : z.steps=4*w+4 := hs
    rw [hzsteps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixUnaryTemplate

namespace NearCubicWires.RepairOrdinary.MatrixDimensionPrepare
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `prepare_run`, also exposing the second unary copy (tape 2), the field's zero run (tape 5) and the
normalizer's spare cell (tape 6). -/
theorem scratch_run (pre suffix : List Bool) (w n : ℕ) (hn : n<2^w) :
    let source := pre ++ List.replicate w true ++ false :: (binary w n ++ suffix)
    ∃ r : ExecutionReceipt 11 (8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))),
      runFrom machine (budget w n) (Composition.leftConfig _ (input source pre.length))=some r ∧
      r.final.tapes 0=source ∧ r.final.heads 0=pre.length+2*w+1 ∧
      r.final.tapes 1=List.replicate w true ∧ r.final.heads 1=0 ∧
      r.final.tapes 2=List.replicate w true ∧ r.final.heads 2=0 ∧
      r.final.tapes 3=UnaryTemplate.tape w ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=frame (binary w n) ∧ r.final.heads 4=0 ∧
      r.final.tapes 5=List.replicate (2*w+1) false ∧ r.final.heads 5=0 ∧
      ZeroPadding.pad 1 (r.final.tapes 6)=[false] ∧ r.final.heads 6=0 ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=1 ∧ r.steps≤budget w n := by
  dsimp only
  let source := pre ++ List.replicate w true ++ false :: (binary w n ++ suffix)
  obtain ⟨base,hr,hf,hs⟩ := MatrixDimensionField.field_run pre (binary w n) suffix
  simp only [binary_length] at hr hf hs
  have he := TapeEmbedding.run_embed MatrixDimensionField.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ base hr
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  obtain ⟨localRun,hl,hw,h1,hu,ht,hth,hh,hsteps⟩ := MatrixUnaryTemplate.scratch_run w n hn
  let entry := initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input w n)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient unary.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,initialConfiguration,MatrixDimensionField.output,TapeEmbedding.config,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,initialConfiguration,MatrixUnaryTemplate.input,
        MatrixDimensionField.output,TapeEmbedding.config,Fin.addCases]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide)
    MatrixUnaryTemplate.machine ambient.heads ambient.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join field unary (6*w+7) (MatrixUnaryTemplate.budget w n) _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused he hfocus
  have htime : 6*w+7+1+MatrixUnaryTemplate.budget w n=budget w n := by
    unfold budget MatrixUnaryTemplate.budget
    omega
  rw [htime] at hj
  have hnone0 : RecoveryFocus.pick slots (0 : Fin 11)=none := by decide
  have hnone2 : RecoveryFocus.pick slots (2 : Fin 11)=none := by decide
  have hnone3 : RecoveryFocus.pick slots (3 : Fin 11)=none := by decide
  have hnone5 : RecoveryFocus.pick slots (5 : Fin 11)=none := by decide
  have hpick (i : Fin 7) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused,hj,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone0]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.heads 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone0]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 0)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hw
  · change focused.final.heads (slots 0)=0
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hh 0 (by decide)
  · change focused.final.tapes 2=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone2]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,MatrixDimensionField.output,Fin.addCases]
  · change focused.final.heads 2=0
    rw [hff]
    simp only [RecoveryFocus.config,hnone2]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes 3=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone3]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,MatrixDimensionField.output,Fin.addCases]
  · change focused.final.heads 3=1
    rw [hff]
    simp only [RecoveryFocus.config,hnone3]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 5)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hu
  · change focused.final.heads (slots 5)=0
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hh 5 (by decide)
  · change focused.final.tapes 5=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone5]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,MatrixDimensionField.output,Fin.addCases]
  · change focused.final.heads 5=0
    rw [hff]
    simp only [RecoveryFocus.config,hnone5]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change ZeroPadding.pad 1 (focused.final.tapes (slots 1))=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using h1
  · change focused.final.heads (slots 1)=0
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hh 1 (by decide)
  · change focused.final.tapes (slots 6)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using ht
  · change focused.final.heads (slots 6)=1
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hth
  · change base.steps+1+focused.steps≤_
    rw [hs,hfs]
    rw [← htime]
    omega

end NearCubicWires.RepairOrdinary.MatrixDimensionPrepare

namespace NearCubicWires.RepairOrdinary.WilliamsInputHeader
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `header_run`, also exposing the input copy's counter (tape 2, all `false`), the second unary copy
(tape 4), the field's zero run (tape 7) and the normalizer's spare cell (tape 8). -/
theorem scratch_run (n : ℕ) (suffix : List Bool) :
    ∃ r : ExecutionReceipt 13 (5+dimensionStates),
      run machine (budget n suffix) (input (natWord n++suffix))=some r ∧
      r.final.tapes 0=frame (natWord n++suffix) ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=natWord n++suffix ∧ r.final.heads 1=2*natBitLength n+1 ∧
      r.final.tapes 2=List.replicate (natWord n++suffix).length false ∧ r.final.heads 2=0 ∧
      r.final.tapes 3=List.replicate (natBitLength n) true ∧ r.final.heads 3=0 ∧
      r.final.tapes 4=List.replicate (natBitLength n) true ∧ r.final.heads 4=0 ∧
      r.final.tapes 5=UnaryTemplate.tape (natBitLength n) ∧ r.final.heads 5=1 ∧
      r.final.tapes 6=frame (binary (natBitLength n) n) ∧ r.final.heads 6=0 ∧
      r.final.tapes 7=List.replicate (2*natBitLength n+1) false ∧ r.final.heads 7=0 ∧
      ZeroPadding.pad 1 (r.final.tapes 8)=[false] ∧ r.final.heads 8=0 ∧
      r.final.tapes 12=UnaryTemplate.tape n ∧ r.final.heads 12=1 ∧ r.steps≤budget n suffix := by
  let word := natWord n++suffix
  let w := natBitLength n
  obtain ⟨base,hr,hf,hs,_⟩ := Streaming.copy_run word
  have he := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hr
  let ambient := TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base.final
  obtain ⟨localRun,hl,hsource,hpos,hw,hwh,hw2,hwh2,hwidth,hwidthh,hu,huh,hz5,hzh5,hz6,hzh6,hunary,hunaryh,hsteps⟩ :=
    MatrixDimensionPrepare.scratch_run [] suffix w n (Nat.lt_pow_succ_log_self (by decide) n)
  have hword : [] ++ List.replicate w true ++ false :: (binary w n++suffix)=word := by
    simp [word,w,natWord_eq,List.append_assoc]
  rw [hword] at hl hsource
  simp only [List.length_nil,Nat.zero_add] at hl hpos
  let entry : Configuration 11 dimensionStates :=
    Composition.leftConfig _ (MatrixDimensionPrepare.input word 0)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient header.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        Streaming.finished,Streaming.config]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        Streaming.finished,Streaming.config]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide)
    MatrixDimensionPrepare.machine ambient.heads ambient.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join copy header (4*word.length+2)
    (MatrixDimensionPrepare.budget w n) _
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused he hfocus
  have htime : 4*word.length+2+1+MatrixDimensionPrepare.budget w n=budget n suffix := by rfl
  rw [htime] at hj
  have hinput : Composition.leftConfig dimensionStates
      (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
        (initialConfiguration Streaming.machine (fun t => if t.val=0 then frame word else []))) =
      initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hinput] at hj
  have hnone : RecoveryFocus.pick slots (0 : Fin 13)=none := by decide
  have hnone2 : RecoveryFocus.pick slots (2 : Fin 13)=none := by decide
  have hpick (i : Fin 11) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused,hj,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.heads 0=0
    rw [hff]
    simp only [RecoveryFocus.config,hnone]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hsource
  · change focused.final.heads (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hpos
  · change focused.final.tapes 2=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone2]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,Fin.addCases,Streaming.finished,Streaming.config,word]
  · change focused.final.heads 2=0
    rw [hff]
    simp only [RecoveryFocus.config,hnone2]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hw
  · change focused.final.heads (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwh
  · change focused.final.tapes (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hw2
  · change focused.final.heads (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwh2
  · change focused.final.tapes (slots 3)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwidth
  · change focused.final.heads (slots 3)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwidthh
  · change focused.final.tapes (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hu
  · change focused.final.heads (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using huh
  · change focused.final.tapes (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hz5
  · change focused.final.heads (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hzh5
  · change ZeroPadding.pad 1 (focused.final.tapes (slots 6))=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hz6
  · change focused.final.heads (slots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hzh6
  · change focused.final.tapes (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hunary
  · change focused.final.heads (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hunaryh
  · change base.steps+1+focused.steps≤_
    rw [hs,hfs]
    rw [← htime]
    omega

end NearCubicWires.RepairOrdinary.WilliamsInputHeader

namespace NearCubicWires.RepairOrdinary.MatrixScoreHeaders
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `headers_run`, also exposing the all-`false` cells of both parses (tapes 2, 7, 8, 17, 18) and the second
unary copies (tapes 4, 14). -/
theorem scratch_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 23 ((5+D)+D),
      run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧
      actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 2=List.replicate (natWord d++natWord p++suffix).length false ∧ actual.final.heads 2=0 ∧
      actual.final.tapes 3=List.replicate (natBitLength d) true ∧ actual.final.heads 3=0 ∧
      actual.final.tapes 4=List.replicate (natBitLength d) true ∧ actual.final.heads 4=0 ∧
      actual.final.tapes 6=frame (binary (natBitLength d) d) ∧ actual.final.heads 6=0 ∧
      actual.final.tapes 7=List.replicate (2*natBitLength d+1) false ∧ actual.final.heads 7=0 ∧
      ZeroPadding.pad 1 (actual.final.tapes 8)=[false] ∧ actual.final.heads 8=0 ∧
      actual.final.tapes 12=UnaryTemplate.tape d ∧ actual.final.heads 12=1 ∧
      actual.final.tapes 13=List.replicate (natBitLength p) true ∧ actual.final.heads 13=0 ∧
      actual.final.tapes 14=List.replicate (natBitLength p) true ∧ actual.final.heads 14=0 ∧
      actual.final.tapes 16=frame (binary (natBitLength p) p) ∧ actual.final.heads 16=0 ∧
      actual.final.tapes 17=List.replicate (2*natBitLength p+1) false ∧ actual.final.heads 17=0 ∧
      ZeroPadding.pad 1 (actual.final.tapes 18)=[false] ∧ actual.final.heads 18=0 ∧
      actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=1 ∧
      actual.steps≤budget d p suffix := by
  let source := natWord d++natWord p++suffix
  obtain ⟨base,hb,ht0,hh0,ht1,hh1,ht2,hh2,ht3,hh3,ht4,hh4,_,_,ht6,hh6,ht7,hh7,ht8,hh8,ht12,hh12,hbs⟩ :=
    WilliamsInputHeader.scratch_run d (natWord p++suffix)
  simp only [←List.append_assoc] at hb ht0 ht1 ht2
  have he := TapeEmbedding.run_embed WilliamsInputHeader.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base.final
  obtain ⟨last,hl,hs,hpos,hw,hwh,hw2,hwh2,_,_,hv,hvh,hz5,hzh5,hz6,hzh6,hu,huh,hls⟩ := MatrixDimensionPrepare.scratch_run
    (natWord d) suffix (natBitLength p) p (Nat.lt_pow_succ_log_self (by decide) p)
  have hsource : natWord d++List.replicate (natBitLength p) true++
      false::(binary (natBitLength p) p++suffix)=source := by
    simp [source,WilliamsInputHeader.natWord_eq,List.append_assoc]
  have hlength : (natWord d).length=2*natBitLength d+1 := by
    simp [WilliamsInputHeader.natWord_eq]; omega
  rw [hsource] at hl hs
  rw [hlength] at hl hpos
  let entry : Configuration 11 D := Composition.leftConfig _
    (MatrixDimensionPrepare.input source (2*natBitLength d+1))
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry=
      Composition.restart ambient second.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · simpa [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases] using hh1
      all_goals simp [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases]
    · intro i
      fin_cases i
      · simpa [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,source] using ht1
      all_goals simp [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases]
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixDimensionPrepare.machine
    ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hf
  have hj := Composition.run_join first second (WilliamsInputHeader.budget d (natWord p++suffix))
    (MatrixDimensionPrepare.budget (natBitLength p) p) _
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused he hf
  have hin : Composition.leftConfig D (TapeEmbedding.config (fun _ : Fin 10 => 0)
      (fun _ : Fin 10 => []) (initialConfiguration WilliamsInputHeader.machine
        (WilliamsInputHeader.input source)))=initialConfiguration machine (input source) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,WilliamsInputHeader.input]
  rw [hin] at hj
  have pick (i : Fin 11) : RecoveryFocus.pick slots (slots i)=some i :=
    RecoveryFocus.pick_slot slots (by decide) i
  have otherT (i : Fin 13) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
    simp [ambient,TapeEmbedding.config]
  have otherH (i : Fin 13) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
    simp [ambient,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt _ focused,hj,
    (otherT 0 (by decide)).trans ht0,(otherH 0 (by decide)).trans hh0,?_,?_,
    (otherT 2 (by decide)).trans ht2,(otherH 2 (by decide)).trans hh2,
    (otherT 3 (by decide)).trans ht3,(otherH 3 (by decide)).trans hh3,
    (otherT 4 (by decide)).trans ht4,(otherH 4 (by decide)).trans hh4,
    (otherT 6 (by decide)).trans ht6,(otherH 6 (by decide)).trans hh6,
    (otherT 7 (by decide)).trans ht7,(otherH 7 (by decide)).trans hh7,
    (congrArg (ZeroPadding.pad 1) (otherT 8 (by decide))).trans ht8,(otherH 8 (by decide)).trans hh8,
    (otherT 12 (by decide)).trans ht12,(otherH 12 (by decide)).trans hh12,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hs
  · change focused.final.heads (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick,Nat.add_assoc] using hpos
  · change focused.final.tapes (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hw
  · change focused.final.heads (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hwh
  · change focused.final.tapes (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hw2
  · change focused.final.heads (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hwh2
  · change focused.final.tapes (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hv
  · change focused.final.heads (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hvh
  · change focused.final.tapes (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hz5
  · change focused.final.heads (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hzh5
  · change ZeroPadding.pad 1 (focused.final.tapes (slots 6))=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hz6
  · change focused.final.heads (slots 6)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hzh6
  · change focused.final.tapes (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hu
  · change focused.final.heads (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using huh
  · change base.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreHeaders
