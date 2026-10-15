import Proof.Supplier.RowNativeCoordinate
import Proof.Supplier.RowPowerBlockMeaning

/-! One actual selected weight/target is appended as a signed radix block.
The selected child stays in its original cache; the prefix scanner copies no
field, and the signed appender reuses its separate bounded scratch bank. -/
namespace NearCubicWires.RepairOrdinary.RowNativeCoordinateAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 18 := ![0,16,17,15]
theorem injective : Function.Injective slots := by decide
noncomputable def first := RecoveryFocus.machine slots RowNativeCoordinate.machine
noncomputable def last := TapeEmbedding.machine 3 RowPowerNativeReusable.machine
noncomputable def machine := Composition.machine first last
def extraHeads (out : List Bool) : Fin 3 → ℕ := ![1,0,out.length]
def extraTapes (i : ℕ) (backing out : List Bool) : Fin 3 → List Bool :=
  ![UnaryTemplate.tape i,backing,out]
noncomputable def ready (source : List Bool) (pos w C i : ℕ)
    (positive negative backing out : List Bool) : Configuration 18 20 :=
  TapeEmbedding.config (extraHeads out) (extraTapes i backing out)
    ⟨RowPowerNativeReusable.machine.start,RowPowerNativeReusable.heads pos positive negative,
      RowPowerNativeReusable.tapes source w C positive negative⟩
noncomputable def entry (source : List Bool) (pos w C i : ℕ)
    (positive negative backing out : List Bool) :=
  Composition.leftConfig 20 ⟨first.start,
    (ready source pos w C i positive negative backing out).heads,
    (ready source pos w C i positive negative backing out).tapes⟩
def budget {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n) (w C : ℕ) :=
  RowNativeCoordinate.budget g i+1+RowPowerNativeReusable.budget (RowNativeCoordinate.value g i hi) w C

theorem pick (j : Fin 18) : RecoveryFocus.pick slots j=
    (![some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
      some 3,some 1,some 2] : Fin 18 → Option (Fin 4)) j := by
  fin_cases j
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | exact RecoveryFocus.pick_slot slots injective 3
    | decide

theorem coordinate_append_run {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n)
    (pre tail positive negative backing out : List Bool) (w C : ℕ)
    (hC : RowPowerNativeReset.rawTime (RowNativeCoordinate.value g i hi) w+1≤C) :
    let z := RowNativeCoordinate.value g i hi
    let pos := pre.length+(RowNativeCoordinate.prior g i).length+(intWord z).length
    let P := positive++marks (RowPowerNativeReusable.block w z false)
    let N := negative++marks (RowPowerNativeReusable.block w z true)
    ∃ r,runFrom machine (budget g i hi w C)
      (entry (pre++exactWord g++tail) pre.length w C i positive negative backing out)=some r ∧
      r.final.heads=(ready (pre++exactWord g++tail) pos w C i P N
        (RowNativeCoordinate.afterBacking g i backing) out).heads ∧
      r.final.tapes=(ready (pre++exactWord g++tail) pos w C i P N
        (RowNativeCoordinate.afterBacking g i backing) out).tapes ∧
      r.steps=budget g i hi w C := by
  dsimp only
  let source := pre++exactWord g++tail
  let pos := pre.length+(RowNativeCoordinate.prior g i).length
  let before := ready source pre.length w C i positive negative backing out
  let parsed := ready source pos w C i positive negative
    (RowNativeCoordinate.afterBacking g i backing) out
  obtain ⟨scan,hscan,scanH,scanT,scanS⟩ := RowNativeCoordinate.coordinate_run g i hi pre tail backing out
  obtain ⟨focused,hfocused,focusedF,focusedS⟩ := RecoveryFocus.run_config slots injective
    RowNativeCoordinate.machine before.heads before.tapes _ _ scan hscan
  have hstart : RecoveryFocus.config slots before.heads before.tapes
      (RowNativeCoordinate.input g i pre tail backing out)=⟨first.start,before.heads,before.tapes⟩ := by
    apply WilliamsSourceCrop.focus_same slots (⟨first.start,before.heads,before.tapes⟩ : Configuration 18 _)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hstart] at hfocused
  have hheads : focused.final.heads=parsed.heads := by
    rw [focusedF]
    funext j
    fin_cases j <;> simp [RecoveryFocus.config,pick,scanH,before,parsed,ready,
      TapeEmbedding.config,Fin.addCases,extraHeads,RowPowerNativeReusable.heads,pos]
  have htapes : focused.final.tapes=parsed.tapes := by
    rw [focusedF]
    funext j
    fin_cases j <;> simp [RecoveryFocus.config,pick,scanT,before,parsed,ready,
      TapeEmbedding.config,Fin.addCases,extraTapes,RowPowerNativeReusable.tapes,source]
  let z := RowNativeCoordinate.value g i hi
  have hsource : (pre++RowNativeCoordinate.prior g i)++intWord z++(RowNativeCoordinate.suffix g i++tail)=source := by
    dsimp only [source,z]
    rw [RowNativeCoordinate.selected_word g i hi]
    simp only [List.append_assoc]
  obtain ⟨field,hfield,fieldH,fieldT,fieldS⟩ := RowPowerNativeReusable.reusable_run
    (pre++RowNativeCoordinate.prior g i) (RowNativeCoordinate.suffix g i++tail)
    positive negative z w C hC
  simp only [hsource,List.length_append] at hfield fieldT fieldH
  have embedded := TapeEmbedding.run_embed RowPowerNativeReusable.machine (extraHeads out)
    (extraTapes i (RowNativeCoordinate.afterBacking g i backing) out) _ _ field hfield
  have hentry : TapeEmbedding.config (extraHeads out)
      (extraTapes i (RowNativeCoordinate.afterBacking g i backing) out)
      ⟨RowPowerNativeReusable.machine.start,RowPowerNativeReusable.heads pos positive negative,
        RowPowerNativeReusable.tapes source w C positive negative⟩=
      Composition.restart focused.final last.start := by
    apply configuration_ext
    · rfl
    · exact hheads.symm
    · exact htapes.symm
  rw [hentry] at embedded
  let fieldRun := TapeEmbedding.receipt (extraHeads out)
    (extraTapes i (RowNativeCoordinate.afterBacking g i backing) out) field
  have whole := Composition.run_join first last _ _ _ focused fieldRun hfocused embedded
  refine ⟨Composition.joinedReceipt focused fieldRun,whole,?_,?_,?_⟩
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,fieldRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [fieldH]
    rfl
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,fieldRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [fieldT]
    rfl
  · change focused.steps+1+field.steps=_
    rw [focusedS,scanS,fieldS]
    rfl

end NearCubicWires.RepairOrdinary.RowNativeCoordinateAppend
