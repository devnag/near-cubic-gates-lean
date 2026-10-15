import Proof.Supplier.RowCachedChildFields

/-! Original retained native child cache → selected coordinate → one signed
radix block, on a fixed20-tape machine. Cache/arity/selection drivers persist. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 20 := ![0,16,17,18,19]
theorem injective : Function.Injective slots := by decide
noncomputable def first := RecoveryFocus.machine slots DecompositionCachedChild.machine
noncomputable def last := TapeEmbedding.machine 2 RowNativeCoordinateAppend.machine
noncomputable def machine := Composition.machine first last
def extra (n i : ℕ) : Fin 2 → List Bool := ![UnaryTemplate.tape n,UnaryTemplate.tape i]
noncomputable def ready {n : ℕ} (gs : List (ExactThresholdGate n)) (i j pos w C : ℕ)
    (positive negative backing out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 2 => 1) (extra n i)
    (RowNativeCoordinateAppend.ready (exactListWord gs) pos w C j positive negative backing out)
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C : ℕ)
    (positive negative : List Bool) :=
  Composition.leftConfig (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 6)+20) ⟨first.start,(ready gs i j 0 w C positive negative [] []).heads,
    (ready gs i j 0 w C positive negative [] []).tapes⟩
def childPrefix {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) :=
  natWord gs.length++RowCachedChildFields.prior gs i
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C : ℕ) :=
  DecompositionCachedChild.budget gs i+1+RowNativeCoordinateAppend.budget gs[i] j hj w C
def value {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) := RowNativeCoordinate.value gs[i] j hj
def afterBacking {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) := RowNativeCoordinate.afterBacking gs[i] j (RowCachedChildFields.backing gs i)
def endPos {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) :=
  (childPrefix gs i).length+(RowNativeCoordinate.prior gs[i] j).length+(intWord (value gs i hi j hj)).length

theorem pick (j : Fin 20) : RecoveryFocus.pick slots j=
    (![some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
      some 1,some 2,some 3,some 4] : Fin 20 → Option (Fin 5)) j := by
  fin_cases j
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | exact RecoveryFocus.pick_slot slots injective 3
    | exact RecoveryFocus.pick_slot slots injective 4
    | decide

theorem append_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (positive negative : List Bool) (w C : ℕ)
    (hC : RowPowerNativeReset.rawTime (value gs i hi j hj) w+1≤C) :
    let P := positive++marks (RowPowerNativeReusable.block w (value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block w (value gs i hi j hj) true)
    ∃ r,runFrom machine (budget gs i hi j hj w C) (entry gs i j w C positive negative)=some r ∧
      r.final.heads=(ready gs i j (endPos gs i hi j hj) w C P N
        (afterBacking gs i hi j) (RowCachedChildFields.prior gs i)).heads ∧
      r.final.tapes=(ready gs i j (endPos gs i hi j hj) w C P N
        (afterBacking gs i hi j) (RowCachedChildFields.prior gs i)).tapes ∧
      r.steps=budget gs i hi j hj w C := by
  dsimp only
  let before := ready gs i j 0 w C positive negative [] []
  let parsed := ready gs i j (childPrefix gs i).length w C positive negative
    (RowCachedChildFields.backing gs i) (RowCachedChildFields.prior gs i)
  obtain ⟨scan,hs,sh,st,ss⟩ := RowCachedChildFields.position_run gs i hi.le
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config slots injective DecompositionCachedChild.machine
    before.heads before.tapes _ _ scan hs
  have hin : RecoveryFocus.config slots before.heads before.tapes (DecompositionCachedChild.entry gs i)=
      ⟨first.start,before.heads,before.tapes⟩ := by
    apply WilliamsSourceCrop.focus_same slots (⟨first.start,before.heads,before.tapes⟩ : Configuration 20 _)
    · intro a; fin_cases a <;> rfl
    · intro a; fin_cases a <;> rfl
  rw [hin] at hcall
  have ch : called.final.heads=parsed.heads := by
    rw [cf]
    funext a
    fin_cases a <;> simp [RecoveryFocus.config,pick,sh,before,parsed,ready,
      RowNativeCoordinateAppend.ready,TapeEmbedding.config,Fin.addCases,
      RowNativeCoordinateAppend.extraHeads,RowPowerNativeReusable.heads,RowCachedChildFields.heads,childPrefix]
  have ct : called.final.tapes=parsed.tapes := by
    rw [cf]
    funext a
    fin_cases a <;> simp [RecoveryFocus.config,pick,st,before,parsed,ready,
      RowNativeCoordinateAppend.ready,TapeEmbedding.config,Fin.addCases,
      RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes,RowCachedChildFields.tapes,extra]
  have hw : childPrefix gs i++exactWord gs[i]++(gs.drop (i+1)).flatMap exactWord=exactListWord gs :=
    (DecompositionCachedChild.selected_word gs i hi).symm
  obtain ⟨field,hf,fh,ft,fs⟩ := RowNativeCoordinateAppend.coordinate_append_run gs[i] j hj
    (childPrefix gs i) ((gs.drop (i+1)).flatMap exactWord) positive negative
    (RowCachedChildFields.backing gs i) (RowCachedChildFields.prior gs i) w C hC
  simp only [hw] at hf fh ft
  have embed := TapeEmbedding.run_embed RowNativeCoordinateAppend.machine
    (fun _ : Fin 2 => 1) (extra n i) _ _ field hf
  have he : TapeEmbedding.config (fun _ : Fin 2 => 1) (extra n i)
      (RowNativeCoordinateAppend.entry (exactListWord gs) (childPrefix gs i).length w C j
        positive negative (RowCachedChildFields.backing gs i) (RowCachedChildFields.prior gs i))=
      Composition.restart called.final last.start := by
    apply configuration_ext
    · rfl
    · exact ch.symm
    · exact ct.symm
  rw [he] at embed
  let fieldRun := TapeEmbedding.receipt (fun _ : Fin 2 => 1) (extra n i) field
  have whole := Composition.run_join first last _ _ _ called fieldRun hcall embed
  refine ⟨Composition.joinedReceipt called fieldRun,whole,?_,?_,?_⟩
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,fieldRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [fh]
    rfl
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,fieldRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [ft]
    rfl
  · change called.steps+1+field.steps=_
    rw [cs,ss,fs]
    rfl

end NearCubicWires.RepairOrdinary.RowCachedCoordinateAppend
