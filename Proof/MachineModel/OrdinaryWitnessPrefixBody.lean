import Proof.MachineModel.OrdinaryWitnessCounterAdvance

/-! One streamed witness bit followed by the paid small-counter check.
Only local scalar tapes rewind; source and output advance by two positions. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefixBody
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) : Configuration 6 s :=
  TapeEmbedding.config (![cursor,out.length] : Fin 2 → ℕ) (![source,out] : Fin 2 → List Bool)
    (WitnessCounterCheck.config state w counter bound cap flag)
def copyAction (next : Fin 3) (bit : Bool) (clear : Bool) : Action 6 3 :=
  ⟨next,fun i => if i=5 then some bit else if i=2 ∧ clear then some false else none,
    fun i => if i=4 ∨ i=5 then .right else .stay⟩
def copy : Machine 6 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 2
  rule := fun s scanned => if s.val=0 then some (copyAction 1 true true)
    else if s.val=1 then some (copyAction 2 (scanned 4) false) else none
def check : Machine 6 12 := TapeEmbedding.machine 2 WitnessCounterAdvance.machine
def machine : Machine 6 15 := Composition.machine copy check

theorem marker_step (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    step copy (config 0 w counter bound cap true source out cursor) =
      some (config 1 w counter bound cap false source (out++[true]) (cursor+1)) := by
  change some (applyAction _ (copyAction 1 true true)) = _
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,copyAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,HeadMove.apply,Fin.addCases]
  · funext i
    fin_cases i <;> simp [applyAction,copyAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,Fin.addCases,writeTapeBit,Streaming.write_append]

theorem bit_step (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    step copy (config 1 w counter bound cap false source out cursor) =
      some (config 2 w counter bound cap false source (out++[readTapeBit source cursor]) (cursor+1)) := by
  change some (applyAction _ (copyAction 2 (readTapeBit source cursor) false)) = _
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,copyAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,HeadMove.apply,Fin.addCases]
  · funext i
    fin_cases i <;> simp [applyAction,copyAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,Fin.addCases,Streaming.write_append]

theorem copy_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    ∃ r : ExecutionReceipt 6 3,
      runFrom copy 2 (config 0 w counter bound cap true source out cursor) = some r ∧
      r.final = config 2 w counter bound cap false source
        (out++[true,readTapeBit source (cursor+1)]) (cursor+2) := by
  let last := config (2 : Fin 3) w counter bound cap false source
    ((out++[true])++[readTapeBit source (cursor+1)]) ((cursor+1)+1)
  let tail : ExecutionReceipt 6 3 := ⟨last,0,last.tapeCells⟩
  have ht : runFrom copy 0 last = some tail := runFrom_zero_of_halted copy last (by rfl)
  have hb := runFrom_step copy _ _ tail (by rfl)
    (bit_step w counter bound cap source (out++[true]) (cursor+1)) ht
  have hm := runFrom_step copy _ _ _ (by rfl) (marker_step w counter bound cap source out cursor) hb
  refine ⟨_,hm,?_⟩
  simp only [tail,last,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc]

theorem check_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ)
    (hn : counter+1<2^w) (hb : bound<2^w) (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 6 12,
      runFrom check (8*w+7) (config check.start w counter bound cap false source out cursor) = some r ∧
      r.final = config 11 w (counter+1) bound cap (decide (counter+1≤bound)) source out cursor := by
  obtain ⟨base,hr,hf⟩ := WitnessCounterAdvance.check_run w counter bound cap hn hb hcap
  have he := TapeEmbedding.run_embed WitnessCounterAdvance.machine (![cursor,out.length] : Fin 2 → ℕ)
    (![source,out] : Fin 2 → List Bool) _ _ base hr
  refine ⟨TapeEmbedding.receipt (![cursor,out.length] : Fin 2 → ℕ)
    (![source,out] : Fin 2 → List Bool) base,he,?_⟩
  simp only [TapeEmbedding.receipt,hf]
  rfl

theorem body_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ)
    (hn : counter+1<2^w) (hb : bound<2^w) (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 6 15,
      runFrom machine (8*w+10) (config machine.start w counter bound cap true source out cursor) = some r ∧
      r.final = config 14 w (counter+1) bound cap (decide (counter+1≤bound)) source
        (out++[true,readTapeBit source (cursor+1)]) (cursor+2) := by
  obtain ⟨first,hf,hff⟩ := copy_run w counter bound cap source out cursor
  obtain ⟨last,hl,hlf⟩ := check_run w counter bound cap source
    (out++[true,readTapeBit source (cursor+1)]) (cursor+2) hn hb hcap
  have hi : Composition.restart first.final check.start = config check.start w counter bound cap false source
      (out++[true,readTapeBit source (cursor+1)]) (cursor+2) := by rw [hff]; rfl
  rw [← hi] at hl
  have hr := Composition.run_join copy check 2 (8*w+7)
    (config copy.start w counter bound cap true source out cursor) first last hf hl
  have ht : 2+1+(8*w+7) = 8*w+10 := by omega
  rw [ht] at hr
  refine ⟨Composition.joinedReceipt first last,hr,?_⟩
  simp only [Composition.joinedReceipt,hlf]
  rfl

end NearCubicWires.RepairOrdinary.WitnessPrefixBody
