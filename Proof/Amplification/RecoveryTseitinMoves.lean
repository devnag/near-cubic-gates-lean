import Proof.Amplification.RecoveryTseitinClear

/-! Physical literal writes and preserved-field copies for the prefix
query. The same allocated reset tape is reused and its capacity retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open private install_pair from Proof.MachineModel.OrdinarySourceSATLiftMoves
open private install_first from Proof.MachineModel.OrdinaryOracleComposeHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run (destination : Fin 239) (word : List Bool) (cap : Nat)
    (ambient : Fin 239→List Bool) (hd : destination≠238) (hc : word.length ≤ cap)
    (hw : ambient destination=List.replicate cap false)
    (hl : ambient 238=List.replicate cap false) :
    ClockJoin.ReadyRun (literalMachine destination word) (2*word.length+2) ambient
      (Function.update ambient destination (ZeroPadding.pad cap word)) := by
  classical
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready word
  have hbase : ClockJoin.ReadyRun (HierarchyFixedWord.machine word) (2*word.length+2)
      (fun _=>[]) ![word,List.replicate word.length false] := ⟨r,hr,ht,hh,hs.le⟩
  have hpad := PCPPairReusable.padded_ready _ _ _ hbase (fun _=>cap)
  have hout : (fun i : Fin 2=>ZeroPadding.pad cap (![word,List.replicate word.length false] i))=
      ![ZeroPadding.pad cap word,List.replicate cap false] := by
    funext i
    fin_cases i
    · rfl
    · change ZeroPadding.pad cap (List.replicate word.length false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  rw [hout] at hpad
  have hfocus := hpad.focus (literalSlots destination) (literal_injective destination hd) ambient (by
    intro j
    fin_cases j <;> simpa [literalSlots,ZeroPadding.pad] using (by assumption))
  have he : install (literalSlots destination) ambient
      ![ZeroPadding.pad cap word,List.replicate cap false]=
      Function.update ambient destination (ZeroPadding.pad cap word) := by
    rw [←hl]
    exact install_pair _ (literal_injective destination hd) ambient _
  rw [he] at hfocus
  exact hfocus

theorem copy_run (sources : Fin 3→Fin 3) (k : Fin 3) (cap : Nat) (bits padding : List Bool) (ambient : Fin 239→List Bool)
    (hc : (frame bits).length ≤ cap) (hs : ambient (sourceSlot sources k)=frame bits++padding)
    (hb : ambient (destinationSlot k)=List.replicate cap false)
    (hl : ambient 238=List.replicate cap false) :
    ClockJoin.ReadyRun (copyMachine sources k) (4*bits.length+4) ambient
      (Function.update ambient (destinationSlot k) (ZeroPadding.pad cap (frame bits))) := by
  classical
  have hc' : 2*bits.length+1 ≤ cap := by simpa using hc
  have h := (PCPFieldMoves.ready_run bits padding cap cap).focus (copySlots sources k) (copy_injective sources k) ambient (by
    intro j
    fin_cases j <;> simpa [copySlots] using (by assumption))
  have hout : PCPFieldMoves.output [] bits padding cap cap=
      ![ambient (sourceSlot sources k),ZeroPadding.pad cap (frame bits),ambient 238] := by
    funext j
    fin_cases j <;> simp [PCPFieldMoves.output,hs,hl,max_eq_left hc']
  rw [hout] at h
  have he : install (copySlots sources k) ambient
      ![ambient (sourceSlot sources k),ZeroPadding.pad cap (frame bits),ambient 238]=
      Function.update ambient (destinationSlot k) (ZeroPadding.pad cap (frame bits)) := by
    have hi := install_first (copySlots sources k) (copy_injective sources k) ambient (ZeroPadding.pad cap (frame bits)) (ambient 238)
    change install (copySlots sources k) ambient
        ![ambient (sourceSlot sources k),ZeroPadding.pad cap (frame bits),ambient 238]=
      Function.update (Function.update ambient (destinationSlot k) (ZeroPadding.pad cap (frame bits))) 238 (ambient 238) at hi
    rw [hi]
    apply Function.update_eq_self_iff.mpr
    have hne : (238 : Fin 239)≠destinationSlot k := by fin_cases k <;> decide
    simp [Function.update,hne]
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hsteps⟩ := h
  exact ⟨r,hr,ht,hh,hsteps.le⟩

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
