import Proof.Amplification.RecoveryProjectionReusable

/-! Two actual writes append a projected bit in the existing marker/value
stream format. The raw result cell is retained at head zero. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionEmitBit
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=2
  rule := fun q scan=>match q.val with
    | 0=>some ⟨1,![none,some true],![.stay,.right]⟩
    | 1=>some ⟨2,![none,some (scan 0)],![.stay,.right]⟩
    | _=>none

def cfg (q : Fin 3) (source out : List Bool) : Configuration 2 3 :=
  ⟨q,![0,out.length],![source,out]⟩

theorem marker_step (source out : List Bool) :
    step machine (cfg 0 source out)=some (cfg 1 source (out++[true])) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,cfg,HeadMove.apply]
  · funext i; fin_cases i
    · rfl
    · exact Streaming.write_append out true

theorem value_step (source out : List Bool) :
    step machine (cfg 1 source out)=some (cfg 2 source (out++[readTapeBit source 0])) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,cfg,HeadMove.apply]
  · funext i; fin_cases i
    · rfl
    · exact Streaming.write_append out (readTapeBit source 0)

theorem emit_run (source out : List Bool) : ∃ r,
    runFrom machine 2 (cfg 0 source out)=some r ∧
      r.final=cfg 2 source (out++[true,readTapeBit source 0]) ∧ r.steps=2 := by
  have h := (Timed.single (by rfl) (marker_step source out)).trans
    (Timed.single (by rfl) (value_step source (out++[true])))
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  exact ⟨r,hr,by simpa only [List.append_assoc,List.cons_append,List.nil_append] using hf,hs⟩

theorem padded_emit (cap : Nat) (bit : Bool) (out : List Bool) : ∃ r,
    runFrom machine 2 (cfg 0 (ZeroPadding.pad cap [bit]) out)=some r ∧
      r.final=cfg 2 (ZeroPadding.pad cap [bit]) (out++[true,bit]) ∧ r.steps=2 := by
  obtain ⟨r,hr,hf,hs⟩ := emit_run (ZeroPadding.pad cap [bit]) out
  have hb : readTapeBit (ZeroPadding.pad cap [bit]) 0=bit := by
    rw [ZeroPadding.read_pad]
    rfl
  rw [hb] at hf
  exact ⟨r,hr,hf,hs⟩

end NearCubicWires.RepairSource.RecoveryProjectionEmitBit
