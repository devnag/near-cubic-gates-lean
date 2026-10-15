import Proof.Hierarchy.HierarchyBinaryPower

/-! The ordinary three-frame header copier. Each copied physical bit also
advances the paid total-length driver. The output has the literal concatenated
framing used by U, without an added outer frame. -/
namespace NearCubicWires.RepairOrdinary.HierarchyHeader
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def marker (j : Fin 3) : Fin 8 := ⟨2*j.val,by omega⟩
def payload (j : Fin 3) : Fin 8 := ⟨2*j.val+1,by omega⟩
def following (j : Fin 3) : Fin 8 := ⟨2*j.val+2,by omega⟩
def sourceTape (j : Fin 3) : Fin 5 := Fin.castAdd 2 j
def copyAction (j : Fin 3) (b : Bool) (next : Fin 8) : Action 5 8 :=
  ⟨next,fun i => if i.val=4 then some b else none,
    fun i => if i.val=j.val ∨ i.val=3 ∨ i.val=4 then .right else .stay⟩
def raw : Machine 5 8 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==7
  rule := fun s scan => match s.val with
    | 0 => some (if scan 0 then copyAction 0 true 1 else copyAction 0 false 2)
    | 1 => some (copyAction 0 (scan 0) 0)
    | 2 => some (if scan 1 then copyAction 1 true 3 else copyAction 1 false 4)
    | 3 => some (copyAction 1 (scan 1) 2)
    | 4 => some (if scan 2 then copyAction 2 true 5 else copyAction 2 false 6)
    | 5 => some (copyAction 2 (scan 2) 4)
    | 6 => some (if scan 3 then ⟨6,fun i => if i.val=4 then some false else none,
        fun i => if i.val=3 ∨ i.val=4 then .right else .stay⟩
      else ⟨7,fun _ => none,fun _ => .stay⟩)
    | _ => none

def config (state : Fin 8) (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) : Configuration 5 8 :=
  ⟨state,![pos 0,pos 1,pos 2,out.length,out.length],
    ![source 0,source 1,source 2,List.replicate N true,out]⟩
theorem source_scan (state : Fin 8) (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (j : Fin 3) :
    (config state N source pos out).scanned (sourceTape j)=readTapeBit (source j) (pos j) := by
  fin_cases j <;> rfl
theorem copy_config (state next : Fin 8) (N : ℕ) (source : Fin 3 → List Bool)
    (pos : Fin 3 → ℕ) (out : List Bool) (j : Fin 3) (b : Bool) :
    applyAction (config state N source pos out) (copyAction j b next)=
      config next N source (Function.update pos j (pos j+1)) (out++[b]) := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> fin_cases j <;> simp [config,copyAction,applyAction,HeadMove.apply,Function.update]
  · funext i
    fin_cases i <;> simp [config,copyAction,applyAction,Streaming.write_append]

theorem marker_true (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (j : Fin 3) (hread : readTapeBit (source j) (pos j)=true) :
    step raw (config (marker j) N source pos out)=
      some (config (payload j) N source (Function.update pos j (pos j+1)) (out++[true])) := by
  have hscan := (source_scan (marker j) N source pos out j).trans hread
  have hr : raw.rule (marker j) (config (marker j) N source pos out).scanned=
      some (copyAction j true (payload j)) := by
    fin_cases j <;> dsimp [raw,marker,payload,sourceTape] at hscan ⊢ <;> simp [hscan]
  change (raw.rule (marker j) (config (marker j) N source pos out).scanned).map
    (applyAction (config (marker j) N source pos out))=_
  rw [hr]
  exact congrArg some (copy_config (marker j) (payload j) N source pos out j true)

theorem marker_false (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (j : Fin 3) (hread : readTapeBit (source j) (pos j)=false) :
    step raw (config (marker j) N source pos out)=
      some (config (following j) N source (Function.update pos j (pos j+1)) (out++[false])) := by
  have hscan := (source_scan (marker j) N source pos out j).trans hread
  have hr : raw.rule (marker j) (config (marker j) N source pos out).scanned=
      some (copyAction j false (following j)) := by
    fin_cases j <;> dsimp [raw,marker,following,sourceTape] at hscan ⊢ <;> simp [hscan]
  change (raw.rule (marker j) (config (marker j) N source pos out).scanned).map
    (applyAction (config (marker j) N source pos out))=_
  rw [hr]
  exact congrArg some (copy_config (marker j) (following j) N source pos out j false)

theorem payload_step (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (j : Fin 3) (b : Bool) (hread : readTapeBit (source j) (pos j)=b) :
    step raw (config (payload j) N source pos out)=
      some (config (marker j) N source (Function.update pos j (pos j+1)) (out++[b])) := by
  have hscan := (source_scan (payload j) N source pos out j).trans hread
  have hr : raw.rule (payload j) (config (payload j) N source pos out).scanned=
      some (copyAction j b (marker j)) := by
    fin_cases j <;> simpa [raw,marker,payload,sourceTape] using congrArg
      (fun b => some (copyAction _ b _)) hscan
  change (raw.rule (payload j) (config (payload j) N source pos out).scanned).map
    (applyAction (config (payload j) N source pos out))=_
  rw [hr]
  exact congrArg some (copy_config (payload j) (marker j) N source pos out j b)

end NearCubicWires.RepairOrdinary.HierarchyHeader
