import Proof.MachineModel.Bridge
import Proof.CaseAnalysis.RowsCircuitCounterReturn

/-! The raw ordered incidence machine on the existing paid polynomial-bank
backing. Padding supplies no input: the caller owns these physical tapes. -/
namespace NearCubicWires.ExtIncidence.Padded
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos tablePos countPos : ℕ) : Fin 5 → ℕ := ![pos,1,0,tablePos,countPos]
def tapes (C B : ℕ) (source table : List Bool) (count : ℕ) : Fin 5 → List Bool :=
  ![source,ZeroPadding.pad C (UnaryTemplate.tape B),List.replicate C false,
    ZeroPadding.pad C table,ZeroPadding.pad C (List.replicate count true)]
def capacities (C : ℕ) : Fin 5 → ℕ := ![0,C,C,C,C]

theorem zero_pad (C B : ℕ) (h : B ≤ C) :
    ZeroPadding.pad C (List.replicate B false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,
    Nat.add_sub_of_le h]

theorem config_eq (C B : ℕ) (h : B ≤ C) (q : Fin 7)
    (source : List Bool) (pos : ℕ) (out : List Bool) (count : ℕ) :
    ZeroPadding.config (capacities C)
      (ExtIncidence.cfg q source pos B 1 (List.replicate B false) 0 out count)=
      (⟨q,heads pos out.length count,tapes C B source out count⟩ : Configuration 5 7) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> first | rfl | skip
    · exact ZeroPadding.pad_zero source
    · exact zero_pad C B h

theorem raw_run {B : ℕ} (ms : List (List (Fin B))) (C : ℕ) (hB : B ≤ C)
    (pre tail : List Bool) :
    PCPOuter.Exact ExtIncidence.machine (ExtIncidence.cost B (rawIndices ms))
      (heads pre.length 0 0) (tapes C B (pre++stream (rawIndices ms)++tail) [] 0)
      (heads (pre.length+(stream (rawIndices ms)).length) (rawRows ms).flatten.length ms.length)
      (tapes C B (pre++stream (rawIndices ms)++tail) (rawRows ms).flatten ms.length) := by
  obtain ⟨base,hbase,hfinal,hsteps⟩:=raw_rows_run ms pre tail [] 0
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config ExtIncidence.machine (capacities C) _ _ base hbase
  rw [config_eq C B hB] at hr
  rw [hfinal] at rf
  simp only [List.nil_append,Nat.zero_add] at rf
  rw [config_eq C B hB] at rf
  exact ⟨r,hr,congrArg Configuration.heads rf,congrArg Configuration.tapes rf,rs.trans hsteps⟩

theorem raw_rows_length {B : ℕ} (ms : List (List (Fin B))) :
    (rawRows ms).flatten.length=ms.length*B := by
  rw [←raw_table_eq_rows,ExtIncidence.table_length]
  simp only [rawIndices,List.length_map]

end NearCubicWires.ExtIncidence.Padded
