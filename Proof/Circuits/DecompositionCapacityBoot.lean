import Proof.Circuits.DecompositionGlobalBudget

/-! The fixed one-field count is physically written before the existing
counted capacity producer scans the original framed native input. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCapacity
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (D : ℕ) (source field : List Bool) : Fin (PCPSerializerCapacity.tapes D) → List Bool :=
  Fin.addCases ![source,[],field,[],[]] (fun _ => [])
def boot (D : ℕ) : Machine (PCPSerializerCapacity.tapes D) 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if q.val=0 then
      some ⟨1,fun i => if i=PCPSerializerCapacity.old D 2 then some false else none,
        fun i => if i=PCPSerializerCapacity.old D 2 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i=PCPSerializerCapacity.old D 2 then some true else none,fun _ => .stay⟩
    else none
def cfg (D : ℕ) (q : Fin 3) (source field : List Bool) (started : Bool) :
    Configuration (PCPSerializerCapacity.tapes D) 3 :=
  ⟨q,if started then PCPSerializerCapacity.heads D 0 else fun _ => 0,input D source field⟩

theorem boot_run (D : ℕ) (source : List Bool) :
    ∃ r,run (boot D) 2 (input D source [])=some r ∧
      r.final=PCPSerializerCapacity.entry D (2 : Fin 3) source 0 1 ∧ r.steps=2 := by
  have h0 : step (boot D) (cfg D 0 source [] false)=some (cfg D 1 source [false] true) := by
    simp only [step,boot,show (cfg D 0 source [] false).control=0 from rfl,
      Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=5) (n:=_) (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> rfl
      · have hne : j.natAdd 5≠PCPSerializerCapacity.old D 2 := by
          intro h; have hv := congrArg Fin.val h
          change 5+j.val=2 at hv
          omega
        simp only [applyAction,cfg,Bool.false_eq_true,↓reduceIte,
          PCPSerializerCapacity.heads,Fin.addCases_right]
        change (if j.natAdd 5=PCPSerializerCapacity.old D 2 then HeadMove.right else .stay).apply 0=0
        simp only [if_neg hne,HeadMove.apply]
    · funext i
      refine Fin.addCases (m:=5) (n:=_) (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> rfl
      · have hne : j.natAdd 5≠PCPSerializerCapacity.old D 2 := by
          intro h; have hv := congrArg Fin.val h
          change 5+j.val=2 at hv
          omega
        simp only [applyAction,cfg,input,Fin.addCases_right]
        change (match (if j.natAdd 5=PCPSerializerCapacity.old D 2 then some false else none) with
          | none => [] | some b => writeTapeBit [] 0 b)=[]
        simp only [if_neg hne]
  have h1 : step (boot D) (cfg D 1 source [false] true)=
      some (PCPSerializerCapacity.entry D (2 : Fin 3) source 0 1) := by
    simp only [step,boot,show (cfg D 1 source [false] true).control=1 from rfl,
      Fin.val_one,show ¬(1 : ℕ)=0 by decide,ite_false,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      refine Fin.addCases (m:=5) (n:=_) (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> rfl
      · have hne : j.natAdd 5≠PCPSerializerCapacity.old D 2 := by
          intro h; have hv := congrArg Fin.val h
          change 5+j.val=2 at hv
          omega
        simp only [applyAction,cfg,input,PCPSerializerCapacity.entry,PCPSerializerCapacity.input,
          ↓reduceIte,PCPSerializerCapacity.heads,Fin.addCases_right]
        change (match (if j.natAdd 5=PCPSerializerCapacity.old D 2 then some true else none) with
          | none => [] | some b => writeTapeBit [] 0 b)=[]
        simp only [if_neg hne]
  exact ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)

end NearCubicWires.RepairOrdinary.DecompositionCapacity
