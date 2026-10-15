import Proof.PCP.PCPPNativeClauseTripleField

/-! Read the three original clause fields through one reusable parser bank.
The source cursor advances literally and every reference survives the next read. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Run {s : ℕ} (m : Machine 25 s) (fuel : ℕ) (source : List Bool)
    (start finish stride p n C : ℕ) (before after : Fin 3→List Bool) : Prop :=
  ∃ r,runFrom m fuel (entry m start (data source stride p n C before))=some r ∧
    r.final.heads=heads finish ∧ r.final.tapes=data source stride p n C after ∧ r.steps≤fuel

private theorem join {s t : ℕ} (a : Machine 25 s) (b : Machine 25 t)
    (fa fb : ℕ) (source : List Bool) (start middle finish stride p n C : ℕ)
    (before during after : Fin 3→List Bool)
    (ha : Run a fa source start middle stride p n C before during)
    (hb : Run b fb source middle finish stride p n C during after) :
    Run (Composition.machine a b) (fa+1+fb) source start finish stride p n C before after := by
  obtain ⟨ra,hra,rah,rat,ras⟩:=ha
  obtain ⟨rb,hrb,rbh,rbt,rbs⟩:=hb
  have hm : Composition.restart ra.final b.start=entry b middle (data source stride p n C during) :=
    configuration_ext rfl rah rat
  rw [←hm] at hrb
  exact ⟨Composition.joinedReceipt ra rb,Composition.run_join a b fa fb _ ra rb hra hrb,
    rbh,rbt,by change ra.steps+1+rb.steps≤fa+1+fb; omega⟩

def fields (bits : Fin 3→List Bool) := frame (bits 0)++frame (bits 1)++frame (bits 2)
def references (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n : ℕ) : Fin 3→List Bool :=
  fun i=>List.replicate (PCPPNativeClauseReusable.reference (indices i) stride (signs i) p n) true
def budget (bits : Fin 3→List Bool) (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C : ℕ) :=
  PCPPNativeClauseReusable.budget (bits 0) (indices 0) stride (signs 0) p n C+1+
  PCPPNativeClauseReusable.budget (bits 1) (indices 1) stride (signs 1) p n C+1+
  PCPPNativeClauseReusable.budget (bits 2) (indices 2) stride (signs 2) p n C
noncomputable def firstTwo := Composition.machine (fieldMachine 0) (fieldMachine 1)
noncomputable def machine := Composition.machine firstTwo (fieldMachine 2)

theorem triple_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C : ℕ)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C) :
    Run machine (budget bits indices signs stride p n C) (pre++fields bits++tail)
      pre.length (pre++fields bits).length stride p n C (fun _=>[])
      (references indices signs stride p n) := by
  let refs:=references indices signs stride p n
  let empty : Fin 3→List Bool:=fun _=>[]
  let one:=Function.update empty 0 (refs 0)
  let two:=Function.update one 1 (refs 1)
  let three:=Function.update two 2 (refs 2)
  have h0:=field_run pre (bits 0) (frame (bits 1)++frame (bits 2)++tail)
    (indices 0) (signs 0) stride p n C empty 0 rfl (hv 0) (hC 0)
  have h1:=field_run (pre++frame (bits 0)) (bits 1) (frame (bits 2)++tail)
    (indices 1) (signs 1) stride p n C one 1 (by simp [one,empty]) (hv 1) (hC 1)
  have h2:=field_run (pre++frame (bits 0)++frame (bits 1)) (bits 2) tail
    (indices 2) (signs 2) stride p n C two 2 (by simp [two,one,empty]) (hv 2) (hC 2)
  have a : Run (fieldMachine 0) (PCPPNativeClauseReusable.budget (bits 0) (indices 0) stride (signs 0) p n C) (pre++fields bits++tail) pre.length
      (pre++frame (bits 0)).length stride p n C empty one := by
    simpa only [Run,fields,one,refs,references,List.append_assoc,List.length_append,frame_length,Nat.add_assoc] using h0
  have b : Run (fieldMachine 1) (PCPPNativeClauseReusable.budget (bits 1) (indices 1) stride (signs 1) p n C) (pre++fields bits++tail) (pre++frame (bits 0)).length
      (pre++frame (bits 0)++frame (bits 1)).length stride p n C one two := by
    simpa only [Run,fields,two,refs,references,List.append_assoc,List.length_append,frame_length,Nat.add_assoc] using h1
  have c : Run (fieldMachine 2) (PCPPNativeClauseReusable.budget (bits 2) (indices 2) stride (signs 2) p n C) (pre++fields bits++tail) (pre++frame (bits 0)++frame (bits 1)).length
      (pre++fields bits).length stride p n C two three := by
    simpa only [Run,fields,three,refs,references,List.append_assoc,List.length_append,frame_length,Nat.add_assoc] using h2
  have hthree : three=refs := by
    funext i; fin_cases i <;> simp [three,two,one]
  have ab:=join (fieldMachine 0) (fieldMachine 1) _ _ _ _ _ _ _ _ _ _ _ _ _ a b
  have abc:=join firstTwo (fieldMachine 2) _ _ _ _ _ _ _ _ _ _ _ _ _ ab c
  rw [hthree] at abc
  exact abc

end NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
