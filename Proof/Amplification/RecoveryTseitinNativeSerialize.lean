import Proof.Amplification.RecoveryTseitinNativeFramed

/-! The balanced-CNF serializer consumes the actual complete original
circuit formula emitted from four raw inputs, with no prepared workspace. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Serialize
open LocalBitMultitape RepairOrdinary ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 133) : Fin 1506 := if i=0 then 1372 else ⟨1373+i.val,by have hi:=i.isLt; omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def first:=TapeEmbedding.machine 132 Cold.framedMachine
noncomputable def last:=RecoveryFocus.machine slots RecoveryFormulaFrame.machine
noncomputable def machine:=Composition.machine first last
def input {n : Nat} (circuit : BooleanCircuit n) : Fin 1506→List Bool :=
  Fin.addCases (m:=1374) (n:=132) (motive:=fun _=>List Bool) (Cold.framedInput circuit) (fun _=>[])
def budget {n : Nat} (circuit : BooleanCircuit n) :=
  Cold.framedBudget n circuit.nodes.length
    (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length+1+
    RecoveryFormulaFrame.rawBudget (RecoveryFormulaPayload.fields (CircuitInputCNF.circuitInputFormula circuit))

theorem embedded_initial {t e s : Nat} (p : Machine t s) (data : Fin t→List Bool) :
    TapeEmbedding.config (fun _ : Fin e=>0) (fun _ : Fin e=>[]) (initialConfiguration p data)=
      initialConfiguration (TapeEmbedding.machine e p) (Fin.addCases data (fun _ : Fin e=>[])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=e) (fun j=>?_) (fun j=>?_) i
    all_goals simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
  · rfl

theorem serialize_run {n : Nat} (circuit : BooleanCircuit n) : ∃ r,
    run machine (budget circuit) (input circuit)=some r ∧
      r.final.tapes 1504=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula circuit)).bits ∧
      r.steps ≤ budget circuit := by
  let formula:=CircuitInputCNF.circuitInputFormula circuit
  let words:=RecoveryFormulaPayload.fields formula
  obtain ⟨base,hbase,bt,bh,bs⟩:=Cold.framed_run circuit
  let a:=TapeEmbedding.receipt (fun _ : Fin 132=>0) (fun _ : Fin 132=>[]) base
  have ha:=TapeEmbedding.run_embed Cold.framedMachine (fun _ : Fin 132=>0) (fun _ : Fin 132=>[]) _ _ base hbase
  rw [embedded_initial] at ha
  obtain ⟨code,hcode,ct,cs⟩:=RecoveryFormulaFrame.raw_run words
  have hheads (j : Fin 133) : a.final.heads (slots j)=0 := by
    by_cases hj : j=0
    · subst j
      exact (TapeEmbedding.receipt_heads_old _ _ _ (1372 : Fin 1374)).trans (bh 1372)
    · let k : Fin 132:=⟨j.val-1,by have hi:=j.isLt; omega⟩
      have he : slots j=k.natAdd 1374 := by
        apply Fin.ext
        have hn : j.val≠0:=fun h=>hj (Fin.ext h)
        simp only [slots,if_neg hj,Fin.val_natAdd]
        dsimp [k]
        omega
      rw [he]
      exact TapeEmbedding.receipt_heads_new _ _ _ k
  have htapes (j : Fin 133) : a.final.tapes (slots j)=RecoveryFormulaFrame.input words j := by
    by_cases hj : j=0
    · subst j
      exact (TapeEmbedding.receipt_tapes_old _ _ _ (1372 : Fin 1374)).trans bt
    · let k : Fin 132:=⟨j.val-1,by have hi:=j.isLt; omega⟩
      have he : slots j=k.natAdd 1374 := by
        apply Fin.ext
        have hn : j.val≠0:=fun h=>hj (Fin.ext h)
        simp only [slots,if_neg hj,Fin.val_natAdd]
        dsimp [k]
        omega
      rw [he,TapeEmbedding.receipt_tapes_new,RecoveryFormulaPayload.input_tapes]
      change []=(if j.val=0 then frame (FieldList.stream words) else [])
      rw [if_neg (show j.val≠0 from fun h=>hj (Fin.ext h))]
  obtain ⟨b,hb,_bc,bsteps,_bheads,btapes,_bkeep⟩:=RecoveryFocus.dock slots slots_injective
    RecoveryFormulaFrame.machine _ a.final.heads a.final.tapes
    (initialConfiguration RecoveryFormulaFrame.machine (RecoveryFormulaFrame.input words)) hheads htapes code hcode
  obtain ⟨r,hr,_rh,rt,rs⟩:=join_two first last _ _ _ a b ha hb
  refine ⟨r,hr,?_,?_⟩
  · have ht:=ct
    rw [RecoveryFormulaPayload.exact_code] at ht
    exact (congrFun rt 1504).trans ((btapes 131).trans ht)
  · rw [rs,bsteps]
    change base.steps+1+code.steps ≤ _
    unfold budget
    change code.steps ≤ RecoveryFormulaFrame.rawBudget
      (RecoveryFormulaPayload.fields (CircuitInputCNF.circuitInputFormula circuit)) at cs
    omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Serialize
