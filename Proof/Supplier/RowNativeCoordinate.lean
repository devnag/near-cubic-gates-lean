import Proof.Supplier.RowNativeFieldSkip
import Proof.Circuits.DecompositionCachedChildAccess

/-! Physical access to a weight or the target of the selected native child.
Coordinates retain occurrence order, with the target at the actual arity. -/
namespace NearCubicWires.RepairOrdinary.RowNativeCoordinate
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields {n : ℕ} (g : ExactThresholdGate n) := List.ofFn g.weight++[g.target]
theorem fields_length {n : ℕ} (g : ExactThresholdGate n) : (fields g).length=n+1 := by simp [fields]
theorem word_fields {n : ℕ} (g : ExactThresholdGate n) : exactWord g=(fields g).flatMap intWord := by
  simp [fields,exactWord]
theorem field_weight {n : ℕ} (g : ExactThresholdGate n) (i : Fin n) :
    (fields g)[i.val]'(by rw [fields_length]; omega)=g.weight i := by
  unfold fields
  rw [List.getElem_append_left (by simp)]
  simp
theorem field_target {n : ℕ} (g : ExactThresholdGate n) :
    (fields g)[n]'(by rw [fields_length]; omega)=g.target := by
  unfold fields
  rw [List.getElem_append_right (by simp)]
  simp
def prior {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) := ((fields g).take i).flatMap intWord
def suffix {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) := ((fields g).drop (i+1)).flatMap intWord
def value {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n) : ℤ :=
  (fields g)[i]'(by rw [fields_length]; omega)

theorem selected_word {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n) :
    exactWord g=prior g i++intWord (value g i hi)++suffix g i := by
  have hlt : i<(fields g).length := by rw [fields_length]; omega
  have h : (fields g).take i++(fields g)[i]::(fields g).drop (i+1)=fields g := by
    rw [←List.drop_eq_getElem_cons hlt]
    exact List.take_append_drop i (fields g)
  have he := congrArg (fun zs : List ℤ => zs.flatMap intWord) h
  simpa only [word_fields,prior,suffix,value,List.flatMap_append,List.flatMap_cons,List.append_assoc] using he.symm

def budget {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) := (prior g i).length+6*i+3
noncomputable def machine := RowNativeFieldSkip.loop
noncomputable def input {n : ℕ} (g : ExactThresholdGate n) (i : ℕ)
    (pre tail backing out : List Bool) : Configuration 4 (Fintype.card (RepeatMachine.Control 6)) :=
  ⟨machine.start,![pre.length,0,out.length,1],
    ![pre++exactWord g++tail,backing,out,UnaryTemplate.tape i]⟩
def afterBacking {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (backing : List Bool) :=
  RowNativeFieldSkip.savedList ((fields g).take i) backing

theorem coordinate_run {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n)
    (pre tail backing out : List Bool) :
    ∃ r,runFrom machine (budget g i) (input g i pre tail backing out)=some r ∧
      r.final.heads=![pre.length+(prior g i).length,0,out.length,1] ∧
      r.final.tapes=![pre++exactWord g++tail,afterBacking g i backing,out,UnaryTemplate.tape i] ∧
      r.steps=budget g i := by
  have hcount : ((fields g).take i).length=i := by
    rw [List.length_take,fields_length]
    omega
  have hw : (prior g i)++((fields g).drop i).flatMap intWord=exactWord g := by
    rw [prior,←List.flatMap_append,List.take_append_drop,word_fields]
  obtain ⟨base,hb,hf,hs⟩ := RowNativeFieldSkip.list_run pre (((fields g).drop i).flatMap intWord++tail)
    backing out ((fields g).take i)
  rw [hcount] at hb hf hs
  have hsource : pre++(prior g i)++(((fields g).drop i).flatMap intWord++tail)=pre++exactWord g++tail := by
    simp only [←List.append_assoc]
    rw [List.append_assoc pre,hw]
  change runFrom machine (budget g i)
    (RowNativeFieldSkip.cfg 0 (pre++prior g i++(((fields g).drop i).flatMap intWord++tail))
      pre.length backing out i 1)=some base at hb
  rw [hsource] at hb
  change base.final=RowNativeFieldSkip.cfg 3 (pre++prior g i++(((fields g).drop i).flatMap intWord++tail))
    (pre.length+(prior g i).length) (afterBacking g i backing) out i 1 at hf
  rw [hsource] at hf
  let cap : Fin 4 → ℕ := ![0,0,0,i+2]
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config machine cap _ _ base hb
  have he : ZeroPadding.config cap (RowNativeFieldSkip.cfg 0 (pre++exactWord g++tail)
      pre.length backing out i 1)=input g i pre tail backing out := by
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> simp [ZeroPadding.config,cap,RowNativeFieldSkip.cfg,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PCPPQueryField.store,input,
        Fin.addCases,DecompositionSource.Records.template_pad]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs.trans hs⟩
  · rw [rf,hf]
    funext j; fin_cases j <;> rfl
  · rw [rf,hf]
    funext j; fin_cases j <;> simp [ZeroPadding.config,cap,RowNativeFieldSkip.cfg,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PCPPQueryField.store,
      Fin.addCases,DecompositionSource.Records.template_pad]

end NearCubicWires.RepairOrdinary.RowNativeCoordinate
