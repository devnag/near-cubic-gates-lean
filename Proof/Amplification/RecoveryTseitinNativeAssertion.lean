import Proof.Amplification.RecoveryTseitinNativeForward
import Proof.Amplification.RecoveryTseitinNativeBodyOutput
import Proof.Hierarchy.HierarchyFixedWord

/-! The original output assertion is an actual const-true node call at the
retained output gate index. Its fixed native descriptor is printed on tape. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Assertion
open LocalBitMultitape RepairOrdinary RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bits : List Bool := PCPPRequestNodeSchema.native (.const true : BooleanNode 0)
theorem bits_original (n : Nat) : bits=PCPPRequestNodeSchema.native (.const true : BooleanNode n) := rfl
def slots (i : Fin 1338) : Fin 1342 :=
  if i=1 then 1339 else if i=1062 then 1340 else i.castAdd 4
def wordSlots : Fin 2→Fin 1342 := ![1340,1341]
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem word_injective : Function.Injective wordSlots := by decide
theorem word_away (i : Fin 1338) (hi : i≠1062) : ∀ j,wordSlots j≠slots i := by
  intro j he
  have hv:=congrArg Fin.val he
  have hb:=i.isLt
  have hn : i.val≠1062:=fun h=>hi (Fin.ext h)
  fin_cases j <;> dsimp only [wordSlots,slots] at hv <;> split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def writer := RecoveryFocus.machine wordSlots (HierarchyFixedWord.machine bits)
noncomputable def body := RecoveryFocus.machine slots Reuse.machine
noncomputable def machine := Composition.machine writer body
def budget (cap : Nat) := 2*bits.length+2+1+(4*cap+7)

theorem local_run (n index : Nat) (out : List Bool) (cap : Nat)
    (hc : coldNodeBudget index (.const true : BooleanNode n) ≤ cap) : ∃ r,
    runFrom Reuse.machine (4*cap+7)
      ⟨Reuse.machine.start,Reuse.heads 0 out.length,Reuse.data n index bits out cap⟩=some r ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input
        [TseitinCNF.positiveUnit (CircuitInputCNF.circuitInputGateVariable n index)]).length ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input
        [TseitinCNF.positiveUnit (CircuitInputCNF.circuitInputGateVariable n index)] ∧
      r.steps ≤ 4*cap+7 := by
  exact Reuse.body_output index (.const true : BooleanNode n) (by trivial) [] [] out cap hc

theorem assertion_run (n index : Nat) (out : List Bool) (cap : Nat)
    (heads : Fin 1342→Nat) (data : Fin 1342→List Bool)
    (hc : coldNodeBudget index (.const true : BooleanNode n) ≤ cap)
    (hw : ∀ j,heads (wordSlots j)=0 ∧ data (wordSlots j)=[])
    (hh : ∀ i,heads (slots i)=Reuse.heads 0 out.length i)
    (hd : ∀ i,i≠1062 → data (slots i)=Reuse.data n index bits out cap i) : ∃ r,
    runFrom machine (budget cap) ⟨machine.start,heads,data⟩=some r ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input
        [TseitinCNF.positiveUnit (CircuitInputCNF.circuitInputGateVariable n index)]).length ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input
        [TseitinCNF.positiveUnit (CircuitInputCNF.circuitInputGateVariable n index)] ∧
      r.steps ≤ budget cap := by
  obtain ⟨printed,hprinted,pt,ph,ps⟩:=HierarchyFixedWord.word_ready bits
  obtain ⟨a,ha,_ac,as_,ah,atapes,akeep⟩:=RecoveryFocus.dock wordSlots word_injective
    (HierarchyFixedWord.machine bits) _ heads data _
    (by intro j; exact (hw j).1) (by intro j; exact (hw j).2) printed hprinted
  have avh : ∀ i,a.final.heads (slots i)=Reuse.heads 0 out.length i := by
    intro i
    by_cases hi : i=1062
    · subst i
      exact (ah 0).trans (ph 0)
    · exact ((akeep (slots i) (word_away i hi)).1).trans (hh i)
  have avt : ∀ i,a.final.tapes (slots i)=Reuse.data n index bits out cap i := by
    intro i
    by_cases hi : i=1062
    · subst i
      exact (atapes 0).trans (congrFun pt 0)
    · exact ((akeep (slots i) (word_away i hi)).2).trans (hd i hi)
  obtain ⟨base,hbase,bh,bt,bs⟩:=local_run n index out cap hc
  obtain ⟨b,hb,_bc,bstep,bheads,btapes,_bkeep⟩:=RecoveryFocus.dock slots slots_injective
    Reuse.machine _ a.final.heads a.final.tapes _ avh avt base hbase
  obtain ⟨r,hr,rh,rt,rs⟩:=join_two writer body _ _ _ a b ha hb
  refine ⟨r,hr,(congrFun rh 1333).trans ((bheads 1333).trans bh),
    (congrFun rt 1333).trans ((btapes 1333).trans bt),?_⟩
  rw [rs,as_,bstep]
  unfold budget
  omega

theorem output_forward : CursorRestore.NoLeft machine (1333 : Fin 1342) := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward wordSlots (HierarchyFixedWord.machine bits) 1333 (by decide)
  · exact CursorRestore.focus_forward slots slots_injective Reuse.machine 1333
      (CursorRestore.composition_forward _ _ _ Reuse.prefix_forward Reuse.erase_forward)

end NearCubicWires.RepairSource.RecoveryTseitinNative.Assertion
