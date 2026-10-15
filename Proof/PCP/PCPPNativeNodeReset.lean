import Proof.PCP.PCPPNativeNodeTyped

/-! A paid reset of every native-node scratch head and the retained row
cache cursor. The original source/output cursors and the three live raw
counters are excluded. One whole-trace padding transports all internal
parser-to-emitter calls without changing their supplied codecs. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeReset
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 119) := decide (i.val=1 ∨ 6 ≤ i.val)
noncomputable def machine := MaskedReset.machine PCPPNativeNodeMachine.machine selected
def caps (F : ℕ) (i : Fin 120) := if 6 ≤ i.val then F else 0
noncomputable def entry {n r : ℕ} (pre tail : List Bool) (base index C F : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool) :=
  ZeroPadding.config (caps F) (Rewind.recording
    (PCPPNativeNodeMachine.entry (originalSource pre tail node) (rowCache projection) pre.length base (base+2*index) C out) 0)

theorem initial_head (pos : ℕ) (out : List Bool) (i : Fin 119) (hi : selected i=true) :
    initialHeads pos out i=0 := by
  have hv : i.val=1 ∨ 6 ≤ i.val := by simpa only [selected,decide_eq_true_eq] using hi
  have h0 : i≠0 := by intro h; subst i; simp at hv
  have h5 : i≠5 := by intro h; subst i; simp at hv
  simp only [initialHeads,h0,h5,ite_false]

theorem initial_work (source queries : List Bool) (base position C : ℕ) (out : List Bool)
    (i : Fin 119) (hi : 6 ≤ i.val) : (initialData source queries base position C out i).length ≤ C+1 := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h2 : i≠2 := by intro h; subst i; simp at hi
  have h3 : i≠3 := by intro h; subst i; simp at hi
  have h4 : i≠4 := by intro h; subst i; simp at hi
  have h5 : i≠5 := by intro h; subst i; simp at hi
  simp only [initialData,h0,h1,h2,h3,h4,h5,ite_false]
  split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega

theorem reset_run {n r : ℕ} (pre tail : List Bool) (base index C F : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool)
    (hC : nodeCapacity base index C projection node)
    (hF : nodeBudget base index C projection node+1 ≤ F) (hCF : C+1 ≤ F) :
    ∃ result,runFrom machine (2*nodeBudget base index C projection node+2)
      (entry pre tail base index C F projection node out)=some result ∧
      result.steps ≤ 2*nodeBudget base index C projection node+2 ∧
      nodeResult pre tail base index C projection node out
        (fun i => result.final.heads (i.castAdd 1)) (fun i => result.final.tapes (i.castAdd 1)) ∧
      result.final.heads 1=0 ∧
      (∀ i,6 ≤ i.val → result.final.heads i=0 ∧ (result.final.tapes i).length ≤ F) := by
  obtain ⟨raw,hr,rs,meaning⟩ := typed_node_run pre tail base index C projection node out hC
  have hh : ∀ i,selected i=true → raw.final.heads i ≤ raw.steps := by
    intro i hi
    have head := initial_head pre.length out i hi
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 i
    change raw.final.heads i ≤ initialHeads pre.length out i+raw.steps at h
    simpa only [head,Nat.zero_add] using h
  obtain ⟨reset,hreset,rf,rsteps,_⟩ := MaskedReset.reset_run
    PCPPNativeNodeMachine.machine selected _ _ raw hr hh
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine (caps F) _ _ reset hreset
  have more := runFrom_moreFuel machine _
    (2*nodeBudget base index C projection node+2-(2*raw.steps+2)) _ result hresult
  rw [Nat.add_sub_of_le (by omega : 2*raw.steps+2 ≤ 2*nodeBudget base index C projection node+2)] at more
  rcases meaning with ⟨r0,rh0,r1,r5,rh5,retained⟩
  refine ⟨result,more,by rw [resultSteps,rsteps]; omega,?_,?_,?_⟩
  · rw [resultFinal,rf]
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · change ZeroPadding.pad 0 (raw.final.tapes 0)=_
      simpa only [ZeroPadding.pad_zero] using r0
    · exact rh0
    · change ZeroPadding.pad 0 (raw.final.tapes 1)=_
      simpa only [ZeroPadding.pad_zero] using r1
    · change ZeroPadding.pad 0 (raw.final.tapes 5)=_
      simpa only [ZeroPadding.pad_zero] using r5
    · exact rh5
    · intro i
      fin_cases i
      · change raw.final.heads 2=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 2)=List.replicate base true
        simpa [ZeroPadding.pad_zero] using retained 0
      · change raw.final.heads 3=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 3)=List.replicate (base+2*index) true
        simpa [ZeroPadding.pad_zero] using retained 1
      · change raw.final.heads 4=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 4)=List.replicate C true
        simpa [ZeroPadding.pad_zero] using retained 2
  · rw [resultFinal,rf]
    rfl
  · intro i hi
    rw [resultFinal,rf]
    by_cases h119 : i.val < 119
    · let j : Fin 119 := ⟨i.val,h119⟩
      have hij : i=j.castAdd 1 := Fin.ext rfl
      have hsel : selected j=true := by simp only [selected,decide_eq_true_eq]; exact Or.inr hi
      have hc := initial_work (originalSource pre tail node) (rowCache projection) base (base+2*index) C out j hi
      have ht := PCPSerializerReuse.tape_support PCPPNativeNodeMachine.machine _ _ raw hr j (C+1) 0
        (by change initialHeads pre.length out j ≤ 0; rw [initial_head pre.length out j hsel])
        (hc.trans (le_max_left _ _))
      have hcap : caps F (j.castAdd 1)=F := by simp only [caps,Fin.val_castAdd]; exact if_pos hi
      rw [hij]
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left,hsel,ite_true,hcap,ZeroPadding.pad_length]
      refine ⟨True.intro,max_le le_rfl ?_⟩
      simp only [Nat.zero_add] at ht
      exact ht.trans (max_le hCF (by omega))
    · have hij : i=(0 : Fin 1).natAdd 119 := Fin.ext (by change i.val=119; omega)
      rw [hij]
      change 0=0 ∧ (ZeroPadding.pad F (List.replicate raw.steps false)).length ≤ F
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact ⟨rfl,max_le le_rfl (by omega)⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeReset
