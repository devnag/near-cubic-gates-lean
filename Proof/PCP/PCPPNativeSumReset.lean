import Proof.PCP.PCPPNativeSumAppend
import Proof.PCP.PCPSerializerTapeSupport
import Proof.MachineModel.OrdinaryMaskedReset

/-! Reset only the native sum appender's bounded local heads. The live
descriptor cursor and the two retained input counters are excluded. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSumReset
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 21) := decide (2 ≤ i.val ∧ i.val < 20)
noncomputable def machine := MaskedReset.machine PCPPNativeSumAppend.machine selected
def caps (C : ℕ) (i : Fin 22) : ℕ := if 2 ≤ i.val ∧ i.val < 20 ∨ i.val=21 then C else 0
noncomputable def entry (base index C : ℕ) (out : List Bool) :=
  ZeroPadding.config (caps C) (Rewind.recording (PCPPNativeSumAppend.entry base index out) 0)

theorem local_initial (base index : ℕ) (out : List Bool) (i : Fin 21)
    (hi : 2 ≤ i.val ∧ i.val < 20) :
    (PCPPNativeSumAppend.entry base index out).heads i=0 ∧
      (PCPPNativeSumAppend.entry base index out).tapes i=[] := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h20 : i≠20 := by intro h; subst i; simp at hi
  simp only [PCPPNativeSumAppend.entry,PCPPNativeSumAppend.data,
    PCPPNativeSumAppend.heads,h0,h1,h20,ite_false,and_self]

theorem reset_run (base index C : ℕ) (out : List Bool)
    (hC : PCPPNativeSumAppend.budget base index+1 ≤ C) :
    ∃ r,runFrom machine (2*PCPPNativeSumAppend.budget base index+2)
      (entry base index C out)=some r ∧
      r.steps ≤ 2*PCPPNativeSumAppend.budget base index+2 ∧
      r.final.tapes 20=out++RepairRepresentation.natWord ((base+index)) ∧
      r.final.heads 20=(out++RepairRepresentation.natWord ((base+index))).length ∧
      r.final.tapes 0=List.replicate base true ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=List.replicate index true ∧ r.final.heads 1=0 ∧
      (∀ i,2 ≤ i.val ∧ i.val < 20 ∨ i.val=21 →
        r.final.heads i=0 ∧ (r.final.tapes i).length ≤ C) := by
  obtain ⟨raw,hr,rs,rt,rh,r0,rh0,r1,rh1⟩ := PCPPNativeSumAppend.sum_append_run base index out
  have hh : ∀ i,selected i=true → raw.final.heads i ≤ raw.steps := by
    intro i hi
    have hc := (local_initial base index out i (by simpa only [selected,decide_eq_true_eq] using hi)).1
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 i
    simpa only [hc,Nat.zero_add] using h
  obtain ⟨reset,hreset,rf,rsteps,_⟩ := MaskedReset.reset_run
    PCPPNativeSumAppend.machine selected _ _ raw hr hh
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine
    (caps C) _ _ reset hreset
  have runBound := runFrom_moreFuel machine _
    (2*PCPPNativeSumAppend.budget base index+2-(2*raw.steps+2)) _ result hresult
  rw [Nat.add_sub_of_le (by omega : 2*raw.steps+2 ≤
    2*PCPPNativeSumAppend.budget base index+2)] at runBound
  refine ⟨result,runBound,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [resultSteps,rsteps]; omega
  · rw [resultFinal,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 20)=_
    simpa only [ZeroPadding.pad_zero] using rt
  · rw [resultFinal,rf]
    exact rh
  · rw [resultFinal,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 0)=_
    simpa only [ZeroPadding.pad_zero] using r0
  · rw [resultFinal,rf]
    exact rh0
  · rw [resultFinal,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 1)=_
    simpa only [ZeroPadding.pad_zero] using r1
  · rw [resultFinal,rf]
    exact rh1
  · intro i hi
    rw [resultFinal,rf]
    rcases hi with hi | hi
    · let j : Fin 21 := ⟨i.val,by omega⟩
      have hij : i=j.castAdd 1 := Fin.ext rfl
      rw [hij]
      have hj : 2 ≤ j.val ∧ j.val < 20 := hi
      have hc := local_initial base index out j hj
      have ht := PCPSerializerReuse.tape_support PCPPNativeSumAppend.machine _ _ raw hr j 0 0
        (by rw [hc.1]) (by rw [hc.2]; simp)
      have hcap : caps C (j.castAdd 1)=C := by simp [caps,j,hi]
      have hsel : selected j=true := by simp only [selected,decide_eq_true_eq]; exact hj
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left,hsel,
        ite_true,hcap,ZeroPadding.pad_length]
      refine ⟨True.intro,max_le le_rfl ?_⟩
      simp only [Nat.zero_add,max_eq_right (Nat.zero_le _)] at ht
      omega
    · have hij : i=(0 : Fin 1).natAdd 21 := Fin.ext hi
      rw [hij]
      change 0=0 ∧ (ZeroPadding.pad C (List.replicate raw.steps false)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact ⟨rfl,max_le le_rfl (by omega)⟩

end NearCubicWires.RepairOrdinary.PCPPNativeSumReset
