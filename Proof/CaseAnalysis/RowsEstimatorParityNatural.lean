import Proof.CaseAnalysis.RowsEstimatorParityCapacity
import Proof.PCP.PCPPNativeFrame
import Proof.Supplier.EquationRowForward

/-! Actual canonical native naturals fit the local arity work bank, including their framing and reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Natural
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=AppendOutputFrame.machine EquationHeaderAppend.machine 17
def source (n : ℕ) : Fin 22→List Bool:=fun i=>if i=0 then List.replicate n true else []
def input (q n : ℕ) : Fin 22→List Bool:=fun i=>ZeroPadding.pad (Capacity.value q) (source n i)
def budget (n : ℕ):=2*EquationHeaderAppend.budget n+4*(natWord n).length+7

theorem input_eq (n : ℕ) : AppendOutputFrame.input (EquationHeaderAppend.tapes n [])=source n := by
  funext i;fin_cases i <;>rfl

theorem budget_fit (q n : ℕ) (hn:n≤q) : budget n+1≤Capacity.value q := by
  have hw:natBitLength n≤n+1:=Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  have hsq:n*n≤q*q:=Nat.mul_self_le_mul_self hn
  simp only [budget,EquationHeaderAppend.budget,DecompositionSource.natWord_length,Capacity.value]
  nlinarith

theorem native_run (q n : ℕ) (hn:n≤q) : ∃ out,
    ClockJoin.ReadyRun machine (budget n) (input q n) out ∧
      out 20=ZeroPadding.pad (Capacity.value q) (frame (natWord n)) ∧
      out 17=ZeroPadding.pad (Capacity.value q) (natWord n) ∧
      (∀ i,(out i).length=Capacity.value q) := by
  obtain ⟨base,hb,bword,bhead,_b1,_bh1,bs⟩:=EquationHeaderAppend.append_run n []
  have he:EquationHeaderAppend.entry n []=
      initialConfiguration EquationHeaderAppend.machine (EquationHeaderAppend.tapes n []):=by
    apply configuration_ext
    · rfl
    · funext i;simp [EquationHeaderAppend.entry,EquationHeaderAppend.heads,initialConfiguration]
    · rfl
  rw [he] at hb
  obtain ⟨framed,hf,word,heads,_old,steps⟩:=PCPPNativeFrame.frame_run EquationHeaderAppend.machine 17
    EquationRowRaw.header_append_forward _ (EquationHeaderAppend.tapes n []) base hb (natWord n)
    (by simpa only [List.nil_append] using bword) (by simpa only [List.nil_append] using bhead)
  have ht:2*base.steps+4*(natWord n).length+7≤budget n:=by unfold budget;omega
  have more:=run_moreFuel machine _ (budget n-(2*base.steps+4*(natWord n).length+7)) _ framed hf
  rw [Nat.add_sub_of_le ht,input_eq] at more
  have hfit:=budget_fit q n hn
  have small:=RecoveryTapeSupport.run_support machine _ _ framed more (Capacity.value q) 0
    (by intros;exact Nat.zero_le _) (by
      intro i
      change (source n i).length≤ max (Capacity.value q) 0
      rw [max_eq_left (Nat.zero_le _)]
      unfold source
      split_ifs
      · simp only [List.length_replicate]
        exact hn.trans (by unfold Capacity.value;nlinarith)
      · simp)
  have bounded (i : Fin 22):(framed.final.tapes i).length≤Capacity.value q:=by
    have fs':framed.steps+1≤Capacity.value q:=by
      have hs:=runFrom_steps_le machine _ _ framed more
      omega
    simpa only [Nat.zero_add,max_eq_left fs'] using small i
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config machine (fun _=>Capacity.value q) _ _ framed more
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rs.le.trans (runFrom_steps_le machine _ _ framed more)⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact heads i
  · rw [rf]
    change ZeroPadding.pad (Capacity.value q) (framed.final.tapes 20)=_
    exact congrArg (ZeroPadding.pad (Capacity.value q)) word
  · rw [rf]
    change ZeroPadding.pad (Capacity.value q) (framed.final.tapes 17)=_
    exact congrArg (ZeroPadding.pad (Capacity.value q)) ((_old 17).trans (by simpa only [List.nil_append] using bword))
  · intro i;rw [rf]
    change (ZeroPadding.pad (Capacity.value q) (framed.final.tapes i)).length=_
    rw [ZeroPadding.pad_length,max_eq_left (bounded i)]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Natural
