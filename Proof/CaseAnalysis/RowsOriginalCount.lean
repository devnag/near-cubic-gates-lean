import Proof.CaseAnalysis.CaseTwoMetadata
import Proof.CaseAnalysis.CapacityPower
import Proof.Circuits.DecompositionCountDrivers
import Proof.MachineModel.Layout

/-! The original source header physically produces the clause count once.
Both raw and template forms come from that same actual clauseBits field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCount
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (A : Fin 19→List Bool) : Fin 74→List Bool:=Fin.addCases (m:=56) (n:=18) (motive:=fun _=>List Bool)
  (CloseoutCaseTwo.Metadata.input A) (fun _ : Fin 18=>[])
def heads (H : Fin 19→ℕ) : Fin 74→ℕ:=Fin.addCases (m:=56) (n:=18) (motive:=fun _=>ℕ)
  (CloseoutCaseTwo.Metadata.heads H) (fun _ : Fin 18=>0)
def copySlots : Fin 3→Fin 74:=![48,56,57]
def powerSlots (j : Fin 17) : Fin 74:=if j=0 then 56 else ⟨j.val+57,by omega⟩
theorem power_injective : Function.Injective powerSlots := by
  intro i j h
  have hv:=congrArg Fin.val h
  simp only [powerSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all only [Fin.ext_iff] <;> omega
theorem power_above (j : Fin 17) : 56≤(powerSlots j).val := by
  unfold powerSlots;split_ifs <;>dsimp <;>omega
noncomputable def first:=TapeEmbedding.machine 18 CloseoutCaseTwo.Metadata.machine
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def power:=RecoveryFocus.machine powerSlots RepairSource.CloseoutCapacity.Power.machine
noncomputable def machine:=Composition.machine first (Composition.machine copy power)
def budget {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit):=
  CloseoutCaseTwo.Metadata.budget r p+1+(2*p.clauseBits+6+1+RepairSource.CloseoutCapacity.Power.budget p.clauseBits)

theorem run_with_systematic {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (H : Fin 19→ℕ) (A : Fin 19→List Bool) (h0 : H 0=0) (h13 : H 13=1)
    (a0 : A 0=pcppOutput r p) (a13 : A 13=UnaryTemplate.tape r.arity) :
    ∃ out,Step machine (budget r p) (heads H) (input A) (heads H) out ∧
      (∀ j : Fin 19,out (j.castAdd 55)=A j) ∧
      out 70=UnaryTemplate.tape (2^p.clauseBits) ∧ out 72=List.replicate (2^p.clauseBits) true ∧
      out 28=UnaryTemplate.tape p.systematicBits := by
  obtain ⟨r0,hr0,_rs0,rh0,cache,_ar1,_ar2,sys,_aux,clause⟩:=
    CloseoutCaseTwo.Metadata.metadata_run r p H A h0 h13 a0 a13
  have raw:=Step.of_run hr0 rh0 rfl
  have stage0:=raw.embed (fun _ : Fin 18=>0) (fun _ : Fin 18=>[])
  let mid0 : Fin 74→List Bool:=Fin.addCases (m:=56) (n:=18) (motive:=fun _=>List Bool)
    r0.final.tapes (fun _ : Fin 18=>[])
  obtain ⟨rc,hrc,tc,hc,_sc⟩:=DecompositionCountDrivers.template_ready false false p.clauseBits
  have cstep:=Step.of_run hrc (funext hc) tc
  have hcopy : ∀ j,heads H (copySlots j)=0 := by intro j;fin_cases j <;>rfl
  have ccall:=cstep.dock copySlots (by decide) (heads H) mid0 hcopy (by
    intro j;fin_cases j
    · exact clause
    · rfl
    · rfl)
  have cready:=ccall.congr (dockH_existing copySlots _ _ hcopy) rfl
  let mid1:=install copySlots mid0 ![UnaryTemplate.tape p.clauseBits,
    UWalkUnary.output false false p.clauseBits,List.replicate (p.clauseBits+2) false]
  obtain ⟨B,rb,nraw,ntemplate⟩:=RepairSource.CloseoutCapacity.Power.power_run p.clauseBits
  obtain ⟨rp,hrp,tp,hp,_sp⟩:=rb
  have pstep:=Step.of_run hrp (funext hp) tp
  have hpower : ∀ j,heads H (powerSlots j)=0 := by
    intro j
    have hj:=power_above j
    simp [heads,Fin.addCases,show ¬(powerSlots j).val<56 by omega]
  have pcall:=pstep.dock powerSlots power_injective (heads H) mid1 hpower (by
    intro j
    by_cases hj : j=0
    · subst j
      exact install_slot copySlots (by decide) _ _ 1
    · rw [show RepairSource.CloseoutCapacity.Power.input p.clauseBits j=[] by
        simp [RepairSource.CloseoutCapacity.Power.input,show j.val≠0 from fun h=>hj (Fin.ext h)]]
      dsimp only [mid1]
      rw [install_other copySlots _ _ _ (by
        intro k he
        have hv:=congrArg Fin.val he
        fin_cases k <;>simp [copySlots,powerSlots,hj] at hv)]
      simp [mid0,Fin.addCases,powerSlots,hj])
  have pready:=pcall.congr (dockH_existing powerSlots _ _ hpower) rfl
  refine ⟨_,stage0.seq (cready.seq pready),?_,?_,?_,?_⟩
  · intro j
    rw [install_other powerSlots _ _ _ (by
      intro k he
      have hv:=congrArg Fin.val he
      have hk:=power_above k
      simp only [Fin.val_castAdd] at hv;omega)]
    dsimp only [mid1]
    rw [install_other copySlots _ _ _ (by
      intro k he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      fin_cases k <;>simp [copySlots] at hv <;>omega)]
    exact (Fin.addCases_left (j.castAdd 37)).trans (cache j)
  · exact (install_slot powerSlots power_injective _ _ 13).trans ntemplate
  · exact (install_slot powerSlots power_injective _ _ 15).trans nraw

  · rw [install_other powerSlots _ _ _ (by
      intro k he
      have hv:=congrArg Fin.val he
      have hk:=power_above k
      change (powerSlots k).val=28 at hv
      omega)]
    dsimp only [mid1]
    rw [install_other copySlots _ _ _ (by decide)]
    exact sys

theorem run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (H : Fin 19→ℕ) (A : Fin 19→List Bool) (h0 : H 0=0) (h13 : H 13=1)
    (a0 : A 0=pcppOutput r p) (a13 : A 13=UnaryTemplate.tape r.arity) :
    ∃ out,Step machine (budget r p) (heads H) (input A) (heads H) out ∧
      (∀ j : Fin 19,out (j.castAdd 55)=A j) ∧
      out 70=UnaryTemplate.tape (2^p.clauseBits) ∧ out 72=List.replicate (2^p.clauseBits) true := by
  obtain ⟨out,hr,hcache,htemplate,hraw,_hsystematic⟩ :=
    run_with_systematic r p H A h0 h13 a0 a13
  exact ⟨out,hr,hcache,htemplate,hraw⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCount
