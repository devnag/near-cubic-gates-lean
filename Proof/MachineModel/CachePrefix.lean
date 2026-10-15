import Proof.MachineModel.CacheStart

/-! The physical total finalizer feeds exactly one native cache header.
The original total template and incidence scratch stay outside the header bank. -/
namespace NearCubicWires.ExtDecompositionBatch.CachePrefix
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 19) : Fin 21:=i.natAdd 2
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg (fun x : Fin 21=>x.val) h
  exact Fin.ext (by simp only [slots,Fin.val_natAdd] at hv;omega)
def heads (n : ℕ) (i : Fin 21):=
  if i=0 then 1 else if i=19 then (natWord n).length else 0
noncomputable def headerMachine:=RecoveryFocus.machine slots CacheHeader.machine
noncomputable def machine:=Composition.machine CacheStart.machine headerMachine

theorem header_run (C n : ℕ) (hC:PCPPNativeNaturalAppend.budget n≤C) :
    ∃ A:Fin 21 → List Bool,
      Step headerMachine (2*PCPPNativeNaturalAppend.budget n+2)
        CacheStart.totalHeads (CacheStart.unaryData C n) (heads n) A ∧
      A 0=UnaryTemplate.tape n ∧ A 1=List.replicate n false ∧
      A 19=natWord n ∧ A 20=List.replicate C false := by
  obtain ⟨output,core,hout⟩:=CacheHeader.header_run C n hC
  have ih:∀j,CacheStart.totalHeads (slots j)=0:=by
    intro j
    have hj:slots j≠0:=by intro h;have hv:=congrArg (fun x : Fin 21=>x.val) h;simp [slots] at hv
    simp [CacheStart.totalHeads,hj]
  have ia:∀j,CacheStart.unaryData C n (slots j)=CacheHeader.input C n j:=by
    intro j;fin_cases j <;>
      simp [slots,CacheStart.unaryData,CacheStart.totalData,CacheHeader.input,CacheHeader.data,
        Fin.addCases,Fin.castLT]
  have run:=core.dock slots slots_injective CacheStart.totalHeads (CacheStart.unaryData C n) ih ia
  have he:dockH slots CacheStart.totalHeads (CacheHeader.heads n)=heads n:=by
    funext i
    refine Fin.addCases (m:=2) (n:=19) (fun j=>?_) (fun j=>?_) i
    · have other:∀k,slots k≠j.castAdd 19:=by
        intro k h
        have hv:=congrArg (fun x : Fin 21=>x.val) h
        have hj:=j.isLt
        simp only [slots,Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      rw [dockH_other slots _ _ _ other]
      fin_cases j <;> rfl
    · change dockH slots CacheStart.totalHeads (CacheHeader.heads n) (slots j)=_
      rw [dockH_slot slots slots_injective]
      by_cases hj:j=17
      · subst j;rfl
      · have h0:slots j≠0:=by intro h;have hv:=congrArg (fun x : Fin 21=>x.val) h;simp [slots] at hv
        have h19:slots j≠19:=by
          intro h;apply hj;apply Fin.ext
          have hv:=congrArg (fun x : Fin 21=>x.val) h
          simp only [slots,Fin.val_natAdd] at hv
          omega
        change CacheHeader.heads n j=heads n (slots j)
        simp [CacheHeader.heads,heads,hj,h0,h19]
  let out:Fin 19 → List Bool:=fun i=>Fin.addCases output (fun _ : Fin 1=>List.replicate C false) i
  refine ⟨install slots (CacheStart.unaryData C n) out,run.congr he rfl,?_,?_,?_,?_⟩
  · rw [install_other slots _ _ 0 (by intro j h;have hv:=congrArg (fun x : Fin 21=>x.val) h;simp [slots] at hv)]
    rfl
  · rw [install_other slots _ _ 1 (by intro j h;have hv:=congrArg (fun x : Fin 21=>x.val) h;simp [slots] at hv;omega)]
    rfl
  · have h:=install_slot slots slots_injective (CacheStart.unaryData C n) out 17
    apply h.trans
    change Fin.addCases output (fun _ : Fin 1=>List.replicate C false) ((17 : Fin 18).castAdd 1)=natWord n
    rw [Fin.addCases_left]
    exact hout
  · have h:=install_slot slots slots_injective (CacheStart.unaryData C n) out 18
    exact h.trans (by rfl)

theorem prefix_run (C n : ℕ) (hn:n+2≤C) (hC:PCPPNativeNaturalAppend.budget n≤C) :
    ∃ A:Fin 21 → List Bool,
      Step machine (5*n+2*PCPPNativeNaturalAppend.budget n+18)
        (CacheStart.inputHeads n) (CacheStart.input C n) (heads n) A ∧
      A 0=UnaryTemplate.tape n ∧ A 1=List.replicate n false ∧
      A 19=natWord n ∧ A 20=List.replicate C false := by
  obtain ⟨A,header,h0,h1,h19,h20⟩:=header_run C n hC
  have run:=(CacheStart.start_run C n hn).seq header
  have time:5*n+15+1+(2*PCPPNativeNaturalAppend.budget n+2)=
      5*n+2*PCPPNativeNaturalAppend.budget n+18:=by omega
  rw [time] at run
  exact ⟨A,run,h0,h1,h19,h20⟩

end NearCubicWires.ExtDecompositionBatch.CachePrefix
