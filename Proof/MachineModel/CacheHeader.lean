import Proof.MachineModel.FinalUnary
import Proof.PCP.PCPPNativeNaturalAppend

/-! Print exactly one native total-count header from the physically produced
raw count. All private heads return, while the cache append cursor is retained. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheHeader
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cap (C : ℕ) (i : Fin 18) := if i=0 ∨ i=17 then 0 else C
def data (C n : ℕ) (i : Fin 18) : List Bool :=
  if i=0 then List.replicate n true else if i=17 then [] else List.replicate C false
def heads (n : ℕ) (i : Fin 19) := if i=(17 : Fin 18).castAdd 1 then (natWord n).length else 0
def input (C n : ℕ) (i : Fin 19) : List Bool :=
  Fin.addCases (data C n) (fun _ : Fin 1=>List.replicate C false) i
def selected (i : Fin 18) : Bool:=decide (i≠17)
noncomputable def machine:=MaskedReset.machine PCPPNativeNaturalAppend.machine selected

theorem header_run (C n : ℕ) (hC : PCPPNativeNaturalAppend.budget n≤C) :
    ∃ output : Fin 18 → List Bool,
      Step machine (2*PCPPNativeNaturalAppend.budget n+2) (fun _=>0) (input C n)
        (heads n) (Fin.addCases output (fun _ : Fin 1=>List.replicate C false)) ∧
      output 17=natWord n := by
  obtain ⟨r,hr,hs,ht,hh,_raw,_rawH⟩:=PCPPNativeNaturalAppend.append_run n []
  have base:Step PCPPNativeNaturalAppend.machine (PCPPNativeNaturalAppend.budget n)
      (fun _=>0) (PCPPNativeNaturalAppend.data n []) r.final.heads r.final.tapes := by
    have hzero:PCPPNativeNaturalAppend.heads []=(fun _=>0):=by
      funext i;simp [PCPPNativeNaturalAppend.heads]
    change runFrom PCPPNativeNaturalAppend.machine _
      ⟨PCPPNativeNaturalAppend.machine.start,PCPPNativeNaturalAppend.heads [],PCPPNativeNaturalAppend.data n []⟩=some r at hr
    rw [hzero] at hr
    exact ⟨r,hr,rfl,rfl,hs⟩
  have padded:=base.pad (cap C)
  have initial:(fun i=>ZeroPadding.pad (cap C i) (PCPPNativeNaturalAppend.data n [] i))=data C n:=by
    funext i
    by_cases h0:i=0
    · subst i;simp [cap,PCPPNativeNaturalAppend.data,data,ZeroPadding.pad_zero]
    by_cases h17:i=17
    · subst i;simp [cap,PCPPNativeNaturalAppend.data,data,ZeroPadding.pad_zero]
    · simp [cap,PCPPNativeNaturalAppend.data,data,h0,h17,ZeroPadding.pad]
  rw [initial] at padded
  have run:=padded.mask selected (by intro i _;rfl) hC
  have hi:(Fin.addCases (fun _ : Fin 18=>0) (fun _ : Fin 1=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (m:=18) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  rw [hi] at run
  let result:=fun i=>ZeroPadding.pad (cap C i) (r.final.tapes i)
  have result17:result 17=natWord n:=by
    simp only [result,cap,Fin.isValue,or_true,↓reduceIte,ZeroPadding.pad_zero,ht,List.nil_append]
  refine ⟨result,run.congr ?_ rfl,result17⟩
  funext i
  refine Fin.addCases (m:=18) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left]
    by_cases hj:j=17
    · subst j
      simp only [selected,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,hh,List.nil_append,heads]
    · have hd:j.castAdd 1≠(17 : Fin 18).castAdd 1:=fun he=>hj (Fin.ext (congrArg (fun x : Fin 19=>x.val) he))
      simp only [selected,ne_eq,hj,not_false_eq_true,decide_true,↓reduceIte,heads,hd]
  · have hj:j=0:=Fin.eq_zero j
    subst hj
    simp only [Fin.addCases_right,heads]
    rfl

end NearCubicWires.ExtDecompositionBatch.CacheHeader
