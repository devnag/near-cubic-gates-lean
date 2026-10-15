import Proof.MachineModel.NativeMasterBounds

/-! One whole ordinary run measures the actual cache, produces every static
word and C, then physically initializes the native bank. -/
namespace NearCubicWires.ExtIncidence.NativeInitialize
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraH (pos : ℕ) (out : List Bool) (i : Fin 128):=
  if i=31 then out.length else if i=113 then pos else 0
def extraA (source out : List Bool) (i : Fin 128):=
  if i=31 then out else if i=113 then source else []
noncomputable def first:=TapeEmbedding.machine 128 NativeMaster.machine
noncomputable def machine:=Composition.machine first NativeFanoutLayout.machine
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) (pos : ℕ) (out : List Bool):=
  Fin.addCases (m:=149) (n:=128) (motive:=fun _=>ℕ) (NativeMaster.heads gs) (extraH pos out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (source out : List Bool):=
  Fin.addCases (m:=149) (n:=128) (motive:=fun _=>List Bool) (NativeMaster.input gs Q w) (extraA source out)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  NativeMaster.budget gs Q w+1+(2*NativeMeasured.capacity gs Q w+4)

theorem initialize_run {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w pos : ℕ)
    (source out : List Bool) : ∃ H O,
    Step machine (budget gs Q w) (heads gs pos out) (input gs Q w source out) H O ∧
      (∀ j,H (ports j)=0) ∧
      (∀ j,O (ports j)=NativeFanout.output choice (NativeMaster.words gs Q w)
        (NativeMeasured.capacity gs Q w) j) ∧
      H (bank 31)=out.length ∧ O (bank 31)=out ∧
      H (bank 113)=pos ∧ O (bank 113)=source:=by
  obtain ⟨H,A,start,hh,ha,ch,ca⟩:=NativeMaster.master_run gs Q w
  have firstRun:=start.embed (extraH pos out) (extraA source out)
  let H' : Fin 277→ℕ:=Fin.addCases (m:=149) (n:=128) (motive:=fun _=>ℕ) H (extraH pos out)
  let A' : Fin 277→List Bool:=Fin.addCases (m:=149) (n:=128) (motive:=fun _=>List Bool) A (extraA source out)
  have destH (j : Fin 124) : H' (bank (targets j))=0:=by
    have n104 : targets j≠104:=by revert j;decide
    have n31 : targets j≠31:=by revert j;decide
    have n113 : targets j≠113:=by revert j;decide
    simp only [H',bank,if_neg n104,Fin.addCases_right,extraH,if_neg n31,if_neg n113]
  have destA (j : Fin 124) : A' (bank (targets j))=[]:=by
    have n104 : targets j≠104:=by revert j;decide
    have n31 : targets j≠31:=by revert j;decide
    have n113 : targets j≠113:=by revert j;decide
    simp only [A',bank,if_neg n104,Fin.addCases_right,extraA,if_neg n31,if_neg n113]
  have readyH : ∀ j,H' (ports j)=0:=by
    intro j
    refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
      · simp only [ports,sources,H',Fin.addCases_left];exact hh a
      · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simpa only [ports,Fin.addCases_left,Fin.addCases_right] using destH a
        · simp only [ports,Fin.addCases_left,Fin.addCases_right]
          exact ch
    · simp only [ports,Fin.addCases_right]
      change H' ((105 : Fin 128).natAdd 149)=0
      simp only [H',Fin.addCases_right];rfl
  have readyA : ∀ j,A' (ports j)=NativeFanout.input (NativeMaster.words gs Q w)
      (NativeMeasured.capacity gs Q w) j:=by
    intro j
    refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
      · simp only [ports,sources,A',NativeFanout.input,Fin.addCases_left];exact ha a
      · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simpa only [ports,NativeFanout.input,Fin.addCases_left,Fin.addCases_right] using destA a
        · simp only [ports,NativeFanout.input,Fin.addCases_left,Fin.addCases_right]
          exact ca
    · simp only [ports,NativeFanout.input,Fin.addCases_right]
      change A' ((105 : Fin 128).natAdd 149)=[]
      simp only [A',Fin.addCases_right];rfl
  obtain ⟨r,hr,rh,rt,_rs⟩:=(NativeFanout.ready choice (NativeMaster.words gs Q w)
    (NativeMeasured.capacity gs Q w) (NativeMaster.words_fit gs Q w)).focus_at
      ports ports_injective H' A' readyA readyH
  have whole:=firstRun.seq (Step.of_run hr rh rt)
  let O:=install ports A' (NativeFanout.output choice (NativeMaster.words gs Q w)
    (NativeMeasured.capacity gs Q w))
  refine ⟨H',O,whole,readyH,?_,?_,?_,?_,?_⟩
  · intro j;exact install_slot ports ports_injective A' _ j
  · change H' ((31 : Fin 128).natAdd 149)=out.length
    simp only [H',Fin.addCases_right];rfl
  · rw [show O (bank 31)=A' (bank 31) from install_other ports A' _ _ (by decide)]
    change A' ((31 : Fin 128).natAdd 149)=out
    simp only [A',Fin.addCases_right];rfl
  · change H' ((113 : Fin 128).natAdd 149)=pos
    simp only [H',Fin.addCases_right];rfl
  · rw [show O (bank 113)=A' (bank 113) from install_other ports A' _ _ (by decide)]
    change A' ((113 : Fin 128).natAdd 149)=source
    simp only [A',Fin.addCases_right];rfl

end NearCubicWires.ExtIncidence.NativeInitialize
