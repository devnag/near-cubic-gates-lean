import Proof.MachineModel.NativeInitialize

/-! The initialized bank exposes exact native words, including the shared
measured driver, without any prepared native-input premise. -/
namespace NearCubicWires.ExtIncidence.NativeInitializedPorts
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout NativeInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (data : Fin 15→List Bool) (C : ℕ) (source out : List Bool) (i : Fin 128):=
  if i=31 then out else if i=104 then List.replicate C true
  else if i=105 then List.replicate (C+1) false else if i=113 then source
  else ZeroPadding.pad C ((selection i.val).elim [] data)

theorem covers (i : Fin 128) (h31 : i≠31) (h104 : i≠104) (h105 : i≠105) (h113 : i≠113) :
    ∃ j,targets j=i:=by revert i;decide

theorem fields (H : Fin 277→ℕ) (A : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C pos : ℕ) (source out : List Bool)
    (hh : ∀ j,H (ports j)=0) (ha : ∀ j,A (ports j)=NativeFanout.output choice data C j)
    (oh : H (bank 31)=out.length) (oa : A (bank 31)=out)
    (sh : H (bank 113)=pos) (sa : A (bank 113)=source) (i : Fin 128) :
    H (bank i)=extraH pos out i ∧ A (bank i)=word data C source out i:=by
  by_cases h31 : i=31
  · subst i;exact ⟨oh,oa⟩
  by_cases h104 : i=104
  · subst i
    change H (bank 104)=0 ∧ A (bank 104)=List.replicate C true
    have rh:=hh (((0 : Fin 1).natAdd 124).natAdd 15 |>.castAdd 1)
    have ra:=ha (((0 : Fin 1).natAdd 124).natAdd 15 |>.castAdd 1)
    simpa only [ports,NativeFanout.output,Fin.addCases_left,Fin.addCases_right] using And.intro rh ra
  by_cases h105 : i=105
  · subst i
    change H (bank 105)=0 ∧ A (bank 105)=List.replicate (C+1) false
    have rh:=hh ((0 : Fin 1).natAdd (15+(124+1)))
    have ra:=ha ((0 : Fin 1).natAdd (15+(124+1)))
    simpa only [ports,NativeFanout.output,Fin.addCases_right] using And.intro rh ra
  by_cases h113 : i=113
  · subst i
    exact ⟨sh,sa⟩
  obtain ⟨j,hj⟩:=covers i h31 h104 h105 h113
  have rh:=hh ((j.castAdd 1).natAdd 15 |>.castAdd 1)
  have ra:=ha ((j.castAdd 1).natAdd 15 |>.castAdd 1)
  simp only [ports,NativeFanout.output,Fin.addCases_left,Fin.addCases_right] at rh ra
  rw [hj] at rh
  have raw : NativeFanout.word choice data j=(selection i.val).elim [] data:=by
    simp only [NativeFanout.word,choice,hj]
  rw [raw,hj] at ra
  simpa only [extraH,word,h31,h104,h105,h113,↓reduceIte] using And.intro rh ra

theorem initialized {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w pos : ℕ)
    (source out : List Bool) : ∃ H A,
    Step NativeInitialize.machine (budget gs Q w) (heads gs pos out) (input gs Q w source out) H A ∧
      ∀ i,H (bank i)=extraH pos out i ∧
        A (bank i)=word (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w) source out i:=by
  obtain ⟨H,A,run,hh,ha,oh,oa,sh,sa⟩:=initialize_run gs Q w pos source out
  exact ⟨H,A,run,fields H A _ _ _ _ _ hh ha oh oa sh sa⟩

end NearCubicWires.ExtIncidence.NativeInitializedPorts
