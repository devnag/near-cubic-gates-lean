import Proof.Amplification.RecoveryTseitinNativeReadyData

/-! The actual allocated tape bank has the original node-clause consumer view. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def viewData (refs : Fin 3→List Bool) (cap : Nat) (i : Fin 239) : List Bool :=
  if h : i.val<3 then refs ⟨i.val,h⟩ else
  if i=3 then List.replicate cap true else
  if i=4 then List.replicate (cap+1) false else List.replicate cap false

theorem kernel_view_core {z : Nat} (k : Fin 6) (refs : Fin 3→List Bool) (cap : Nat) (out : List Bool)
    (ambient : Configuration 1335 z)
    (href : ∀ j,ambient.tapes (generatedRef (referencePorts (k) j))=refs j ∧
      ambient.heads (generatedRef (referencePorts (k) j))=0)
    (hd : ambient.tapes 17=List.replicate (cap) true)
    (hl : ambient.tapes 18=List.replicate (cap+1) false)
    (hdh : ambient.heads 17=0) (hlh : ambient.heads 18=0)
    (hw : ∀ i,ambient.tapes (kernelWork i)=List.replicate (cap) false ∧
      ambient.heads (kernelWork i)=0)
    (hout : ambient.tapes 1333=out) (houth : ambient.heads 1333=out.length) :
    ∀ i,ambient.tapes (kernelSlots (decide (k=2)) i)=
      RecoveryTseitinClauseAppend.input (viewData refs cap) out (cap) i ∧
      ambient.heads (kernelSlots (decide (k=2)) i)=RecoveryTseitinClauseAppend.heads out.length i := by
  intro i
  rcases i with ⟨_ | _ | _ | _ | _ | v,hk⟩
  · change ambient.tapes (kernelSlots _ ((sourceSlot 0).castAdd 2))=refs 0 ∧
      ambient.heads (kernelSlots _ ((sourceSlot 0).castAdd 2))=0
    rw [kernel_reference]; exact href 0
  · change ambient.tapes (kernelSlots _ ((sourceSlot 1).castAdd 2))=refs 1 ∧
      ambient.heads (kernelSlots _ ((sourceSlot 1).castAdd 2))=0
    rw [kernel_reference]; exact href 1
  · change ambient.tapes (kernelSlots _ ((sourceSlot 2).castAdd 2))=refs 2 ∧
      ambient.heads (kernelSlots _ ((sourceSlot 2).castAdd 2))=0
    rw [kernel_reference]; exact href 2
  · exact ⟨hd,hdh⟩
  · exact ⟨hl,hlh⟩
  · by_cases hs : v < 234
    · let w : Fin 235:=⟨v,by omega⟩
      have he : (⟨v+5,hk⟩ : Fin 241)=(⟨v,by omega⟩ : Fin 236).natAdd 5 := Fin.ext (Nat.add_comm _ _)
      have he' : (⟨v+5,hk⟩ : Fin 241)=(⟨v+5,by omega⟩ : Fin 239).castAdd 2 := Fin.ext rfl
      have hslt : kernelSlots (decide (k=2)) (⟨v+5,hk⟩ : Fin 241)=kernelWork w := by
        rw [he]
        simp only [kernelSlots,Fin.addCases_right,kernelWork,w,if_pos hs]
      have hi : RecoveryTseitinClauseAppend.input (viewData refs cap) out
          (cap) (⟨v+5,hk⟩ : Fin 241)=
          List.replicate (cap) false := by
        rw [he']
        simp only [RecoveryTseitinClauseAppend.input,Fin.addCases_left,viewData]
        rw [dif_neg (by omega)]
        have h3 : (⟨v+5,by omega⟩ : Fin 239)≠3 := by
          intro h; have hv:=congrArg Fin.val h; change v+5=3 at hv; omega
        have h4 : (⟨v+5,by omega⟩ : Fin 239)≠4 := by
          intro h; have hv:=congrArg Fin.val h; change v+5=4 at hv; omega
        rw [if_neg h3,if_neg h4]
      have hh : RecoveryTseitinClauseAppend.heads out.length (⟨v+5,hk⟩ : Fin 241)=0 := by
        rw [he']; simp only [RecoveryTseitinClauseAppend.heads,Fin.addCases_left]
      change ambient.tapes (kernelSlots _ (⟨v+5,hk⟩ : Fin 241))=_ ∧ ambient.heads (kernelSlots _ (⟨v+5,hk⟩ : Fin 241))=_
      rw [hslt,hi,hh]
      exact hw w
    · have hk' : v=234 ∨ v=235 := by omega
      rcases hk' with rfl|rfl
      · exact ⟨hout,houth⟩
      · exact hw 234

end NearCubicWires.RepairSource.RecoveryTseitinNative
