import Proof.CaseAnalysis.WitnessSupportDock
import Proof.Foundations.OrdinaryTapeRenaming

/-! Static exchange of the last two labels restores the original repeat
counter alias while putting retained support last. No tape movement runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout (t : ℕ) : Fin (t+1+1) ≃ Fin (t+1+1):=
  Equiv.swap ⟨t,by omega⟩ ⟨t+1,by omega⟩

theorem old (t : ℕ) (i : Fin t) :
    (layout t).symm ((i.castAdd 1).castAdd 1)=(i.castAdd 1).castAdd 1:=by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h;have hv:=congrArg Fin.val h;change i.val=t at hv;omega
  · intro h;have hv:=congrArg Fin.val h;change i.val=t+1 at hv;omega

theorem exchange {t : ℕ} {α : Type} (base : Fin t→α) (a b : α) :
    lift (lift base a) b ∘ (layout t).symm=lift (lift base b) a:=by
  funext i
  refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j
    · intro k
      simp only [Function.comp_apply,old,lift,Fin.addCases_left]
    · intro k
      have hk:k=(0 : Fin 1):=Subsingleton.elim _ _
      subst k
      have h:(layout t).symm (((0 : Fin 1).natAdd t).castAdd 1)=(0 : Fin 1).natAdd (t+1):=
        Equiv.swap_apply_left _ _
      simp only [Function.comp_apply,h,lift,Fin.addCases_left,Fin.addCases_right]
  · intro j
    have hj:j=(0 : Fin 1):=Subsingleton.elim _ _
    subst j
    have h:(layout t).symm ((0 : Fin 1).natAdd (t+1))=((0 : Fin 1).natAdd t).castAdd 1:=
      Equiv.swap_apply_right _ _
    simp only [Function.comp_apply,h,lift,Fin.addCases_left,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
