import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout
import Proof.Foundations.OrdinaryTapeEmbedding

/-! Focus a checked run at its actual ambient cursors. This packages only
the transport already proved by run_config; no machine or cost is changed. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RecoveryFocus
theorem dock {t u s : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (p : Machine t s) (fuel : ℕ) (heads : Fin u → ℕ) (data : Fin u → List Bool)
    (src : Configuration t s) (hh : ∀ j,heads (slots j)=src.heads j)
    (ht : ∀ j,data (slots j)=src.tapes j) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel src=some r) :
    ∃ result,runFrom (machine slots p) fuel ⟨src.control,heads,data⟩=some result ∧
      result.final.control=r.final.control ∧ result.steps=r.steps ∧
      (∀ j,result.final.heads (slots j)=r.final.heads j) ∧
      (∀ j,result.final.tapes (slots j)=r.final.tapes j) ∧
      (∀ i,(∀ j,slots j≠i) → result.final.heads i=heads i ∧ result.final.tapes i=data i) := by
  have same : config slots heads data src=(⟨src.control,heads,data⟩ : Configuration u s) :=
    WilliamsSourceCrop.focus_same slots (⟨src.control,heads,data⟩ : Configuration u s) src hh ht
  obtain ⟨result,hresult,hfinal,hsteps⟩ := run_config slots hi p heads data fuel src r hr
  rw [same] at hresult
  refine ⟨result,hresult,by rw [hfinal]; rfl,hsteps,?_,?_,?_⟩
  · intro j
    rw [hfinal]
    simp only [config,pick_slot slots hi]
  · intro j
    rw [hfinal]
    simp only [config,pick_slot slots hi]
  · intro i hn
    have he : ¬∃ j,slots j=i := by rintro ⟨j,hj⟩; exact hn j hj
    rw [hfinal]
    simp only [config,pick,dif_neg he,and_self]

end RecoveryFocus

namespace TapeEmbedding
@[simp] theorem receipt_tapes_old {t e s : ℕ} (eh : Fin e → ℕ) (et : Fin e → List Bool)
    (r : ExecutionReceipt t s) (i : Fin t) :
    (receipt eh et r).final.tapes (i.castAdd e)=r.final.tapes i := by
  simp only [receipt,config,Fin.addCases_left]
@[simp] theorem receipt_tapes_new {t e s : ℕ} (eh : Fin e → ℕ) (et : Fin e → List Bool)
    (r : ExecutionReceipt t s) (i : Fin e) :
    (receipt eh et r).final.tapes (i.natAdd t)=et i := by
  simp only [receipt,config,Fin.addCases_right]
@[simp] theorem receipt_heads_old {t e s : ℕ} (eh : Fin e → ℕ) (et : Fin e → List Bool)
    (r : ExecutionReceipt t s) (i : Fin t) :
    (receipt eh et r).final.heads (i.castAdd e)=r.final.heads i := by
  simp only [receipt,config,Fin.addCases_left]
@[simp] theorem receipt_heads_new {t e s : ℕ} (eh : Fin e → ℕ) (et : Fin e → List Bool)
    (r : ExecutionReceipt t s) (i : Fin e) :
    (receipt eh et r).final.heads (i.natAdd t)=eh i := by
  simp only [receipt,config,Fin.addCases_right]

end TapeEmbedding
end NearCubicWires.RepairOrdinary
