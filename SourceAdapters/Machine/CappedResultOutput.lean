import SourceAdapters.Machine.CappedResultChoice

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: both observable capped-run outcomes at a single linear bound. -/
namespace NearCubicGates.Adapters.Machine.Capped.ResultWriter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem result_run (source marker : List Bool) (cap : ℕ) (status : Bool)
    (hm : OutputTracking.Marked source marker) (hcap : status=true → source.length ≤ cap) :
    ∃ result, run machine (12*cap+19) (input source marker cap status)=some result ∧
      result.final.tapes 1=frame (if status then true::frame source else false::frame []) := by
  cases status with
  | false =>
    obtain ⟨r,hr,hout⟩ := failure_run (input source marker cap false) (by rfl)
    obtain ⟨result,hresult,ht⟩ := selected_run 2 (Or.inr rfl) _ 5 r (by rfl) hr
    have hmore := run_moreFuel machine 7 (12*cap+19-7) _ result hresult
    have hb : 7 ≤ 12*cap+19 := by omega
    rw [Nat.add_sub_of_le hb] at hmore
    refine ⟨result,hmore,?_⟩
    rw [ht]
    exact hout
  | true =>
    obtain ⟨r,hr,hout⟩ := success_run source marker cap true hm (hcap rfl)
    obtain ⟨result,hresult,ht⟩ := selected_run 1 (Or.inl rfl) _ (12*cap+17) r (by rfl) hr
    refine ⟨result,hresult,?_⟩
    rw [ht]
    exact hout

end NearCubicGates.Adapters.Machine.Capped.ResultWriter
