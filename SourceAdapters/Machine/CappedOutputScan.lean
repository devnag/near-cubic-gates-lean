import SourceAdapters.Machine.CappedOutputEnd

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: locate the true physical tape extent with a paid linear scan. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem scan_run (source marker : List Bool) (cap : ℕ)
    (hm : OutputTracking.Marked source marker) (hcap : source.length ≤ cap) :
    ∃ fuel, fuel ≤ 8*cap+11 ∧ ∃ r,
      runFrom machine fuel (walk 2 source marker cap 0)=some r ∧
      r.final=ready source marker cap ∧ r.steps=fuel := by
  obtain ⟨fuel,hfuel,r,hr,hf,hs⟩ := end_run source marker cap hm
  let stop := source.length-1
  have hstop : stop ≤ cap := by dsimp [stop]; omega
  have hz : ∀ p, stop < p → p ≤ stop+(cap-stop) → readTapeBit marker p=false := by
    intro p hp _
    have hlen : marker.length ≤ p := by have := hm.1; dsimp [stop] at hp; omega
    unfold readTapeBit
    exact List.getD_eq_default _ _ hlen
  obtain ⟨back,hback,hbf,hbs⟩ := backward_run source marker cap stop (cap-stop) hz fuel r hr
  have hsum : stop+(cap-stop)=cap := Nat.add_sub_of_le hstop
  rw [hsum] at hback
  obtain ⟨result,hresult,hrf,hrs⟩ := forward_run source marker cap 0 cap (by omega) _ back hback
  refine ⟨fuel+4*(cap-stop)+4*cap+1,by omega,result,hresult,hrf.trans (hbf.trans hf),?_⟩
  rw [hrs,hbs,hs]

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
