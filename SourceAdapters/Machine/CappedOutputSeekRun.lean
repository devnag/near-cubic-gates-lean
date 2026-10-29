import SourceAdapters.Machine.CappedOutputScan

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: physical cold-start output-end locator with linear budget. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

def input (source marker : List Bool) (cap : ℕ) : Fin 5 → List Bool :=
  fun i => if i.val=0 then source else if i.val=3 then marker else if i.val=4 then List.replicate cap true else []

theorem boot_run (source marker : List Bool) (cap fuel : ℕ) (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (walk 2 source marker cap 0)=some r) :
    ∃ result, run machine (fuel+2) (input source marker cap)=some result ∧
      result.final=r.final ∧ result.steps=r.steps+2 := by
  have h0 : step machine (initialConfiguration machine (input source marker cap)) =
      some (config 1 source [] marker cap 0 1 0 0) := by
    change some (applyAction (initialConfiguration machine (input source marker cap)) initialAction) = _
    congr 1
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h1 := step_known 1 2 source [] marker cap 0 1 0 0
    .stay .right .stay .stay none (by rfl)
  simp only [written,HeadMove.apply] at h1
  have e1 := runFrom_step machine _ _ r (by rfl) h1 hr
  have e0 := runFrom_step machine _ _ _ (by rfl) h0 e1
  exact ⟨_,e0,rfl,by simp only⟩

theorem seek_run (source marker : List Bool) (cap : ℕ)
    (hm : OutputTracking.Marked source marker) (hcap : source.length ≤ cap) :
    ∃ result, run machine (8*cap+13) (input source marker cap)=some result ∧
      result.final=ready source marker cap := by
  obtain ⟨fuel,hfuel,r,hr,hf,_⟩ := scan_run source marker cap hm hcap
  obtain ⟨result,hresult,hrf,_⟩ := boot_run source marker cap fuel r hr
  have hb : fuel+2 ≤ 8*cap+13 := by omega
  have hmore := run_moreFuel machine (fuel+2) (8*cap+13-(fuel+2)) _ result hresult
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨result,hmore,hrf.trans hf⟩

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
