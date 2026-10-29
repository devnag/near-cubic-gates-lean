import SourceAdapters.Machine.CappedOutputFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: four actual writes place one nested-frame payload bit. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def blockStart (source marker : List Bool) (k mh : ℕ) (tail : List Bool) : Configuration 4 8 :=
  config 0 source (List.replicate (4*k+6) false ++ tail) marker k (4*k+5) mh

def blockEnd (source marker : List Bool) (k mh : ℕ) (bit : Bool) (tail : List Bool) : Configuration 4 8 :=
  config (if k=0 then 4 else 0) source
    (List.replicate (4*k+2) false ++ true::true::true::bit::tail) marker (k-1) (4*k+1) mh

theorem block_run (source marker : List Bool) (k mh : ℕ) (bit : Bool) (tail : List Bool)
    (hb : readTapeBit source k=bit) (fuel : ℕ) (r : ExecutionReceipt 4 8)
    (hr : runFrom machine fuel (blockEnd source marker k mh bit tail)=some r) :
    ∃ result, runFrom machine (fuel+4) (blockStart source marker k mh tail)=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4 := by
  have h0 := step_known 0 1 source (List.replicate (4*k+6) false ++ tail) marker
    k (4*k+5) mh .stay .left (some bit) (by
      change some (action 1 .stay .left (some (readTapeBit source k))) = _
      rw [hb])
  have h1 := step_known 1 2 source (List.replicate (4*k+5) false ++ bit::tail) marker
    k (4*k+4) mh .stay .left (some true) (by rfl)
  have h2 := step_known 2 3 source (List.replicate (4*k+4) false ++ true::bit::tail) marker
    k (4*k+3) mh .stay .left (some true) (by rfl)
  have h3 := step_known 3 (if k=0 then 4 else 0) source
    (List.replicate (4*k+3) false ++ true::true::bit::tail) marker
    k (4*k+2) mh (if k=0 then .stay else .left) .left (some true) (by
      cases k <;> rfl)
  have hm : (if k=0 then HeadMove.stay else HeadMove.left).apply k=k-1 := by cases k <;> rfl
  simp only [written, write_before_suffix, HeadMove.apply] at h0 h1 h2
  rw [hm] at h3
  simp only [written, write_before_suffix, HeadMove.apply] at h3
  have ha5 : 4*k+5-1=4*k+4 := by omega
  have ha4 : 4*k+4-1=4*k+3 := by omega
  have ha3 : 4*k+3-1=4*k+2 := by omega
  have ha2 : 4*k+2-1=4*k+1 := by omega
  rw [ha5] at h0
  rw [ha4] at h1
  rw [ha3] at h2
  rw [ha2] at h3
  have e3 := runFrom_step machine _ _ r (by rfl) h3 hr
  have e2 := runFrom_step machine _ _ _ (by rfl) h2 e3
  have e1 := runFrom_step machine _ _ _ (by rfl) h1 e2
  have e0 := runFrom_step machine _ _ _ (by rfl) h0 e1
  exact ⟨_, e0, rfl, by simp only⟩

end NearCubicGates.Adapters.Machine.Capped.OutputFrame
