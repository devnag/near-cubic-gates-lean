import SourceAdapters.Machine.CappedLoaderData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: the full ambient request loader supplies all simulator inputs. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem loader_run (p : Program) (cap : ℕ) (word : List Bool) :
    ∃ receipt : ExecutionReceipt (tapes p) 13, run (loader p) (30*(cap+word.length+1))
        (extend p (RequestLoader.requestInput (cap,word)))=some receipt ∧
      (∀ i, receipt.final.heads i=0) ∧
      (∀ i, receipt.final.tapes (preparedSlot p i)=preparedInput p cap word i) ∧
      receipt.final.tapes (outputSlot p)=[] ∧ receipt.final.tapes (originSlot p)=[] := by
  obtain ⟨r,hr,hh,h1,h2,h3⟩ := RequestLoader.request_run cap word
  rw [request_slots.1] at h1
  rw [request_slots.2.1] at h2
  rw [request_slots.2.2] at h3
  let eh := fun _ : Fin (p.tapeCount+6) => 0
  let et := fun _ : Fin (p.tapeCount+6) => ([] : List Bool)
  have he := TapeEmbedding.run_embed RequestLoader.requestMachine eh et _ _ r hr
  have hi : TapeEmbedding.config eh et
      (initialConfiguration RequestLoader.requestMachine (RequestLoader.requestInput (cap,word))) =
      initialConfiguration (loader p) (extend p (RequestLoader.requestInput (cap,word))) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
      · simp only [TapeEmbedding.config,Fin.addCases_left,initialConfiguration]
      · simp only [TapeEmbedding.config,Fin.addCases_right,initialConfiguration,eh]
    · rfl
  rw [hi] at he
  refine ⟨_,he,?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (TapeEmbedding.receipt_heads_old eh et r j).trans (hh j)
    · exact TapeEmbedding.receipt_heads_new eh et r j
  · intro i
    exact extend_prepared p cap word r.final.tapes h1 h2 h3 i
  · exact extend_output p r.final.tapes
  · exact extend_origin p r.final.tapes

end NearCubicGates.Adapters.Machine.Capped.Layout
