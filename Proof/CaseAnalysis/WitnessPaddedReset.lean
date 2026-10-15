import Proof.MachineModel.OrdinaryMaskedReset
import Proof.PCP.PCPSerializerTapeSupport

/-! The existing masked reset, with a reusable local capacity. Abstract tape
and state counts keep this configuration transport independent of the large
finite control of the concrete witness reader. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.PaddedReset
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads {t : ℕ} (selected : Fin t → Bool) (cap : ℕ) (i : Fin t) : ℕ:=
  if selected i then cap else 0
def entry {t s : ℕ} (selected : Fin t → Bool) (cap : ℕ) (c : Configuration t s):=
  ZeroPadding.config (Rewind.Workspace.capacities t cap)
    (Rewind.recording (ZeroPadding.config (pads selected cap) c) 0)

theorem reset_run {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s) (hr : runFrom p fuel c=some source)
    (hhead : ∀ i,selected i=true → c.heads i=0)
    (hlen : ∀ i,selected i=true → (c.tapes i).length ≤ cap)
    (hcap : source.steps+1 ≤ cap) : ∃ result,
    runFrom (MaskedReset.machine p selected) (2*source.steps+2) (entry selected cap c)=some result ∧
      result.steps=2*source.steps+2 ∧
      (∀ i,result.final.heads (i.castAdd 1)=if selected i then 0 else source.final.heads i) ∧
      (∀ i,result.final.tapes (i.castAdd 1)=ZeroPadding.pad (pads selected cap i) (source.final.tapes i)) ∧
      (∀ i,selected i=true → (result.final.tapes (i.castAdd 1)).length ≤ cap) ∧
      result.final.heads ((0 : Fin 1).natAdd t)=0 ∧
      result.final.tapes ((0 : Fin 1).natAdd t)=List.replicate cap false:=by
  obtain ⟨padded,hp,pf,ps,_⟩:=ZeroPadding.run_config p (pads selected cap) fuel c source hr
  have localBound (i : Fin t) (hi : selected i=true) : (padded.final.tapes i).length ≤ cap:=by
    have h:=PCPSerializerReuse.tape_support p fuel _ padded hp i cap 0
      (by change c.heads i ≤ 0;rw [hhead i hi])
      (by
        simp only [ZeroPadding.config,ZeroPadding.pad_length,pads,hi,if_true]
        exact max_le (Nat.le_max_left _ _) ((hlen i hi).trans (Nat.le_max_left _ _)))
    rw [ps] at h
    omega
  obtain ⟨r,hrun,rf,rs,_⟩:=MaskedReset.workspace_run p selected fuel cap _ padded hp
    (by intro i hi;exact hhead i hi) (by rw [ps];omega)
  rw [ps] at hrun rs
  refine ⟨r,hrun,rs,?_,?_,?_,?_,?_⟩
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left,pf,ZeroPadding.config]
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left,pf,ZeroPadding.config]
  · intro i hi
    simpa only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left] using localBound i hi
  · simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_right]
  · simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutWitness.PaddedReset
