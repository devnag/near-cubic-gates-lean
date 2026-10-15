import Proof.PCP.PCPPNativeForwardQuery
import Proof.Assembly.AppendOutputFrame

/-! The existing physical append-output framer also retains every original
native tape, in particular the actual raw domain and padded size counters. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeFrame
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old {t : ℕ} (i : Fin t) : Fin ((t+2)+2) := (i.castAdd 2).castAdd 2
theorem old_away {t : ℕ} (target i : Fin t) (hi : i≠target) :
    ∀ j,AppendOutputFrame.slots target j≠old i := by
  intro j hj
  have hv := congrArg Fin.val hj
  have hit : i.val<t := i.isLt
  fin_cases j
  · change target.val=i.val at hv
    exact hi (Fin.ext hv.symm)
  · change t+0=i.val at hv
    omega
  · change t+2+0=i.val at hv
    omega
  · change t+2+1=i.val at hv
    omega

theorem frame_run {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : CursorRestore.NoLeft p target)
    (fuel : ℕ) (a : Fin t → List Bool) (source : ExecutionReceipt t s) (hr : run p fuel a=some source)
    (out : List Bool) (ht : source.final.tapes target=out) (hh : source.final.heads target=out.length) :
    ∃ result,run (AppendOutputFrame.machine p target) (2*source.steps+4*out.length+7)
      (AppendOutputFrame.input a)=some result ∧
      result.final.tapes ((0 : Fin 2).natAdd (t+2))=frame out ∧
      (∀ i,result.final.heads i=0) ∧
      (∀ i,result.final.tapes (old i)=source.final.tapes i) ∧
      result.steps ≤ 2*source.steps+4*out.length+7 := by
  obtain ⟨counted,hc,ct,cl,ch,cs⟩ := AppendOutputLength.length_run p target forward fuel a source hr
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) counted
  have hp := TapeEmbedding.run_embed (AppendOutputLength.machine p target)
    (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ counted hc
  have oldT (i : Fin (t+2)) : prepared.final.tapes (i.castAdd 2)=counted.final.tapes i :=
    TapeEmbedding.receipt_tapes_old _ _ _ _
  have freshT (i : Fin 2) : prepared.final.tapes (i.natAdd (t+2))=[] :=
    TapeEmbedding.receipt_tapes_new _ _ _ _
  have allH : ∀ i,prepared.final.heads i=0 := by
    intro i
    refine Fin.addCases (m := t+2) (n := 2) (fun j => ?_) (fun j => ?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ _ _).trans (ch j)
    · exact TapeEmbedding.receipt_heads_new _ _ _ _
  obtain ⟨base,hb,bt,bh,bs⟩ := AppendFrameKernel.ready out
  obtain ⟨last,hl,_,ls,lh,lt,lk⟩ := RecoveryFocus.dock (AppendOutputFrame.slots target)
    (AppendOutputFrame.slots_injective target) AppendFrameKernel.machine _
    prepared.final.heads prepared.final.tapes _ (by intro j; exact allH _)
    (by intro j; fin_cases j
        · exact (oldT ((target.castAdd 1).castAdd 1)).trans ((ct target).trans ht)
        · have h := (oldT (((0 : Fin 1).natAdd t).castAdd 1)).trans cl
          rw [hh] at h
          exact h
        · exact freshT 0
        · exact freshT 1) base hb
  have joined := Composition.run_join (AppendOutputFrame.first p target) (AppendOutputFrame.last target)
    _ _ _ prepared last hp hl
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
      (initialConfiguration (AppendOutputLength.machine p target)
        (AppendOutputLength.input (AppendOutputLength.input a))))=
      initialConfiguration (AppendOutputFrame.machine p target) (AppendOutputFrame.input a) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at joined
  have htime : (2*source.steps+2)+1+(4*out.length+4)=2*source.steps+4*out.length+7 := by omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt prepared last,joined,?_,?_,?_,?_⟩
  · exact (lt 2).trans (by rw [bt]; rfl)
  · intro i
    by_cases hi : ∃ j,AppendOutputFrame.slots target j=i
    · obtain ⟨j,rfl⟩ := hi
      exact (lh j).trans (bh j)
    · exact ((lk i (fun j hj => hi ⟨j,hj⟩)).1).trans (allH i)
  · intro i
    by_cases hi : i=target
    · subst i
      exact (lt 0).trans ((by rw [bt]; rfl : base.final.tapes 0=out).trans ht.symm)
    · exact ((lk (old i) (old_away target i hi)).2).trans
        ((oldT ((i.castAdd 1).castAdd 1)).trans (ct i))
  · change counted.steps+1+last.steps ≤ _
    rw [cs,ls]
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeFrame
