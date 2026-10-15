import Proof.Assembly.AppendOutputLength
import Proof.Hierarchy.CompetitorRationalProducts
import Proof.Assembly.AppendFrameKernel

/-! An append-only ordinary producer can frame its actual output with a
constant-factor paid wrapper, using the measured output head as its length. -/
namespace NearCubicWires.RepairOrdinary.AppendOutputFrame
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {t : ℕ} (target : Fin t) : Fin 4 → Fin ((t+2)+2) :=
  ![(target.castAdd 2).castAdd 2,(((0 : Fin 1).natAdd t).castAdd 1).castAdd 2,
    (0 : Fin 2).natAdd (t+2),(1 : Fin 2).natAdd (t+2)]
theorem slots_injective {t : ℕ} (target : Fin t) : Function.Injective (slots target) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ht := target.isLt
  fin_cases a <;> fin_cases b <;> simp [slots] at hv ⊢ <;> omega
noncomputable def first {t s : ℕ} (p : Machine t s) (target : Fin t) :=
  TapeEmbedding.machine 2 (AppendOutputLength.machine p target)
noncomputable def last {t : ℕ} (target : Fin t) := RecoveryFocus.machine (slots target) AppendFrameKernel.machine
noncomputable def machine {t s : ℕ} (p : Machine t s) (target : Fin t) :=
  Composition.machine (first p target) (last target)
def input {t : ℕ} (a : Fin t → List Bool) : Fin ((t+2)+2) → List Bool :=
  fun i => Fin.addCases (m := t+2) (n := 2) (motive := fun _ => List Bool)
    (AppendOutputLength.input (AppendOutputLength.input a)) (fun _ => []) i

theorem frame_run {t s : ℕ} (p : Machine t s) (target : Fin t) (forward : CursorRestore.NoLeft p target)
    (fuel : ℕ) (a : Fin t → List Bool) (source : ExecutionReceipt t s) (hr : run p fuel a=some source)
    (out : List Bool) (ht : source.final.tapes target=out) (hh : source.final.heads target=out.length) :
    ∃ r,run (machine p target) (2*source.steps+4*out.length+7) (input a)=some r ∧
      r.final.tapes ((0 : Fin 2).natAdd (t+2))=frame out ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ 2*source.steps+4*out.length+7 := by
  obtain ⟨counted,hc,ct,cl,ch,cs⟩ := AppendOutputLength.length_run p target forward fuel a source hr
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) counted
  have he := TapeEmbedding.run_embed (AppendOutputLength.machine p target) (fun _ : Fin 2 => 0)
    (fun _ : Fin 2 => []) _ _ counted hc
  have oldT (i : Fin (t+2)) : prepared.final.tapes (i.castAdd 2)=counted.final.tapes i := by
    change (Fin.addCases (m := t+2) (n := 2) (motive := fun _ => List Bool)
      counted.final.tapes (fun _ => [])) (i.castAdd 2)=_
    rw [Fin.addCases_left]
  have freshT (i : Fin 2) : prepared.final.tapes (i.natAdd (t+2))=[] := by
    change (Fin.addCases (m := t+2) (n := 2) (motive := fun _ => List Bool)
      counted.final.tapes (fun _ => [])) (i.natAdd (t+2))=[]
    rw [Fin.addCases_right]
  have allH : ∀ i,prepared.final.heads i=0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (Fin.addCases (m := t+2) (n := 2) (motive := fun _ => ℕ)
        counted.final.heads (fun _ => 0)) (j.castAdd 2)=0
      rw [Fin.addCases_left]
      exact ch j
    · change (Fin.addCases (m := t+2) (n := 2) (motive := fun _ => ℕ)
        counted.final.heads (fun _ => 0)) (j.natAdd (t+2))=0
      rw [Fin.addCases_right]
  obtain ⟨base,hb,bt,bh,bs⟩ := AppendFrameKernel.ready out
  have hi : RecoveryFocus.config (slots target) prepared.final.heads prepared.final.tapes
      (initialConfiguration AppendFrameKernel.machine (AppendFrameKernel.input out))=
      Composition.restart prepared.final (last target).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; exact allH _
    · intro j; fin_cases j
      · exact (oldT ((target.castAdd 1).castAdd 1)).trans ((ct target).trans ht)
      · have h := (oldT (((0 : Fin 1).natAdd t).castAdd 1)).trans cl
        rw [hh] at h
        exact h
      · exact freshT 0
      · exact freshT 1
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (slots target) (slots_injective target)
    AppendFrameKernel.machine prepared.final.heads prepared.final.tapes _ _ base hb
  rw [hi] at hf
  have joined := Composition.run_join (first p target) (last target) _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
      (initialConfiguration (AppendOutputLength.machine p target)
        (AppendOutputLength.input (AppendOutputLength.input a))))=
      initialConfiguration (machine p target) (input a) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at joined
  refine ⟨Composition.joinedReceipt prepared focused,?_,?_,?_,?_⟩
  · have hn : (2*source.steps+2)+1+(4*out.length+4)=2*source.steps+4*out.length+7 := by omega
    simpa only [run,machine,hn] using joined
  · change focused.final.tapes (slots target 2)=frame out
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots target) (slots_injective target),bt]
    rfl
  · intro i
    change focused.final.heads i=0
    rw [ff]
    cases hp : RecoveryFocus.pick (slots target) i <;> simp [RecoveryFocus.config,hp,allH,bh]
  · change counted.steps+1+focused.steps ≤ _
    rw [cs,fs]
    omega

end NearCubicWires.RepairOrdinary.AppendOutputFrame
