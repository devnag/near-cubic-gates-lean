import Proof.PCP.PCPOuterFresh

/-! Compose any actual producer with the whole four-field serializer on
129 fresh tapes. Four existing field tapes are physically shared; every
other old tape and head is retained across the serializer call. -/
namespace NearCubicWires.RepairOrdinary.PCPOuterDock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawSlot (u : ℕ) : Fin (u+129) := (78 : Fin 129).natAdd u
def frameSlot (u : ℕ) : Fin (u+129) := (77 : Fin 129).natAdd u
noncomputable def machine {u s : ℕ} (producer : Machine u s) (source : Fin 4 → Fin u) :=
  Composition.machine (TapeEmbedding.machine 129 producer) (RecoveryFocus.machine (slots source) PCPOuter.machine)

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl
private theorem joined_steps {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).steps=r.steps+1+s.steps := rfl

theorem dock_run {u s : ℕ} (producer : Machine u s) (source : Fin 4 → Fin u)
    (inj : Function.Injective source) (fp : ℕ) (c : Configuration u s)
    (p : ExecutionReceipt u s) (hp : runFrom producer fp c=some p)
    (a b cword d sa sb sc sd : List Bool)
    (ph : ∀ j,p.final.heads (source j)=0)
    (pt : ∀ j,p.final.tapes (source j)=frame (data a b cword d j)++data sa sb sc sd j) :
    ∃ r,runFrom (machine producer source) (fp+1+PCPOuter.budget (PCPOuter.size a b cword d))
      (Composition.leftConfig _ (TapeEmbedding.config
        (fun _ : Fin 129 => 0) (fun _ : Fin 129 => []) c))=some r ∧
      r.final.tapes (rawSlot u)=(PCPTraversal.code (PCPOuter.fields a b cword d)).bits ∧
      r.final.heads (rawSlot u)=0 ∧
      r.final.tapes (frameSlot u)=ZeroPadding.pad (PCPPairReusable.capacity (2*PCPOuter.size a b cword d+4))
        (frame (PCPTraversal.code (PCPOuter.fields a b cword d)).bits) ∧
      (∀ i : Fin u,r.final.tapes (i.castAdd 129)=p.final.tapes i) ∧
      (∀ i : Fin u,(∀ j,source j≠i) → r.final.heads (i.castAdd 129)=p.final.heads i) ∧
      r.steps≤fp+1+PCPOuter.budget (PCPOuter.size a b cword d) := by
  let prepared := TapeEmbedding.receipt (fun _ : Fin 129 => 0) (fun _ : Fin 129 => []) p
  have hprepared := TapeEmbedding.run_embed producer
    (fun _ : Fin 129 => 0) (fun _ : Fin 129 => []) _ _ p hp
  obtain ⟨ih,it⟩ := fresh_input source a b cword d sa sb sc sd p.final ph pt
  obtain ⟨finished,hf,ft,fh,ff,old,other,fs⟩ := PCPOuter.focused_run (slots source)
    (slots_injective source inj) a b cword d sa sb sc sd prepared.final.heads prepared.final.tapes ih it
  have joined := Composition.run_join (TapeEmbedding.machine 129 producer)
    (RecoveryFocus.machine (slots source) PCPOuter.machine) _ _ _ prepared finished hprepared hf
  have hr : slots source 82=rawSlot u := slots_new source (78 : Fin 129)
  have hfr : slots source 81=frameSlot u := slots_new source (77 : Fin 129)
  rw [hr] at ft fh
  rw [hfr] at ff
  have oldH (i : Fin u) : prepared.final.heads (i.castAdd 129)=p.final.heads i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldT (i : Fin u) : prepared.final.tapes (i.castAdd 129)=p.final.tapes i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have allOld (i : Fin u) : finished.final.tapes (i.castAdd 129)=p.final.tapes i := by
    classical
    by_cases hi : ∃ j,source j=i
    · obtain ⟨j,hj⟩ := hi
      have hold := old j
      rw [slots_old,hj] at hold
      exact hold.trans (oldT i)
    · have hnone : ∀ j,source j≠i := by simpa using hi
      exact ((other (i.castAdd 129) (old_unselected source i hnone)).2).trans (oldT i)
  refine ⟨Composition.joinedReceipt prepared finished,joined,?_⟩
  rw [joined_tapes,joined_heads,joined_steps]
  refine ⟨ft,fh,ff,allOld,?_,?_⟩
  · intro i hi
    exact ((other (i.castAdd 129) (old_unselected source i hi)).1).trans (oldH i)
  · have ps := runFrom_steps_le producer fp c p hp
    change p.steps+1+finished.steps≤_
    omega

end NearCubicWires.RepairOrdinary.PCPOuterDock
