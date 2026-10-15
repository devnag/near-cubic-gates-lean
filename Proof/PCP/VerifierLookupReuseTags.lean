import Proof.PCP.VerifierLookupCanonicalRun

/-! Array consumption leaves the selected tag tape at its trailing marker.
This paid local rewind restores the next lookup's actual output-head entry. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def usedCfg {n : ℕ} (q : Fin n) (d : Store) (tagPos : ℕ) : Configuration 21 n :=
  ⟨q,fun i=>if i.val=12 then tagPos else (cfg q d).heads i,(cfg q d).tapes⟩
def resetTagSlots : Fin 2→Fin 21 := ![12,20]
noncomputable def resetTagProgram := RecoveryFocus.machine resetTagSlots (LookupWalk.machine .left)

theorem usedCfg_zero {n : ℕ} (q : Fin n) (d : Store) : usedCfg q d 0=cfg q d := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem reset_tag_place (q : Fin 4) (d : Store) (tagPos nextPos : ℕ) :
    RecoveryFocus.config resetTagSlots (usedCfg q d tagPos).heads (usedCfg q d tagPos).tapes
      (LookupWalk.cfg q d.tags nextPos (4*d.t) 1)=usedCfg q d nextPos := by
  apply TransitionEvent.focused_eq resetTagSlots (by decide) (usedCfg q d tagPos)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i _; rfl

theorem reset_tags_run (d : Store) (tagPos : ℕ) (hp : tagPos≤8*d.t) :
    ∃ r,runFrom resetTagProgram (12*d.t+2) (usedCfg resetTagProgram.start d tagPos)=some r ∧
      r.final=cfg 3 d ∧ r.steps=12*d.t+2 := by
  obtain ⟨base,hb,hbf,hbs⟩ := LookupWalk.walk_run .left d.tags tagPos (4*d.t)
  have ht : 3*(4*d.t)+2=12*d.t+2 := by omega
  rw [ht] at hb hbs
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config resetTagSlots (by decide) (LookupWalk.machine .left)
    (usedCfg (0 : Fin 4) d tagPos).heads (usedCfg (0 : Fin 4) d tagPos).tapes _ _ base hb
  rw [reset_tag_place] at hr
  have hz : tagPos-2*(4*d.t)=0 := by omega
  refine ⟨r,hr,?_,hrs.trans hbs⟩
  rw [hrf,hbf]
  change RecoveryFocus.config resetTagSlots (usedCfg (0 : Fin 4) d tagPos).heads (usedCfg (0 : Fin 4) d tagPos).tapes
    (LookupWalk.cfg 3 d.tags (tagPos-2*(4*d.t)) (4*d.t) 1)=cfg 3 d
  rw [hz]
  have he : RecoveryFocus.config resetTagSlots (usedCfg (0 : Fin 4) d tagPos).heads (usedCfg (0 : Fin 4) d tagPos).tapes
      (LookupWalk.cfg 3 d.tags 0 (4*d.t) 1)=usedCfg 3 d 0 := reset_tag_place 3 d tagPos 0
  exact he.trans (usedCfg_zero 3 d)

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
