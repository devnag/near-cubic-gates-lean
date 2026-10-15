import Proof.MachineModel.OrdinaryMatrixCoordinateLoad

/-! Append the two loaded coordinate fields in reversed order, using the
actual bounded field copier and retaining both global cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots : Fin 6 → Fin 12 := ![4,8,0,9,10,11]
noncomputable def pair : Machine 12 10 := RecoveryFocus.machine pairSlots KeyPair.machine

theorem cfg_tapes_out_other {s k : ℕ} (q : Fin s) (q' : Fin k) (w cap : ℕ)
    (source record clone rank out out' : List Bool) (pos : ℕ) (i : Fin 12) (hi : i≠10) :
    (cfg q w cap source pos record clone rank out).tapes i=
      (cfg q' w cap source pos record clone rank out').tapes i := by
  fin_cases i <;> simp_all [cfg]

theorem pair_output (w cap : ℕ) (a b source out : List Bool) (pos : ℕ) :
    RecoveryFocus.config pairSlots
      (cfg pair.start w cap source pos (frame (a++b)) (frame (a++b)) (frame b) out).heads
      (cfg pair.start w cap source pos (frame (a++b)) (frame (a++b)) (frame b) out).tapes
      (KeyPair.config (9 : Fin 10) (frame b) (frame (List.replicate w false))
        (frame (a++b)) (frame (List.replicate w false)) (out++frame (b++a)) cap)=
      cfg 9 w cap source pos (frame (a++b)) (frame (a++b)) (frame b) (out++frame (b++a)) := by
  have hout : RecoveryFocus.pick pairSlots 10=some 4 := RecoveryFocus.pick_slot pairSlots (by decide) 4
  apply configuration_ext
  · rfl
  · funext i
    cases hi : RecoveryFocus.pick pairSlots i with
    | none =>
      have hn : i≠10 := by intro he; subst i; rw [hout] at hi; contradiction
      simp only [RecoveryFocus.config,hi,cfg]
      fin_cases i <;> first | exact False.elim (hn rfl) | rfl
    | some j =>
      have hij := RecoveryFocus.slot_of_pick pairSlots hi
      simp only [RecoveryFocus.config,hi]
      rw [←hij]
      fin_cases j <;> simp [KeyPair.config,cfg,pairSlots]
  · funext i
    cases hi : RecoveryFocus.pick pairSlots i with
    | none =>
      have hn : i≠10 := by intro he; subst i; rw [hout] at hi; contradiction
      simp only [RecoveryFocus.config,hi]
      exact cfg_tapes_out_other _ _ w cap source (frame (a++b)) (frame (a++b)) (frame b)
        out (out++frame (b++a)) pos i hn
    | some j =>
      have hij := RecoveryFocus.slot_of_pick pairSlots hi
      simp only [RecoveryFocus.config,hi]
      rw [←hij]
      fin_cases j <;> simp [KeyPair.config,cfg,pairSlots]

theorem pair_run (w cap : ℕ) (a b source out : List Bool) (pos : ℕ)
    (ha : a.length=w) (hb : b.length=w) (hcap : 2*w ≤ cap) :
    ∃ actual : ExecutionReceipt 12 10,
      runFrom pair (8*w+7) (cfg pair.start w cap source pos
        (frame (a++b)) (frame (a++b)) (frame b) out)=some actual ∧
      actual.final=cfg 9 w cap source pos (frame (a++b)) (frame (a++b)) (frame b)
        (out++frame (b++a)) ∧ actual.steps ≤ 8*w+7 := by
  obtain ⟨base,hbase,hf,hs,_⟩ := KeyPair.pair_run b [false] (List.replicate w false)
    a (frame b) (List.replicate w false) out cap (by simp [hb]) (by simp [ha])
    (by simpa [hb] using hcap) (by simpa [ha] using hcap)
  rw [RankBody.marks_frame,←frame_append] at hbase hf
  simp only [ha,hb] at hbase hs
  have htime : 4*(w+w)+7=8*w+7 := by omega
  rw [htime] at hbase hs
  let entry := cfg pair.start w cap source pos (frame (a++b)) (frame (a++b)) (frame b) out
  let part := KeyPair.config (0 : Fin 10) (frame b) (frame (List.replicate w false))
    (frame (a++b)) (frame (List.replicate w false)) out cap
  have hi : RecoveryFocus.config pairSlots entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config pairSlots (by decide) KeyPair.machine
    entry.heads entry.tapes _ part base hbase
  rw [hi] at hr
  refine ⟨actual,hr,?_,by omega⟩
  rw [hfinal,hf]
  exact pair_output w cap a b source out pos

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
