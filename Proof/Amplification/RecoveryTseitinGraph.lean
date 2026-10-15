import Proof.Amplification.RecoveryTseitinOperands

/-! Paid call/return paths inside the fixed prefix-query graph. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def atCall (j : Fin 6) (tapes : Fin 239→List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) tapes)
def Path (j k : Fin 6) (fuel : Nat) (before after : Fin 239→List Bool) : Prop :=
  ∃ n ≤ fuel,Timed machine n (atCall j before) (atCall k after)

theorem Path.refl (j : Fin 6) (tapes : Fin 239→List Bool) : Path j j 0 tapes tapes :=
  ⟨0,Nat.le_refl _,Timed.refl _ _⟩

theorem Path.trans {j k l : Fin 6} {a b : Nat} {x y z : Fin 239→List Bool}
    (h : Path j k a x y) (g : Path k l b y z) : Path j l (a+b) x z := by
  obtain ⟨n,hn,ht⟩ := h
  obtain ⟨m,hm,gt⟩ := g
  exact ⟨n+m,by omega,ht.trans gt⟩

theorem Path.enlarge {j k : Fin 6} {a b : Nat} {x y : Fin 239→List Bool}
    (h : Path j k a x y) (hab : a ≤ b) : Path j k b x y := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn.trans hab,ht⟩

theorem ready_path (j k : Fin 6) (fuel : Nat) (input output : Fin 239→List Bool)
    (h : ClockJoin.ReadyRun (programs j) fuel input output)
    (hn : ∀ q scanned,next j q scanned=some k) : Path j k (fuel+1) input output := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  obtain ⟨n,hb,hpath⟩ := call_receipt sizes programs 0 next j k fuel
    (initialConfiguration (programs j) input) r hr (hn _ _)
  have he : RecoveryCalls.restarted (programs k) r.final.heads r.final.tapes=
      initialConfiguration (programs k) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hpath
  exact ⟨n,hb,hpath⟩

theorem finish_path {fuel last : Nat} {input middle output : Fin 239→List Bool}
    (h : Path 0 5 fuel input middle)
    (g : ClockJoin.ReadyRun (programs 5) last middle output) :
    ClockJoin.ReadyRun machine (fuel+last+1) input output := by
  obtain ⟨n,hn,hpath⟩ := h
  obtain ⟨r,hr,ht,hh,hs⟩ := g
  obtain ⟨m,hm,hlast⟩ := stop_receipt sizes programs 0 next 5 last
    (initialConfiguration (programs 5) middle) r hr (by rfl)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes=
      RecoveryCalls.stopped sizes (fun _ : Fin 239=>0) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hlast
  have whole := hpath.trans hlast
  obtain ⟨out,ho,hf,hsteps⟩ := whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n+m ≤ fuel+last+1 := by omega
  have hmore := runFrom_moreFuel machine (n+m) (fuel+last+1-(n+m)) _ out ho
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨out,hmore,by simp [hf,RecoveryCalls.stopped],
    by intro i; simp [hf,RecoveryCalls.stopped],hsteps.trans_le hb⟩

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
