import Proof.Hierarchy.CompetitorSignedResidue
import Proof.MachineModel.OrdinaryMatrixScoreCanonicalFold

/-! Shifted matrix scores reuse the accepted borrow subtraction. The offset
is already on the positive accumulator; its fit is proved at the exact
(S+1)-bit carrier, including negative scores. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreShifted
open LocalBitMultitape SignedSortKey MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem offset_fit (s p : ℕ) (hp : p<2^s) : 2^s+p<2^(s+1) := by
  rw [Nat.pow_succ]
  omega

theorem shifted_value (s p n : ℕ) (hn : n<2^s) :
    shifted s ((p : ℤ)-n)=2^s+p-n := by
  have h0 : n≤2^s+p := by omega
  have he : (p : ℤ)-(n : ℤ)+(2^s : ℕ)=((2^s+p-n : ℕ) : ℤ) := by omega
  unfold shifted
  rw [he]
  simp

theorem residue_value (s p n : ℕ) (hp : p<2^s) (hn : n<2^s) :
    CompetitorSignedResidue.residue (s+1) (s+1) (2^s+p) n=shifted s ((p : ℤ)-n) := by
  rw [shifted_value s p n hn]
  unfold CompetitorSignedResidue.residue
  have he : 2^s+p+2^(s+1)-n=(2^s+p-n)+2^(s+1) := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (offset_fit s p hp))

theorem shifted_run (s p n c : ℕ) (hp : p<2^s) (hn : n<2^s) (hc : 4*(s+1)+5≤c) :
    ∃ actual,
      run CompetitorSignedResidue.subtractProgram (4*(s+1)+4)
        ![scalar c (s+1) (2^s+p),scalar c (s+1) n,zeros c,zeros c]=some actual ∧
      actual.final.tapes 0=scalar c (s+1) (2^s+p) ∧
      actual.final.tapes 1=scalar c (s+1) n ∧
      actual.final.tapes 2=scalar c (s+1) (shifted s ((p : ℤ)-n)) ∧
      (∀ i,actual.final.heads i=0) ∧ (∀ i,(actual.final.tapes i).length≤c) ∧
      actual.steps≤4*(s+1)+4 := by
  have hn' : n<2^(s+1) := hn.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,h0,h1,h2⟩ := CompetitorSignedResidue.subtract_ready (s+1) (2^s+p) n (offset_fit s p hp) hn'
  have hv := residue_value s p n hp hn
  rw [hv] at h2
  have hc' : 2*(s+1)+1≤c := by omega
  have support := RecoveryTapeSupport.run_support CompetitorSignedResidue.subtractProgram _ _ base hr c 0
    (by intro i; exact Nat.zero_le _) (by
      intro i
      fin_cases i <;> simp [initialConfiguration] <;> omega)
  have hb (i : Fin 4) : (base.final.tapes i).length≤c := by
    have hsteps : base.steps+1≤c := by omega
    simpa only [Nat.zero_add,max_eq_left hsteps] using support i
  obtain ⟨actual,ha,hf,has,_⟩ := ZeroPadding.run_config CompetitorSignedResidue.subtractProgram (fun _ => c) _ _ base hr
  have hi : ZeroPadding.config (fun _ : Fin 4 => c)
      (initialConfiguration CompetitorSignedResidue.subtractProgram
        ![frame (binary (s+1) (2^s+p)),frame (binary (s+1) n),[],[]])=
      initialConfiguration CompetitorSignedResidue.subtractProgram
        ![scalar c (s+1) (2^s+p),scalar c (s+1) n,zeros c,zeros c] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,scalar,zeros,ZeroPadding.pad]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,?_,?_,?_,has.trans_le hs⟩
  · rw [hf]
    change ZeroPadding.pad c (base.final.tapes 0)=_
    rw [ht,h0]
    rfl
  · rw [hf]
    change ZeroPadding.pad c (base.final.tapes 1)=_
    rw [ht,h1]
    rfl
  · rw [hf]
    change ZeroPadding.pad c (base.final.tapes 2)=_
    rw [ht,h2]
    rfl
  · intro i; rw [hf]; exact hh i
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le le_rfl (hb i)

end NearCubicWires.RepairOrdinary.MatrixScoreShifted
