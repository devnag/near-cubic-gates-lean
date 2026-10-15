import Proof.Supplier.EquationCutBase

/-! One paid source-cursor restoration around the entire first cut.
The growing output is never rewound or copied. -/
namespace NearCubicWires.RepairOrdinary.EquationCut
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def restoreHeads (pos : Nat) (out : List Bool) : Fin 6→Nat :=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>Nat) (heads pos out) (fun _=>0)
def restoreTapes (C : Nat) (source out : List Bool) (L p : Nat) (odd : Bool) : Fin 6→List Bool :=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool) (tapes source out L p odd) (fun _=>List.replicate C false)
def restoreCaps (C : Nat) : Fin 6→Nat :=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>C)

theorem base_bound (L p : Nat) : baseBudget L p ≤ 32*(L+1)*(p+1) := by
  unfold baseBudget
  nlinarith

theorem restore_run (pre suffix out : List Bool) (C p : Nat) (odd : Bool) (c : Cut)
    (hf : EquationRow.Fits p c) (hC : 128*((weights c).length+1)*(p+1) ≤ C) :
    ∃ r,runFrom restored (2*baseBudget (weights c).length p+2)
      ⟨restored.start,restoreHeads pre.length out,
        restoreTapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩=some r ∧
      r.final.heads=restoreHeads pre.length (out++cutWord (p+1) (EquationRow.padded odd c)) ∧
      r.final.tapes=restoreTapes C (pre++cutWord p c++suffix)
        (out++cutWord (p+1) (EquationRow.padded odd c)) (weights c).length p odd ∧
      r.steps ≤ 2*baseBudget (weights c).length p+2 := by
  obtain ⟨source,hr,sh,st,ss⟩ := base_run pre suffix out p odd c hf
  obtain ⟨reset,delta,hh,hd,hs,hf⟩ := CursorRestore.restore_run base 0 base_forward _ _ source hr
  obtain ⟨r,hp,rt,rs,_⟩ := ZeroPadding.run_config restored (restoreCaps C) _ _ reset hh
  have hc : delta ≤ C := by have hb:=base_bound (weights c).length p; nlinarith
  have hi : ZeroPadding.config (restoreCaps C)
      (Rewind.recording (⟨base.start,heads pre.length out,tapes (pre++cutWord p c++suffix) out (weights c).length p odd⟩ : Configuration 5 _) 0)=
      (⟨restored.start,restoreHeads pre.length out,restoreTapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩ : Configuration 6 _) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [ZeroPadding.config,restoreCaps,restoreTapes,Rewind.recording,Rewind.config,ZeroPadding.pad,Fin.addCases]
  rw [hi] at hp
  have ht : 2*source.steps+2 ≤ 2*baseBudget (weights c).length p+2 := by omega
  have hm := runFrom_moreFuel restored _ ((2*baseBudget (weights c).length p+2)-(2*source.steps+2)) _ r hp
  rw [Nat.add_sub_of_le ht] at hm
  refine ⟨r,hm,?_,?_,by omega⟩
  · rw [rt,hf]
    funext i; fin_cases i <;>
      simp [ZeroPadding.config,SelectiveReset.finished,Rewind.config,sh,restoreHeads,heads,Fin.addCases]
  · rw [rt,hf]
    funext i; fin_cases i <;>
      simp [ZeroPadding.config,SelectiveReset.finished,Rewind.config,st,restoreTapes,restoreCaps,Fin.addCases]
    exact PCPSerializerReuse.pad_zeros C delta hc

end
end NearCubicWires.RepairOrdinary.EquationCut
