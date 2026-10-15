import Proof.Gates.CounterAsm.Prog

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (ratWord outputWord)
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Expand.PolyTab (idealStart)

theorem marks_len (u : List Bool) : (marks u).length = 2 * u.length := by simp [marks]; omega

theorem frame_cat (u v : List Bool) : frame (u ++ v) = marks u ++ marks v ++ [false] := by
  rw [Codec.frame_eq_marks]; simp [marks]

section Runs
variable {RD RK RO : Type} {iD oD : RD → List Bool} {bD : RD → ℕ} {iK oK : RK → List Bool} {bK : RK → ℕ}
  {iO oO : RO → List Bool} {bO : RO → ℕ}

/-- Value facts of the layout, for `omega`. -/
macro "fne" : tactic => `(tactic| first
  | (intro hh
     have hv := congrArg Fin.val hh
     simp only [sDO_val, sKIN_val, sKO_val, sOIN_val, sOUT_val, sLD_val, sLK_val, sLO_val, kmap_val, omap_val] at hv
     omega)
  | (intro hh
     simp only [sDO_val, sKIN_val, sKO_val, sOIN_val, sOUT_val, sLD_val, sLK_val, sLO_val, kmap_val, omap_val] at hh
     omega))

/-- **The cell path.** -/
theorem cell_run (fD : WordFunction RD iD oD bD) (fK : WordFunction RK iK oK bK) (fO : WordFunction RO iO oO bO)
    (rd : RD) (rk : RK) (ro : RO) (cT n S U : ℕ) (vs : List ℕ) (recs : List (List Bool))
    (hne : ∀ x ∈ recs, x ≠ []) (hD : oD rd = natWord 1 ++ (n :: vs).flatMap natWord)
    (hK : iK rk = (n :: vs).flatMap natWord) (hKo : oK rk = recs.flatMap frame ++ [false])
    (hO : iO ro = iK rk ++ oK rk) (hOo : oO ro = ratWord (S : ℚ) ++ natWord U)
    (hfit : S + 2 ^ (kOf cT n - 1) * U < 2 ^ (n + 1))
    (lens : Fin (NSc fD.program fK.program fO.program + 1) → ℕ)
    (hLD : lens (sLD fD.program fK.program fO.program) = bD rd)
    (hLK : lens (sLK fD.program fK.program fO.program) = bK rk)
    (hLO : lens (sLO fD.program fK.program fO.program) = bO ro)
    (hlz : ∀ i, i ≠ sLD fD.program fK.program fO.program → i ≠ sLK fD.program fK.program fO.program →
      i ≠ sLO fD.program fK.program fO.program → lens i = 0)
    (cap : ℕ) (hcap : cellCap ((n :: vs).flatMap natWord).length (recs.flatMap frame).length n cT ≤ cap) :
    ∃ τ : WState (NSc fD.program fK.program fO.program) 64,
      WXExec cap (ctrP fD.program fK.program fO.program cT) (idealStart _ 64 (iD rd) lens) τ
        (cellCost (bD rd) (bK rk) (bO ro) ((n :: vs).flatMap natWord).length (recs.flatMap frame).length n cT) ∧
      τ.st (sOUT fD.program fK.program fO.program) = outputWord (ivl S U (kOf cT n) n) := by
  obtain ⟨ci, hci⟩ : ∃ ci, ci = (n :: vs).flatMap natWord := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = recs.flatMap frame := ⟨_, rfl⟩
  rw [← hci] at hD hK hcap ⊢
  rw [← hF] at hKo hcap ⊢
  have cK : 4 * ci.length + 2 ^ (natBitLength n + 1) + 10 ≤ cap := by
    unfold cellCap at hcap; generalize 2 ^ (natBitLength n + 1) = Pw at hcap ⊢
    generalize 100 * (n + kOf cT n + cT + 10) ^ 2 = Qw at hcap; omega
  have cO : 4 * (2 * ci.length + F.length) + 10 ≤ cap := by
    unfold cellCap at hcap; generalize 2 ^ (natBitLength n + 1) = Pw at hcap
    generalize 100 * (n + kOf cT n + cT + 10) ^ 2 = Qw at hcap; omega
  have cT' : 100 * (n + kOf cT n + cT + 10) ^ 2 ≤ cap := by
    unfold cellCap at hcap; generalize 2 ^ (natBitLength n + 1) = Pw at hcap
    generalize 100 * (n + kOf cT n + cT + 10) ^ 2 = Qw at hcap ⊢; omega
  have tD2 := fD.program.twoTapes
  have tK2 := fK.program.twoTapes
  have tO2 := fO.program.twoTapes
  have dO1 := fD.program.outputFresh
  have dO2 := fD.program.outputTape.isLt
  have kO1 := fK.program.outputFresh
  have kO2 := fK.program.outputTape.isLt
  have oO1 := fO.program.outputFresh
  have oO2 := fO.program.outputTape.isLt
  -- the front
  obtain ⟨σ, e0, hst, hsh, hval, hrest⟩ := front_run fD fK.program fO.program rd lens hLD hlz cap
  have hlens0 : ∀ i : Fin (NSc fD.program fK.program fO.program + 1), i.val ≠ 12 → i.val ≠ 13 → i.val ≠ 14 →
      lens i = 0 := fun i h1 h2 h3 => hlz i (by fne) (by fne) (by fne)
  have hb : wbit σ (sDO fD.program fK.program fO.program) = true := by
    unfold wbit; rw [hst, hsh, hD]; exact bit_one _
  -- step past the tag
  have ef := WXExec.fwd (cap := cap) (sDO fD.program fK.program fO.program) σ
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = σ.seth (sDO fD.program fK.program fO.program)
      (σ.sh (sDO fD.program fK.program fO.program) + 1) := ⟨_, rfl⟩
  rw [← hσ1] at ef
  have k1 : ∀ i, i ≠ sDO fD.program fK.program fO.program → Keep σ σ1 i := fun i h => by
    rw [hσ1]; exact keep_seth σ i _ _ h

  have hDK : sDO fD.program fK.program fO.program ≠ sKIN fD.program fK.program fO.program := by fne
  have hDO : sDO fD.program fK.program fO.program ≠ sOIN fD.program fK.program fO.program := by fne
  have hKO : sKIN fD.program fK.program fO.program ≠ sOIN fD.program fK.program fO.program := by fne
  have rKIN := hrest (sKIN fD.program fK.program fO.program) (by fne) (by right; rw [sKIN_val])
  have rOIN := hrest (sOIN fD.program fK.program fO.program) (by fne) (by right; rw [sOIN_val]; omega)
  rw [hlens0 (sKIN fD.program fK.program fO.program) (by fne) (by fne) (by fne)] at rKIN
  rw [hlens0 (sOIN fD.program fK.program fO.program) (by fne) (by fne) (by fne)] at rOIN
  obtain ⟨σ2, e2, s2K, s2Kh, s2O, s2Oh, s2op, s2N, s2z, s2keep⟩ := inK_run cap hDK hDO hKO n vs σ1
    (by rw [hσ1]; simp [hst, hD, hci]) (by rw [hσ1]; simp [hsh])
    (by rw [(k1 _ (Ne.symm hDK)).1]; exact rKIN.1) (by rw [(k1 _ (Ne.symm hDK)).2]; exact rKIN.2)
    (by rw [(k1 _ (Ne.symm hDO)).1]; exact rOIN.1) (by rw [(k1 _ (Ne.symm hDO)).2]; exact rOIN.2)
    (by intro r; rw [hσ1]; simp [hval]) (by rw [← hci]; exact cK)
  rw [← hci] at e2 s2K s2O s2Oh s2op
  have k2 : ∀ i, i ≠ sDO fD.program fK.program fO.program → i ≠ sKIN fD.program fK.program fO.program →
      i ≠ sOIN fD.program fK.program fO.program → Keep σ σ2 i := fun i h1 h2 h3 =>
    (k1 i h1).trans (s2keep i h1 h2 h3)
  -- CellTables
  have kLK : ∀ j, kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j ≠
      sLK fD.program fK.program fO.program := fun j => by fne
  have kfar : ∀ j, j ≠ tape0 fK.program → Keep σ σ2 (kmap fD.program.tapeCount fK.program.tapeCount
      fO.program.tapeCount j) := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    refine k2 _ (by fne) ?_ (by have := j.isLt; fne)
    intro h; apply hj; exact kmap_inj _ _ _ h
  have kfar0 : ∀ j, j ≠ tape0 fK.program → σ.st (kmap fD.program.tapeCount fK.program.tapeCount
      fO.program.tapeCount j) = [] ∧ σ.sh (kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) = 0 := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have h := hrest (kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) (by fne)
      (by right; rw [kmap_val]; omega)
    have hz : lens (kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) = 0 :=
      hlens0 _ (by rw [kmap_val]; omega) (by rw [kmap_val]; omega) (by rw [kmap_val]; omega)
    rw [hz] at h; exact h
  have rLK := hrest (sLK fD.program fK.program fO.program) (by fne) (by left; rw [sLK_val]; omega)
  rw [hLK] at rLK
  have kLK2 := k2 (sLK fD.program fK.program fO.program) (by fne) (by fne) (by fne)
  obtain ⟨τ3, e3, h3out, h3sh, h3oth, h3val⟩ := wfDock_exact fK rk cap
    (kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount) (kmap_inj _ _ _)
    (sLK fD.program fK.program fO.program) kLK σ2 (by rw [hK]; exact s2K)
    (fun j hj => by rw [(kfar j hj).1]; exact (kfar0 j hj).1)
    (fun j => by
      by_cases hj : j = tape0 fK.program
      · subst hj; exact s2Kh
      · rw [(kfar j hj).2]; exact (kfar0 j hj).2)
    (bK rk) (by rw [kLK2.1]; exact rLK.1) (by rw [kLK2.2]; exact rLK.2) le_rfl
  have k3 : ∀ i, (∀ j, kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j ≠ i) →
      Keep σ2 τ3 i := fun i h => h3oth i h

  have hKOO : sKO fD.program fK.program fO.program ≠ sOIN fD.program fK.program fO.program := by fne
  have notKO : ∀ i : Fin (NSc fD.program fK.program fO.program + 1), i.val < 14 + fD.program.tapeCount ∨
      14 + fD.program.tapeCount + fK.program.tapeCount ≤ i.val →
      ∀ j, kmap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j ≠ i :=
    notK fD.program fK.program fO.program
  have kOIN := k3 (sOIN fD.program fK.program fO.program) (notKO _ (by right; rw [sOIN_val]))
  obtain ⟨σ4, e4, s4O, s4Oh, s4op, s4v, s4keep⟩ := inO_run cap hKOO (marks ci) recs hne τ3
    (by rw [← hF]; exact h3out.trans hKo) (h3sh _) (by rw [kOIN.1]; exact s2O)
    (by rw [kOIN.2, s2Oh, marks_len]) (by rw [h3val, s2op, marks_len])
    (by rw [h3val]; exact s2z _ (by decide) (by decide))
    (by rw [← hF, marks_len]; exact cO)
  rw [← hF] at e4 s4O
  have k4 : ∀ i, i ≠ sKO fD.program fK.program fO.program → i ≠ sOIN fD.program fK.program fO.program →
      Keep τ3 σ4 i := fun i h1 h2 => s4keep i h1 h2

  have oLO : ∀ j, omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j ≠
      sLO fD.program fK.program fO.program := fun j => by fne
  have ofar : ∀ j, j ≠ tape0 fO.program → Keep σ σ4 (omap fD.program.tapeCount fK.program.tapeCount
      fO.program.tapeCount j) ∧ σ.st (omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) = [] ∧
      σ.sh (omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) = 0 := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have hO' : omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j ≠
        sOIN fD.program fK.program fO.program := fun h => hj (omap_inj _ _ _ h)
    refine ⟨(k2 _ (by fne) (by fne) hO').trans ((k3 _ (notKO _ (by right; rw [omap_val]; omega))).trans
      (k4 _ (by fne) hO')), ?_⟩
    have h := hrest (omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) (by fne)
      (by right; rw [omap_val]; omega)
    have hz : lens (omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount j) = 0 :=
      hlens0 _ (by rw [omap_val]; omega) (by rw [omap_val]; omega) (by rw [omap_val]; omega)
    rw [hz] at h; exact h
  have rLO := hrest (sLO fD.program fK.program fO.program) (by fne) (by left; rw [sLO_val])
  rw [hLO] at rLO
  have kLO4 := (k2 (sLO fD.program fK.program fO.program) (by fne) (by fne) (by fne)).trans
    ((k3 _ (notKO _ (by left; rw [sLO_val]; omega))).trans (k4 _ (by fne) (by fne)))
  obtain ⟨τ5, e5, h5out, h5sh, h5oth, h5val⟩ := wfDock_exact fO ro cap
    (omap fD.program.tapeCount fK.program.tapeCount fO.program.tapeCount) (omap_inj _ _ _)
    (sLO fD.program fK.program fO.program) oLO σ4
    (by rw [hO, hK, hKo, frame_cat]; exact s4O)
    (fun j hj => by rw [(ofar j hj).1.1]; exact (ofar j hj).2.1)
    (fun j => by
      by_cases hj : j = tape0 fO.program
      · subst hj; exact s4Oh
      · rw [(ofar j hj).1.2]; exact (ofar j hj).2.2)
    (bO ro) (by rw [kLO4.1]; exact rLO.1) (by rw [kLO4.2]; exact rLO.2) le_rfl
  -- the tail
  have hPP : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) →
      τ5.st (PP fD.program fK.program fO.program i) = [] ∧ τ5.sh (PP fD.program fK.program fO.program i) = 0 := by
    have h4all : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) → i.val ≠ 4 := by decide
    have hvall : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) → 1 ≤ pv i ∧ pv i ≤ 7 := by decide
    intro i hi
    have h4 : i.val ≠ 4 := h4all i hi
    have hv : (PP fD.program fK.program fO.program i).val = pv i := PP_val _ _ _ i h4
    have hv1 : 1 ≤ pv i ∧ pv i ≤ 7 := hvall i hi
    have kk : Keep σ τ5 (PP fD.program fK.program fO.program i) := by
      refine (k2 _ (by fne) (by fne) (by fne)).trans ((k3 _ (notKO _ (by left; rw [hv]; omega))).trans
        ((k4 _ (by fne) (by fne)).trans (h5oth _ (notO fD.program fK.program fO.program _ (by rw [hv]; omega)))))
    have h := hrest (PP fD.program fK.program fO.program i) (by rw [hv]; omega) (by left; rw [hv]; omega)
    rw [hlens0 _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)] at h
    exact ⟨kk.1.trans h.1, kk.2.trans h.2⟩
  have v5 : ∀ r, τ5.val r = σ4.val r := fun r => by rw [h5val]
  obtain ⟨τ6, e6, h6out⟩ := tail_run cap cT n S U (PP fD.program fK.program fO.program) τ5
    (by rw [v5, s4v _ (by decide) (by decide), h3val]; exact s2N)
    (fun r h1 h2 => by
      rw [v5]
      by_cases hr : r = opO
      · subst hr; exact s4op
      · rw [s4v r hr h2, h3val]; exact s2z r hr h1)
    (by rw [PP_four]; exact h5out.trans hOo) (by rw [PP_four]; exact h5sh _) hPP hfit
    cT'
  refine ⟨τ6, ?_, by rw [← PP_zero]; exact h6out⟩
  refine WXExec.mono (WXExec.seq e0 (WXExec.ifsT hb (WXExec.seq ef (WXExec.seq (WXExec.wm e2)
    (WXExec.seq e3 (WXExec.seq (WXExec.wm e4) (WXExec.seq e5 e6))))))) ?_
  rw [marks_len]; unfold cellCost; omega

end Runs

end NearCubicGates.Close.CounterAsm
