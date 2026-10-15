import Proof.Gates.Setup.PhaseB
import Proof.Wire_3_5.PrimAsmHashCellA

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

section Prog
variable (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))

/-- **Phase R**: `1^ν` onto `NU`, the A-run, `FL := [SrcFits]`. -/
def phR : WMX (nsW D) nrW :=
  .seq (.wm (WireExponent3_5.PrimAsm.HashCell.wrU (sNU D) pT1 rNu pT2 pT3))
  (.seq (WMX.machZ R.M (mR D W R) (sL D)) (.ifs (sRF D W R) WMX.skip (WMX.wr (sFL D) false)))

end Prog

structure AfterR (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (ι : WState (nsW D) nrW) : Prop where
  x : ι.st (sX D) = RepairOrdinary.frame (List.ofFn x)
  bw : ι.st (sBW D) = RepairOrdinary.frame bits
  wt : ι.st (sWT D) = guessWord N bits pad
  fl : ι.st (sFL D) = [decide (Outer.SrcFits g.lenExp (nu N) B.src)]
  d1 : ι.st (sD1 D W) = PCPPNative.descriptor B.src
  d2 : ι.st (sD2 D W) = PCPPNative.descriptor B.pf
  mw : ι.st (sMW D W R) = mwWord s g N B.src
  blank : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 16 → i.val ≠ 17 →
    (i.val < 21 ∨ 16 + D.tA ≤ i.val) → ι.st i = []
  sh : ι.sh = fun i => if i = sWT D then pairEnd (guessWord N bits pad) else 0
  val : ι.val = fun r => if r = regE 6 then width s g N else if r = rN then N else if r = rNu then nu N else 0
  cell : ι.cell = false

/-- The cost of phase R. -/
def costR (R : OuterM.ARun s.mw (g.sv s)) (N : ℕ) : ℕ := 40 * nu N + 10 + 1 + (2 * (R.K * (nu N + 1) ^ R.e) + 2) + 1 + 2

theorem phR_ideal (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (hL : Lay D W R) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad cap : ℕ) (B : Outer.OuterGuess (width s g N))
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B) (hcap : nu N ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterB D W x bits pad ι) :
    ∃ τ ι', WXExec cap (phR D W R) ι τ (costR R N) ∧ SimW ι' τ ∧ AfterR D W R x bits pad B ι' := by
  classical
  have htO := tO_eq
  have hA := tA_eq hL
  have vFL := sFL_val hL
  have vNU := sNU_val hL
  have vD1 := sD1_val hL
  have vD2 := sD2_val hL
  have vMW := sMW_val hL
  have vRF := sRF_val hL
  have hok : oracleOK s g N (guessWord N bits pad) = true := Worker.oracleOK_of_decodes s g hdec
  have hval : ∀ r, r ≠ regE 6 → r ≠ rN → r ≠ rNu → ι.val r = 0 := fun r h1 h2 h3 => by
    rw [hι.val]; simp [h1, h2, h3]
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have hnu : ι.val rNu = nu N := by
    rw [hι.val]; simp only; rw [if_neg (by decide), if_neg (by decide)]; simp
  -- 1. `1^ν` onto `NU`
  have hNU : ι.st (sNU D) = [] := hι.blank _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have e1 := WireExponent3_5.PrimAsm.HashCell.wrU_spec cap (sNU D) pT1 rNu pT2 pT3 (by decide) (by decide)
    (by decide) (by decide) (by decide) ι hNU (hsh _ (fin_ne_of_val (by simp [sWT, fixS]; omega)))
    (hval _ (by decide) (by decide) (by decide)) (hval _ (by decide) (by decide) (by decide))
    (hval _ (by decide) (by decide) (by decide)) (by rw [hnu]; omega)
  rw [hnu] at e1
  set ι1 := ι.sets (sNU D) (List.replicate (nu N) true) with hι1
  -- 2. the A-run
  obtain ⟨out, hrun, hoD, hoN, hoF, hoW⟩ := R.run (nu N) (width s g N) B.src
  have nd := R.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  obtain ⟨⟨hdn, hdf, hdw⟩, ⟨hnf, hnw⟩, hfw⟩ := nd
  have hRF : mR D W R R.fOut = sRF D W R := by simp [mR, Ne.symm hdf, Ne.symm hnf, sRF]
  have hMW : mR D W R R.wOut = sMW D W R := by simp [mR, Ne.symm hdw, Ne.symm hnw, sMW]
  have hD1 : mR D W R R.dIn = sD1 D W := by simp [mR]
  have hNUm : mR D W R R.nIn = sNU D := by simp [mR, Ne.symm hdn]
  have hmL : ∀ j, mR D W R j ≠ sL D := fun j => fin_ne_of_val (by rw [mR_val hL]; simp [sL, fixS]; split_ifs <;> omega)
  have st1 : ∀ i, i ≠ sNU D → ι1.st i = ι.st i := fun i hi => by simp [hι1, Function.update_of_ne hi]
  obtain ⟨τ2, e2, s2⟩ := Worker.donor_ideal R.M _ _ out hrun (cap := cap) (mR D W R) (mR_inj hL) (sL D) hmL ι1
    (fun j => by
      have := mR_val hL j
      simp only [hι1, WState.sets_sh]
      exact hsh _ (fin_ne_of_val (by simp [sWT, fixS]; split_ifs at this <;> omega)))
    (fun j => by
      unfold OuterM.aBank
      by_cases h1 : j = R.dIn
      · subst h1
        rw [if_pos rfl, hD1, st1 _ (fin_ne_of_val (by omega)), hι.d1 B.src hdec.1]
        exact RdEq.refl _
      · rw [if_neg h1]
        by_cases h2 : j = R.nIn
        · subst h2
          rw [if_pos rfl, hNUm]
          simp only [hι1, WState.sets_st, Function.update_self]
          exact RdEq.refl _
        · rw [if_neg h2]
          have := mR_val hL j
          rw [if_neg h1, if_neg h2] at this
          rw [st1 _ (fin_ne_of_val (by omega)), hι.blank _ (by omega) (by omega) (by omega) (by omega)
            (by omega)]
          exact RdEq.refl _)
    (by
      rw [st1 _ (fin_ne_of_val (by simp [sL, fixS]; omega))]
      intro p; rw [hι.blank _ (by simp [sL, fixS]) (by simp [sL, fixS]) (by simp [sL, fixS])
        (by simp [sL, fixS] <;> omega) (by simp [sL, fixS] <;> omega)]; rfl)
    (by simp only [hι1, WState.sets_sh]; exact hsh _ (fin_ne_of_val (by simp [sL, sWT, fixS])))
  set ι2 := updS (mR D W R) ι1 (fun _ => 0) out with hι2
  have nR : ∀ i : Fin (nsW D + 1), i.val ≠ 17 → i.val ≠ 21 + 2 * tWB W + 2 * tWU W + 1299 →
      (i.val < 21 + 2 * tWB W + 2 * tWU W + 2 * tO ∨ 16 + D.tA ≤ i.val) → ∀ j, mR D W R j ≠ i :=
    fun i h1 h2 h3 => notIn _ _ (fun j => by rw [mR_val hL]; split_ifs <;> omega)
  have st2 : ∀ i : Fin (nsW D + 1), i.val ≠ 17 → i.val ≠ 21 + 2 * tWB W + 2 * tWU W + 1299 →
      (i.val < 21 + 2 * tWB W + 2 * tWU W + 2 * tO ∨ 16 + D.tA ≤ i.val) → ι2.st i = ι.st i := fun i h1 h2 h3 => by
    rw [hι2, updS_st_other _ _ _ _ i (nR i h1 h2 h3), st1 i (fin_ne_of_val (by omega))]
  have sh2 : ∀ i, i ≠ sWT D → ι2.sh i = 0 := fun i hi => by
    rw [hι2, updS_sh_zero _ (mR_inj hL)]; split_ifs
    · rfl
    · simp [hι1, hsh i hi]
  -- 3. the flag
  have hF2 : ι2.st (sRF D W R) = [decide (Outer.SrcFits g.lenExp (nu N) B.src)] := by
    rw [hι2, ← hRF, updS_st_slot _ _ _ _ (mR_inj hL)]; exact hoF
  have hFL2 : ι2.st (sFL D) = [true] := by
    rw [st2 _ (by omega) (by omega) (by omega), hι.fl, hok]
  have w3 : wbit ι2 (sRF D W R) = decide (Outer.SrcFits g.lenExp (nu N) B.src) := by
    unfold wbit; rw [hF2, sh2 _ (fin_ne_of_val (by simp [sWT, fixS]; omega))]; rfl
  have e3 : WXExec cap (.ifs (sRF D W R) WMX.skip (WMX.wr (sFL D) false)) ι2
      (ι2.sets (sFL D) [decide (Outer.SrcFits g.lenExp (nu N) B.src)]) 2 := by
    by_cases hf : Outer.SrcFits g.lenExp (nu N) B.src
    · refine WXExec.cast cap (WXExec.ifsT (by rw [w3]; simp [hf]) (WXExec.skip cap ι2)) ?_ (by omega)
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = sFL D
      · subst hi; simp [hFL2, hf]
      · simp [Function.update_of_ne hi]
    · refine WXExec.cast cap (WXExec.ifsF (by rw [w3]; simp [hf]) (WXExec.wr (cap := cap) (sFL D) false ι2)) ?_
        (by omega)
      rw [hFL2, sh2 _ (fin_ne_of_val (by simp [sWT, fixS]; omega))]
      simp [hf]; rfl
  set ι3 := ι2.sets (sFL D) [decide (Outer.SrcFits g.lenExp (nu N) B.src)] with hι3
  obtain ⟨τ, e, sτ⟩ := Worker.seq_sim (WXExec.wm e1) (SimW.refl _) (Worker.seq_sim e2 s2 ⟨_, e3, SimW.refl _⟩)
  refine ⟨τ, ι3, WXExec.mono e (by unfold costR; omega), sτ, ?_⟩
  have st3 : ∀ i, i ≠ sFL D → ι3.st i = ι2.st i := fun i hi => by simp [hι3, Function.update_of_ne hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [st3 _ (fin_ne_of_val (by simp [sX, fixS]; omega)),
      st2 _ (by simp [sX, fixS]) (by simp [sX, fixS] <;> omega) (by simp [sX, fixS] <;> omega)]; exact hι.x
  · rw [st3 _ (fin_ne_of_val (by simp [sBW, fixS]; omega)),
      st2 _ (by simp [sBW, fixS]) (by simp [sBW, fixS] <;> omega) (by simp [sBW, fixS] <;> omega)]; exact hι.bw
  · rw [st3 _ (fin_ne_of_val (by simp [sWT, fixS]; omega)),
      st2 _ (by simp [sWT, fixS]) (by simp [sWT, fixS] <;> omega) (by simp [sWT, fixS] <;> omega)]; exact hι.wt
  · simp [hι3]
  · rw [st3 _ (fin_ne_of_val (by omega)), hι2, ← hD1, updS_st_slot _ _ _ _ (mR_inj hL), hoD]
  · rw [st3 _ (fin_ne_of_val (by omega)), st2 _ (by omega) (by omega) (by omega)]; exact hι.d2 B.pf hdec.2
  · rw [st3 _ (fin_ne_of_val (by omega)), hι2, ← hMW, updS_st_slot _ _ _ _ (mR_inj hL), hoW]; rfl
  · intro i h0 h1 h2 h16 h17 hr
    rw [st3 _ (fin_ne_of_val (by omega)), st2 _ (by omega) (by omega) (by omega)]
    exact hι.blank i h0 h1 h2 h16 (by omega)
  · rw [hι3, WState.sets_sh]
    funext i
    by_cases hi : i = sWT D
    · subst hi
      rw [if_pos rfl, hι2, updS_sh_zero _ (mR_inj hL), if_neg (fun ⟨j, hj⟩ => by
        have := mR_val hL j; rw [hj] at this; simp [sWT, fixS] at this; split_ifs at this <;> omega)]
      simp [hι1, hι.sh]
    · rw [if_neg hi, sh2 i hi]
  · rw [hι3, WState.sets_val, hι2, updS_val, hι1, WState.sets_val]; exact hι.val
  · simp only [hι3, hι2, hι1, WState.sets_cell, updS_cell]; exact hι.cell

end

end NearCubicGates.Close.Setup
