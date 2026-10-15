import Proof.Gates.CounterAsm.Setup

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Recovery.HTParts

variable {ns : ℕ} (cap : ℕ)

section InK
variable (DO KIN OIN : Fin (ns + 1))

/-- Copy the cell input to `KIN` (framed) and to `OIN` (marked), rewind, read `n`. -/
def inK : WM ns 64 :=
  .seq (natLoop DO scD kC (emitPair KIN opK)) (.seq (emitC KIN opK false) (.seq (WM.rewind KIN opK)
  (.seq (pairLoop KIN scK (fun _ => WM.skip) (emitPair OIN opO)) (.seq (WM.rewind KIN scK)
  (.seq (WM.rewind DO scD) (readNatM false DO rf rc rN rp rt))))))

/-- The cost bound of `inK`. -/
def inKCost (L n : ℕ) : ℕ := 100 * L + 100 + (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40)

theorem natWord_one : natWord 1 = [true, false, true] := by decide
theorem natWord_zero : natWord 0 = [true, false, false] := by decide

variable {DO KIN OIN}

theorem inK_run (hDK : DO ≠ KIN) (hDO : DO ≠ OIN) (hKO : KIN ≠ OIN) (n : ℕ) (vs : List ℕ) (σ : WState ns 64)
    (hD : σ.st DO = natWord 1 ++ (n :: vs).flatMap natWord) (hDh : σ.sh DO = 3)
    (hK : σ.st KIN = []) (hKh : σ.sh KIN = 0) (hO : σ.st OIN = []) (hOh : σ.sh OIN = 0)
    (hz : ∀ r, σ.val r = 0)
    (hcap : 4 * ((n :: vs).flatMap natWord).length + 2 ^ (natBitLength n + 1) + 10 ≤ cap) :
    ∃ τ : WState ns 64, WExec cap (inK DO KIN OIN) σ τ (inKCost ((n :: vs).flatMap natWord).length n) ∧
      τ.st KIN = frame ((n :: vs).flatMap natWord) ∧ τ.sh KIN = 0 ∧
      τ.st OIN = marks ((n :: vs).flatMap natWord) ∧ τ.sh OIN = 2 * ((n :: vs).flatMap natWord).length ∧
      τ.val opO = 2 * ((n :: vs).flatMap natWord).length ∧ τ.val rN = n ∧
      (∀ r, r ≠ opO → r ≠ rN → τ.val r = 0) ∧
      (∀ i, i ≠ DO → i ≠ KIN → i ≠ OIN → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) := by
  obtain ⟨ci, hci⟩ : ∃ ci, ci = (n :: vs).flatMap natWord := ⟨_, rfl⟩
  rw [← hci] at hD hcap ⊢
  have hKD := Ne.symm hDK
  have hOD := Ne.symm hDO
  have hOK := Ne.symm hKO
  have hcapn : 2 ^ (natBitLength n + 1) ≤ cap := by omega
  have hcapL : 4 * ci.length + 10 ≤ cap := by have := Nat.zero_le (2 ^ (natBitLength n + 1)); omega
  -- 1. copy to KIN, as marked pairs
  have e1 := natLoop_spec cap (src := DO) (dst := KIN) (OP := opK) (SC := scD) hDK (by decide) (K := kC)
    (by decide) (by decide) (emits_pair cap) (d := 2) (fun _ => by simp) [] rfl (n :: vs) (natWord 1) σ
    (by rw [hD, hci, List.append_nil]) (by rw [hDh]; rfl) (by rw [hK, hKh]; rfl) (hz _)
    (by rw [hz, ← hci]; omega) (by rw [hz, ← hci]; omega) (by rw [← hci]; omega)
  rw [← hci] at e1
  obtain ⟨s1, hs1⟩ : ∃ s, s = adv DO KIN opK scD σ (ci.flatMap fun b => [true, b]) ci.length := ⟨_, rfl⟩
  rw [← hs1] at e1
  have hu : (ci.flatMap fun b => [true, b]) = marks ci := rfl
  have hul : (marks ci).length = 2 * ci.length := by simp [marks]; omega
  rw [hu] at hs1
  have s1K : s1.st KIN = marks ci := by rw [hs1, adv_st_dst, hK]; rfl
  have s1Kh : s1.sh KIN = 2 * ci.length := by rw [hs1, adv_sh_dst hDK, hKh, hul]; omega
  have s1op : s1.val opK = 2 * ci.length := by rw [hs1, adv_val_OP (by decide), hz, hul]; omega
  -- 2. the end marker
  have e2 := emits_raw cap (dst := KIN) (OP := opK) false s1 (by rw [s1K, s1Kh, hul])
    (by rw [s1op]; simp only [List.length_singleton]; omega)
  obtain ⟨s2, hs2⟩ : ∃ s, s = appendO s1 KIN opK [false] := ⟨_, rfl⟩
  rw [← hs2] at e2
  have s2K : s2.st KIN = frame ci := by rw [hs2]; simp [appendO, s1K, Codec.frame_eq_marks]
  have s2Kh : s2.sh KIN = 2 * ci.length + 1 := by rw [hs2]; simp [appendO, s1Kh]
  have s2op : s2.val opK = 2 * ci.length + 1 := by rw [hs2]; simp [appendO, s1op]
  -- 3. rewind KIN
  have e3 := wrewind_spec cap KIN opK (2 * ci.length + 1) s2 s2op (by omega)
  obtain ⟨s3, hs3⟩ : ∃ s, s = (s2.setv opK 0).seth KIN (s2.sh KIN - (2 * ci.length + 1)) := ⟨_, rfl⟩
  rw [← hs3] at e3
  have s3K : s3.st KIN = marks ci ++ [false] := by rw [hs3]; simp [s2K, Codec.frame_eq_marks]
  have s3Kh : s3.sh KIN = 0 := by rw [hs3]; simp [s2Kh]
  have s3O : s3.st OIN = [] := by
    rw [hs3]; simp only [WState.seth_st, WState.setv_st]
    rw [hs2]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, if_neg hOK]
    rw [hs1, adv_st_other _ _ _ _ hOK, hO]
  have s3Oh : s3.sh OIN = 0 := by
    rw [hs3]; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, if_neg hOK]
    rw [hs2]; simp only [appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, if_neg hOK]
    rw [hs1, adv_sh_other _ _ _ _ hOK hOD, hOh]
  have s3v : ∀ r, r ≠ opK → s3.val r = s1.val r := by
    intro r hr; rw [hs3]; simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg hr]
    rw [hs2]; simp [appendO, Function.update_apply, hr]
  have s3opK : s3.val opK = 0 := by rw [hs3]; simp
  -- 4. the marked pairs to OIN
  have e4 := pairLoop_spec cap (src := KIN) (dst := OIN) (OP := opO) (SC := scK) hKO (by decide)
    (emits_none cap) (emits_pair cap) [false] rfl ci [] s3 (by rw [s3K]; rfl) (by rw [s3Kh]; rfl)
    (by rw [s3O, s3Oh]; rfl)
    (by rw [s3v _ (by decide), hs1, adv_val_other _ _ _ _ (by decide) (by decide), hz]; simp; omega)
    (by rw [s3v _ (by decide), hs1, adv_val_other _ _ _ _ (by decide) (by decide), hz]; omega)
  obtain ⟨s4, hs4⟩ : ∃ s, s = adv KIN OIN opO scK s3 (ci.flatMap fun b => [] ++ [true, b]) (2 * ci.length) :=
    ⟨_, rfl⟩
  rw [← hs4] at e4
  have hu2 : (ci.flatMap fun b => ([] : List Bool) ++ [true, b]) = marks ci := by simp [marks]
  rw [hu2] at hs4
  have s4scK : s4.val scK = 2 * ci.length := by
    rw [hs4, adv_val_SC, s3v _ (by decide), hs1, adv_val_other _ _ _ _ (by decide) (by decide), hz]; omega
  have s4Kh : s4.sh KIN = 2 * ci.length := by rw [hs4, adv_sh_src, s3Kh]; omega
  -- 5. rewind KIN
  have e5 := wrewind_spec cap KIN scK (2 * ci.length) s4 s4scK (by omega)
  obtain ⟨s5, hs5⟩ : ∃ s, s = (s4.setv scK 0).seth KIN (s4.sh KIN - 2 * ci.length) := ⟨_, rfl⟩
  rw [← hs5] at e5
  have s5scD : s5.val scD = ci.length := by
    rw [hs5]; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hs4, adv_val_other _ _ _ _ (by decide) (by decide), s3v _ (by decide), hs1, adv_val_SC, hz]
    omega
  have s5Dh : s5.sh DO = 3 + ci.length := by
    rw [hs5]; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, if_neg hDK]
    rw [hs4, adv_sh_other _ _ _ _ hDO hDK, hs3]
    simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, if_neg hDK]
    rw [hs2]; simp only [appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, if_neg hDK]
    rw [hs1, adv_sh_src, hDh]
  -- 6. rewind DO
  have e6 := wrewind_spec cap DO scD ci.length s5 s5scD (by omega)
  obtain ⟨s6, hs6⟩ : ∃ s, s = (s5.setv scD 0).seth DO (s5.sh DO - ci.length) := ⟨_, rfl⟩
  rw [← hs6] at e6
  have s6D : s6.st DO = natWord 1 ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc false (natWord n) ++ vs.flatMap natWord := by
    rw [hs6]; simp only [WState.seth_st, WState.setv_st]
    rw [hs5]; simp only [WState.seth_st, WState.setv_st]
    rw [hs4, adv_st_other _ _ _ _ hDO, hs3]; simp only [WState.seth_st, WState.setv_st]
    rw [hs2]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, if_neg hDK]
    rw [hs1, adv_st_src hDK, hD, hci]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc]
  have s6Dh : s6.sh DO = (natWord 1).length := by rw [hs6]; simp [s5Dh]; decide
  have s6v : ∀ r, r ≠ opO → s6.val r = 0 := by
    intro r hr
    rw [hs6]; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs with h1; · rfl
    rw [hs5]; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs with h2; · rfl
    rw [hs4, adv_val_other _ _ _ _ hr h2]
    by_cases h3 : r = opK
    · subst h3; exact s3opK
    rw [s3v _ h3, hs1, adv_val_other _ _ _ _ h3 h1, hz]
  have s6op : s6.val opO = 2 * ci.length := by
    rw [hs6]; simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg (by decide : opO ≠ scD)]
    rw [hs5]; simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg (by decide : opO ≠ scK)]
    rw [hs4, adv_val_OP (by decide), s3v _ (by decide), hs1, adv_val_other _ _ _ _ (by decide) (by decide), hz, hul]
    omega
  -- 7. read `n`
  have e7 := readNatM_spec (cap := cap) false DO rf rc rN rp rt (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n (natWord 1) (vs.flatMap natWord) s6
    s6D s6Dh (s6v _ (by decide)) (s6v _ (by decide)) (s6v _ (by decide)) (s6v _ (by decide))
    (by rw [s6v _ (by decide)]; omega)
  obtain ⟨s7, hs7⟩ : ∃ s, s = (s6.seth DO ((natWord 1).length + stp false * (natWord n).length)).setv rN
      (s6.val rN + n) := ⟨_, rfl⟩
  rw [← hs7] at e7
  -- facts on the other streams through every step
  have other : ∀ i, i ≠ DO → i ≠ KIN → i ≠ OIN → s7.st i = σ.st i ∧ s7.sh i = σ.sh i := by
    intro i h1 h2 h3
    have a1 : s1.st i = σ.st i ∧ s1.sh i = σ.sh i :=
      ⟨by rw [hs1, adv_st_other _ _ _ _ h2], by rw [hs1, adv_sh_other _ _ _ _ h2 h1]⟩
    have a2 : s2.st i = σ.st i ∧ s2.sh i = σ.sh i := by
      rw [hs2]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        WState.sets_sh, Function.update_apply, if_neg h2]; exact a1
    have a3 : s3.st i = σ.st i ∧ s3.sh i = σ.sh i := by
      rw [hs3]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
        if_neg h2]; exact a2
    have a4 : s4.st i = σ.st i ∧ s4.sh i = σ.sh i :=
      ⟨by rw [hs4, adv_st_other _ _ _ _ h3]; exact a3.1, by rw [hs4, adv_sh_other _ _ _ _ h3 h2]; exact a3.2⟩
    have a5 : s5.st i = σ.st i ∧ s5.sh i = σ.sh i := by
      rw [hs5]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
        if_neg h2]; exact a4
    have a6 : s6.st i = σ.st i ∧ s6.sh i = σ.sh i := by
      rw [hs6]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
        if_neg h1]; exact a5
    rw [hs7]; simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
      if_neg h1]; exact a6
  have s7K : s7.st KIN = frame ci ∧ s7.sh KIN = 0 := by
    rw [hs7]; simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
      if_neg hKD]
    rw [hs6]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
      if_neg hKD]
    rw [hs5]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
      if_true]
    rw [s4Kh, hs4, adv_st_src hKO, s3K, Codec.frame_eq_marks]; exact ⟨rfl, by omega⟩
  have s7O : s7.st OIN = marks ci ∧ s7.sh OIN = 2 * ci.length := by
    rw [hs7]; simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
      if_neg hOD]
    rw [hs6]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
      if_neg hOD]
    rw [hs5]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
      if_neg hOK]
    rw [hs4, adv_st_dst, adv_sh_dst hKO, s3O, s3Oh, hul]; exact ⟨rfl, by omega⟩
  refine ⟨s7, ?_, s7K.1, s7K.2, s7O.1, s7O.2, ?_, ?_, ?_, other⟩
  · refine WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
      ?_
    unfold inKCost; nlinarith
  · rw [hs7]; simp only [WState.setv_val, Function.update_apply, if_neg (by decide : opO ≠ rN)]; exact s6op
  · rw [hs7]; simp [s6v _ (by decide : rN ≠ opO)]
  · intro r h1 h2
    rw [hs7]; simp only [WState.setv_val, Function.update_apply, if_neg h2]; exact s6v r h1

end InK

end NearCubicGates.Close.CounterAsm

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Recovery.HTParts

variable {ns : ℕ} (cap : ℕ)

section InO
variable (KO OIN : Fin (ns + 1))

/-- Append the cell tables' frames to `OIN` as marked pairs, close the frame, rewind. -/
def inO : WM ns 64 :=
  .seq (frameLoop KO scW (emitPair OIN opO)) (.seq (emitPair OIN opO false) (.seq (emitC OIN opO false)
    (WM.rewind OIN opO)))

variable {KO OIN}

theorem inO_run (hKO : KO ≠ OIN) (u0 : List Bool) (recs : List (List Bool)) (hne : ∀ x ∈ recs, x ≠ [])
    (σ : WState ns 64) (hK : σ.st KO = recs.flatMap frame ++ [false]) (hKh : σ.sh KO = 0)
    (hO : σ.st OIN = u0) (hOh : σ.sh OIN = u0.length) (hop : σ.val opO = u0.length) (hsc : σ.val scW = 0)
    (hcap : 4 * (u0.length + (recs.flatMap frame).length) + 10 ≤ cap) :
    ∃ τ : WState ns 64, WExec cap (inO KO OIN) σ τ (100 * (u0.length + (recs.flatMap frame).length) + 100) ∧
      τ.st OIN = u0 ++ marks (recs.flatMap frame ++ [false]) ++ [false] ∧ τ.sh OIN = 0 ∧ τ.val opO = 0 ∧
      (∀ r, r ≠ opO → r ≠ scW → τ.val r = σ.val r) ∧
      (∀ i, i ≠ KO → i ≠ OIN → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) := by
  obtain ⟨F, hF⟩ : ∃ F, F = recs.flatMap frame := ⟨_, rfl⟩
  rw [← hF] at hK hcap ⊢
  have hOK := Ne.symm hKO
  have hul : (marks F).length = 2 * F.length := by simp [marks]; omega
  have e1 := frameLoop_spec cap (src := KO) (dst := OIN) (OP := opO) (SC := scW) hKO (by decide)
    (emits_pair cap) (d := 2) (fun _ => by simp) [false] rfl recs [] σ hne (by rw [hK, hF]; rfl) (by rw [hKh]; rfl)
    (by rw [hO, hOh]) (by rw [hop, ← hF]; omega) (by rw [hsc, ← hF]; omega)
  rw [← hF] at e1
  obtain ⟨s1, hs1⟩ : ∃ s, s = adv KO OIN opO scW σ (F.flatMap fun b => [true, b]) F.length := ⟨_, rfl⟩
  rw [← hs1] at e1
  have hu : (F.flatMap fun b => [true, b]) = marks F := rfl
  rw [hu] at hs1
  have s1O : s1.st OIN = u0 ++ marks F := by rw [hs1, adv_st_dst, hO]
  have s1Oh : s1.sh OIN = u0.length + 2 * F.length := by rw [hs1, adv_sh_dst hKO, hOh, hul]
  have s1op : s1.val opO = u0.length + 2 * F.length := by rw [hs1, adv_val_OP (by decide), hop, hul]
  have e2 := emits_pair cap (dst := OIN) (OP := opO) false s1 (by rw [s1O, s1Oh]; simp [hul])
    (by rw [s1op]; simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨s2, hs2⟩ : ∃ s, s = appendO s1 OIN opO [true, false] := ⟨_, rfl⟩
  rw [← hs2] at e2
  have s2O : s2.st OIN = u0 ++ marks F ++ [true, false] := by rw [hs2]; simp [appendO, s1O]
  have s2Oh : s2.sh OIN = u0.length + 2 * F.length + 2 := by rw [hs2]; simp [appendO, s1Oh]
  have s2op : s2.val opO = u0.length + 2 * F.length + 2 := by rw [hs2]; simp [appendO, s1op]
  have e3 := emits_raw cap (dst := OIN) (OP := opO) false s2 (by rw [s2O, s2Oh]; simp [hul]; omega)
    (by rw [s2op]; simp only [List.length_singleton]; omega)
  obtain ⟨s3, hs3⟩ : ∃ s, s = appendO s2 OIN opO [false] := ⟨_, rfl⟩
  rw [← hs3] at e3
  have s3op : s3.val opO = u0.length + 2 * F.length + 3 := by rw [hs3]; simp [appendO, s2op]
  have s3Oh : s3.sh OIN = u0.length + 2 * F.length + 3 := by rw [hs3]; simp [appendO, s2Oh]
  have e4 := wrewind_spec cap OIN opO (u0.length + 2 * F.length + 3) s3 s3op (by omega)
  obtain ⟨s4, hs4⟩ : ∃ s, s = (s3.setv opO 0).seth OIN (s3.sh OIN - (u0.length + 2 * F.length + 3)) := ⟨_, rfl⟩
  rw [← hs4] at e4
  refine ⟨s4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_
    nlinarith
  · rw [hs4]; simp only [WState.seth_st, WState.setv_st]
    rw [hs3]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [s2O]
    have : marks (F ++ [false]) = marks F ++ [true, false] := by simp [marks]
    rw [this]; simp
  · rw [hs4]; simp [s3Oh]
  · rw [hs4]; simp
  · intro r h1 h2
    rw [hs4]; simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg h1]
    rw [hs3]; simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, if_neg h1]
    rw [hs2]; simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, if_neg h1]
    rw [hs1, adv_val_other _ _ _ _ h1 h2]
  · intro i h1 h2
    rw [hs4]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_apply,
      if_neg h2]
    rw [hs3]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
      WState.sets_sh, Function.update_apply, if_neg h2]
    rw [hs2]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
      WState.sets_sh, Function.update_apply, if_neg h2]
    exact ⟨by rw [hs1, adv_st_other _ _ _ _ h2], by rw [hs1, adv_sh_other _ _ _ _ h2 h1]⟩

end InO

end NearCubicGates.Close.CounterAsm
