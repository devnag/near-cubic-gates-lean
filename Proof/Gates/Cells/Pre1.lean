import Proof.Gates.Cells.Walk

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def wG : Fin VV := ⟨73, by decide⟩
def wC : Fin VV := ⟨74, by decide⟩
def wTb : Fin VV := ⟨75, by decide⟩

def circW (ts tw : Fin VV) : St VV MM :=
  .seq (rdW wG) (.seq (.op (.mul wG gS wY)) (.seq skW (.seq (rdW wC) (.seq (.op (.copy wY wC))
  (.seq (.op (.shl wY)) (.seq skW (.seq (rdW wTb) (.seq (.op (.copy ts wPos)) (.seq (.op (.copy tw wTb))
  (.seq (.op (.sub tw v1)) (.seq (.op (.half tw)) (.seq (.op (.copy wY wTb)) skW))))))))))))

theorem circN_len {n : ℕ} (Cc : NCircuit n) : (circN Cc).length =
    1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 + Cc.table.length := by
  simp only [circN, List.length_append, List.length_singleton, flatMap_intN_length, flatMap_gateN_length,
    List.length_map]

theorem circW_spec {n : ℕ} (ts tw : Fin VV) (hts : ts ∉ [wG, wY, wC, wTb, wPos, gS, v1, c0, vJ])
    (htw : tw ∉ [wG, wY, wC, wTb, wPos, gS, v1, c0, vJ, ts]) (L : List ℕ) (e : DS VV MM) (pos : ℕ)
    (Cc : NCircuit n) (rest : List ℕ) (h : WSt L e pos (circN Cc ++ rest)) (hc : Cst e)
    (hS : e.env gS = 2 * n + 3) (hT1 : 1 ≤ Cc.table.length)
    (hW : pos + (circN Cc).length + 2 * n + 4 < 2 ^ C.Wd) :
    Hs C (circW ts tw) e (20 * (circN Cc).length + 100) (fun d =>
      WSt L d (pos + (circN Cc).length) rest ∧
      d.env ts = pos + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 ∧
      d.env tw = (Cc.table.length - 1) / 2 ∧ L.drop (d.env ts) = Cc.table.map bitN ++ rest ∧
      Agr e d [sN] [wG, wY, wC, wTb, wPos, c0, vJ, ts, tw]) := by
  have hcl := circN_len Cc
  have hG3 : Cc.gates.length ≤ Cc.gates.length * (2 * n + 3) := Nat.le_mul_of_pos_right _ (by omega)
  have hsp : circN Cc ++ rest = Cc.gates.length :: (Cc.gates.flatMap gateN ++ (Cc.coeffs.length :: (Cc.coeffs.flatMap intN ++
      (Cc.table.length :: (Cc.table.map bitN ++ rest))))) := by simp [circN, List.append_assoc]
  rw [hsp] at h
  -- gates
  refine Hs.bseq (rdW_spec wG (by decide) L e pos Cc.gates.length _ h (by omega)) (by omega) (fun e1 ⟨u1, w1, a1⟩ => ?_)
  have e1S : e1.env gS = 2 * n + 3 := by rw [a1.fr gS (by decide), hS]
  refine Hs.bseq (hs_mul C wG gS wY e1 (by decide) (by decide) (by decide) (by rw [u1, e1S]; omega))
    (by omega) (fun e2 he2 => ?_)
  subst he2
  have w2 : WSt L (e1.set wY (e1.env wG * e1.env gS)) (pos + 1) (Cc.gates.flatMap gateN ++ (Cc.coeffs.length ::
      (Cc.coeffs.flatMap intN ++ (Cc.table.length :: (Cc.table.map bitN ++ rest))))) :=
    ⟨w1.ram, w1.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact w1.pv, w1.dr, w1.le⟩
  have hsk := skW_spec (C := C) L _ (pos + 1) _ _ w2 (by rw [DS.set_env_self, u1, e1S, flatMap_gateN_length])
    (by rw [flatMap_gateN_length]; omega)
  rw [flatMap_gateN_length] at hsk
  refine Hs.bseq hsk (by omega) (fun e3 ⟨w3, _, a3⟩ => ?_)
  -- coefficients
  refine Hs.bseq (rdW_spec wC (by decide) L e3 _ Cc.coeffs.length _ w3 (by omega)) (by omega) (fun e4 ⟨u4, w4, a4⟩ => ?_)
  refine Hs.bseq (hs_copy C wY wC e4 (by decide)) (by omega) (fun e5 he5 => ?_)
  subst he5
  refine Hs.bseq (hs_shl C wY _ (by rw [DS.set_env_self, u4]; omega)) (by omega) (fun e6 he6 => ?_)
  subst he6
  have w6 : WSt L ((e4.set wY (e4.env wC)).set wY (2 * (e4.set wY (e4.env wC)).env wY)) (pos + 1 + Cc.gates.length * (2 * n + 3) + 1)
      (Cc.coeffs.flatMap intN ++ (Cc.table.length :: (Cc.table.map bitN ++ rest))) :=
    ⟨w4.ram, w4.rc, by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact w4.pv, w4.dr, w4.le⟩
  have hsk2 := skW_spec (C := C) L _ _ _ _ w6 (by rw [DS.set_env_self, DS.set_env_self, u4, flatMap_intN_length])
    (by rw [flatMap_intN_length]; omega)
  rw [flatMap_intN_length] at hsk2
  refine Hs.bseq hsk2 (by omega) (fun e7 ⟨w7, _, a7⟩ => ?_)
  -- table
  refine Hs.bseq (rdW_spec wTb (by decide) L e7 _ Cc.table.length _ w7 (by omega)) (by omega) (fun e8 ⟨u8, w8, a8⟩ => ?_)
  have hts' : ts ≠ wPos ∧ ts ≠ wTb ∧ ts ≠ v1 ∧ ts ≠ wY := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hts; exact ⟨hts.2.2.2.2.1, hts.2.2.2.1,
      hts.2.2.2.2.2.2.1, hts.2.1⟩
  have htw' : tw ≠ wPos ∧ tw ≠ wTb ∧ tw ≠ v1 ∧ tw ≠ wY ∧ tw ≠ ts := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htw; exact ⟨htw.2.2.2.2.1, htw.2.2.2.1,
      htw.2.2.2.2.2.2.1, htw.2.1, htw.2.2.2.2.2.2.2.2.2⟩
  have e8v1 : e8.env v1 = 1 := by
    rw [a8.fr v1 (by decide), a7.fr v1 (by decide)]
    simp only [DS.set_env_ne _ _ (show v1 ≠ wY by decide)]
    rw [a4.fr v1 (by decide), a3.fr v1 (by decide), DS.set_env_ne _ _ (by decide), a1.fr v1 (by decide), hc.one]
  refine Hs.bseq (hs_copy C ts wPos e8 hts'.1) (by omega) (fun e9 he9 => ?_)
  subst he9
  refine Hs.bseq (hs_copy C tw wTb _ htw'.2.1) (by omega) (fun e10 he10 => ?_)
  subst he10
  refine Hs.bseq (hs_sub C tw v1 _ htw'.2.2.1 (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (Ne.symm htw'.2.2.1), DS.set_env_ne _ _ (Ne.symm hts'.2.2.1),
      DS.set_env_ne _ _ (Ne.symm hts'.2.1), e8v1, u8]; exact hT1)) (by omega) (fun e11 he11 => ?_)
  subst he11
  refine Hs.bseq (hs_half C tw _) (by omega) (fun e12 he12 => ?_)
  subst he12
  refine Hs.bseq (hs_copy C wY wTb _ (by decide)) (by omega) (fun e13 he13 => ?_)
  subst he13
  have hAgr : ∀ (f : DS VV MM), Agr e8 f [sN] [wG, wY, wC, wTb, wPos, c0, vJ, ts, tw] →
      Agr e f [sN] [wG, wY, wC, wTb, wPos, c0, vJ, ts, tw] := fun f hf =>
    (a1.weaken (by decide) (by simp)).trans ((Agr.set _ _ _ (by simp)).trans ((a3.weaken (by decide) (by simp)).trans
      ((a4.weaken (by decide) (by simp)).trans ((Agr.set _ _ _ (by simp)).trans ((Agr.set _ _ _ (by simp)).trans
      ((a7.weaken (by decide) (by simp)).trans ((a8.weaken (by decide) (by simp)).trans hf)))))))
  refine Hs.mono (skW_spec (C := C) L _ _ (Cc.table.map bitN) rest ⟨?_, ?_, ?_, w8.dr, w8.le⟩ ?_ ?_)
    (by simp only [List.length_map]; omega) ?_
  · simp only [DS.set_ram]; exact w8.ram
  · simp only [DS.set_rc]; exact w8.rc
  · simp only [DS.set_env_ne _ _ (show wPos ≠ wY by decide), DS.set_env_ne _ _ (Ne.symm htw'.1),
      DS.set_env_ne _ _ (Ne.symm hts'.1)]; exact w8.pv
  · rw [DS.set_env_self]
    simp only [DS.set_env_ne _ _ (show wTb ≠ wY by decide), DS.set_env_ne _ _ (Ne.symm htw'.2.1),
      DS.set_env_ne _ _ (Ne.symm hts'.2.1)]
    rw [u8, List.length_map]
  · simp only [List.length_map]; omega
  · rintro d ⟨d1, d2, d3⟩
    have hp : pos + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 + (Cc.table.map bitN).length =
        pos + (circN Cc).length := by rw [List.length_map, hcl]; omega
    have hts2 : d.env ts = pos + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 := by
      rw [d3.fr ts (by simp at hts ⊢; tauto)]
      simp only [DS.set_env_ne _ _ hts'.2.2.2, DS.set_env_ne _ _ (Ne.symm htw'.2.2.2.2), DS.set_env_self]
      rw [w8.pv]
    refine ⟨by rw [← hp]; exact d1, ?_, ?_, by rw [hts2]; exact w8.dr, hAgr d (((Agr.set _ _ _ (by simp)).trans ((Agr.set _ _ _ (by simp)).trans
      ((Agr.set _ _ _ (by simp)).trans ((Agr.set _ _ _ (by simp)).trans (Agr.set _ _ _ (by simp)))))).trans
      (d3.weaken (by decide) (by simp)))⟩
    · rw [d3.fr ts (by simp at hts ⊢; tauto)]
      simp only [DS.set_env_ne _ _ hts'.2.2.2, DS.set_env_ne _ _ (Ne.symm htw'.2.2.2.2), DS.set_env_self]
      rw [w8.pv]
    · rw [d3.fr tw (by simp at htw ⊢; tauto)]
      simp only [DS.set_env_ne _ _ htw'.2.2.2.1, DS.set_env_self]
      simp only [DS.set_env_ne _ _ (Ne.symm htw'.2.2.1), DS.set_env_ne _ _ (Ne.symm hts'.2.2.1), DS.set_env_self,
        DS.set_env_ne _ _ (Ne.symm hts'.2.1), e8v1, u8]

end NearCubicGates.Close.Cells
