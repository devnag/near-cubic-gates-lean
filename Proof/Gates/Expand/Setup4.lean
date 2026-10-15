import Proof.Gates.Expand.Setup3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem U_NB (i : Fin 10) (hi : i ≠ 0) : U i = NB ⟨i.val - 1, by omega⟩ := (NB_U i hi).symm

theorem evAt_of_mv (Wb : ℕ) (w : Fin 53 → ℕ) (τ : WState NS NR) (hw : MV NB Wb w τ) (inp : List Bool)
    (hinp : τ.st (U 0) = inp) (hhd : τ.sh (U 0) = 0) (hR : ∀ j, τ.val (R j) = 0) (h0 : w 0 = 0) (h7 : w 7 = 1) :
    EvAt U R Wb (w 5) (w 6) (w 8) inp 0 [] τ := by
  refine ⟨⟨fun i hi => ?_, ?_, ?_, ?_, ?_, fun j _ => hR j⟩, hinp, hhd, ?_⟩
  · have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    exact ⟨_, by rw [U_NB i hi0]; exact hw _⟩
  · rw [U_NB 6 (by decide)]; exact hw 5
  · rw [U_NB 7 (by decide)]; exact hw 6
  · rw [U_NB 8 (by decide)]; have := hw 7; rwa [h7] at this
  · rw [U_NB 9 (by decide)]; exact hw 8
  · rw [U_NB 1 (by decide)]; have := hw 0; rwa [h0] at this

theorem nb_evS (j : Fin 53) (hj : 5 ≤ j.val) : NB j ∉ evS U := by
  intro hm
  have : (NB j).val ≤ 5 := by
    simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> rw [h] <;> simp
  simp only [NB_val, nbv] at this; split_ifs at this <;> omega

theorem mv_of_evAt (Wb m k t : ℕ) (w : Fin 53 → ℕ) (σ τ : WState NS NR) (hw : MV NB Wb w σ) {Rg : List (Fin NR)}
    (f : SameExcept σ τ (evS U) Rg) (inp : List Bool) (hd : ℕ) (xs : List ℕ)
    (he : EvAt U R Wb m k t inp hd xs τ) (x : ℕ) (hx : NumOn τ (U 2) Wb x) :
    ∃ w', MV NB Wb w' τ ∧ (∀ j : Fin 53, 5 ≤ j.val → w' j = w j) ∧ w' 1 = x ∧ w' 0 = senc m xs := by
  classical
  have hex : ∀ j : Fin 53, ∃ y, NumOn τ (NB j) Wb y ∧ (5 ≤ j.val → y = w j) ∧ (j = 1 → y = x) ∧
      (j = 0 → y = senc m xs) := by
    intro j
    by_cases h5 : 5 ≤ j.val
    · refine ⟨w j, f.numOn (nb_evS j h5) (hw j), fun _ => rfl, fun e => by subst e; simp at h5,
        fun e => by subst e; simp at h5⟩
    · have hU : NB j = U ⟨j.val + 1, by omega⟩ := by
        apply Fin.ext; simp only [NB_val, U_val, nbv]; split_ifs <;> omega
      by_cases e0 : j = 0
      · subst e0; refine ⟨senc m xs, ?_, fun h => by simp at h, fun h => by simp at h, fun _ => rfl⟩
        rw [hU]; exact he.stk
      · by_cases e1 : j = 1
        · subst e1; refine ⟨x, ?_, fun h => by simp at h, fun _ => rfl, fun h => by simp at h⟩
          rw [hU]; exact hx
        · obtain ⟨y, hy⟩ := he.ev.num ⟨j.val + 1, by omega⟩ (by
            have := Fin.val_ne_of_ne e0; have := Fin.val_ne_of_ne e1
            simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff] at *
            simp only [Fin.isValue, Fin.val_one, Fin.val_two, Fin.val_zero] at *
            omega)
          exact ⟨y, by rw [hU]; exact hy, fun h => absurd h h5, fun h => absurd h e1, fun h => absurd h e0⟩
  choose w' hw' using hex
  exact ⟨w', fun j => (hw' j).1, fun j hj => (hw' j).2.1 hj, (hw' 1).2.2.1 rfl, (hw' 0).2.2.2 rfl⟩

/-- One evaluation pass followed by `toReg` of its result into `T`. -/
def passA (hs : List (WMX NS NR)) (T : Fin NR) : WMX NS NR := .seq (evalPass U R (Y 0) (Y 1) hs) (toReg 1 8 7 T)

theorem passA_spec (cap Wb m k c : ℕ) (A : Alg) (hA : A.Closed m) (hm2 : 2 ≤ m) (hs : List (WMX NS NR))
    (hlen : hs.length = 7) (r : FormulaReq)
    (hh : ∀ tok ∈ toks r.2, HSpec U R cap Wb m k 0 A (hs.getD (tagOf tok) WMX.skip) tok c)
    (T : Fin NR) (hT : ∀ j, R j ≠ T) (hT1 : T ≠ GLr) (hT2 : T ≠ F0) (hT3 : T ≠ R0)
    (σ : WState NS NR) (w : Fin 53 → ℕ) (hw : MV NB Wb w σ) (h0 : w 0 = 0) (h5 : w 5 = m) (h6 : w 6 = k)
    (h7 : w 7 = 1) (h8 : w 8 = 0) (hinp : σ.st (U 0) = frame (formulaWord r)) (hhd : σ.sh (U 0) = 0)
    (hR : ∀ j, σ.val (R j) = 0) (hY0 : σ.val (Y 0) = 2 * (formulaWord r).length + 1) (hY1 : σ.val (Y 1) = 0)
    (hF : σ.val F0 = 0) (hR0 : σ.val R0 = 0) (hG : σ.val GLr = 0) (hTv : σ.val T = 0)
    (hval : A.eval r.2 < 2 ^ Wb) (hdepth : m ^ ((toks r.2).length + 2) ≤ 2 ^ Wb) (hcapW : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ ((formulaWord r).length + 4) ≤ cap) (hcapT : A.eval r.2 + 1 ≤ cap) :
    Runs cap (passA hs T) σ (evalCost Wb c r.1 (toks r.2).length (formulaWord r).length + 1 +
        toRegCost Wb (A.eval r.2))
      (fun τ => (∃ w', MV NB Wb w' τ ∧ (∀ j : Fin 53, 5 ≤ j.val → w' j = w j) ∧ w' 0 = 0 ∧ w' 1 = 0) ∧
        τ.val T = A.eval r.2 ∧ τ.st (U 0) = frame (formulaWord r) ∧ τ.sh (U 0) = 0 ∧ (∀ j, τ.val (R j) = 0) ∧
        (∀ q, q ∉ (T :: (evR R ++ [R 11])) → τ.val q = σ.val q) ∧
        ∀ x, x ∉ nbList → x ≠ U 0 → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) := by
  have hE := evAt_of_mv Wb w σ hw _ hinp hhd hR h0 h7
  rw [h5, h6, h8] at hE
  have hRL : ∀ j, R j ≠ Y 0 := fun j => rne (by have := j.isLt; simp; omega)
  have hRL2 : ∀ j, R j ≠ Y 1 := fun j => rne (by have := j.isLt; simp; omega)
  refine Runs.seq (evalPass_spec cap Wb m k 0 c A hA hm2 hs hlen r hh (Y 0) (Y 1) hRL hRL2 (rne (by simp)) σ hE
    (hR 11) hY0 hY1 hdepth hcapW hcapL) (fun τ1 ⟨e1, n1, r11, rl1, rl21, f1⟩ => ?_)
  obtain ⟨w1, hw1, hw1j, hw11, hw10⟩ := mv_of_evAt Wb m k 0 w σ τ1 hw f1 _ 0 [] e1 _ n1
  have nR : ∀ q, q ∉ evR R ++ [R 11] → τ1.val q = σ.val q := fun q hq => f1.val hq
  have kF : F0 ∉ evR R ++ [R 11] := by simp [evR, F0, Fin.ext_iff]
  have kR0 : R0 ∉ evR R ++ [R 11] := by simp [evR, R0, Fin.ext_iff]
  have kG : GLr ∉ evR R ++ [R 11] := by simp [evR, GLr, Fin.ext_iff]
  have kT : T ∉ evR R ++ [R 11] := by
    simp only [evR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨(hT 0).symm, (hT 1).symm, (hT 2).symm, (hT 3).symm, (hT 4).symm, (hT 5).symm, (hT 6).symm, (hT 7).symm,
      (hT 8).symm, (hT 9).symm, (hT 10).symm⟩, (hT 11).symm⟩
  have hts : TS T τ1 τ1 0 0 := ⟨by rw [nR _ kF, hF], by rw [nR _ kR0, hR0], by rw [nR _ kG, hG],
    by rw [nR _ kT, hTv], fun _ _ _ _ => rfl⟩
  have hw17 : w1 7 = 1 := by rw [hw1j 7 (by decide), h7]
  have hw18 : w1 8 = 0 := by rw [hw1j 8 (by decide), h8]
  refine (toReg_spec cap Wb 1 8 7 (by decide) (by decide) T hT1 hT2 hT3 τ1 w1 hw1 hw18 hw17 (by rw [hw11]; exact hval)
    0 hts (by omega) (by rw [hw11]; omega)).mono (by rw [hw11]) (fun τ ⟨m2, ⟨s0, s1, sg, st, so⟩, fx⟩ => ?_)
  have hU0 : U 0 ≠ NB 1 := (NB_ne_0 1).symm
  refine ⟨⟨_, m2, fun j hj => ?_, ?_, ?_⟩, by rw [st, hw11]; simp, ?_, ?_, fun j => ?_, fun q hq => ?_, fun x hx h0x => ?_⟩
  · rw [Function.update_of_ne (by rintro rfl; simp at hj), hw1j j hj]
  · rw [Function.update_of_ne (by decide), hw10]; rfl
  · simp
  · rw [(fx (U 0) hU0).1]; exact e1.inp
  · rw [(fx (U 0) hU0).2]; exact e1.hd
  · rw [so (R j) (rne (by have := j.isLt; simp [GLr]; omega)) (hT j) (rne (by have := j.isLt; simp [F0]; omega))]
    by_cases h11 : j = 11
    · subst h11; exact r11
    · exact e1.ev.zero j h11
  · simp only [List.mem_cons, not_or] at hq
    by_cases eG : q = GLr
    · subst eG; rw [sg, hG]
    · by_cases eF : q = F0
      · subst eF; rw [s0, hF]
      · rw [so q eG hq.1 eF]; exact nR q hq.2
  · have hxn : x ≠ NB 1 := fun e => hx (e ▸ mem_nbList 1)
    rw [(fx x hxn).1, (fx x hxn).2]
    have hxe : x ∉ evS U := by
      intro hm
      simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h0x rfl
      all_goals exact hx (by rw [U_NB _ (by decide)]; exact mem_nbList _)
    exact ⟨f1.st hxe, f1.sh hxe⟩

end NearCubicGates.Close.Expand.Layout
