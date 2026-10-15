import Proof.Gates.WorkerArith.TermB

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit)

variable {ns nr : ℕ}

/-- The stream distinctions of a term environment. -/
theorem TermBase.dis {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
    {rows : ℕ → List ℕ} {Rn : ℕ} {w pre rest : List Bool} {σ : WState ns nr}
    (hB : TermBase E tmap Cs N rows Rn w pre rest σ) :
    (E.CW ≠ E.SUP ∧ E.CW ≠ E.S1 ∧ E.CW ≠ E.S2 ∧ E.CW ≠ E.TL ∧ E.CW ≠ E.G ∧ E.CW ≠ E.L ∧ E.CW ≠ E.VI ∧ E.CW ≠ E.WT) ∧
    (E.SUP ≠ E.S1 ∧ E.SUP ≠ E.S2 ∧ E.SUP ≠ E.TL ∧ E.SUP ≠ E.G ∧ E.SUP ≠ E.L ∧ E.SUP ≠ E.VI ∧ E.SUP ≠ E.WT) ∧
    (E.S1 ≠ E.S2 ∧ E.S1 ≠ E.TL ∧ E.S1 ≠ E.G ∧ E.S1 ≠ E.L ∧ E.S1 ≠ E.VI ∧ E.S1 ≠ E.WT) ∧
    (E.S2 ≠ E.TL ∧ E.S2 ≠ E.G ∧ E.S2 ≠ E.L ∧ E.S2 ≠ E.VI ∧ E.S2 ≠ E.WT) ∧
    (E.TL ≠ E.G ∧ E.TL ≠ E.L ∧ E.TL ≠ E.VI ∧ E.TL ≠ E.WT) ∧ (E.G ≠ E.L ∧ E.G ≠ E.VI ∧ E.G ≠ E.WT) ∧
    (E.L ≠ E.VI ∧ E.L ≠ E.WT) ∧ E.VI ≠ E.WT := by
  have hd := hB.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨a, b, c, d, e, f, g, h, -⟩ := hd
  exact ⟨a, b, c, d, e, f, g, h⟩

theorem TermBase.tne {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
    {rows : ℕ → List ℕ} {Rn : ℕ} {w pre rest : List Bool} {σ : WState ns nr}
    (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (j : Fin t) :
    tmap j ≠ E.CW ∧ tmap j ≠ E.SUP ∧ tmap j ≠ E.S1 ∧ tmap j ≠ E.S2 ∧ tmap j ≠ E.TL ∧ tmap j ≠ E.G ∧ tmap j ≠ E.L ∧
      tmap j ≠ E.VI ∧ tmap j ≠ E.WT := by
  have h := hB.tdis j
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

theorem gIdx_lo : ∀ i : Fin 8, i ≠ 7 → 10 ≤ (gIdx i).val ∧ (gIdx i).val ≤ 16 := by decide
theorem pIdx_hi : ∀ f : Fin 40, ∀ i : Fin 8, 2 ≤ i.val → 26 ≤ (pIdx f i).val ∧ (pIdx f i).val ≤ 31 := by decide
theorem pIdx_gIdx : ∀ i k : Fin 8, pIdx 0 i ≠ gIdx k ∧ pIdx 39 i ≠ gIdx k := by decide

theorem pT_gT_ne (R : Fin 40 ↪ Fin nr) (f : Fin 40) (hf : f = 0 ∨ f = 39) (i k : Fin 8) : pT R f hf i ≠ gT R k := by
  rw [pT_apply, gT_apply]
  intro h
  have h' := R.injective h
  rcases hf with rfl | rfl
  · exact (pIdx_gIdx i k).1 h'
  · exact (pIdx_gIdx i k).2 h'

theorem pT_zero (R : Fin 40 ↪ Fin nr) (f : Fin 40) (hf : f = 0 ∨ f = 39) : pT R f hf 0 = R f := rfl
theorem pT_one (R : Fin 40 ↪ Fin nr) (f : Fin 40) (hf : f = 0 ∨ f = 39) : pT R f hf 1 = R 17 := rfl
theorem gT_seven (R : Fin 40 ↪ Fin nr) : gT R 7 = R 9 := rfl

/-- The state right after a call writer. -/
structure FinPre (E : TermEnv ns nr) (σ ρ : WState ns nr) (c : Call) (Z : ℕ) : Prop where
  s1 : ρ.st E.S1 = frame (callWord c)
  s1h : ρ.sh E.S1 = (frame (callWord c)).length
  v17 : ρ.val (E.R 17) = (frame (callWord c)).length
  cws : ρ.st E.CW = σ.st E.CW
  cw : ρ.sh E.CW ≤ σ.val (E.R 7)
  sups : ρ.st E.SUP = σ.st E.SUP
  sup : ρ.sh E.SUP ≤ σ.val (E.R 8)
  fr : SameExcept σ ρ [E.S1, E.CW, E.SUP] [E.R 17, E.R 23, E.R 24]
  v23 : ρ.val (E.R 23) ≤ Z
  v24 : ρ.val (E.R 24) ≤ Z

section Fin
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {w pre rest : List Bool} {σ ρ : WState ns nr} {c : Call} {Z : ℕ}

theorem FinPre.stO (hF : FinPre E σ ρ c Z) (x : Fin (ns + 1)) (a : x ≠ E.S1) (b : x ≠ E.CW) (d : x ≠ E.SUP) :
    ρ.st x = σ.st x ∧ ρ.sh x = σ.sh x :=
  hF.fr.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b, d⟩)

theorem FinPre.vO (hF : FinPre E σ ρ c Z) (k : Fin 40) (a : k ≠ 17) (b : k ≠ 23) (d : k ≠ 24) :
    ρ.val (E.R k) = σ.val (E.R k) :=
  hF.fr.2.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨R_ne E a, R_ne E b, R_ne E d⟩)

theorem FinPre.zO (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z) (k : Fin 40)
    (a : 10 ≤ k.val) (b : k.val < 39) (d : k ≠ 17) (e : k ≠ 23) (g : k ≠ 24) : ρ.val (E.R k) = 0 := by
  rw [hF.vO k d e g]; exact hB.z k a b

/-- Rewinding the call stream. -/
theorem callFin_front (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z)
    (hc : (frame (callWord c)).length ≤ cap) :
    WExec cap (.seq (Codec.dupR (E.R 17) (E.R 38) (E.R 35)) (WM.rewind E.S1 (E.R 38))) ρ (ρ.seth E.S1 0)
      (23 * (frame (callWord c)).length + 5) := by
  set n := (frame (callWord c)).length with hn
  have e1 := Codec.dupR_spec cap (E.R 17) (E.R 38) (E.R 35) (R_ne E (by decide)) (R_ne E (by decide))
    (R_ne E (by decide)) ρ (hF.zO hB 35 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hF.v17, hF.zO hB 38 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  rw [hF.v17, hF.zO hB 38 (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_add] at e1
  have e2 := wrewind_spec (cap := cap) E.S1 (E.R 38) n (ρ.setv (E.R 38) n) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · simp only [WState.seth, WState.setv, hF.s1h, ← hn, Nat.sub_self]
  · funext r
    by_cases hr : r = E.R 38
    · subst hr; simp [hF.zO hB 38 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · simp [Function.update_of_ne hr]

end Fin

/-- The cost of `callFinW` beyond the call tail. -/
def finCost (t cw w b n Z : ℕ) : ℕ := tailCost t cw w b + 30 * n + 60 * Z + 100

/-- The call tail from the rewound state. -/
theorem callFin_tail {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) (f : Fin 40) (hf : f = 0 ∨ f = 39)
    {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {c : Call} {w pre rest : List Bool}
    (cap Z : ℕ) {σ ρ : WState ns nr} (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z)
    (hcap : σ.val (E.R 9) + 8 * ((callWord c).length + w.length + ctr.budget c w) + 60 ≤ cap) :
    ∃ τ3, WXExec cap (callTailP ctr tmap E.S1 E.S2 E.TL E.G E.L E.VI E.WT (gT E.R) (pT E.R f hf)) (ρ.seth E.S1 0) τ3
        (tailCost ctr.program.program.tapeCount (callWord c).length w.length (ctr.budget c w)) ∧
      SimW (tailIdeal (ρ.seth E.S1 0) tmap E.S1 E.S2 E.TL E.G E.VI E.WT (E.R 9) (E.R 17)
        (pre.length + w.length + 1 + w.length) (bitWord (decide (σ.val (E.R f) ≠ 0)) ++ outputWord (ctr.value c w))) τ3 := by
  obtain ⟨⟨cS, c1, c2, cT, cG, cL, cV, cW⟩, ⟨s1, s2, sT, sG, sL, sV, sW⟩, ⟨h12, h1T, h1G, h1L, h1V, h1W⟩,
    ⟨h2T, h2G, h2L, h2V, h2W⟩, ⟨hTG, hTL, hTV, hTW⟩, ⟨hGL, hGV, hGW⟩, ⟨hLV, hLW⟩, hVW⟩ := hB.dis
  have sh2 : ∀ x, x ≠ E.S1 → (ρ.seth E.S1 0).sh x = ρ.sh x := fun x hx => by simp [Function.update_of_ne hx]
  have st2 : ∀ x, (ρ.seth E.S1 0).st x = ρ.st x := fun x => rfl
  have v2 : ∀ r, (ρ.seth E.S1 0).val r = ρ.val r := fun r => rfl
  have zz : ∀ k : Fin 40, 10 ≤ k.val → k.val ≤ 31 → k ≠ 17 → k ≠ 23 → k ≠ 24 → (ρ.seth E.S1 0).val (E.R k) = 0 :=
    fun k a b d e g => by rw [v2]; exact hF.zO hB k a (by omega) d e g
  obtain ⟨τ3, e3, s3⟩ := callTail_ideal ctr c w cap tmap E.S1 E.S2 E.TL E.G E.L E.VI E.WT (gT E.R) (pT E.R f hf) pre rest
    (ρ.seth E.S1 0) hB.inj (fun j => (hB.tne j).2.2.1) (fun j => (hB.tne j).2.2.2.1) (fun j => (hB.tne j).2.2.2.2.1)
    (fun j => (hB.tne j).2.2.2.2.2.1) (fun j => (hB.tne j).2.2.2.2.2.2.1) (fun j => (hB.tne j).2.2.2.2.2.2.2.1)
    (fun j => (hB.tne j).2.2.2.2.2.2.2.2) hB.nd.of_cons.of_cons (pT_gT_ne E.R f hf)
    (by rw [st2]; exact hF.s1) (by simp) (by rw [pT_one, v2, hF.v17])
    (by rw [st2, (hF.stO _ (Ne.symm h12) (Ne.symm c2) (Ne.symm s2)).1]; exact hB.b2)
    (by rw [sh2 _ (Ne.symm h12), (hF.stO _ (Ne.symm h12) (Ne.symm c2) (Ne.symm s2)).2]; exact hB.h2)
    (fun j => by
      rw [st2, (hF.stO _ (hB.tne j).2.2.1 (hB.tne j).1 (hB.tne j).2.1).1]; exact hB.bt j)
    (fun j => by
      rw [sh2 _ (hB.tne j).2.2.1, (hF.stO _ (hB.tne j).2.2.1 (hB.tne j).1 (hB.tne j).2.1).2]; exact hB.ht j)
    (by rw [st2, (hF.stO _ (Ne.symm h1T) (Ne.symm cT) (Ne.symm sT)).1]; exact hB.bTL)
    (by rw [sh2 _ (Ne.symm h1T), (hF.stO _ (Ne.symm h1T) (Ne.symm cT) (Ne.symm sT)).2]; exact hB.hTL)
    (by rw [st2, (hF.stO _ (Ne.symm h1G) (Ne.symm cG) (Ne.symm sG)).1]; exact hB.bG)
    (by rw [sh2 _ (Ne.symm h1G), (hF.stO _ (Ne.symm h1G) (Ne.symm cG) (Ne.symm sG)).2]; exact hB.hG)
    (by rw [st2, (hF.stO _ (Ne.symm h1L) (Ne.symm cL) (Ne.symm sL)).1]; exact hB.bL)
    (by rw [sh2 _ (Ne.symm h1L), (hF.stO _ (Ne.symm h1L) (Ne.symm cL) (Ne.symm sL)).2]; exact hB.hL)
    (by rw [st2, (hF.stO _ (Ne.symm h1W) (Ne.symm cW) (Ne.symm sW)).1]; exact hB.wt)
    (by rw [sh2 _ (Ne.symm h1W), (hF.stO _ (Ne.symm h1W) (Ne.symm cW) (Ne.symm sW)).2]; exact hB.wth)
    (by rw [st2, sh2 _ (Ne.symm h1V), (hF.stO _ (Ne.symm h1V) (Ne.symm cV) (Ne.symm sV)).1,
          (hF.stO _ (Ne.symm h1V) (Ne.symm cV) (Ne.symm sV)).2]; exact hB.vi)
    (fun i hi => by
      rw [gT_apply]; have h := gIdx_lo i hi
      exact zz _ h.1 (by omega) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)))
    (fun i hi => by
      rw [pT_apply]; have h := pIdx_hi f i hi
      exact zz _ (by omega) h.2 (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)))
    (by rw [gT_seven, v2, hF.vO 9 (by decide) (by decide) (by decide)]; exact hcap)
  have hfl : (ρ.seth E.S1 0).val (pT E.R f hf 0) = σ.val (E.R f) := by
    rw [pT_zero, v2]
    rcases hf with rfl | rfl <;> exact hF.vO _ (by decide) (by decide) (by decide)
  rw [hfl] at s3
  exact ⟨τ3, e3, s3⟩

section Clean
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {w pre rest : List Bool} {σ ρ : WState ns nr} {c : Call} {Z : ℕ}

/-- The state after the call tail. -/
noncomputable abbrev finI3 (ρ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (E : TermEnv ns nr) (hW : ℕ)
    (entry : List Bool) : WState ns nr :=
  tailIdeal (ρ.seth E.S1 0) tmap E.S1 E.S2 E.TL E.G E.VI E.WT (E.R 9) (E.R 17) hW entry

/-- The state after the restore. -/
noncomputable abbrev finI4 (ρ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (E : TermEnv ns nr) (hW : ℕ)
    (entry : List Bool) : WState ns nr :=
  ((((finI3 ρ tmap E hW entry).setv (E.R 23) 0).setv (E.R 24) 0).seth E.CW 0).seth E.SUP 0

theorem finI3_val (hW : ℕ) (entry : List Bool) :
    (finI3 ρ tmap E hW entry).val = Function.update (Function.update ρ.val (E.R 9) (ρ.val (E.R 9) + (marks entry).length))
      (E.R 17) 0 := by
  simp only [finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets]

open Classical in
theorem finI3_sh (hW : ℕ) (entry : List Bool) (x : Fin (ns + 1)) (a : x ≠ E.VI)
    (b : ¬ ((∃ j, tmap j = x) ∨ x = E.TL ∨ x = E.G ∨ x = E.S1 ∨ x = E.S2)) (d : x ≠ E.WT) :
    (finI3 ρ tmap E hW entry).sh x = ρ.sh x := by
  have x1 : x ≠ E.S1 := fun h => b (Or.inr (Or.inr (Or.inr (Or.inl h))))
  simp only [finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne a]
  rw [if_neg b, if_neg d, Function.update_of_ne x1]

theorem callFin_clean (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z)
    (hW : ℕ) (entry : List Bool) (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z) (hZc : Z ≤ cap) :
    WXExec cap (.wm (cleanW E)) (finI3 ρ tmap E hW entry) (finI4 ρ tmap E hW entry) (60 * Z + 30) := by
  obtain ⟨⟨cS, c1, c2, cT, cG, cL, cV, cW⟩, ⟨s1, s2, sT, sG, sL, sV, sW⟩, -, -, -, -, -, -⟩ := hB.dis
  have i3vk : ∀ k : Fin 40, k ≠ 9 → k ≠ 17 → (finI3 ρ tmap E hW entry).val (E.R k) = ρ.val (E.R k) := fun k a b => by
    rw [finI3_val, Function.update_of_ne (R_ne E b), Function.update_of_ne (R_ne E a)]
  have hCWsp : ¬ ((∃ j, tmap j = E.CW) ∨ E.CW = E.TL ∨ E.CW = E.G ∨ E.CW = E.S1 ∨ E.CW = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).1 h
    · exact cT h
    · exact cG h
    · exact c1 h
    · exact c2 h
  have hSUPsp : ¬ ((∃ j, tmap j = E.SUP) ∨ E.SUP = E.TL ∨ E.SUP = E.G ∨ E.SUP = E.S1 ∨ E.SUP = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).2.1 h
    · exact sT h
    · exact sG h
    · exact s1 h
    · exact s2 h
  set ι3 := finI3 ρ tmap E hW entry with hι3
  have c1e := wclear_spec (cap := cap) (E.R 23) (ρ.val (E.R 23)) ι3 (i3vk 23 (by decide) (by decide))
    (by rw [i3vk 23 (by decide) (by decide)]; have := hF.v23; omega)
  have c2e := wclear_spec (cap := cap) (E.R 24) (ρ.val (E.R 24)) (ι3.setv (E.R 23) 0)
    (by rw [WState.setv_val, Function.update_of_ne (R_ne E (by decide)), i3vk 24 (by decide) (by decide)])
    (by rw [WState.setv_val, Function.update_of_ne (R_ne E (by decide)), i3vk 24 (by decide) (by decide)]
        have := hF.v24; omega)
  set ι3b := (ι3.setv (E.R 23) 0).setv (E.R 24) 0 with hι3b
  have i3bv : ∀ k : Fin 40, k ≠ 9 → k ≠ 17 → k ≠ 23 → k ≠ 24 → ι3b.val (E.R k) = σ.val (E.R k) := fun k a b d g => by
    rw [hι3b, WState.setv_val, Function.update_of_ne (R_ne E g), WState.setv_val, Function.update_of_ne (R_ne E d),
      i3vk k a b, hF.vO k b d g]
  have c3e := Codec.rewindCW_spec cap E.CW (E.R 7) (E.R 21) (E.R 20) (R_ne E (by decide)) (R_ne E (by decide))
    (R_ne E (by decide)) ι3b
    (by rw [i3bv 21 (by decide) (by decide) (by decide) (by decide)]; exact hB.z 21 (by decide) (by decide))
    (by rw [i3bv 20 (by decide) (by decide) (by decide) (by decide)]; exact hB.z 20 (by decide) (by decide))
    (by rw [show ι3b.sh E.CW = ι3.sh E.CW from rfl, hι3, finI3_sh hW entry _ cV hCWsp cW,
          i3bv 7 (by decide) (by decide) (by decide) (by decide)]; exact hF.cw)
    (by rw [i3bv 7 (by decide) (by decide) (by decide) (by decide)]; omega)
  have c4e := Codec.rewindCW_spec cap E.SUP (E.R 8) (E.R 21) (E.R 20) (R_ne E (by decide)) (R_ne E (by decide))
    (R_ne E (by decide)) (ι3b.seth E.CW 0)
    (by rw [WState.seth_val, i3bv 21 (by decide) (by decide) (by decide) (by decide)]
        exact hB.z 21 (by decide) (by decide))
    (by rw [WState.seth_val, i3bv 20 (by decide) (by decide) (by decide) (by decide)]
        exact hB.z 20 (by decide) (by decide))
    (by rw [WState.seth_sh, Function.update_of_ne (Ne.symm cS), show ι3b.sh E.SUP = ι3.sh E.SUP from rfl, hι3,
          finI3_sh hW entry _ sV hSUPsp sW, WState.seth_val, i3bv 8 (by decide) (by decide) (by decide) (by decide)]
        exact hF.sup)
    (by rw [WState.seth_val, i3bv 8 (by decide) (by decide) (by decide) (by decide)]; omega)
  rw [i3bv 7 (by decide) (by decide) (by decide) (by decide)] at c3e
  rw [WState.seth_val, i3bv 8 (by decide) (by decide) (by decide) (by decide)] at c4e
  have := hF.v23; have := hF.v24
  exact WXExec.mono (WXExec.wm (WExec.seq c1e (WExec.seq c2e (WExec.seq c3e c4e)))) (by omega)

open Classical in
theorem callFin_final (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z)
    (hW : ℕ) (entry : List Bool) : SimW (termIdeal σ tmap E hW entry) (finI4 ρ tmap E hW entry) := by
  obtain ⟨⟨cS, c1, c2, cT, cG, cL, cV, cW⟩, ⟨s1, s2, sT, sG, sL, sV, sW⟩, ⟨h12, h1T, h1G, h1L, h1V, h1W⟩,
    ⟨h2T, h2G, h2L, h2V, h2W⟩, ⟨hTG, hTL, hTV, hTW⟩, ⟨hGL, hGV, hGW⟩, ⟨hLV, hLW⟩, hVW⟩ := hB.dis
  have hCWsp : ¬ ((∃ j, tmap j = E.CW) ∨ E.CW = E.TL ∨ E.CW = E.G ∨ E.CW = E.S1 ∨ E.CW = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).1 h
    · exact cT h
    · exact cG h
    · exact c1 h
    · exact c2 h
  have hSUPsp : ¬ ((∃ j, tmap j = E.SUP) ∨ E.SUP = E.TL ∨ E.SUP = E.G ∨ E.SUP = E.S1 ∨ E.SUP = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).2.1 h
    · exact sT h
    · exact sG h
    · exact s1 h
    · exact s2 h
  have hVsp : ¬ ((∃ j, tmap j = E.VI) ∨ E.VI = E.TL ∨ E.VI = E.G ∨ E.VI = E.S1 ∨ E.VI = E.S2) := by
    rintro (⟨j, h⟩ | h | h | h | h)
    · exact (hB.tne j).2.2.2.2.2.2.2.1 h
    · exact hTV h.symm
    · exact hGV h.symm
    · exact h1V h.symm
    · exact h2V h.symm
  apply termIdeal_simW σ _ tmap E hW entry hVsp hVW
  · intro i hi
    simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets]
    by_cases iS : i = E.SUP
    · subst iS; rw [Function.update_self, if_neg hSUPsp, if_neg sW, hB.suph]
    rw [Function.update_of_ne iS]
    by_cases iC : i = E.CW
    · subst iC; rw [Function.update_self, if_neg hCWsp, if_neg cW, hB.cwh]
    rw [Function.update_of_ne iC, Function.update_of_ne hi]
    by_cases hsp : (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2
    · rw [if_pos hsp, if_pos hsp]
    rw [if_neg hsp, if_neg hsp]
    by_cases iW : i = E.WT
    · rw [if_pos iW, if_pos iW]
    rw [if_neg iW, if_neg iW]
    have i1 : i ≠ E.S1 := fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inl h))))
    rw [Function.update_of_ne i1, (hF.stO i i1 iC iS).2]
  · simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets]
    rw [Function.update_of_ne (Ne.symm sV), Function.update_of_ne (Ne.symm cV), Function.update_self, if_neg hVsp,
      if_neg hVW, Function.update_of_ne (Ne.symm h1V), (hF.stO _ (Ne.symm h1V) (Ne.symm cV) (Ne.symm sV)).2]
  · intro i hi hsp
    simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne hi,
      if_neg hsp]
    by_cases iC : i = E.CW
    · subst iC; exact hF.cws
    by_cases iS : i = E.SUP
    · subst iS; exact hF.sups
    exact (hF.stO i (fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inl h))))) iC iS).1
  · intro i hsp
    have hiV : i ≠ E.VI := fun h => hVsp (h ▸ hsp)
    simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets, Function.update_of_ne hiV,
      if_pos hsp]
    intro p; rfl
  · simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets, Function.update_self,
      if_neg hVsp]
    rw [(hF.stO _ (Ne.symm h1V) (Ne.symm cV) (Ne.symm sV)).1]
  · funext r
    simp only [finI4, WState.seth_val, WState.setv_val]
    rw [finI3_val]
    by_cases r24 : r = E.R 24
    · subst r24; rw [Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      exact (hB.z 24 (by decide) (by decide)).symm
    rw [Function.update_of_ne r24]
    by_cases r23 : r = E.R 23
    · subst r23; rw [Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      exact (hB.z 23 (by decide) (by decide)).symm
    rw [Function.update_of_ne r23]
    by_cases r17 : r = E.R 17
    · subst r17; rw [Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      exact (hB.z 17 (by decide) (by decide)).symm
    rw [Function.update_of_ne r17]
    by_cases r9 : r = E.R 9
    · subst r9; rw [Function.update_self, Function.update_self, hF.vO 9 (by decide) (by decide) (by decide)]
    rw [Function.update_of_ne r9, Function.update_of_ne r9]
    exact hF.fr.2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨r17, r23, r24⟩)
  · simp only [finI4, finI3, tailIdeal, appendO, WState.setv, WState.seth, WState.sets]
    exact hF.fr.2.2

end Clean

/-- **The end of a call term in ideal form.** -/
theorem callFin_ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) (f : Fin 40) (hf : f = 0 ∨ f = 39)
    {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {c : Call} {w pre rest : List Bool}
    (cap Z : ℕ) {σ ρ : WState ns nr} (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hF : FinPre E σ ρ c Z)
    (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z) (hZc : Z + (frame (callWord c)).length ≤ cap)
    (hcap : σ.val (E.R 9) + 8 * ((callWord c).length + w.length + ctr.budget c w) + 60 ≤ cap) :
    ∃ τ, WXExec cap (callFinW E ctr tmap f hf) ρ τ
        (finCost ctr.program.program.tapeCount (callWord c).length w.length (ctr.budget c w)
          (frame (callWord c)).length Z) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R f) ≠ 0)) ++ outputWord (ctr.value c w))) τ := by
  have e1 := callFin_front cap hB hF (by omega)
  obtain ⟨τ3, e3, s3⟩ := callFin_tail ctr E tmap f hf cap Z hB hF hcap
  have e4 := callFin_clean cap hB hF (pre.length + w.length + 1 + w.length)
    (bitWord (decide (σ.val (E.R f) ≠ 0)) ++ outputWord (ctr.value c w)) h7 h8 (by omega)
  obtain ⟨τ, e, s⟩ := Worker.seq_sim (WXExec.wm e1) (SimW.refl _) (Worker.seq_sim e3 s3 ⟨_, e4, SimW.refl _⟩)
  refine ⟨τ, WXExec.mono e ?_, CheckedPCPP.SimW.trans (callFin_final hB hF _ _) s⟩
  unfold finCost; omega

end NearCubicGates.Close.WorkerArith
