import Proof.Gates.WorkerArith.CallTailDefs
import Proof.Gates.WorkerArith.Entries

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
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord)

variable {ns nr : ℕ}

theorem frame_len' (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]; ring

/-- `clearFrameP` on an exact state (the guard empty). -/
theorem clearFrameM (cap : ℕ) (X G : Fin (ns + 1)) (K T RG R : Fin nr) (u : List Bool) (σ : WState ns nr)
    (hXG : X ≠ G) (hr : [K, T, RG, R].Nodup) (hX : σ.st X = frame u) (hXh : σ.sh X = 0) (hG : σ.st G = [])
    (hGh : σ.sh G = 0) (hK : σ.val K = 0) (hT : σ.val T = 0) (hRG : σ.val RG = 0) (hR : σ.val R = 0)
    (hc : 2 * u.length + 2 ≤ cap) :
    WXExec cap (clearFrameP X G K T RG R) σ ((σ.sets X (clearPrefix (2 * u.length + 2) (frame u))).sets G
      (List.replicate (2 * u.length + 2) false)) (150 * (u.length + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hr
  obtain ⟨⟨hKT, hKG, hKR⟩, ⟨hTG, hTR⟩, hGR, -⟩ := hr
  set m := 2 * u.length + 2 with hm
  have e1 := guardM cap X G K T RG hKT hKG hTG σ u hX hXh hXG hG hGh hK hT hRG hc
  set σ1 := ((σ.sets G (List.replicate m true)).seth G m).setv RG m with hσ1
  have e2 := wrewind_spec (cap := cap) G RG m σ1 (by simp [hσ1]) (by simp [hσ1]; omega)
  set σ2 := (σ1.setv RG 0).seth G (σ1.sh G - m) with hσ2
  have e3 := clearOne_exec X G R hXG m (by omega) σ2 (by simp [hσ2, hσ1]) (by simp [hσ2, hσ1])
    (by simp [hσ2, hσ1, Function.update_of_ne hXG, hXh]) (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hGR), hR])
  set σ3 := σ2.sets X (clearPrefix m (σ2.st X)) with hσ3
  have e4 := clearSelfM cap G R σ3 m (by simp [hσ3, Function.update_of_ne hXG.symm, hσ2, hσ1])
    (by simp [hσ3, hσ2, hσ1]) (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hGR), hR]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 e4))).cast cap ?_ (by nlinarith)
  apply WState.eq
  · funext i; by_cases hi : i = G
    · subst hi; simp [hσ3, hσ2, hσ1, hGh]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hi]
  · funext i; by_cases hi : i = G
    · subst hi; simp [hσ3]
    · by_cases hiX : i = X
      · subst hiX; simp [hσ3, Function.update_of_ne hi, hσ2, hσ1, hX]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hi, Function.update_of_ne hiX]
  · funext r; by_cases hr : r = RG
    · subst hr; simp [hσ3, hσ2, hσ1, hRG]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hr]
  · rfl

theorem clearFrame_ideal (cap : ℕ) (X G : Fin (ns + 1)) (K T RG R : Fin nr) (u : List Bool) (σ : WState ns nr) :
    ClearFrameIdeal cap X G K T RG R u σ := by
  intro hXG hr hX hXh hGb hGh hK hT hRG hR hc
  set σ' := σ.sets G [] with hσ'
  have hs : SimW σ' σ := CheckedPCPP.SimW.symm (Worker.simW_sets σ G [] (blank_nil hGb))
  have e := clearFrameM cap X G K T RG R u σ' hXG hr (by simp [hσ', Function.update_of_ne hXG, hX]) hXh (by simp [hσ'])
    hGh hK hT hRG hR hc
  obtain ⟨τ, e', hs'⟩ := wxexec_sim e σ hs
  refine ⟨τ, e', CheckedPCPP.SimW.trans ?_ hs'⟩
  refine ⟨rfl, rfl, rfl, fun i => ?_⟩
  by_cases hi : i = G
  · subst hi; simp; exact (blank_nil (replicate_false_blank _)).symm
  · by_cases hiX : i = X
    · subst hiX; simp [Function.update_of_ne hi]
      have hb : Worker.Blank (clearPrefix (2 * u.length + 2) (frame u)) := by
        intro q; have := clearPrefix_blank (2 * u.length + 2) (frame u)
          (fun q hq => readTapeBit_beyond _ _ (by rw [frame_len']; omega)) q
        rw [this]; rfl
      exact (blank_nil hb).symm
    · simp [hσ', Function.update_of_ne hi, Function.update_of_ne hiX]; exact RdEq.refl _

/-! ## The front of the call tail (exact states) -/

theorem tailFrontM (cap : ℕ) (S1 S2 S3 WT : Fin (ns + 1)) (hd : [S1, S2, S3, WT].Nodup) (P : Fin 8 ↪ Fin nr)
    (cw w pre rest : List Bool) (σ : WState ns nr) (h1 : σ.st S1 = cw) (h1h : σ.sh S1 = 0)
    (hP1 : σ.val (P 1) = cw.length) (h2 : σ.st S2 = []) (h2h : σ.sh S2 = 0) (h3 : σ.st S3 = []) (h3h : σ.sh S3 = 0)
    (hW : σ.st WT = pre ++ (Worker.Format.countWord w.length ++ w) ++ rest) (hWh : σ.sh WT = pre.length)
    (hz : ∀ i : Fin 8, 2 ≤ i.val → σ.val (P i) = 0) (hc : 4 * (cw.length + w.length) + 10 ≤ cap) :
    ∃ τ, WExec cap (tailFrontW S1 S2 S3 WT P) σ τ (200 * (cw.length + w.length + 1)) ∧
      τ.st S3 = frame (cw ++ frame w) ∧ τ.sh S3 = 0 ∧ τ.st S1 = cw ∧ τ.sh S1 = 0 ∧ τ.st S2 = frame w ∧
      τ.sh S2 = 0 ∧ τ.sh WT = pre.length + w.length + 1 + w.length ∧ τ.st WT = σ.st WT ∧ (∀ i : Fin 8, 1 ≤ i.val → τ.val (P i) = 0) ∧
      SameExcept σ τ [S1, S2, S3, WT] [P 1] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨h12, h13, h1W⟩, ⟨h23, h2W⟩, h3W, -⟩ := hd
  have hPne : ∀ {i j : Fin 8}, i ≠ j → P i ≠ P j := fun h => P.injective.ne h
  have hfw := frame_len' w

  have f1 := Codec.fieldFrameW_spec cap WT S2 (Ne.symm h2W) (P 2) (P 7) (hPne (by decide)) pre w rest σ hW hWh
    (by rw [h2, h2h]; rfl) (hz 7 (by decide)) (by rw [hz 2 (by decide)]; omega) (by omega)
  set σ1 := appendO (σ.seth WT (pre.length + w.length + 1 + w.length)) S2 (P 2) (frame w) with hσ1
  have v1 : σ1.val (P 2) = (frame w).length := by simp [hσ1, appendO, hz 2 (by decide)]
  have f2 := Codec.dupR_spec cap (P 2) (P 4) (P 6) (hPne (by decide)) (hPne (by decide)) (hPne (by decide)) σ1
    (by simp [hσ1, appendO, Function.update_of_ne (hPne (show (6 : Fin 8) ≠ 2 by decide)), hz 6 (by decide)])
    (by rw [v1]; simp [hσ1, appendO, Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 2 by decide)), hz 4 (by decide)]
        omega)
  rw [v1, show σ1.val (P 4) = 0 by simp [hσ1, appendO, Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 2 by decide)),
    hz 4 (by decide)], Nat.zero_add] at f2
  set σ2 := σ1.setv (P 4) (frame w).length with hσ2
  have f3 := wrewind_spec (cap := cap) S2 (P 4) (frame w).length σ2 (by simp [hσ2]) (by simp [hσ2]; omega)
  set σ3 := (σ2.setv (P 4) 0).seth S2 (σ2.sh S2 - (frame w).length) with hσ3
  have f4 := Codec.dupR_spec cap (P 2) (P 4) (P 6) (hPne (by decide)) (hPne (by decide)) (hPne (by decide)) σ3
    (by simp [hσ3, hσ2, Function.update_of_ne (hPne (show (6 : Fin 8) ≠ 4 by decide)), hσ1, appendO,
      Function.update_of_ne (hPne (show (6 : Fin 8) ≠ 2 by decide)), hz 6 (by decide)])
    (by simp [hσ3, hσ2, Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 4 by decide)), v1]; omega)
  have v3 : σ3.val (P 2) = (frame w).length := by
    simp [hσ3, hσ2, Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 4 by decide)), v1]
  rw [v3, show σ3.val (P 4) = 0 by simp [hσ3], Nat.zero_add] at f4
  set σ4 := σ3.setv (P 4) (frame w).length with hσ4
  have v4_1 : σ4.val (P 1) = cw.length := by
    simp [hσ4, hσ3, hσ2, Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 4 by decide)), hσ1, appendO,
      Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 2 by decide)), hP1]
  have v4_3 : σ4.val (P 3) = 0 := by
    simp [hσ4, hσ3, hσ2, Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 4 by decide)), hσ1, appendO,
      Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 2 by decide)), hz 3 (by decide)]
  have f5 := Codec.dupR_spec cap (P 1) (P 3) (P 6) (hPne (by decide)) (hPne (by decide)) (hPne (by decide)) σ4
    (by simp [hσ4, hσ3, hσ2, Function.update_of_ne (hPne (show (6 : Fin 8) ≠ 4 by decide)), hσ1, appendO,
      Function.update_of_ne (hPne (show (6 : Fin 8) ≠ 2 by decide)), hz 6 (by decide)])
    (by rw [v4_1, v4_3]; omega)
  rw [v4_1, v4_3, Nat.zero_add] at f5
  set σ5 := σ4.setv (P 3) cw.length with hσ5

  have s5_1 : σ5.st S1 = cw ++ [] := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne h12, h1]
  have s5_2 : σ5.st S2 = frame w ++ [] := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO, h2]
  have s5_2h : σ5.sh S2 = 0 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne h2W, h2h]
  have s5_1h : σ5.sh S1 = 0 := by
    simp [hσ5, hσ4, hσ3, Function.update_of_ne h12, hσ2, hσ1, appendO, Function.update_of_ne h1W, h1h]
  have s5_3 : σ5.sh S3 = (σ5.st S3).length := by
    simp [hσ5, hσ4, hσ3, Function.update_of_ne (Ne.symm h23), hσ2, hσ1, appendO, Function.update_of_ne h3W, h3, h3h]
  have v5_1 : σ5.val (P 1) = cw.length := by
    simp [hσ5, Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 3 by decide)), v4_1]
  have v5_2 : σ5.val (P 2) = (frame w).length := by
    simp [hσ5, Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 3 by decide)), hσ4,
      Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 4 by decide)), v3]
  have v5_5 : σ5.val (P 5) = 0 := by
    simp [hσ5, Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 3 by decide)), hσ4,
      Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 4 by decide)), hσ3, hσ2, hσ1, appendO,
      Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 2 by decide)), hz 5 (by decide)]
  have st3 : σ5.st S3 = [] := by
    simp [hσ5, hσ4, hσ3, Function.update_of_ne (Ne.symm h23), hσ2, hσ1, appendO, Function.update_of_ne h3W, h3]
  have g1 := Codec.frameStream_spec cap S1 S3 h13 (P 5) (P 1) (hPne (by decide)) cw [] [] σ5 (by simpa using s5_1)
    (by simpa using s5_1h) s5_3 v5_1 (by omega) (by rw [v5_5]; omega)
  set ρ1 := ((appendO σ5 S3 (P 5) (marks cw)).setv (P 1) 0).seth S1 (([] : List Bool).length + cw.length) with hρ1
  have g2 := Codec.frameStream_spec cap S2 S3 h23 (P 5) (P 2) (hPne (by decide)) (frame w) [] [] ρ1
    (by simp [hρ1, appendO, Function.update_of_ne h23]; simpa using s5_2)
    (by simp [hρ1, Function.update_of_ne (Ne.symm h12), appendO, Function.update_of_ne h23, s5_2h])
    (by simp [hρ1, Function.update_of_ne (Ne.symm h13), appendO, s5_3])
    (by simp [hρ1, Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 1 by decide)), appendO,
      Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 5 by decide)), v5_2]) (by omega)
    (by simp [hρ1, Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 1 by decide)), appendO, v5_5,
      Codec.marks_length]; omega)
  set ρ2 := ((appendO ρ1 S3 (P 5) (marks (frame w))).setv (P 2) 0).seth S2 (([] : List Bool).length +
    (frame w).length) with hρ2
  have g3 := emitC_spec (cap := cap) S3 (P 5) false ρ2
    (by simp [hρ2, Function.update_of_ne (Ne.symm h23), appendO, hρ1, Function.update_of_ne (Ne.symm h13), s5_3]; omega)
    (by simp [hρ2, Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 2 by decide)), appendO, hρ1,
      Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 1 by decide)), v5_5, Codec.marks_length]; omega)
  set τ6 := ((ρ2.sets S3 (ρ2.st S3 ++ [false])).seth S3 (ρ2.sh S3 + 1)).setv (P 5) (ρ2.val (P 5) + 1) with hτ6
  have f6 : WExec cap (Codec.pairFrame S1 S2 S3 (P 5) (P 1) (P 2)) σ5 τ6 (22 * cw.length + 22 * (frame w).length + 11) :=
    (WExec.seq g1 (WExec.seq g2 g3)).mono (by omega)
  have t6_3 : τ6.st S3 = frame (cw ++ frame w) := by
    simp [hτ6, hρ2, appendO, hρ1, st3, Codec.frame_eq_marks, Codec.marksApp]
  have hlen3 : (frame (cw ++ frame w)).length = 2 * cw.length + 2 * (frame w).length + 1 := by
    rw [frame_len', List.length_append]; ring
  have t6_5 : τ6.val (P 5) = (frame (cw ++ frame w)).length := by
    simp [hτ6, hρ2, Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 2 by decide)), appendO, hρ1,
      Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 1 by decide)), v5_5, Codec.marks_length]
    omega
  have f7 := wrewind_spec (cap := cap) S3 (P 5) (frame (cw ++ frame w)).length τ6 t6_5 (by
    rw [t6_5, hlen3, hfw]; omega)
  set τ7 := (τ6.setv (P 5) 0).seth S3 (τ6.sh S3 - (frame (cw ++ frame w)).length) with hτ7
  have v6_3 : τ6.val (P 3) = cw.length := by
    simp [hτ6, Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 5 by decide)), hρ2, appendO,
      Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 2 by decide)), hρ1,
      Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 1 by decide)), hσ5]
  have f8 := wrewind_spec (cap := cap) S1 (P 3) cw.length τ7
    (by simp [hτ7, Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 5 by decide)), v6_3]) (by
      simp [hτ7, Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 5 by decide)), v6_3]; omega)
  set τ8 := (τ7.setv (P 3) 0).seth S1 (τ7.sh S1 - cw.length) with hτ8
  have v6_4 : τ6.val (P 4) = (frame w).length := by
    simp [hτ6, Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 5 by decide)), hρ2, appendO,
      Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 2 by decide)), hρ1,
      Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 1 by decide)), hσ5,
      Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 3 by decide)), hσ4]
  have f9 := wrewind_spec (cap := cap) S2 (P 4) (frame w).length τ8
    (by simp [hτ8, Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 3 by decide)), hτ7,
      Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 5 by decide)), v6_4])
    (by simp [hτ8, Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 3 by decide)), hτ7,
      Function.update_of_ne (hPne (show (4 : Fin 8) ≠ 5 by decide)), v6_4]; omega)
  set τ9 := (τ8.setv (P 4) 0).seth S2 (τ8.sh S2 - (frame w).length) with hτ9
  refine ⟨τ9, (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 (WExec.seq f4 (WExec.seq f5 (WExec.seq f6
    (WExec.seq f7 (WExec.seq f8 f9)))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfw]; nlinarith
  · simp [hτ9, hτ8, hτ7, t6_3]
  · simp [hτ9, Function.update_of_ne (Ne.symm h23), hτ8, Function.update_of_ne (Ne.symm h13), hτ7, hτ6, hρ2, hρ1, appendO,
      Function.update_of_ne (Ne.symm h23), Function.update_of_ne (Ne.symm h13), s5_3, st3, Codec.marks_length, hlen3]
    try omega
  · simp [hτ9, hτ8, hτ7, hτ6, Function.update_of_ne h13, hρ2, appendO, hρ1, s5_1]
  · simp [hτ9, Function.update_of_ne h12, hτ8, hτ7, Function.update_of_ne h13, hτ6, hρ2, appendO, hρ1]
  · simp [hτ9, hτ8, hτ7, hτ6, Function.update_of_ne h23, hρ2, appendO, hρ1, Function.update_of_ne (Ne.symm h12), s5_2]
  · simp [hτ9, hτ8, hτ7, hτ6, Function.update_of_ne h23, hρ2, appendO, hρ1, Function.update_of_ne h12,
      Function.update_of_ne (Ne.symm h12), s5_2h]
  · simp [hτ9, Function.update_of_ne (Ne.symm h2W), hτ8, Function.update_of_ne (Ne.symm h1W), hτ7, Function.update_of_ne (Ne.symm h3W),
      hτ6, hρ2, appendO, hρ1, hσ5, hσ4, hσ3, hσ2, hσ1]
  · simp [hτ9, hτ8, hτ7, hτ6, Function.update_of_ne (Ne.symm h3W), hρ2, appendO, hρ1, hσ5, hσ4, hσ3, hσ2, hσ1,
      Function.update_of_ne (Ne.symm h2W)]
  · intro i hi
    by_cases h4 : i = 4
    · subst h4; simp [hτ9]
    by_cases h3' : i = 3
    · subst h3'; simp [hτ9, Function.update_of_ne (hPne (show (3 : Fin 8) ≠ 4 by decide)), hτ8]
    by_cases h5 : i = 5
    · subst h5; simp [hτ9, Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 4 by decide)), hτ8,
        Function.update_of_ne (hPne (show (5 : Fin 8) ≠ 3 by decide)), hτ7]
    by_cases h2' : i = 2
    · subst h2'; simp [hτ9, Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 4 by decide)), hτ8,
        Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 3 by decide)), hτ7,
        Function.update_of_ne (hPne (show (2 : Fin 8) ≠ 5 by decide)), hτ6, hρ2]
    by_cases h1' : i = 1
    · subst h1'; simp [hτ9, Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 4 by decide)), hτ8,
        Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 3 by decide)), hτ7,
        Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 5 by decide)), hτ6, hρ2,
        Function.update_of_ne (hPne (show (1 : Fin 8) ≠ 2 by decide)), appendO, hρ1]
    simp [hτ9, Function.update_of_ne (hPne h4), hτ8, Function.update_of_ne (hPne h3'), hτ7, Function.update_of_ne (hPne h5),
      hτ6, hρ2, Function.update_of_ne (hPne h2'), appendO, hρ1, Function.update_of_ne (hPne h1'), hσ5, hσ4, hσ3, hσ2, hσ1]
    exact hz i (by have := i.isLt; omega)
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨x1, x2, x3, x4⟩ := hx
      simp [hτ9, Function.update_of_ne x2, hτ8, Function.update_of_ne x1, hτ7, Function.update_of_ne x3, hτ6, hρ2,
        appendO, hρ1, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne x4]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases r4 : r = P 4
      · subst r4; simp [hτ9, hz 4 (by decide)]
      by_cases r3 : r = P 3
      · subst r3; simp [hτ9, Function.update_of_ne r4, hτ8, hz 3 (by decide)]
      by_cases r5 : r = P 5
      · subst r5; simp [hτ9, Function.update_of_ne r4, hτ8, Function.update_of_ne r3, hτ7, hz 5 (by decide)]
      by_cases r2 : r = P 2
      · subst r2; simp [hτ9, Function.update_of_ne r4, hτ8, Function.update_of_ne r3, hτ7, Function.update_of_ne r5,
          hτ6, hρ2, hz 2 (by decide)]
      simp [hτ9, Function.update_of_ne r4, hτ8, Function.update_of_ne r3, hτ7, Function.update_of_ne r5, hτ6, hρ2,
        Function.update_of_ne r2, appendO, hρ1, Function.update_of_ne hr, hσ5, hσ4, hσ3, hσ2, hσ1]
    · simp [hτ9, hτ8, hτ7, hτ6, hρ2, hρ1, appendO, hσ5, hσ4, hσ3, hσ2, hσ1]

/-! ## The output of a word function is no longer than its budget plus one -/

theorem wf_output_len {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) : (output req).length ≤ budget req + 1 := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  have h := runFrom_len f.program.machine f.program.outputTape (budget req) _ 0 receipt hrun
    (by simp [initialConfiguration])
    (by simp [initialConfiguration, Program.inputTapes, f.program.outputFresh])
  have hs := runFrom_steps_le _ _ _ receipt hrun
  rw [hout] at h; omega

/-! ## The flip bit -/

theorem flipM (cap : ℕ) (o : Fin (ns + 1)) (OP F : Fin nr) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 6 ≤ cap) :
    WXExec cap (flipW o OP F) σ (appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0))))) 49 := by
  unfold flipW
  by_cases hF : σ.val F = 0
  · have e := Codec.emitMarks_spec cap o OP (bitWord false) σ ho (by rw [bitWord_len]; omega)
    rw [bitWord_len] at e
    simpa [hF] using (WXExec.ifrF hF (WXExec.wm e)).mono (by omega)
  · have e := Codec.emitMarks_spec cap o OP (bitWord true) σ ho (by rw [bitWord_len]; omega)
    rw [bitWord_len] at e
    simpa [hF] using (WXExec.ifrT hF (WXExec.wm e)).mono (by omega)

end NearCubicGates.Close.WorkerArith
