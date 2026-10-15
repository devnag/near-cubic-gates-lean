import Proof.Gates.WorkerArith.CallTail

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
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord)

variable {ns nr : ℕ}

theorem outputWord_outN (v : ℚ × ℚ) : outputWord v = (outN v).flatMap natWord := by
  simp [outputWord, outN, ratWord_eq, List.flatMap_append]

theorem tailCost_le (t cw w b o : ℕ) (ho : o ≤ b + 1) :
    200 * ((2 * cw + 1) + w + 1) + 1 + (49 + 1 + (ctrCost t ((2 * cw + 1) + (2 * w + 1)) b o + 1 +
      (150 * (cw + 1) + 1 + 150 * (w + 1)))) ≤ tailCost t cw w b := by
  unfold ctrCost tailCost
  have ht : t * o ≤ t * (b + 1) := Nat.mul_le_mul_left _ ho
  nlinarith [ht]

open Classical in
theorem callTail_ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (c : Call) (w : List Bool) (cap : ℕ)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) (S1 S2 TL G L VI WT : Fin (ns + 1))
    (Rg P : Fin 8 ↪ Fin nr) (pre rest : List Bool) (σ : WState ns nr) :
    CallTailIdeal ctr c w cap tmap S1 S2 TL G L VI WT Rg P pre rest σ := by
  intro hinj hS1 hS2 hTL hG hL hVI hWT hd hPR hst1 hsh1 hP1 hb2 hsh2 hbt hsht hbTL hshTL hbG hshG hbL hshL hWst hWsh
    hVIe hRg hPz hcap
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨h12, h1T, h1G, h1L, h1V, h1W⟩, ⟨h2T, h2G, h2L, h2V, h2W⟩, ⟨hTG, hTL', hTV, hTW⟩, ⟨hGL, hGV, hGW⟩,
    ⟨hLV, hLW⟩, hVW, -⟩ := hd
  set iT := inTape ctr.program.program with hiT
  set S3 := tmap iT with hS3
  -- the exact start
  let σ0 : WState ns nr := ⟨σ.sh, fun i => if (∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S2 then [] else σ.st i,
    σ.val, σ.cell⟩
  have s0 : ∀ i, ¬ ((∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S2) → σ0.st i = σ.st i := fun i h => by
    simp only [σ0]; rw [if_neg h]
  have s0e : ∀ i, ((∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S2) → σ0.st i = [] := fun i h => by
    simp only [σ0]; rw [if_pos h]
  have hsim0 : SimW σ0 σ := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases h : (∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S2
    · rw [s0e i h]
      rcases h with ⟨j, rfl⟩ | rfl | rfl | rfl
      · exact (blank_nil (hbt j)).symm
      · exact (blank_nil hbTL).symm
      · exact (blank_nil hbG).symm
      · exact (blank_nil hb2).symm
    · rw [s0 i h]; exact RdEq.refl _
  have nS1 : ¬ ((∃ j, tmap j = S1) ∨ S1 = TL ∨ S1 = G ∨ S1 = S2) := by
    rintro (⟨j, h⟩ | h | h | h)
    · exact hS1 j h
    · exact h1T h
    · exact h1G h
    · exact h12 h
  have nWT : ¬ ((∃ j, tmap j = WT) ∨ WT = TL ∨ WT = G ∨ WT = S2) := by
    rintro (⟨j, h⟩ | h | h | h)
    · exact hWT j h
    · exact hTW h.symm
    · exact hGW h.symm
    · exact h2W h.symm
  have nVI : ¬ ((∃ j, tmap j = VI) ∨ VI = TL ∨ VI = G ∨ VI = S2) := by
    rintro (⟨j, h⟩ | h | h | h)
    · exact hVI j h
    · exact hTV h.symm
    · exact hGV h.symm
    · exact h2V h.symm
  -- the front
  have hdF : [S1, S2, S3, WT].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨h12, fun h => hS1 iT h.symm, h1W⟩, ⟨fun h => hS2 iT h.symm, h2W⟩, hWT iT, fun h => h⟩
  obtain ⟨τA, eA, tA3, tA3h, tA1, tA1h, tA2, tA2h, tAW, tAWs, tAP, tAfr⟩ := tailFrontM cap S1 S2 S3 WT hdF P
    (frame (callWord c)) w pre rest σ0 (by rw [s0 S1 nS1]; exact hst1) hsh1 hP1 (s0e S2 (Or.inr (Or.inr (Or.inr rfl))))
    hsh2 (s0e S3 (Or.inl ⟨iT, rfl⟩)) (hsht iT) (by rw [s0 WT nWT]; exact hWst) hWsh hPz
    (by rw [frame_len']; omega)
  -- the flip bit
  have hfrVI : VI ∉ [S1, S2, S3, WT] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h1V, Ne.symm h2V, (hVI iT).symm, hVW⟩
  have tAVI : τA.st VI = σ.st VI := by rw [tAfr.st hfrVI, s0 VI nVI]
  have tAVIh : τA.sh VI = σ.sh VI := by rw [tAfr.sh hfrVI]
  have tAval : ∀ r, r ≠ P 1 → τA.val r = σ.val r := fun r hr => tAfr.val (by simp [hr])
  have hF : τA.val (P 0) = σ.val (P 0) := tAval _ (P.injective.ne (by decide))
  have h7 : τA.val (Rg 7) = σ.val (Rg 7) := tAval _ (hPR 1 7).symm
  have eB := flipM cap VI (Rg 7) (P 0) τA (by rw [tAVIh, tAVI]; exact hVIe) (by rw [h7]; omega)
  rw [hF] at eB
  set f := decide (σ.val (P 0) ≠ 0) with hf
  set τB := appendO τA VI (Rg 7) (marks (bitWord f)) with hτB
  -- the counter call
  have hrq : ctr.program.program = ctr.program.program := rfl
  obtain ⟨τ3, e3, s3⟩ := ctrCall_ideal ctr.program (c, w) (outN (ctr.value c w)) cap tmap TL G L VI Rg τB
    (outputWord_outN _) hinj hTL hG hL hVI (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      exact ⟨⟨hTG, hTL', hTV⟩, ⟨hGL, hGV⟩, hLV, fun h => h⟩)
    (by simp [hτB, appendO, Function.update_apply, hVI]; exact tA3)
    (fun j hj => by
      have hj' : tmap j ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hS1 j, hS2 j, fun h => hj (hinj h), hWT j⟩
      simp [hτB, appendO, Function.update_of_ne (hVI j)]
      rw [tAfr.st hj', s0e _ (Or.inl ⟨j, rfl⟩)]
      intro p; rfl)
    (fun j => by
      by_cases hj : j = iT
      · subst hj; simp [hτB, appendO, Function.update_apply, hVI]; exact tA3h
      · have hj' : tmap j ∉ [S1, S2, S3, WT] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hS1 j, hS2 j, fun h => hj (hinj h), hWT j⟩
        simp [hτB, appendO, Function.update_of_ne (hVI j)]; rw [tAfr.sh hj']; exact hsht j)
    (by
      have hTLn : TL ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1T, Ne.symm h2T, (hTL iT).symm, hTW⟩
      simp [hτB, appendO, Function.update_of_ne hTV]; rw [tAfr.st hTLn, s0e _ (Or.inr (Or.inl rfl))]
      intro p; rfl)
    (by
      have hTLn : TL ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1T, Ne.symm h2T, (hTL iT).symm, hTW⟩
      simp [hτB, appendO, Function.update_of_ne hTV]; rw [tAfr.sh hTLn]; exact hshTL)
    (by
      have hGn : G ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1G, Ne.symm h2G, (hG iT).symm, hGW⟩
      simp [hτB, appendO, Function.update_of_ne hGV]; rw [tAfr.st hGn, s0e _ (Or.inr (Or.inr (Or.inl rfl)))]
      intro p; rfl)
    (by
      have hGn : G ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1G, Ne.symm h2G, (hG iT).symm, hGW⟩
      simp [hτB, appendO, Function.update_of_ne hGV]; rw [tAfr.sh hGn]; exact hshG)
    (by
      have hLn : L ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1L, Ne.symm h2L, (hL iT).symm, hLW⟩
      have nL : ¬ ((∃ j, tmap j = L) ∨ L = TL ∨ L = G ∨ L = S2) := by
        rintro (⟨j, h⟩ | h | h | h)
        · exact hL j h
        · exact hTL' h.symm
        · exact hGL h.symm
        · exact h2L h.symm
      simp [hτB, appendO, Function.update_of_ne hLV]; rw [tAfr.st hLn, s0 L nL]; exact hbL)
    (by
      have hLn : L ∉ [S1, S2, S3, WT] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h1L, Ne.symm h2L, (hL iT).symm, hLW⟩
      simp [hτB, appendO, Function.update_of_ne hLV]; rw [tAfr.sh hLn]; exact hshL)
    (by simp [hτB, appendO]; rw [tAVIh, tAVI]; exact hVIe)
    (fun i hi => by
      simp [hτB, appendO, Function.update_of_ne (Rg.injective.ne hi)]
      rw [tAval _ (hPR 1 i).symm]; exact hRg i hi)
    (by
      have hw := wf_output_len ctr.program (c, w)
      simp only at hw
      simp [hτB, appendO, h7, Codec.marks_length, bitWord_len, frame_len']
      omega)
  have hl6 : (outN (ctr.value c w)).length = 6 := by simp [outN, ratN]
  rw [hl6] at e3
  set out := outputWord (ctr.value c w) with hout
  set ι3 := ctrIdeal τB tmap TL G VI (Rg 7) out with hι3
  have s3' : SimW ι3 τ3 := s3
  -- facts on `ι3`
  have nsp : ∀ x, x ∈ [S1, S2, WT] → ¬ ((∃ j, tmap j = x) ∨ x = TL ∨ x = G) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rintro (⟨j, h⟩ | h | h)
      · exact hS1 j h
      · exact h1T h
      · exact h1G h
    · rintro (⟨j, h⟩ | h | h)
      · exact hS2 j h
      · exact h2T h
      · exact h2G h
    · rintro (⟨j, h⟩ | h | h)
      · exact hWT j h
      · exact hTW h.symm
      · exact hGW h.symm
  have i3st : ∀ x, x ∈ [S1, S2, WT] → ι3.st x = τA.st x ∧ ι3.sh x = τA.sh x := by
    intro x hx
    have hxV : x ≠ VI := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact h1V
      · exact h2V
      · exact Ne.symm hVW
    simp only [hι3, ctrIdeal, appendO, WState.setv, WState.seth, WState.sets, hτB]
    simp only [Function.update_of_ne hxV, if_neg (nsp x hx), and_self]
  have i3v : ι3.val = Function.update (Function.update τA.val (Rg 7) (τA.val (Rg 7) + (marks (bitWord f)).length))
      (Rg 7) (τA.val (Rg 7) + (marks (bitWord f)).length + (marks out).length) := by
    simp only [hι3, ctrIdeal, appendO, WState.setv, WState.seth, WState.sets, hτB, Function.update_self]
  have hRi : ∀ {a b : Fin 8}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  have i3r : ∀ k : Fin 8, k ≠ 7 → ι3.val (Rg k) = 0 := fun k hk => by
    rw [i3v, Function.update_of_ne (hRi hk), Function.update_of_ne (hRi hk), tAval _ (hPR 1 k).symm, hRg k hk]
  -- the two clears
  have hcw : 2 * (callWord c).length + 2 ≤ cap := by omega
  obtain ⟨τ4, e4, s4⟩ := clearFrame_ideal cap S1 G (Rg 3) (Rg 4) (Rg 5) (Rg 0) (callWord c) ι3 h1G
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨hRi (by decide), hRi (by decide), hRi (by decide)⟩, ⟨hRi (by decide), hRi (by decide)⟩, hRi (by decide),
          fun h => h⟩)
    (by rw [(i3st S1 (by simp)).1, tA1]) (by rw [(i3st S1 (by simp)).2, tA1h])
    (by simp [hι3, ctrIdeal, appendO, Function.update_of_ne hGV]; intro p; rfl)
    (by simp [hι3, ctrIdeal, appendO, Function.update_of_ne hGV])
    (i3r 3 (by decide)) (i3r 4 (by decide)) (i3r 5 (by decide)) (i3r 0 (by decide)) hcw
  set ι4 := (ι3.sets S1 []).sets G [] with hι4
  obtain ⟨τ5, e5, s5⟩ := clearFrame_ideal cap S2 G (Rg 3) (Rg 4) (Rg 5) (Rg 0) w ι4 h2G
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨hRi (by decide), hRi (by decide), hRi (by decide)⟩, ⟨hRi (by decide), hRi (by decide)⟩, hRi (by decide),
          fun h => h⟩)
    (by simp only [hι4, WState.sets, Function.update_of_ne h2G, Function.update_of_ne (Ne.symm h12)]
        rw [(i3st S2 (by simp)).1, tA2])
    (by simp only [hι4, WState.sets]; rw [(i3st S2 (by simp)).2, tA2h])
    (by simp [hι4]; intro p; rfl) (by simp [hι4, hι3, ctrIdeal, appendO, Function.update_of_ne hGV])
    (i3r 3 (by decide)) (i3r 4 (by decide)) (i3r 5 (by decide)) (i3r 0 (by decide)) (by omega)
  set ι5 := (ι4.sets S2 []).sets G [] with hι5
  -- compose
  have hrun := Worker.seq_sim (WXExec.wm eA) (SimW.refl τA) (Worker.seq_sim eB (SimW.refl _)
    (Worker.seq_sim e3 s3' (Worker.seq_sim e4 s4 ⟨τ5, e5, s5⟩)))
  obtain ⟨τ6, e6, s6⟩ := hrun
  obtain ⟨τ, e, s⟩ := wxexec_sim e6 σ hsim0
  refine ⟨τ, WXExec.mono e ?_, SimW.trans ?_ (SimW.trans s6 s)⟩
  · have hw := wf_output_len ctr.program (c, w)
    simp only at hw
    have := tailCost_le ctr.program.program.tapeCount (callWord c).length w.length (ctr.budget c w)
      (outputWord (ctr.value c w)).length hw
    simp only [List.length_append, frame_len'] at this ⊢
    exact this
  · have hVsp : ¬ ((∃ j, tmap j = VI) ∨ VI = TL ∨ VI = G) := by
      rintro (⟨j, h⟩ | h | h)
      · exact hVI j h
      · exact hTV h.symm
      · exact hGV h.symm
    have hVsp' : ¬ ((∃ j, tmap j = VI) ∨ VI = TL ∨ VI = G ∨ VI = S1 ∨ VI = S2) := by
      rintro (⟨j, h⟩ | h | h | h | h)
      · exact hVI j h
      · exact hTV h.symm
      · exact hGV h.symm
      · exact h1V h.symm
      · exact h2V h.symm
    have up : ∀ i, ((∃ j, tmap j = i) ∨ i = TL ∨ i = G) →
        ((∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S1 ∨ i = S2) :=
      fun i h => h.elim Or.inl (fun h => Or.inr (h.elim Or.inl (fun h => Or.inr (Or.inl h))))
    have dn : ∀ i, ¬ ((∃ j, tmap j = i) ∨ i = TL ∨ i = G) → i ≠ S1 → i ≠ S2 →
        ¬ ((∃ j, tmap j = i) ∨ i = TL ∨ i = G ∨ i = S1 ∨ i = S2) := fun i h a b hh => by
      rcases hh with h' | h' | h' | h' | h'
      exacts [h (Or.inl h'), h (Or.inr (Or.inl h')), h (Or.inr (Or.inr h')), a h', b h']
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · funext i
      simp only [hι5, hι4, WState.sets, hι3, ctrIdeal, tailIdeal, appendO, WState.setv, WState.seth, hτB]
      by_cases hiV : i = VI
      · subst hiV
        simp only [Function.update_self, if_neg hVsp, if_neg hVsp', if_neg hVW, tAVIh, Codec.marks_length,
          List.length_append]
        ring
      · simp only [Function.update_of_ne hiV]
        by_cases hsp : (∃ j, tmap j = i) ∨ i = TL ∨ i = G
        · rw [if_pos hsp, if_pos (up i hsp)]
        · rw [if_neg hsp]
          by_cases h1 : i = S1
          · subst h1; rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact tA1h
          by_cases h2 : i = S2
          · subst h2; rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact tA2h
          rw [if_neg (dn i hsp h1 h2)]
          by_cases hW : i = WT
          · subst hW; rw [if_pos rfl]; exact tAW
          rw [if_neg hW]
          apply (tAfr.1 i _).2
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨h1, h2, fun h => hsp (Or.inl ⟨iT, h.symm⟩), hW⟩
    · funext r
      simp only [hι5, hι4, WState.sets]
      rw [i3v]
      simp only [tailIdeal, appendO, WState.setv, WState.seth, WState.sets]
      by_cases r1 : r = P 1
      · subst r1
        rw [Function.update_self, Function.update_of_ne (hPR 1 7), Function.update_of_ne (hPR 1 7)]
        exact tAP 1 (by decide)
      · rw [Function.update_of_ne r1]
        by_cases r7 : r = Rg 7
        · subst r7
          simp only [Function.update_self, h7, Codec.marks_length, List.length_append]
          ring
        · rw [Function.update_of_ne r7, Function.update_of_ne r7, Function.update_of_ne r7]; exact tAval r r1
    · simp only [hι5, hι4, WState.sets, hι3, ctrIdeal, tailIdeal, appendO, WState.setv, WState.seth, hτB]
      exact tAfr.2.2
    · have hst : ι5.st i = (tailIdeal σ tmap S1 S2 TL G VI WT (Rg 7) (P 1) (pre.length + w.length + 1 + w.length)
          (bitWord f ++ out)).st i := by
        simp only [hι5, hι4, WState.sets, hι3, ctrIdeal, tailIdeal, appendO, WState.setv, WState.seth, hτB]
        by_cases hG' : i = G
        · subst hG'
          rw [Function.update_self, Function.update_of_ne hGV, if_pos (Or.inr (Or.inr (Or.inl rfl)))]
        rw [Function.update_of_ne hG']
        by_cases h2 : i = S2
        · subst h2
          rw [Function.update_self, Function.update_of_ne h2V, if_pos (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
        rw [Function.update_of_ne h2, Function.update_of_ne hG']
        by_cases h1 : i = S1
        · subst h1
          rw [Function.update_self, Function.update_of_ne h1V, if_pos (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
        rw [Function.update_of_ne h1]
        by_cases hiV : i = VI
        · subst hiV
          simp only [Function.update_self, if_neg hVsp, if_neg hVsp', tAVI, Codec.marksApp, List.append_assoc]
        simp only [Function.update_of_ne hiV]
        by_cases hsp : (∃ j, tmap j = i) ∨ i = TL ∨ i = G
        · rw [if_pos hsp, if_pos (up i hsp)]
        rw [if_neg hsp, if_neg (dn i hsp h1 h2)]
        by_cases hW : i = WT
        · subst hW; rw [tAWs, s0 _ nWT]
        rw [(tAfr.1 i ?_).1, s0 i ?_]
        · rintro (h | h | h | h)
          · exact hsp (Or.inl h)
          · exact hsp (Or.inr (Or.inl h))
          · exact hsp (Or.inr (Or.inr h))
          · exact h2 h
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨h1, h2, fun h => hsp (Or.inl ⟨iT, h.symm⟩), hW⟩
      rw [← hst]; exact RdEq.refl _

end NearCubicGates.Close.WorkerArith
