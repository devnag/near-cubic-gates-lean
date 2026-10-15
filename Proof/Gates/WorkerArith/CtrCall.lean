import Proof.Gates.WorkerArith.CtrCallC

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.OrdinaryOracleCompose
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

variable {ns nr : ℕ}

theorem blank_nil {l : List Bool} (h : Worker.Blank l) : RdEq l [] := by
  have := Worker.blank_rdEq l h 0; simpa using this

theorem clearPrefix_blank' (m : ℕ) (l : List Bool) (hl : Worker.Blank l) : Worker.Blank (clearPrefix m l) := by
  intro q; have := clearPrefix_blank m l (fun q _ => hl q) q; rw [this]; rfl

theorem replicate_false_blank (m : ℕ) : Worker.Blank (List.replicate m false) := by
  intro q; unfold readTapeBit; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem inTape_iff (p : Program) (j : Fin p.tapeCount) : j = inTape p ↔ j.val = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; exact Fin.ext h

/-- The composed cost is in the class. -/
theorem ctrCost_ok (t win B o s X : ℕ) (hs : s ≤ B) (hX : X = t) :
    40 * win + 40 + 1 + (2 * B + 2 + 1 + (121 * o + 1 + (25 * (2 * win + 2 + s) + 10 + 1 +
      (20 * (2 * win + 2 + s) + 5 + 1 + (X * (18 * (2 * win + 2 + s) + 4) + 1 +
      ((2 * win + 2 + s) * 18 + 3 + 1 + (20 * (2 * win + 2 + s) + 5))))))) ≤ ctrCost t win B o := by
  subst hX
  unfold ctrCost
  have h1 : X * (18 * (2 * win + 2 + s) + 4) ≤ X * (40 * (win + B + o + 1)) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (60 * X + 600) * (win + B + o + 1) = 60 * (X * (win + B + o + 1)) + 600 * (win + B + o + 1) := by ring
  have h3 : X * (40 * (win + B + o + 1)) = 40 * (X * (win + B + o + 1)) := by ring
  rw [h2]
  generalize X * (win + B + o + 1) = TP at *
  generalize X * (18 * (2 * win + 2 + s) + 4) = Q at *
  linarith

open Classical in
theorem ctrCall_ideal {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (outN : List ℕ) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (TL G L VI : Fin (ns + 1)) (Rg : Fin 8 ↪ Fin nr)
    (σ : WState ns nr) : CtrCallIdeal f req outN cap tmap TL G L VI Rg σ := by
  intro hout hinj hTL hG hL hVI hd hin hblank hsh0 hTLb hTLh hGb hGh hLb hLh hVIe hz hcap
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨hTG, hTLL, hTV⟩, ⟨hGL, hGV⟩, hLV, -⟩ := hd
  have hoi : f.program.outputTape ≠ inTape f.program := by
    intro h; apply f.program.outputFresh; have := congrArg Fin.val h; simpa [inTape] using this
  -- the exact start
  let σ0 : WState ns nr := ⟨σ.sh, fun i => if (∃ j, tmap j = i ∧ j ≠ (inTape f.program)) ∨ i = TL ∨ i = G then [] else
    if i = L then List.replicate (budget req) false else σ.st i, σ.val, σ.cell⟩
  have s0sh : ∀ i, σ0.sh i = σ.sh i := fun _ => rfl
  have s0val : ∀ r, σ0.val r = σ.val r := fun _ => rfl
  have s0tm : ∀ j, σ0.st (tmap j) = f.program.inputTapes (input req) j := by
    intro j
    simp only [σ0, Program.inputTapes]
    by_cases hj : j = (inTape f.program)
    · subst hj
      have hn : ¬ ((∃ j', tmap j' = tmap (inTape f.program) ∧ j' ≠ (inTape f.program)) ∨ tmap (inTape f.program) = TL ∨ tmap (inTape f.program) = G) := by
        rintro (⟨j', h1, h2⟩ | h | h)
        · exact h2 (hinj h1)
        · exact hTL _ h
        · exact hG _ h
      rw [if_neg hn, if_neg (hL (inTape f.program)), if_pos ((inTape_iff _ _).1 rfl)]; exact hin
    · rw [if_pos (Or.inl ⟨j, rfl, hj⟩), if_neg (fun h => hj ((inTape_iff _ _).2 h))]
  have s0TL : σ0.st TL = [] := by simp [σ0]
  have s0G : σ0.st G = [] := by simp [σ0]
  have s0L : σ0.st L = List.replicate (budget req) false := by
    have hn : ¬ ((∃ j, tmap j = L ∧ j ≠ (inTape f.program)) ∨ L = TL ∨ L = G) := by
      rintro (⟨j, h1, -⟩ | h | h)
      · exact hL j h1
      · exact hTLL h.symm
      · exact hGL h.symm
    simp only [σ0]; rw [if_neg hn]; simp
  have s0o : ∀ i, (∀ j, tmap j ≠ i) → i ≠ TL → i ≠ G → i ≠ L → σ0.st i = σ.st i := by
    intro i h1 h2 h3 h4
    have hn : ¬ ((∃ j, tmap j = i ∧ j ≠ (inTape f.program)) ∨ i = TL ∨ i = G) := by
      rintro (⟨j, h, -⟩ | h | h)
      · exact h1 j h
      · exact h2 h
      · exact h3 h
    simp only [σ0]; rw [if_neg hn, if_neg h4]
  have hsim0 : SimW σ0 σ := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases h1 : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := h1
      rw [s0tm j]
      by_cases hj : j = (inTape f.program)
      · subst hj; simp only [Program.inputTapes, if_pos ((inTape_iff _ _).1 rfl)]; rw [hin]; exact RdEq.refl _
      · simp only [Program.inputTapes, if_neg (fun h => hj ((inTape_iff _ _).2 h))]
        exact (blank_nil (hblank j hj)).symm
    · push Not at h1
      by_cases h2 : i = TL
      · subst h2; rw [s0TL]; exact (blank_nil hTLb).symm
      · by_cases h3 : i = G
        · subst h3; rw [s0G]; exact (blank_nil hGb).symm
        · by_cases h4 : i = L
          · subst h4; rw [s0L]; exact (Worker.blank_rdEq _ hLb (budget req)).symm
          · rw [s0o i h1 h2 h3 h4]; exact RdEq.refl _
  -- step 1: the guard
  have hw2 : 2 * (input req).length + 2 ≤ cap := by omega
  have s0VI : σ0.st VI = σ.st VI := s0o VI hVI (Ne.symm hTV) (Ne.symm hGV) (Ne.symm hLV)
  have e1 := guardM cap (tmap (inTape f.program)) G (Rg 3) (Rg 4) (Rg 5) (Codec.Rne Rg (by decide)) (Codec.Rne Rg (by decide))
    (Codec.Rne Rg (by decide)) σ0 (input req) (by rw [s0tm]; simp [Program.inputTapes, inTape]) (hsh0 (inTape f.program)) (hG (inTape f.program))
    s0G hGh (hz 3 (by decide)) (hz 4 (by decide)) (hz 5 (by decide)) hw2
  set σ1 := ((σ0.sets G (List.replicate (2 * (input req).length + 2) true)).seth G (2 * (input req).length + 2)).setv
    (Rg 5) (2 * (input req).length + 2) with hσ1
  -- step 2: the clocked counter
  obtain ⟨receipt, τ2, hrun, hrout, hsteps, e2, t2tm, t2TL, t2sh, t2TLh, t2o, t2val, t2cell⟩ :=
    clockDock f req cap tmap hinj TL L hTL hL hTLL σ1
      (fun j => by simp [hσ1, Function.update_of_ne (hG j)]; exact s0tm j) (by simp [hσ1, Function.update_of_ne hTG, s0TL])
      (fun j => by simp [hσ1, Function.update_of_ne (hG j), s0sh, hsh0 j])
      (by simp [hσ1, Function.update_of_ne hTG, s0sh, hTLh])
      (by simp [hσ1, Function.update_of_ne (Ne.symm hGL), s0L]) (by simp [hσ1, Function.update_of_ne (Ne.symm hGL), s0sh, hLh])
  -- step 3: copy the output word
  have hoN : τ2.st (tmap f.program.outputTape) = [] ++ outN.flatMap natWord ++ [] := by rw [t2tm, hrout]; simp [hout]
  have e3 := copyKM cap (tmap f.program.outputTape) VI (hVI f.program.outputTape) Rg outN τ2 [] [] hoN (t2sh f.program.outputTape)
    (by rw [(t2o VI hVI (Ne.symm hTV)).1, (t2o VI hVI (Ne.symm hTV)).2]
        simp [hσ1, Function.update_of_ne (Ne.symm hGV), s0sh, s0VI, hVIe])
    (by rw [t2val]; simp [hσ1, Codec.Rne Rg (show (1 : Fin 8) ≠ 5 by decide), s0val, hz 1 (by decide)])
    (by rw [t2val]; simp [hσ1, Codec.Rne Rg (show (2 : Fin 8) ≠ 5 by decide), s0val, hz 2 (by decide)])
    (by
      rw [t2val]
      have h7 : σ1.val (Rg 7) = σ.val (Rg 7) := by
        simp [hσ1, Codec.Rne Rg (show (7 : Fin 8) ≠ 5 by decide), s0val]
      rw [h7, ← hout]; omega)
  rw [← hout] at e3
  simp only [List.length_nil, Nat.zero_add] at e3
  set τ3 := (appendO τ2 VI (Rg 7) (marks (output req))).seth (tmap f.program.outputTape) (output req).length with hτ3
  -- step 4: the tally
  have e4 := tallyM cap TL G hTG (Rg 5) (Rg 6) (Codec.Rne Rg (by decide)) τ3 (2 * (input req).length + 2)
    receipt.steps
    (by rw [hτ3]; simp [appendO, Function.update_of_ne hGV, (t2o G hG (Ne.symm hTG)).1, hσ1])
    (by rw [hτ3]; simp [appendO, Function.update_of_ne hGV, Function.update_of_ne (hG f.program.outputTape).symm,
      (t2o G hG (Ne.symm hTG)).2, hσ1])
    (by rw [hτ3]; simp [appendO, Codec.Rne Rg (show (5 : Fin 8) ≠ 7 by decide), t2val, hσ1])
    (by rw [hτ3]; simp [appendO, Function.update_of_ne hTV, t2TL])
    (by rw [hτ3]; simp [appendO, Function.update_of_ne hTV, Function.update_of_ne (hTL f.program.outputTape).symm, t2TLh])
    (by rw [hτ3]; simp [appendO, Codec.Rne Rg (show (6 : Fin 8) ≠ 7 by decide), t2val, hσ1,
      Codec.Rne Rg (show (6 : Fin 8) ≠ 5 by decide), s0val, hz 6 (by decide)])
    (by omega)
  set τ4 := ((τ3.sets G (List.replicate (2 * (input req).length + 2 + receipt.steps) true)).seth G 0).setv (Rg 5) 0
    with hτ4
  -- the output tape's length
  have hoT0 : f.program.outputTape.val ≠ 0 := f.program.outputFresh
  have hlen := runFrom_len f.program.machine f.program.outputTape (budget req) _ 0 receipt hrun (by simp [initialConfiguration])
    (by simp [initialConfiguration, Program.inputTapes, hoT0])
  rw [hrout] at hlen
  -- step 5a: clear the output tape backwards
  obtain ⟨l5, e5a, hl5⟩ := clearBackM cap (tmap f.program.outputTape) G (hG f.program.outputTape) (Rg 0) τ4 (2 * (input req).length + 2 + receipt.steps)
    (output req).length
    (by rw [hτ4]; simp) (by rw [hτ4]; simp)
    (by rw [hτ4]; simp [Codec.Rne Rg (show (0 : Fin 8) ≠ 5 by decide), hτ3, appendO,
      Codec.Rne Rg (show (0 : Fin 8) ≠ 7 by decide), t2val, hσ1, s0val, hz 0 (by decide)])
    (by rw [hτ4]; simp [Function.update_of_ne (hG f.program.outputTape), hτ3])
    (fun q hq => by
      rw [hτ4]; simp [Function.update_of_ne (hG f.program.outputTape), hτ3, appendO, Function.update_of_ne (hVI f.program.outputTape), t2tm, hrout]
      exact readTapeBit_beyond _ _ (by omega))
    (by omega) (by omega)
  set τ5a := (τ4.sets (tmap f.program.outputTape) l5).seth (tmap f.program.outputTape) 0 with hτ5a
  -- step 5b: clearOne on every counter tape
  set Xs := (List.finRange f.program.tapeCount).map tmap with hXs
  have hXnd : Xs.Nodup := (List.nodup_finRange _).map hinj
  have hXmem : ∀ i, i ∈ Xs ↔ ∃ j, tmap j = i := by intro i; simp [hXs]
  have e5b := clearAllM cap G (Rg 0) (2 * (input req).length + 2 + receipt.steps) (by omega) Xs τ5a hXnd
    (fun X hX => by obtain ⟨j, rfl⟩ := (hXmem X).1 hX; exact hG j)
    (by rw [hτ5a]; simp [Function.update_of_ne (hG f.program.outputTape).symm, hτ4])
    (by rw [hτ5a]; simp [Function.update_of_ne (hG f.program.outputTape).symm, hτ4])
    (by rw [hτ5a]; simp [hτ4, Codec.Rne Rg (show (0 : Fin 8) ≠ 5 by decide), hτ3, appendO,
      Codec.Rne Rg (show (0 : Fin 8) ≠ 7 by decide), t2val, hσ1, s0val, hz 0 (by decide)])
    (fun X hX => by
      obtain ⟨j, rfl⟩ := (hXmem X).1 hX
      by_cases hj : j = f.program.outputTape
      · subst hj; rw [hτ5a]; simp
      · rw [hτ5a]
        simp [Function.update_of_ne (hinj.ne hj), hτ4, Function.update_of_ne (hG j), hτ3,
          Function.update_of_ne (hVI j), t2sh j])
  set τ5b : WState ns nr := ⟨τ5a.sh, fun i => if i ∈ Xs then
    clearPrefix (2 * (input req).length + 2 + receipt.steps) (τ5a.st i) else τ5a.st i, τ5a.val, τ5a.cell⟩ with hτ5b
  -- step 5c: clear the tally
  have e5c := clearOne_exec (cap := cap) TL G (Rg 0) hTG (2 * (input req).length + 2 + receipt.steps) (by omega) τ5b
    (by simp [hτ5b, (hXmem G), hG, hτ5a, Function.update_of_ne (hG f.program.outputTape).symm, hτ4])
    (by simp [hτ5b, hτ5a, Function.update_of_ne (hG f.program.outputTape).symm, hτ4])
    (by simp [hτ5b, hτ5a, Function.update_of_ne (hTL f.program.outputTape).symm, hτ4, Function.update_of_ne hTG, hτ3,
      Function.update_of_ne hTV, t2TLh])
    (by simp [hτ5b, hτ5a, hτ4, Codec.Rne Rg (show (0 : Fin 8) ≠ 5 by decide), hτ3, appendO,
      Codec.Rne Rg (show (0 : Fin 8) ≠ 7 by decide), t2val, hσ1, s0val, hz 0 (by decide)])
  set τ5c := τ5b.sets TL (clearPrefix (2 * (input req).length + 2 + receipt.steps) (τ5b.st TL)) with hτ5c
  -- step 5d: blank the guard
  have e5d := clearSelfM cap G (Rg 0) τ5c (2 * (input req).length + 2 + receipt.steps)
    (by simp [hτ5c, Function.update_of_ne (Ne.symm hTG), hτ5b, (hXmem G), hG, hτ5a, Function.update_of_ne (hG f.program.outputTape).symm,
      hτ4])
    (by simp [hτ5c, hτ5b, hτ5a, Function.update_of_ne (hG f.program.outputTape).symm, hτ4])
    (by simp [hτ5c, hτ5b, hτ5a, hτ4, Codec.Rne Rg (show (0 : Fin 8) ≠ 5 by decide), hτ3, appendO,
      Codec.Rne Rg (show (0 : Fin 8) ≠ 7 by decide), t2val, hσ1, s0val, hz 0 (by decide)]) (by omega)
  set τ5 := τ5c.sets G (List.replicate (2 * (input req).length + 2 + receipt.steps) false) with hτ5
  -- the run on the exact start, transferred
  have E := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.seq e4 (WXExec.seq e5a
    (WXExec.seq e5b (WXExec.seq e5c e5d))))))
  obtain ⟨τ, eτ, hsτ⟩ := wxexec_sim E σ hsim0
  refine ⟨τ, eτ.mono ?_, CheckedPCPP.SimW.trans ?_ hsτ⟩
  · -- the cost class
    exact ctrCost_ok _ _ _ _ _ _ hsteps (by simp [hXs])
  · -- the end state reads like the ideal
    set mm := 2 * (input req).length + 2 + receipt.steps with hmm
    have hnVI : ¬ ((∃ j, tmap j = VI) ∨ VI = TL ∨ VI = G) := by
      rintro (⟨j, h⟩ | h | h)
      · exact hVI j h
      · exact hTV h.symm
      · exact hGV h.symm
    have id_sh : ∀ i, (ctrIdeal σ tmap TL G VI (Rg 7) (output req)).sh i =
        if i = VI then σ.sh VI + (marks (output req)).length else
          if (∃ j, tmap j = i) ∨ i = TL ∨ i = G then 0 else σ.sh i := by
      intro i; by_cases hi : i = VI
      · subst hi; simp only [ctrIdeal, appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh,
          Function.update_self, if_true]; rw [if_neg hnVI]
      · simp only [ctrIdeal, appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne hi,
          if_neg hi]
    have id_st : ∀ i, (ctrIdeal σ tmap TL G VI (Rg 7) (output req)).st i =
        if i = VI then σ.st VI ++ marks (output req) else
          if (∃ j, tmap j = i) ∨ i = TL ∨ i = G then [] else σ.st i := by
      intro i; by_cases hi : i = VI
      · subst hi; simp only [ctrIdeal, appendO, WState.setv_st, WState.seth_st, WState.sets_st,
          Function.update_self, if_true]; rw [if_neg hnVI]
      · simp only [ctrIdeal, appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hi,
          if_neg hi]
    -- the end state, component by component
    have hframe : ∀ w : List Bool, (frame w).length = 2 * w.length + 1 := by
      intro w; induction w with
      | nil => rfl
      | cons b w ih => simp [frame, ih]; ring
    have far : ∀ j, j ≠ f.program.outputTape → ∀ q, mm ≤ q → readTapeBit (receipt.final.tapes j) q = false := by
      intro j _ q hq
      have hb : (f.program.inputTapes (input req) j).length ≤ 2 * (input req).length + 1 := by
        simp only [Program.inputTapes]; split_ifs
        · rw [hframe]
        · simp
      have := runFrom_far f.program.machine j (budget req) _ (f.program.inputTapes (input req) j).length receipt hrun
        (by simp [initialConfiguration]) (fun q hq => readTapeBit_beyond _ _ (by simp [initialConfiguration]; omega))
      exact this.2 q (by omega)
    have t5tm : ∀ j, Worker.Blank (τ5.st (tmap j)) ∧ τ5.sh (tmap j) = 0 := by
      intro j
      have hmem : tmap j ∈ Xs := (hXmem _).2 ⟨j, rfl⟩
      constructor
      · have e : τ5.st (tmap j) = clearPrefix mm (τ5a.st (tmap j)) := by
          simp [hτ5, Function.update_of_ne (hG j), hτ5c, Function.update_of_ne (hTL j), hτ5b, hmem]
        rw [e]
        by_cases hj : j = f.program.outputTape
        · subst hj; rw [hτ5a]; simp only [WState.seth_st, WState.sets_st, Function.update_self]
          exact clearPrefix_blank' _ _ hl5
        · have e2 : τ5a.st (tmap j) = receipt.final.tapes j := by
            simp [hτ5a, Function.update_of_ne (hinj.ne hj), hτ4, Function.update_of_ne (hG j), hτ3, appendO,
              Function.update_of_ne (hVI j), t2tm]
          rw [e2]
          intro q; have := clearPrefix_blank mm _ (far j hj) q; rw [this]; rfl
      · by_cases hj : j = f.program.outputTape
        · subst hj; simp [hτ5, hτ5c, hτ5b, hτ5a]
        · simp [hτ5, hτ5c, hτ5b, hτ5a, Function.update_of_ne (hinj.ne hj), hτ4, Function.update_of_ne (hG j), hτ3,
            appendO, Function.update_of_ne (hVI j), t2sh]
    have t5TL : Worker.Blank (τ5.st TL) ∧ τ5.sh TL = 0 := by
      have hn : TL ∉ Xs := fun h => by obtain ⟨j, hj⟩ := (hXmem _).1 h; exact hTL j hj
      constructor
      · have e : τ5.st TL = clearPrefix mm (List.replicate receipt.steps true) := by
          simp [hτ5, Function.update_of_ne hTG, hτ5c, hτ5b, hn, hτ5a, Function.update_of_ne (hTL _).symm, hτ4,
            hτ3, appendO, Function.update_of_ne hTV, t2TL]
        rw [e]; intro q
        have := clearPrefix_blank mm (List.replicate receipt.steps true)
          (fun q hq => readTapeBit_beyond _ _ (by simp; omega)) q
        rw [this]; rfl
      · simp [hτ5, hτ5c, hτ5b, hτ5a, Function.update_of_ne (hTL _).symm, hτ4, Function.update_of_ne hTG, hτ3,
          appendO, Function.update_of_ne hTV, t2TLh]
    have t5G : Worker.Blank (τ5.st G) ∧ τ5.sh G = 0 := by
      refine ⟨by simp [hτ5]; exact replicate_false_blank _, ?_⟩
      simp [hτ5, hτ5c, hτ5b, hτ5a, Function.update_of_ne (hG _).symm, hτ4]
    have t5VI : τ5.st VI = σ.st VI ++ marks (output req) ∧ τ5.sh VI = σ.sh VI + (marks (output req)).length := by
      have hn : VI ∉ Xs := fun h => by obtain ⟨j, hj⟩ := (hXmem _).1 h; exact hVI j hj
      constructor
      · simp [hτ5, Function.update_of_ne (Ne.symm hGV), hτ5c, Function.update_of_ne (Ne.symm hTV), hτ5b, hn, hτ5a,
          Function.update_of_ne (hVI _).symm, hτ4, hτ3, appendO, (t2o VI hVI (Ne.symm hTV)).1, hσ1, s0VI]
      · simp [hτ5, hτ5c, hτ5b, hτ5a, Function.update_of_ne (hVI _).symm, hτ4, Function.update_of_ne (Ne.symm hGV),
          hτ3, appendO, (t2o VI hVI (Ne.symm hTV)).2, hσ1, s0sh]
    have t5o : ∀ i, (∀ j, tmap j ≠ i) → i ≠ TL → i ≠ G → i ≠ VI → τ5.st i = σ0.st i ∧ τ5.sh i = σ.sh i := by
      intro i h1 h2 h3 h4
      have hn : i ∉ Xs := fun h => by obtain ⟨j, hj⟩ := (hXmem _).1 h; exact h1 j hj
      have ho : i ≠ tmap f.program.outputTape := fun h => h1 _ h.symm
      constructor
      · simp [hτ5, Function.update_of_ne h3, hτ5c, Function.update_of_ne h2, hτ5b, hn, hτ5a, Function.update_of_ne ho,
          hτ4, hτ3, appendO, Function.update_of_ne h4, (t2o i h1 h2).1, hσ1]
      · simp [hτ5, hτ5c, hτ5b, hτ5a, Function.update_of_ne ho, hτ4, Function.update_of_ne h3, hτ3, appendO,
          Function.update_of_ne h4, (t2o i h1 h2).2, hσ1, s0sh]
    have t5val : τ5.val = Function.update σ.val (Rg 7) (σ.val (Rg 7) + (marks (output req)).length) := by
      funext r
      by_cases h7 : r = Rg 7
      · subst h7; simp [hτ5, hτ5c, hτ5b, hτ5a, hτ4, Codec.Rne Rg (show (7 : Fin 8) ≠ 5 by decide), hτ3, appendO,
          t2val, hσ1, s0val]
      · by_cases h5 : r = Rg 5
        · subst h5; simp [hτ5, hτ5c, hτ5b, hτ5a, hτ4, h7, s0val, hz 5 (by decide)]
        · simp [hτ5, hτ5c, hτ5b, hτ5a, hτ4, Function.update_of_ne h5, hτ3, appendO, Function.update_of_ne h7, t2val,
            hσ1, s0val]
    have t5cell : τ5.cell = σ.cell := by simp [hτ5, hτ5c, hτ5b, hτ5a, hτ4, hτ3, appendO, t2cell, hσ1]; rfl
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · funext i
      rw [id_sh]
      by_cases hi : ∃ j, tmap j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [if_neg (hVI j), if_pos (Or.inl ⟨j, rfl⟩), (t5tm j).2]
      · push Not at hi
        by_cases h2 : i = TL
        · subst h2; rw [if_neg hTV, if_pos (Or.inr (Or.inl rfl)), t5TL.2]
        · by_cases h3 : i = G
          · subst h3; rw [if_neg hGV, if_pos (Or.inr (Or.inr rfl)), t5G.2]
          · by_cases h4 : i = VI
            · subst h4; rw [if_pos rfl, t5VI.2]
            · rw [if_neg h4, if_neg (by rintro (⟨j, hj⟩ | h | h); exacts [hi j hj, h2 h, h3 h]), (t5o i hi h2 h3 h4).2]
    · rw [t5val]; simp [ctrIdeal, appendO]
    · rw [t5cell]; rfl
    · rw [id_st]
      by_cases hi : ∃ j, tmap j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [if_neg (hVI j), if_pos (Or.inl ⟨j, rfl⟩)]; exact (blank_nil (t5tm j).1).symm
      · push Not at hi
        by_cases h2 : i = TL
        · subst h2; rw [if_neg hTV, if_pos (Or.inr (Or.inl rfl))]; exact (blank_nil t5TL.1).symm
        · by_cases h3 : i = G
          · subst h3; rw [if_neg hGV, if_pos (Or.inr (Or.inr rfl))]; exact (blank_nil t5G.1).symm
          · by_cases h4 : i = VI
            · subst h4; rw [if_pos rfl, t5VI.1]; exact RdEq.refl _
            · rw [if_neg h4, if_neg (by rintro (⟨j, hj⟩ | h | h); exacts [hi j hj, h2 h, h3 h]), (t5o i hi h2 h3 h4).1]
              by_cases h5 : i = L
              · subst h5; rw [s0L]; exact Worker.blank_rdEq _ hLb _
              · rw [s0o i hi h2 h3 h5]; exact RdEq.refl _

theorem wordFunction_blank_ideal {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (f.program.inputTapes (input req) j)) (hLb : Worker.Blank (σ.st L))
    (hLsh : σ.sh L = 0) :
    ∃ τ tout, WXExec cap (WMX.machZ f.program.machine tmap L) σ τ (2 * budget req + 2) ∧
      SimW (updS tmap σ (fun _ => 0) tout) τ ∧ tout f.program.outputTape = output req := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  set σ' := σ.sets L (List.replicate (budget req) false) with hσ'
  have hs : SimW σ' σ := CheckedPCPP.SimW.symm (Worker.simW_sets σ L _ (Worker.blank_rdEq _ hLb _))
  have hrel : ConfRel (fun _ => False) (initialConfiguration f.program.machine (f.program.inputTapes (input req)))
      ⟨f.program.machine.start, fun _ => 0, fun j => σ'.st (tmap j)⟩ :=
    ⟨rfl, rfl, fun j => by simp [hσ', Function.update_of_ne (hL j)]; exact (hin j).symm, fun _ h => h.elim⟩
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel f.program.machine _ (budget req) hrel receipt hrun
  have hd := docked_updS tmap hinj σ' (fun _ => 0) r'.final.tapes
  have e := WXExec.machZ cap (τ := updS tmap σ' (fun _ => 0) r'.final.tapes) hinj hL
    (Step.of_run (r := r') hr' rfl rfl) (fun j => by simp [hσ', h0 j]) (by simp [hσ']) (by simp [hσ', hLsh]) le_rfl
    hd.st hd.sh hd.other hd.val hd.cell
  obtain ⟨τ, e', hs'⟩ := wxexec_sim e σ hs
  refine ⟨τ, receipt.final.tapes, e', CheckedPCPP.SimW.trans ?_ hs', hout⟩
  refine ⟨?_, rfl, rfl, fun i => ?_⟩
  · funext i
    by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [updS_sh_slot tmap _ _ _ hinj, updS_sh_slot tmap _ _ _ hinj]
    · push Not at hi
      rw [updS_sh_other tmap _ _ _ i hi, updS_sh_other tmap _ _ _ i hi]; simp [hσ']
  · by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [updS_st_slot tmap _ _ _ hinj, updS_st_slot tmap _ _ _ hinj]
      exact hrel'.read j
    · push Not at hi
      rw [updS_st_other tmap _ _ _ i hi, updS_st_other tmap _ _ _ i hi]
      by_cases hiL : i = L
      · subst hiL; simp [hσ']; exact (Worker.blank_rdEq _ hLb _)
      · simp [hσ', Function.update_of_ne hiL]; exact RdEq.refl _

end NearCubicGates.Close.WorkerArith
