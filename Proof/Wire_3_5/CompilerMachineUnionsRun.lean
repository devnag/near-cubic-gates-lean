import Proof.Wire_3_5.CompilerMachineUnionsMach

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The state of pass 1 -/

/-- The new entries written so far, and the registers `R`, `Z`, `Z2` and the cell `C`. -/
structure U1 where
  outs : List (List Bool)
  R : List Bool
  Z : List Bool
  Z2 : List Bool
  C : Bool

/-- One entry of pass 1. -/
def u1step (Q W : ℕ) (g : List Bool) (st : U1) (r : List Bool) : U1 :=
  if testW Q W r then ⟨st.outs ++ [orW (incrW Q W r) g], r, incrW Q W r, orW (incrW Q W r) g, true⟩
  else ⟨st.outs, r, ZipMap.map andOut keep r (lastT Q W) false, st.Z2, false⟩

theorem foldl_u1step_outs (Q W : ℕ) (g : List Bool) : ∀ (E : List (List Bool)) (st : U1),
    (E.foldl (u1step Q W g) st).outs = st.outs ++ (E.filter (testW Q W)).map (fun r => orW (incrW Q W r) g)
  | [], st => by simp
  | r :: E, st => by
    rw [List.foldl_cons, foldl_u1step_outs Q W g E]
    by_cases h : testW Q W r
    · simp [u1step, h]
    · simp [u1step, h]

/-- Every register holds a word of the entries' width. -/
def U1Inv (L : ℕ) (st : U1) : Prop := st.R.length = L ∧ st.Z.length = L ∧ st.Z2.length = L

theorem u1step_inv (Q W : ℕ) (g : List Bool) (hg : g.length = Q + W + 1) (hQ : 1 ≤ Q) (st : U1) (r : List Bool)
    (hr : r.length = Q + W + 1) (h : U1Inv (Q + W + 1) st) : U1Inv (Q + W + 1) (u1step Q W g st r) := by
  obtain ⟨_, _, h3⟩ := h
  have hi : (incrW Q W r).length = Q + W + 1 := by
    unfold incrW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hr, levelT_length]), hr]
  have ho : (orW (incrW Q W r) g).length = Q + W + 1 := by
    unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hi, hg]), hi]
  have ha : (ZipMap.map andOut keep r (lastT Q W) false).length = Q + W + 1 := by
    rw [ZipMap.map_length _ _ _ _ _ (by rw [hr, lastT_length Q W hQ]), hr]
  unfold u1step
  split_ifs
  · exact ⟨hr, hi, ho⟩
  · exact ⟨hr, ha, h3⟩

theorem foldl_u1step_inv (Q W : ℕ) (g : List Bool) (hg : g.length = Q + W + 1) (hQ : 1 ≤ Q) :
    ∀ (E : List (List Bool)) (st : U1), (∀ r ∈ E, r.length = Q + W + 1) → U1Inv (Q + W + 1) st →
      U1Inv (Q + W + 1) (E.foldl (u1step Q W g) st)
  | [], _, _, h => h
  | r :: E, st, hE, h => by
    rw [List.foldl_cons]
    exact foldl_u1step_inv Q W g hg hQ E _ (fun r' hr' => hE r' (List.mem_cons_of_mem r hr'))
      (u1step_inv Q W g hg hQ st r (hE r List.mem_cons_self) h)

/-- Pass 1's heads: the entries' cursor, the new entries' cursor. -/
def uH (p : ℕ) (outs : List (List Bool)) : Fin 11 → ℕ := ![p, (outs.flatMap frame).length, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Pass 1's tapes. -/
def uA (S BW g : List Bool) (Q W cap : ℕ) (st : U1) : Fin 11 → List Bool :=
  ![S, overlay (st.outs.flatMap frame) BW, frame g, frame st.R, frame st.Z, frame st.Z2, frame (lastT Q W),
    frame (levelT Q W), frame (zeroT Q W), [st.C], List.replicate cap false]

/-- The uniform cost bound of one entry of pass 1, at width `L`. -/
def uBodyCost (L : ℕ) : ℕ := 24 * L + 33

theorem zeroHeads3 : (![0, 0, 0] : Fin 3 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

theorem read_cell' (c : Bool) : readTapeBit [c] 0 = c := by cases c <;> rfl

/-- **One entry of pass 1.** -/
theorem ubody_run (pre r post BW g : List Bool) (Q W cap : ℕ) (st : U1) (hQ : 1 ≤ Q)
    (hr : r.length = Q + W + 1) (hg : g.length = Q + W + 1) (h : U1Inv (Q + W + 1) st)
    (hcap : 2 * (Q + W + 1) + 1 ≤ cap) :
    Step uBodyM (uBodyCost (Q + W + 1)) (uH pre.length st.outs) (uA (pre ++ frame r ++ post) BW g Q W cap st)
      (uH (pre.length + (2 * r.length + 1)) (u1step Q W g st r).outs)
      (uA (pre ++ frame r ++ post) BW g Q W cap (u1step Q W g st r)) := by
  obtain ⟨hR, hZ, hZ2⟩ := h
  have hcap' : 2 * r.length + 1 ≤ cap := by omega
  have hlT : r.length = (lastT Q W).length := by rw [hr, lastT_length Q W hQ]
  have hvT : r.length = (levelT Q W).length := by rw [hr, levelT_length]
  have ha : (ZipMap.map andOut keep r (lastT Q W) false).length = r.length := ZipMap.map_length _ _ _ _ _ hlT
  have hi : (incrW Q W r).length = r.length := ZipMap.map_length _ _ _ _ _ hvT
  have hzT : (zeroT Q W).length = Q + W + 1 := by simp [zeroT]
  have ho : (orW (incrW Q W r) g).length = r.length := by
    unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hi, hr, hg]), hi]
  have s1 := uload_step cap (overlay (st.outs.flatMap frame) BW) (frame g) (frame st.Z) (frame st.Z2) (frame (lastT Q W)) (frame (levelT Q W))
    (frame (zeroT Q W)) [st.C] (st.outs.flatMap frame).length pre r post st.R (by rw [hR, hr]) hcap'
  have s2 := unudge_step cap (pre ++ frame r ++ post) (overlay (st.outs.flatMap frame) BW) (frame g) (frame r) (frame st.Z) (frame st.Z2) (frame (lastT Q W)) (frame (levelT Q W))
    (frame (zeroT Q W)) [st.C] (pre.length + 2 * r.length) (st.outs.flatMap frame).length
  have s3 := uand_step cap (pre ++ frame r ++ post) (overlay (st.outs.flatMap frame) BW) (frame g) (frame st.Z2) (frame (levelT Q W)) (frame (zeroT Q W)) [st.C]
    (pre.length + 2 * r.length + 1) (st.outs.flatMap frame).length r (lastT Q W) st.Z hlT (by rw [hZ, hr]) hcap'
  have s4 := ueq_step cap (pre ++ frame r ++ post) (overlay (st.outs.flatMap frame) BW) (frame g) (frame r) (frame st.Z2) (frame (lastT Q W)) (frame (levelT Q W))
    (pre.length + 2 * r.length + 1) (st.outs.flatMap frame).length (ZipMap.map andOut keep r (lastT Q W) false) (zeroT Q W) st.C
    (by rw [ha, hzT, hr]) (by rw [ha]; exact hcap')
  have s1234 := ((s1.seq s2).seq s3).seq s4
  by_cases ht : testW Q W r = true
  · have e1 := uincr_step cap (pre ++ frame r ++ post) (overlay (st.outs.flatMap frame) BW) (frame g) (frame st.Z2) (frame (lastT Q W)) (frame (zeroT Q W)) [testW Q W r]
      (pre.length + 2 * r.length + 1) (st.outs.flatMap frame).length r (levelT Q W) (ZipMap.map andOut keep r (lastT Q W) false) hvT ha hcap'
    have e2 := uor_step cap (pre ++ frame r ++ post) (overlay (st.outs.flatMap frame) BW) (frame r) (frame (lastT Q W)) (frame (levelT Q W)) (frame (zeroT Q W)) [testW Q W r]
      (pre.length + 2 * r.length + 1) (st.outs.flatMap frame).length (incrW Q W r) g st.Z2 (by rw [hi, hr, hg]) (by rw [hZ2, hi, hr])
      (by rw [hi]; exact hcap')
    have e3 := uemit_step cap (pre ++ frame r ++ post) (frame g) (frame r) (frame (incrW Q W r)) (frame (lastT Q W)) (frame (levelT Q W))
      (frame (zeroT Q W)) [testW Q W r] (pre.length + 2 * r.length + 1) (orW (incrW Q W r) g)
      (st.outs.flatMap frame) BW (by rw [ho]; exact hcap')
    have eB := branch_true (9 : Fin 11) (idle 11) ((e1.seq e2).seq e3)
      (by show readTapeBit [testW Q W r] 0 = true; rw [ht]; rfl)
    have hu : u1step Q W g st r = ⟨st.outs ++ [orW (incrW Q W r) g], r, incrW Q W r, orW (incrW Q W r) g, true⟩ := by
      unfold u1step; rw [if_pos ht]
    rw [hu]
    refine ((s1234.seq eB).enlarge (m := uBodyCost (Q + W + 1))
      (by unfold uBodyCost; rw [ho, hi, ha]; omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [uH, frame_length]
      all_goals omega
    · funext i; fin_cases i <;> simp [uA, orW, incrW, ht]
  · have hf : testW Q W r = false := by simpa using ht
    have eB := branch_false (9 : Fin 11) uExtendM
      (idleStep ![pre.length + 2 * r.length + 1, (st.outs.flatMap frame).length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        ![pre ++ frame r ++ post, overlay (st.outs.flatMap frame) BW, frame g, frame r, frame (ZipMap.map andOut keep r (lastT Q W) false), frame st.Z2, frame (lastT Q W),
          frame (levelT Q W), frame (zeroT Q W), [decide (ZipMap.map andOut keep r (lastT Q W) false = zeroT Q W)],
          List.replicate cap false])
      (by show readTapeBit [testW Q W r] 0 = false; rw [hf]; rfl)
    have hu : u1step Q W g st r = ⟨st.outs, r, ZipMap.map andOut keep r (lastT Q W) false, st.Z2, false⟩ := by
      unfold u1step; rw [if_neg (by simp [hf])]
    have hfp : ¬ ZipMap.map andOut keep r (lastT Q W) false = zeroT Q W := fun h => by
      have : testW Q W r = true := decide_eq_true h
      rw [hf] at this; exact Bool.false_ne_true this
    rw [hu]
    refine ((s1234.seq eB).enlarge (m := uBodyCost (Q + W + 1))
      (by unfold uBodyCost; simp only [ha, hr]; omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [uH]
      all_goals omega
    · funext i; fin_cases i <;> simp [uA, hfp]

/-! ## The stream loop of pass 1 -/

theorem uloop_run (E : List (List Bool)) (staleS BW g : List Bool) (Q W cap : ℕ) (s0 : U1) (hQ : 1 ≤ Q)
    (hE : ∀ r ∈ E, r.length = Q + W + 1) (hg : g.length = Q + W + 1) (h0 : U1Inv (Q + W + 1) s0)
    (hcap : 2 * (Q + W + 1) + 1 ≤ cap) :
    Step (StreamController.machine uBodyM 0) (E.length * (uBodyCost (Q + W + 1) + 2) + 1) (uH 0 s0.outs)
      (uA (streamTape E staleS) BW g Q W cap s0)
      (uH (E.flatMap frame).length (E.foldl (u1step Q W g) s0).outs)
      (uA (streamTape E staleS) BW g Q W cap (E.foldl (u1step Q W g) s0)) := by
  refine streamRun uBodyM 0 E staleS (fun r hr h => by have := hE r hr; rw [h] at this; simp at this)
    (u1step Q W g) s0 (fun st p => uH p st.outs) (fun st => uA (streamTape E staleS) BW g Q W cap st)
    (fun _ => rfl) (fun _ _ => rfl) (uBodyCost (Q + W + 1)) ?_
  intro j hj
  have hlen := hE _ (List.getElem_mem hj)
  have hst : (E.take (j + 1)).foldl (u1step Q W g) s0 = u1step Q W g ((E.take j).foldl (u1step Q W g) s0) E[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  have hinv := foldl_u1step_inv Q W g hg hQ (E.take j) s0 (fun r hr => hE r (List.mem_of_mem_take hr)) h0
  have hb := ubody_run ((E.take j).flatMap frame) E[j] ((E.drop (j + 1)).flatMap frame ++ false :: staleS) BW g Q W cap
    ((E.take j).foldl (u1step Q W g) s0) hQ hlen hg hinv hcap
  rw [← streamTape_split E staleS j hj] at hb
  rw [hst, off_succ E j hj]
  exact hb

/-- The new entries of one lift step: the extensions of the entries below size `Q`, then `g`'s own entry. -/
def liftN (Q W : ℕ) (g : List Bool) (E : List (List Bool)) : List (List Bool) :=
  (E.filter (testW Q W)).map (fun r => orW (incrW Q W r) g) ++ [incrW Q W g]

theorem liftStepW_eq (Q W : ℕ) (E : List (List Bool)) (g : List Bool) : liftStepW Q W E g = E ++ liftN Q W g E := by
  simp [liftStepW, liftN, List.append_assoc]

/-- The cost of pass 1 before its reset, for `n` entries of width `L`. -/
def pass1Cost (n L : ℕ) : ℕ :=
  n * (uBodyCost L + 2) + 1 + 1 + (2 * (2 * L + 1) + 2) + 1 + (2 * (2 * L + 1) + 2) + 1 + 1

/-- **Pass 1**: the new entries, then `g`'s own entry and the terminator on `O`. -/
theorem upass1_run (E : List (List Bool)) (staleS BW g : List Bool) (Q W cap : ℕ) (s0 : U1) (hQ : 1 ≤ Q)
    (hE : ∀ r ∈ E, r.length = Q + W + 1) (hg : g.length = Q + W + 1) (h0 : U1Inv (Q + W + 1) s0) (hs0 : s0.outs = [])
    (hcap : 2 * (Q + W + 1) + 1 ≤ cap) :
    Step uPass1LoopM (pass1Cost E.length (Q + W + 1)) (uH 0 s0.outs) (uA (streamTape E staleS) BW g Q W cap s0)
      ![(E.flatMap frame).length, ((liftN Q W g E).flatMap frame).length + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![streamTape E staleS, overlay ((liftN Q W g E).flatMap frame ++ [false]) BW, frame g,
        frame (E.foldl (u1step Q W g) s0).R, frame (incrW Q W g), frame (E.foldl (u1step Q W g) s0).Z2,
        frame (lastT Q W), frame (levelT Q W), frame (zeroT Q W), [(E.foldl (u1step Q W g) s0).C],
        List.replicate cap false] := by
  have L := uloop_run E staleS BW g Q W cap s0 hQ hE hg h0 hcap
  obtain ⟨hR, hZ, hZ2⟩ := foldl_u1step_inv Q W g hg hQ E s0 hE h0
  have houts : (E.foldl (u1step Q W g) s0).outs = (E.filter (testW Q W)).map (fun r => orW (incrW Q W r) g) := by
    rw [foldl_u1step_outs, hs0, List.nil_append]
  have hvT : g.length = (levelT Q W).length := by rw [hg, levelT_length]
  have hig : (incrW Q W g).length = Q + W + 1 := by unfold incrW; rw [ZipMap.map_length _ _ _ _ _ hvT, hg]
  set fin := E.foldl (u1step Q W g) s0
  have s5 := uincrG_step cap (streamTape E staleS) (overlay (fin.outs.flatMap frame) BW) (frame fin.R) (frame fin.Z2)
    (frame (lastT Q W)) (frame (zeroT Q W)) [fin.C] (E.flatMap frame).length (fin.outs.flatMap frame).length
    g (levelT Q W) fin.Z hvT (by rw [hZ, hg]) (by rw [hg]; exact hcap)
  have s6 := uemitZ_step cap (streamTape E staleS) (frame g) (frame fin.R) (frame fin.Z2) (frame (lastT Q W))
    (frame (levelT Q W)) (frame (zeroT Q W)) [fin.C] (E.flatMap frame).length (incrW Q W g)
    (fin.outs.flatMap frame) BW (by rw [hig]; exact hcap)
  have s7 := uput_step cap (streamTape E staleS) (frame g) (frame fin.R) (frame (incrW Q W g)) (frame fin.Z2)
    (frame (lastT Q W)) (frame (levelT Q W)) (frame (zeroT Q W)) [fin.C] (E.flatMap frame).length
    (fin.outs.flatMap frame ++ frame (incrW Q W g)) BW
  have s6' := s6.congr (hout' := ![(E.flatMap frame).length, (fin.outs.flatMap frame ++ frame (incrW Q W g)).length,
      0, 0, 0, 0, 0, 0, 0, 0, 0]) (by funext i; fin_cases i <;> simp [frame_length]) rfl
  have hall := ((L.seq s5).seq s6').seq s7
  have hN : liftN Q W g E = fin.outs ++ [incrW Q W g] := by rw [houts]; rfl
  refine (hall.enlarge (by unfold pass1Cost; rw [hig]; omega)).congr ?_ ?_
  · funext i; fin_cases i <;> simp [hN]
  · funext i; fin_cases i <;> simp [hN]

/-! ## One lift step -/

theorem uApp_inj : Function.Injective uApp := by decide

theorem install_uApp (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install uApp A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_slot uApp uApp_inj A v 0
  · exact install_slot uApp uApp_inj A v 1
  · exact install_other uApp A v 2 (by decide)
  · exact install_other uApp A v 3 (by decide)
  · exact install_other uApp A v 4 (by decide)
  · exact install_other uApp A v 5 (by decide)
  · exact install_other uApp A v 6 (by decide)
  · exact install_other uApp A v 7 (by decide)
  · exact install_other uApp A v 8 (by decide)
  · exact install_other uApp A v 9 (by decide)
  · exact install_other uApp A v 10 (by decide)
  · exact install_slot uApp uApp_inj A v 2

theorem dockH_uApp (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH uApp H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot uApp uApp_inj H v 0
  · exact dockH_slot uApp uApp_inj H v 1
  · exact dockH_other uApp H v 2 (by decide)
  · exact dockH_other uApp H v 3 (by decide)
  · exact dockH_other uApp H v 4 (by decide)
  · exact dockH_other uApp H v 5 (by decide)
  · exact dockH_other uApp H v 6 (by decide)
  · exact dockH_other uApp H v 7 (by decide)
  · exact dockH_other uApp H v 8 (by decide)
  · exact dockH_other uApp H v 9 (by decide)
  · exact dockH_other uApp H v 10 (by decide)
  · exact dockH_slot uApp uApp_inj H v 2

/-- The cost of one lift step on `n` entries of width `L`. -/
def liftCost (n L : ℕ) : ℕ := (2 * pass1Cost n L + 2) + 1 + (2 * appendCost n (n + 1) L + 2)

theorem appendCost_mono (m : ℕ) {n n' : ℕ} (L : ℕ) (h : n ≤ n') : appendCost m n L ≤ appendCost m n' L := by
  unfold appendCost
  have := Nat.mul_le_mul_right (2 * L + 1 + 1 + 1 + 2) h
  omega

theorem liftN_length_le (Q W : ℕ) (g : List Bool) (E : List (List Bool)) : (liftN Q W g E).length ≤ E.length + 1 := by
  unfold liftN
  simp only [List.length_append, List.length_map, List.length_singleton]
  have := List.length_filter_le (testW Q W) E
  omega

theorem liftN_widths (Q W : ℕ) (g : List Bool) (hg : g.length = Q + W + 1) (E : List (List Bool))
    (hE : ∀ r ∈ E, r.length = Q + W + 1) : ∀ r ∈ liftN Q W g E, r.length = Q + W + 1 := by
  intro r hr
  have hvT : ∀ x : List Bool, x.length = Q + W + 1 → (incrW Q W x).length = Q + W + 1 := by
    intro x hx; unfold incrW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hx, levelT_length]), hx]
  unfold liftN at hr
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton] at hr
  rcases hr with ⟨x, ⟨hx, _⟩, rfl⟩ | rfl
  · have := hvT x (hE x hx)
    unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [this, hg]), this]
  · exact hvT g hg

theorem lift_run (E : List (List Bool)) (staleS BW g R0 Z0 Z20 : List Bool) (C0 : Bool) (Q W cap cap2 : ℕ)
    (hQ : 1 ≤ Q) (hE : ∀ r ∈ E, r.length = Q + W + 1) (hg : g.length = Q + W + 1)
    (h0 : U1Inv (Q + W + 1) ⟨[], R0, Z0, Z20, C0⟩) (hcap : 2 * (Q + W + 1) + 1 ≤ cap)
    (hcap2 : pass1Cost E.length (Q + W + 1) ≤ cap2 ∧ appendCost E.length (E.length + 1) (Q + W + 1) ≤ cap2) :
    Step uLiftM (liftCost E.length (Q + W + 1)) (fun _ => 0)
      ![streamTape E staleS, BW, frame g, frame R0, frame Z0, frame Z20, frame (lastT Q W), frame (levelT Q W),
        frame (zeroT Q W), [C0], List.replicate cap false, List.replicate cap2 false]
      (fun _ => 0)
      ![streamTape (liftStepW Q W E g) ((streamTape E staleS).drop (((liftStepW Q W E g).flatMap frame).length + 1)),
        streamTape (liftN Q W g E) (BW.drop (((liftN Q W g E).flatMap frame).length + 1)), frame g,
        frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).R, frame (incrW Q W g),
        frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).Z2, frame (lastT Q W), frame (levelT Q W),
        frame (zeroT Q W), [(E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).C], List.replicate cap false,
        List.replicate cap2 false] := by
  have h1 := upass1_run E staleS BW g Q W cap ⟨[], R0, Z0, Z20, C0⟩ hQ hE hg h0 rfl hcap
  have hm := h1.mask (cap := cap2) uSelSO (by intro i hi; fin_cases i <;> simp_all [uSelSO, uH]) hcap2.1
  rw [overlay_stream] at hm
  have hN := liftN_widths Q W g hg E hE
  have ha := appendRun E (liftN Q W g E) staleS (BW.drop (((liftN Q W g E).flatMap frame).length + 1)) (Q + W + 1)
    cap2 hE hN (by omega) ((appendCost_mono E.length (Q + W + 1) (liftN_length_le Q W g E)).trans hcap2.2)
  have hd := dockKeep ha uApp uApp_inj (fun _ => 0)
    ![streamTape E staleS, streamTape (liftN Q W g E) (BW.drop (((liftN Q W g E).flatMap frame).length + 1)), frame g,
      frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).R, frame (incrW Q W g),
      frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).Z2, frame (lastT Q W), frame (levelT Q W),
      frame (zeroT Q W), [(E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).C], List.replicate cap false,
      List.replicate cap2 false]
    (fun _ => rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_uApp] at hd
  have hm' := hm.congr_in (hin' := fun _ => 0) (tin' := ![streamTape E staleS, BW, frame g, frame R0, frame Z0,
      frame Z20, frame (lastT Q W), frame (levelT Q W), frame (zeroT Q W), [C0], List.replicate cap false,
      List.replicate cap2 false])
    (by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl)
    (by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl)
  have hm'' := hm'.congr (hout' := fun _ => 0) (tout' := ![streamTape E staleS,
      streamTape (liftN Q W g E) (BW.drop (((liftN Q W g E).flatMap frame).length + 1)), frame g,
      frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).R, frame (incrW Q W g),
      frame (E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).Z2, frame (lastT Q W), frame (levelT Q W),
      frame (zeroT Q W), [(E.foldl (u1step Q W g) ⟨[], R0, Z0, Z20, C0⟩).C], List.replicate cap false,
      List.replicate cap2 false])
    (by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl)
    (by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl)
  have hall := hm''.seq hd
  rw [← liftStepW_eq] at hall
  have hmono := appendCost_mono E.length (Q + W + 1) (liftN_length_le Q W g E)
  exact hall.enlarge (by unfold liftCost; omega)

end NearCubicWires.WireExponent3_5.CompilerMachine.Unions
