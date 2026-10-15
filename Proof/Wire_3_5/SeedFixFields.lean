import Proof.Wire_3_5.SeedFixFrames

/-! # C4.Sb, machine part 8: the counter's fields as framed words, and copies of framed streams

`fieldsLoop_run`: `m` consecutive fields of `r` bits of a plain source become `m` framed words appended to the output
(the counter's labels and walk digits); `framesLoop_run`: `m` framed words copied from a stream.

Paper quantities of the main types: the words `fields.flatMap frame` (`fieldsLoop_run`, `framesLoop_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

def f5B : Fin 4 → Fin 5 := ![1, 2, 3, 4]

theorem install_f5B (A : Fin 5 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install f5B A v = ![A 0, v 0, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f5B (H : Fin 5 → ℕ) (v : Fin 4 → ℕ) :
    dockH f5B H v = ![H 0, v 0, v 1, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def f5E : Fin 1 → Fin 5 := ![3]

theorem install_f5E (A : Fin 5 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install f5E A v = ![A 0, A 1, A 2, v 0, A 4] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f5E (H : Fin 5 → ℕ) (v : Fin 1 → ℕ) :
    dockH f5E H v = ![H 0, H 1, H 2, v 0, H 4] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def f5N : Fin 1 → Fin 5 := ![0]

theorem install_f5N (A : Fin 5 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install f5N A v = ![v 0, A 1, A 2, A 3, A 4] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f5N (H : Fin 5 → ℕ) (v : Fin 1 → ℕ) :
    dockH f5N H v = ![v 0, H 1, H 2, H 3, H 4] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def selRR : Fin 3 → Bool := ![true, false, false]

/-- One field: its bits (ruler rewound), the word's terminator, one step of the field ruler. -/
noncomputable def fieldBody :=
  Composition.machine (Composition.machine (RecoveryFocus.machine f5B (MaskedReset.machine bitsLoopM selRR))
    (RecoveryFocus.machine f5E EndF.machine)) (RecoveryFocus.machine f5N nudgeM)

noncomputable def fieldsLoopM := StreamController.machine fieldBody 0

def fieldsH (pre o : List Bool) (r : ℕ) (fs : List (List Bool)) (i : ℕ) : Fin 5 → ℕ :=
  ![i, 0, pre.length + i * r, (o ++ (fs.take i).flatMap frame).length, 0]

def fieldsA (MR RR S o B : List Bool) (fs : List (List Bool)) (cL : ℕ) (i : ℕ) : Fin 5 → List Bool :=
  ![MR, RR, S, overlay (o ++ (fs.take i).flatMap frame) B, List.replicate cL false]

def fieldCost (r : ℕ) : ℕ := 2 * (r * (2 + 2) + 1) + 2 + 1 + 1 + 1 + 1

theorem field_step (m r : ℕ) (mus rus pre post o B : List Bool) (fs : List (List Bool)) (cL : ℕ)
    (hfs : ∀ f ∈ fs, f.length = r) (hcL : r * (2 + 2) + 1 ≤ cL) (i : ℕ) (hi : i < fs.length) :
    Step fieldBody (fieldCost r) (fieldsH pre o r fs i)
      (fieldsA (List.replicate m true ++ false :: mus) (List.replicate r true ++ false :: rus) (pre ++ fs.flatten ++ post)
        o B fs cL i)
      (fieldsH pre o r fs (i + 1))
      (fieldsA (List.replicate m true ++ false :: mus) (List.replicate r true ++ false :: rus) (pre ++ fs.flatten ++ post)
        o B fs cL (i + 1)) := by
  set MR := List.replicate m true ++ false :: mus
  set RR := List.replicate r true ++ false :: rus
  set S := pre ++ fs.flatten ++ post
  set f := fs[i]
  set oi := o ++ (fs.take i).flatMap frame
  have hfl : f.length = r := hfs f (List.getElem_mem hi)
  have hflat : ((fs.take i).flatten).length = i * r := by
    rw [List.length_flatten]
    have : ∀ g ∈ fs.take i, g.length = r := fun g hg => hfs g (List.mem_of_mem_take hg)
    rw [List.map_congr_left (fun g hg => this g hg), List.map_const', List.sum_replicate, List.length_take,
      Nat.min_eq_left (by omega), smul_eq_mul]
  have eS : S = (pre ++ (fs.take i).flatten) ++ f ++ ((fs.drop (i + 1)).flatten ++ post) := by
    have e : fs = fs.take i ++ f :: fs.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    simp only [S]
    conv_lhs => rw [e]
    simp [List.append_assoc]
  -- 1: the field's bits
  have hb := bitsLoop_run r rus (pre ++ (fs.take i).flatten) f ((fs.drop (i + 1)).flatten ++ post) oi B hfl
  rw [← eS] at hb
  have hb0 : Step bitsLoopM (r * (2 + 2) + 1) ![0, pre.length + i * r, oi.length] ![RR, S, overlay oi B]
      ![r, pre.length + i * r + r, (oi ++ pairsOf f).length] ![RR, S, overlay (oi ++ pairsOf f) B] := by
    refine (hb.congr_in ?_ rfl).congr ?_ rfl
    · funext j; fin_cases j <;> simp [hflat]
    · funext j; fin_cases j <;> simp [hflat]
  have hm := hb0.mask (cap := cL) selRR (by intro j hj; fin_cases j <;> first | rfl | simp [selRR] at hj) hcL
  have hm' : Step (MaskedReset.machine bitsLoopM selRR) (2 * (r * (2 + 2) + 1) + 2)
      ![0, pre.length + i * r, oi.length, 0] ![RR, S, overlay oi B, List.replicate cL false]
      ![0, pre.length + i * r + r, (oi ++ pairsOf f).length, 0]
      ![RR, S, overlay (oi ++ pairsOf f) B, List.replicate cL false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s1 := dockRun hm' f5B (by decide) (fieldsH pre o r fs i) (fieldsA MR RR S o B fs cL i)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_f5B, install_f5B] at s1
  -- 2: the word's terminator
  have he := EndF.run (oi ++ pairsOf f) B
  have s2 := dockRun he f5E (by decide) ![i, 0, pre.length + i * r + r, (oi ++ pairsOf f).length, 0]
    ![MR, RR, S, overlay (oi ++ pairsOf f) B, List.replicate cL false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [dockH_f5E, install_f5E] at s2
  -- 3: one step of the field ruler
  have s3 := dockRun (nudge_run MR i) f5N (by decide) ![i, 0, pre.length + i * r + r, (oi ++ pairsOf f).length + 1, 0]
    ![MR, RR, S, overlay (oi ++ pairsOf f ++ [false]) B, List.replicate cL false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [dockH_f5N, install_f5N] at s3
  have hall := ((s1.congr (hout' := ![i, 0, pre.length + i * r + r, (oi ++ pairsOf f).length, 0])
      (tout' := ![MR, RR, S, overlay (oi ++ pairsOf f) B, List.replicate cL false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![i, 0, pre.length + i * r + r, (oi ++ pairsOf f).length + 1, 0])
      (tout' := ![MR, RR, S, overlay (oi ++ pairsOf f ++ [false]) B, List.replicate cL false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq s3
  have eo : oi ++ pairsOf f ++ [false] = o ++ (fs.take (i + 1)).flatMap frame := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_pairs, oi, f, List.append_assoc]
  unfold fieldCost
  rw [eo] at hall
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · rfl
    · rfl
    · show pre.length + i * r + r = pre.length + (i + 1) * r; ring
    · show (oi ++ pairsOf f).length + 1 = (o ++ (fs.take (i + 1)).flatMap frame).length
      rw [← eo]; simp; omega
    · rfl
  · funext j; fin_cases j <;> rfl

/-- **`m` fields of `r` bits as framed words.** -/
theorem fieldsLoop_run (r : ℕ) (mus rus pre post o B : List Bool) (fs : List (List Bool)) (cL : ℕ)
    (hfs : ∀ f ∈ fs, f.length = r) (hcL : r * (2 + 2) + 1 ≤ cL) :
    Step fieldsLoopM (fs.length * (fieldCost r + 2) + 1) ![0, 0, pre.length, o.length, 0]
      ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post,
        overlay o B, List.replicate cL false]
      ![fs.length, 0, pre.length + fs.length * r, (o ++ fs.flatMap frame).length, 0]
      ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post,
        overlay (o ++ fs.flatMap frame) B, List.replicate cL false] := by
  set MR := List.replicate fs.length true ++ false :: mus
  let L : WhileBody 5 _ :=
    { body := fieldBody
      tape := 0
      bound := fs.length
      H := fieldsH pre o r fs
      A := fieldsA MR (List.replicate r true ++ false :: rus) (pre ++ fs.flatten ++ post) o B fs cL
      cost := fun _ => fieldCost r
      step := fun i hi => field_step fs.length r mus rus pre post o B fs cL hfs hcL i hi
      cont := fun i hi => by
        show readTapeBit MR i = true
        exact read_rep_app fs.length i (false :: mus) hi
      halt := by
        show readTapeBit MR fs.length = false
        simpa using Streaming.read_append (List.replicate fs.length true) mus false }
  have h := L.run
  rw [L.rest_const (fieldCost r) (fun _ => rfl)] at h
  have e0 : fieldsH pre o r fs 0 = ![0, 0, pre.length, o.length, 0] := by funext j; fin_cases j <;> simp [fieldsH]
  have e1 : fieldsA MR (List.replicate r true ++ false :: rus) (pre ++ fs.flatten ++ post) o B fs cL 0 =
      ![MR, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post, overlay o B, List.replicate cL false] := by
    funext j; fin_cases j <;> simp [fieldsA]
  have e2 : fieldsH pre o r fs fs.length = ![fs.length, 0, pre.length + fs.length * r, (o ++ fs.flatMap frame).length, 0] := by
    funext j; fin_cases j <;> simp [fieldsH]
  have e3 : fieldsA MR (List.replicate r true ++ false :: rus) (pre ++ fs.flatten ++ post) o B fs cL fs.length =
      ![MR, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post, overlay (o ++ fs.flatMap frame) B,
        List.replicate cL false] := by
    funext j; fin_cases j <;> simp [fieldsA]
  exact (h.congr_in e0 e1).congr e2 e3

/-! ## Framed words copied from a stream (tapes 0 the count ruler, 1 the source stream, 2 the output) -/

def g3T : Fin 2 → Fin 3 := ![1, 2]

theorem install_g3T (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install g3T A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_g3T (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH g3T H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def g3N : Fin 1 → Fin 3 := ![0]

theorem install_g3N (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install g3N A v = ![v 0, A 1, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_g3N (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH g3N H v = ![v 0, H 1, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

noncomputable def frameBody := Composition.machine (RecoveryFocus.machine g3T frameT) (RecoveryFocus.machine g3N nudgeM)
noncomputable def framesLoopM := StreamController.machine frameBody 0

/-- **`m` framed words copied** from a stream of framed words. -/
theorem framesLoop_run (mus pre post o B : List Bool) (ws : List (List Bool)) :
    Step framesLoopM (((List.range (ws.length - 0)).map (fun i => 2 * (ws.getD (0 + i) []).length + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1)
      ![0, pre.length, o.length] ![List.replicate ws.length true ++ false :: mus, pre ++ ws.flatMap frame ++ post, overlay o B]
      ![ws.length, pre.length + (ws.flatMap frame).length, (o ++ ws.flatMap frame).length]
      ![List.replicate ws.length true ++ false :: mus, pre ++ ws.flatMap frame ++ post, overlay (o ++ ws.flatMap frame) B] := by
  set MR := List.replicate ws.length true ++ false :: mus
  set S := pre ++ ws.flatMap frame ++ post
  have split : ∀ i (hi : i < ws.length), S = (pre ++ (ws.take i).flatMap frame) ++ frame ws[i] ++
      ((ws.drop (i + 1)).flatMap frame ++ post) := by
    intro i hi
    have e : ws = ws.take i ++ ws[i] :: ws.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    rw [show S = pre ++ (ws.take i ++ ws[i] :: ws.drop (i + 1)).flatMap frame ++ post from by simp only [S]; rw [← e]]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  let L : WhileBody 3 _ :=
    { body := frameBody
      tape := 0
      bound := ws.length
      H := fun i => ![i, pre.length + ((ws.take i).flatMap frame).length, (o ++ (ws.take i).flatMap frame).length]
      A := fun i => ![MR, S, overlay (o ++ (ws.take i).flatMap frame) B]
      cost := fun i => 2 * (ws.getD i []).length + 1 + 1 + 1 + 1 + 1
      step := fun i hi => by
        have hc := frameT_run (pre ++ (ws.take i).flatMap frame) ws[i] ((ws.drop (i + 1)).flatMap frame ++ post)
          (o ++ (ws.take i).flatMap frame) B
        rw [← split i hi] at hc
        have s1 := dockRun hc g3T (by decide)
          ![i, pre.length + ((ws.take i).flatMap frame).length, (o ++ (ws.take i).flatMap frame).length]
          ![MR, S, overlay (o ++ (ws.take i).flatMap frame) B] (by intro j; fin_cases j <;> simp [g3T])
          (by intro j; fin_cases j <;> rfl)
        rw [dockH_g3T, install_g3T] at s1
        have s2 := dockRun (nudge_run MR i) g3N (by decide)
          ![i, (pre ++ (ws.take i).flatMap frame).length + (frame ws[i]).length,
            (o ++ (ws.take i).flatMap frame ++ frame ws[i]).length]
          ![MR, S, overlay (o ++ (ws.take i).flatMap frame ++ frame ws[i]) B] (by intro j; fin_cases j; rfl)
          (by intro j; fin_cases j; rfl)
        rw [dockH_g3N, install_g3N] at s2
        have hall := (s1.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq s2
        have et : (ws.take (i + 1)).flatMap frame = (ws.take i).flatMap frame ++ frame ws[i] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append]; simp
        rw [show ws.getD i [] = ws[i] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl]
        refine hall.congr ?_ ?_
        · funext j; fin_cases j
          · rfl
          · show (pre ++ (ws.take i).flatMap frame).length + (frame ws[i]).length =
              pre.length + ((ws.take (i + 1)).flatMap frame).length
            rw [et]; simp; omega
          · show (o ++ (ws.take i).flatMap frame ++ frame ws[i]).length = (o ++ (ws.take (i + 1)).flatMap frame).length
            rw [et]; simp
        · funext j; fin_cases j
          · rfl
          · rfl
          · show overlay (o ++ (ws.take i).flatMap frame ++ frame ws[i]) B = overlay (o ++ (ws.take (i + 1)).flatMap frame) B
            rw [et]; simp
      cont := fun i hi => by
        show readTapeBit MR i = true
        exact read_rep_app ws.length i (false :: mus) hi
      halt := by
        show readTapeBit MR ws.length = false
        simpa using Streaming.read_append (List.replicate ws.length true) mus false }
  have h := L.run
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · show ![0, pre.length + ((ws.take 0).flatMap frame).length, (o ++ (ws.take 0).flatMap frame).length] = _
    funext j; fin_cases j <;> simp
  · show ![MR, S, overlay (o ++ (ws.take 0).flatMap frame) B] = _
    funext j; fin_cases j <;> simp
  · show ![ws.length, pre.length + ((ws.take ws.length).flatMap frame).length,
      (o ++ (ws.take ws.length).flatMap frame).length] = _
    funext j; fin_cases j <;> simp
  · show ![MR, S, overlay (o ++ (ws.take ws.length).flatMap frame) B] = _
    funext j; fin_cases j <;> simp

end NearCubicWires.WireExponent3_5.SeedFix
