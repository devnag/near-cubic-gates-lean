import Proof.Wire_3_5.CompilerMachineKit2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- A 1-bit transducer of two registers written into a third register (all three heads back at cell 0). -/
noncomputable def zipM (out nxt : Bool → Bool → Bool → Bool) (init : Bool) :=
  MaskedReset.machine (ZipMap.machine out nxt init) ![true, true, true]

theorem zipStep (out nxt : Bool → Bool → Bool → Bool) (init : Bool) (u v Z : List Bool) (hl : u.length = v.length)
    (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (zipM out nxt init) (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0] ![frame u, frame v, Z, List.replicate cap false]
      ![0, 0, 0, 0] ![frame u, frame v, overlay (frame (ZipMap.map out nxt u v init)) Z, List.replicate cap false] := by
  have h0 := mapStepO out nxt init [] [] u v [] [] [] Z hl
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h0
  have hZ : overlay [] Z = Z := by simp [overlay]
  rw [hZ] at h0
  have hm := h0.mask ![true, true, true] (by intro i _; fin_cases i <;> rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## Appending a stream after a stream (tape 0 the list `S`, tape 1 the new records `O`) -/

def sS0 : Fin 1 → Fin 2 := ![0]
def sO1 : Fin 1 → Fin 2 := ![1]
def sOS : Fin 2 → Fin 2 := ![1, 0]

noncomputable def skipSD := RecoveryFocus.machine sS0 skipM
noncomputable def skipLoopD := StreamController.machine skipSD 0
noncomputable def appCopyD := RecoveryFocus.machine sOS CopyO.machine
noncomputable def appNudgeD := RecoveryFocus.machine sO1 nudgeM
noncomputable def appBodyD := Composition.machine appCopyD appNudgeD
noncomputable def appLoopD := StreamController.machine appBodyD 1
noncomputable def appPutD := RecoveryFocus.machine sS0 (putM false)

/-- Skip the old records of `S`, copy the records of `O` after them, write the terminator. -/
noncomputable def appendM := Composition.machine (Composition.machine skipLoopD appLoopD) appPutD

/-- The append with both heads returned to cell 0 (log on tape 2). -/
noncomputable def appendResetM := MaskedReset.machine appendM ![true, true]

theorem skip_loop (E : List (List Bool)) (staleS O : List Bool) (W : ℕ) (hE : ∀ r ∈ E, r.length = W) (hW : 1 ≤ W) :
    Step skipLoopD (E.length * (2 * W + 1 + 2) + 1) ![0, 0] ![streamTape E staleS, O]
      ![(E.flatMap frame).length, 0] ![streamTape E staleS, O] := by
  have h := streamRun skipSD 0 E staleS (fun r hr h => by have := hE r hr; rw [h] at this; simp at this; omega)
    (fun (u : Unit) _ => u) () (fun _ p => ![p, 0]) (fun _ => ![streamTape E staleS, O])
    (fun _ => rfl) (fun _ _ => rfl) (2 * W + 1) (by
      intro j hj
      have hs := skipStep ((E.take j).flatMap frame) E[j] ((E.drop (j + 1)).flatMap frame ++ false :: staleS)
      rw [← streamTape_split E staleS j hj, hE _ (List.getElem_mem hj)] at hs
      have hd := dockRun hs sS0 (by decide) ![((E.take j).flatMap frame).length, 0] ![streamTape E staleS, O]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [off_succ E j hj, hE _ (List.getElem_mem hj)]
      refine hd.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval)
  exact h

theorem app_body (pre w post Sv : List Bool) (written : List (List Bool)) :
    Step appBodyD (2 * w.length + 1 + 1 + 1) ![(written.flatMap frame).length, pre.length]
      ![overlay (written.flatMap frame) Sv, pre ++ frame w ++ post]
      ![((written ++ [w]).flatMap frame).length, pre.length + (2 * w.length + 1)]
      ![overlay ((written ++ [w]).flatMap frame) Sv, pre ++ frame w ++ post] := by
  have h1 := dockRun (copyStep pre w post (written.flatMap frame) Sv) sOS (by decide)
    ![(written.flatMap frame).length, pre.length] ![overlay (written.flatMap frame) Sv, pre ++ frame w ++ post]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  have h2 := dockRun (nudge_run (pre ++ frame w ++ post) (pre.length + 2 * w.length)) sO1 (by decide)
    ![(written.flatMap frame).length + (2 * w.length + 1), pre.length + 2 * w.length]
    ![overlay (written.flatMap frame ++ frame w) Sv, pre ++ frame w ++ post]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  have h1' := h1.congr (hout' := ![(written.flatMap frame).length + (2 * w.length + 1), pre.length + 2 * w.length])
    (tout' := ![overlay (written.flatMap frame ++ frame w) Sv, pre ++ frame w ++ post])
    (by funext i; fin_cases i <;> slot_eval) (by funext i; fin_cases i <;> slot_eval)
  have h2' := h2.congr (hout' := ![(written.flatMap frame).length + (2 * w.length + 1), pre.length + 2 * w.length + 1])
    (tout' := ![overlay (written.flatMap frame ++ frame w) Sv, pre ++ frame w ++ post])
    (by funext i; fin_cases i <;> slot_eval) (by funext i; fin_cases i <;> slot_eval)
  refine (h1'.seq h2').congr ?_ ?_
  · funext i; fin_cases i
    · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        frame_length]
      rfl
    · show pre.length + 2 * w.length + 1 = pre.length + (2 * w.length + 1)
      omega
  · funext i; fin_cases i
    · show overlay (written.flatMap frame ++ frame w) Sv = overlay ((written ++ [w]).flatMap frame) Sv
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rfl

theorem foldl_snoc (l : List (List Bool)) : ∀ acc : List (List Bool), l.foldl (fun a r => a ++ [r]) acc = acc ++ l := by
  induction l with
  | nil => simp
  | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp

theorem app_loop (N E : List (List Bool)) (staleO Sv : List Bool) (W : ℕ) (hN : ∀ r ∈ N, r.length = W) (hW : 1 ≤ W) :
    Step appLoopD (N.length * (2 * W + 1 + 1 + 1 + 2) + 1) ![(E.flatMap frame).length, 0]
      ![overlay (E.flatMap frame) Sv, streamTape N staleO]
      ![((E ++ N).flatMap frame).length, (N.flatMap frame).length]
      ![overlay ((E ++ N).flatMap frame) Sv, streamTape N staleO] := by
  have h := streamRun appBodyD 1 N staleO (fun r hr h => by have := hN r hr; rw [h] at this; simp at this; omega)
    (fun a r => a ++ [r]) E (fun st p => ![(st.flatMap frame).length, p])
    (fun st => ![overlay (st.flatMap frame) Sv, streamTape N staleO]) (fun _ => rfl) (fun _ _ => rfl)
    (2 * W + 1 + 1 + 1) (by
      intro j hj
      have hlen := hN _ (List.getElem_mem hj)
      have hst : (N.take (j + 1)).foldl (fun a r => a ++ [r]) E = (N.take j).foldl (fun a r => a ++ [r]) E ++ [N[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
        rfl
      have hb := app_body ((N.take j).flatMap frame) N[j] ((N.drop (j + 1)).flatMap frame ++ false :: staleO) Sv
        ((N.take j).foldl (fun a r => a ++ [r]) E)
      rw [← streamTape_split N staleO j hj, hlen] at hb
      rw [hst, off_succ N j hj, hlen]
      exact hb)
  rw [foldl_snoc] at h
  exact h

/-- The cost of appending `n` records after `m` records, all of width `W`, before the reset. -/
def appendCost (m n W : ℕ) : ℕ := m * (2 * W + 1 + 2) + 1 + 1 + (n * (2 * W + 1 + 1 + 1 + 2) + 1) + 1 + 1

/-- **Append the records of `O` after those of `S`**, both heads back at cell 0. -/
theorem appendRun (E N : List (List Bool)) (staleS staleO : List Bool) (W cap : ℕ) (hE : ∀ r ∈ E, r.length = W)
    (hN : ∀ r ∈ N, r.length = W) (hW : 1 ≤ W) (hcap : appendCost E.length N.length W ≤ cap) :
    Step appendResetM (2 * appendCost E.length N.length W + 2) (fun _ => 0)
      ![streamTape E staleS, streamTape N staleO, List.replicate cap false] (fun _ => 0)
      ![streamTape (E ++ N) ((streamTape E staleS).drop (((E ++ N).flatMap frame).length + 1)),
        streamTape N staleO, List.replicate cap false] := by
  have hS : streamTape E staleS = overlay (E.flatMap frame) (streamTape E staleS) := by
    simp [overlay, streamTape]
  have s1 := skip_loop E staleS (streamTape N staleO) W hE hW
  have s2 := app_loop N E staleO (streamTape E staleS) W hN hW
  rw [← hS] at s2
  have s3 := dockRun (putStep false (overlay ((E ++ N).flatMap frame) (streamTape E staleS))
    ((E ++ N).flatMap frame).length) sS0 (by decide)
    ![((E ++ N).flatMap frame).length, (N.flatMap frame).length]
    ![overlay ((E ++ N).flatMap frame) (streamTape E staleS), streamTape N staleO]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [overlay_write] at s3
  have s3' := s3.congr (hout' := ![((E ++ N).flatMap frame).length + 1, (N.flatMap frame).length])
    (tout' := ![overlay ((E ++ N).flatMap frame ++ [false]) (streamTape E staleS), streamTape N staleO])
    (by funext i; fin_cases i <;> slot_eval) (by funext i; fin_cases i <;> slot_eval)
  have hall := (s1.seq s2).seq s3'
  have hm := hall.mask (cap := cap) ![true, true] (by intro i _; fin_cases i <;> rfl) (by unfold appendCost at hcap; omega)
  rw [overlay_stream] at hm
  refine ((hm.enlarge (by unfold appendCost; omega)).congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Kit
