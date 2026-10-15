import Proof.Wire_3_5.CompilerMachinePolyTerm

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The counter's pass over the factors (on the factor layout, then its log) -/

def jJ : Fin 1 → Fin 20 := ![18]
noncomputable def jNudgeD := RecoveryFocus.machine jJ nudgeM
/-- Step the counter's head onto bit `0`, then the factor loop. -/
noncomputable def jBlockM := Composition.machine jNudgeD (StreamController.machine factorM 0)
def jSel : Fin 20 → Bool := fun i => decide (i = 18)
/-- The factor pass with the counter's head returned to cell 0 (log on tape 20). -/
noncomputable def jBlockRM := MaskedReset.machine jBlockM jSel

theorem jJ_inj : Function.Injective jJ := by decide

theorem install_jJ (A : Fin 20 → List Bool) (v : Fin 1 → List Bool) :
    install jJ A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0, A 19] := by
  funext i
  fin_cases i
  · exact install_other jJ A v 0 (by decide)
  · exact install_other jJ A v 1 (by decide)
  · exact install_other jJ A v 2 (by decide)
  · exact install_other jJ A v 3 (by decide)
  · exact install_other jJ A v 4 (by decide)
  · exact install_other jJ A v 5 (by decide)
  · exact install_other jJ A v 6 (by decide)
  · exact install_other jJ A v 7 (by decide)
  · exact install_other jJ A v 8 (by decide)
  · exact install_other jJ A v 9 (by decide)
  · exact install_other jJ A v 10 (by decide)
  · exact install_other jJ A v 11 (by decide)
  · exact install_other jJ A v 12 (by decide)
  · exact install_other jJ A v 13 (by decide)
  · exact install_other jJ A v 14 (by decide)
  · exact install_other jJ A v 15 (by decide)
  · exact install_other jJ A v 16 (by decide)
  · exact install_other jJ A v 17 (by decide)
  · exact install_slot jJ jJ_inj A v 0
  · exact install_other jJ A v 19 (by decide)

theorem dockH_jJ (H : Fin 20 → ℕ) (v : Fin 1 → ℕ) :
    dockH jJ H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0, H 19] := by
  funext i
  fin_cases i
  · exact dockH_other jJ H v 0 (by decide)
  · exact dockH_other jJ H v 1 (by decide)
  · exact dockH_other jJ H v 2 (by decide)
  · exact dockH_other jJ H v 3 (by decide)
  · exact dockH_other jJ H v 4 (by decide)
  · exact dockH_other jJ H v 5 (by decide)
  · exact dockH_other jJ H v 6 (by decide)
  · exact dockH_other jJ H v 7 (by decide)
  · exact dockH_other jJ H v 8 (by decide)
  · exact dockH_other jJ H v 9 (by decide)
  · exact dockH_other jJ H v 10 (by decide)
  · exact dockH_other jJ H v 11 (by decide)
  · exact dockH_other jJ H v 12 (by decide)
  · exact dockH_other jJ H v 13 (by decide)
  · exact dockH_other jJ H v 14 (by decide)
  · exact dockH_other jJ H v 15 (by decide)
  · exact dockH_other jJ H v 16 (by decide)
  · exact dockH_other jJ H v 17 (by decide)
  · exact dockH_slot jJ jJ_inj H v 0
  · exact dockH_other jJ H v 19 (by decide)

theorem jblock_run (Q : ℕ) (pool : List (List SynEq)) (fs : List (F2Poly ℕ)) (j m : ℕ) (P post staleT : List Bool)
    (ps : PS) (PJ : Bool) (cap cap2 cap3 cap4 d B NF CB : ℕ) (hm : fs.length = m)
    (hp : ∀ f ∈ fs, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (hd : ∀ f ∈ fs, ∀ mono ∈ f, mono.length ≤ d)
    (hNF : ∀ f ∈ fs, f.length ≤ NF) (hCB : ∀ f ∈ fs, ∀ mono ∈ f, (codeBits mono).length ≤ CB)
    (hinv : PInv (Q + pool.flatten.length + 1) ps)
    (hB : ps.G.length + (fs.flatten.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3)
    (hcap4 : 1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1) ≤ cap4) :
    Step jBlockRM (2 * (1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1)) + 2)
      (Fin.addCases (head2 P.length 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (bank2 (P ++ fs.flatMap factorRec ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2
        cap3 (z0 Q pool.flatten.length) (frame (binary m j)) ps PJ) (fun _ : Fin 1 => List.replicate cap4 false))
      (Fin.addCases (head2 (P.length + (fs.flatMap factorRec).length) 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (bank2 (P ++ fs.flatMap factorRec ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2
        cap3 (z0 Q pool.flatten.length) (frame (binary m j)) (fs.foldl (f2i Q pool j) (ps, PJ, 0)).1
        (fs.foldl (f2i Q pool j) (ps, PJ, 0)).2.1) (fun _ : Fin 1 => List.replicate cap4 false)) := by
  set VT := P ++ fs.flatMap factorRec ++ false :: post
  set TT := tableTape (childTable Q pool) staleT
  have s1 := dockRun (nudge_run (frame (binary m j)) 0) jJ jJ_inj (head2 P.length 0)
    (bank2 VT TT cap cap2 cap3 (z0 Q pool.flatten.length) (frame (binary m j)) ps PJ)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_jJ, dockH_jJ] at s1
  have s1' := s1.congr (hout' := head2 P.length 1)
    (tout' := bank2 VT TT cap cap2 cap3 (z0 Q pool.flatten.length) (frame (binary m j)) ps PJ)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have s2 := factors_run Q pool fs j m P post staleT ps PJ cap cap2 cap3 d B NF CB hm hp hd hNF hCB hinv hB hc
  have hall := s1'.seq s2
  rw [hm] at hall
  have hmk := hall.mask (cap := cap4) jSel (by intro i hi; fin_cases i <;> simp_all [jSel, head2]) hcap4
  refine (hmk.congr ?_ rfl)
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · fin_cases k <;> rfl
  · fin_cases k; rfl

/-! ## Appending the unions stream to the output (tape 0 the stream, tape 1 the output, then its log) -/

def oCopy : Fin 2 → Fin 2 := ![0, 1]
def oNudge : Fin 1 → Fin 2 := ![0]
noncomputable def oCopyD := RecoveryFocus.machine oCopy CopyO.machine
noncomputable def oNudgeD := RecoveryFocus.machine oNudge nudgeM
noncomputable def appOutBodyM := Composition.machine oCopyD oNudgeD
noncomputable def appOutM := StreamController.machine appOutBodyM 0
/-- The append with the stream's head returned to cell 0 (log on tape 2). -/
noncomputable def appOutRM := MaskedReset.machine appOutM ![true, false]

theorem oCopy_inj : Function.Injective oCopy := by decide

theorem install_oCopy (A : Fin 2 → List Bool) (v : Fin 2 → List Bool) :
    install oCopy A v = ![v 0, v 1] := by
  funext i
  fin_cases i
  · exact install_slot oCopy oCopy_inj A v 0
  · exact install_slot oCopy oCopy_inj A v 1

theorem dockH_oCopy (H : Fin 2 → ℕ) (v : Fin 2 → ℕ) :
    dockH oCopy H v = ![v 0, v 1] := by
  funext i
  fin_cases i
  · exact dockH_slot oCopy oCopy_inj H v 0
  · exact dockH_slot oCopy oCopy_inj H v 1

theorem oNudge_inj : Function.Injective oNudge := by decide

theorem install_oNudge (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install oNudge A v = ![v 0, A 1] := by
  funext i
  fin_cases i
  · exact install_slot oNudge oNudge_inj A v 0
  · exact install_other oNudge A v 1 (by decide)

theorem dockH_oNudge (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH oNudge H v = ![v 0, H 1] := by
  funext i
  fin_cases i
  · exact dockH_slot oNudge oNudge_inj H v 0
  · exact dockH_other oNudge H v 1 (by decide)

theorem appOut_body (pre w post out BW : List Bool) :
    Step appOutBodyM (2 * w.length + 1 + 1 + 1) ![pre.length, out.length] ![pre ++ frame w ++ post, overlay out BW]
      ![pre.length + (2 * w.length + 1), (out ++ frame w).length] ![pre ++ frame w ++ post, overlay (out ++ frame w) BW] := by
  have h1 := dockRun (copyStep pre w post out BW) oCopy oCopy_inj ![pre.length, out.length]
    ![pre ++ frame w ++ post, overlay out BW] (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_oCopy, dockH_oCopy] at h1
  have h2 := dockRun (nudge_run (pre ++ frame w ++ post) (pre.length + 2 * w.length)) oNudge oNudge_inj
    ![pre.length + 2 * w.length, out.length + (2 * w.length + 1)] ![pre ++ frame w ++ post, overlay (out ++ frame w) BW]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_oNudge, dockH_oNudge] at h2
  refine ((h1.congr (hout' := ![pre.length + 2 * w.length, out.length + (2 * w.length + 1)])
    (tout' := ![pre ++ frame w ++ post, overlay (out ++ frame w) BW]) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)).seq h2).congr ?_ ?_
  · funext i; fin_cases i <;> simp [frame_length]
    all_goals omega
  · funext i; fin_cases i <;> rfl

theorem appOut_loop (E : List (List Bool)) (staleE out BW : List Bool) (W : ℕ) (hE : ∀ r ∈ E, r.length = W)
    (hW : 1 ≤ W) :
    Step appOutM (E.length * (2 * W + 1 + 1 + 1 + 2) + 1) ![0, out.length] ![streamTape E staleE, overlay out BW]
      ![(E.flatMap frame).length, (out ++ E.flatMap frame).length]
      ![streamTape E staleE, overlay (out ++ E.flatMap frame) BW] := by
  have h := streamRun appOutBodyM 0 E staleE (fun r hr h => by have := hE r hr; rw [h] at this; simp at this; omega)
    (fun acc r => acc ++ [r]) ([] : List (List Bool)) (fun st p => ![p, (out ++ st.flatMap frame).length])
    (fun st => ![streamTape E staleE, overlay (out ++ st.flatMap frame) BW]) (fun _ => rfl) (fun _ _ => rfl)
    (2 * W + 1 + 1 + 1) (by
      intro k hk
      have hlen := hE _ (List.getElem_mem hk)
      have hst : (E.take (k + 1)).foldl (fun acc r => acc ++ [r]) [] = (E.take k).foldl (fun acc r => acc ++ [r]) [] ++ [E[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
        rfl
      have hb := appOut_body ((E.take k).flatMap frame) E[k] ((E.drop (k + 1)).flatMap frame ++ false :: staleE)
        (out ++ ((E.take k).foldl (fun acc r => acc ++ [r]) []).flatMap frame) BW
      rw [← streamTape_split E staleE k hk, hlen] at hb
      rw [hst, off_succ E k hk, hlen]
      refine (hb.congr ?_ ?_)
      · funext i; fin_cases i <;> simp [off]
      · funext i; fin_cases i <;> simp)
  have e0 : (E.foldl (fun acc r => acc ++ [r]) []) = E := by simpa using foldl_snoc E []
  rw [e0] at h
  refine h.congr_in ?_ ?_
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

/-- **Append a unions stream to the output**, the stream's head back at cell 0. -/
theorem appOut_run (E : List (List Bool)) (staleE out BW : List Bool) (W cap : ℕ) (hE : ∀ r ∈ E, r.length = W)
    (hW : 1 ≤ W) (hcap : E.length * (2 * W + 1 + 1 + 1 + 2) + 1 ≤ cap) :
    Step appOutRM (2 * (E.length * (2 * W + 1 + 1 + 1 + 2) + 1) + 2) ![0, out.length, 0]
      ![streamTape E staleE, overlay out BW, List.replicate cap false]
      ![0, (out ++ E.flatMap frame).length, 0]
      ![streamTape E staleE, overlay (out ++ E.flatMap frame) BW, List.replicate cap false] := by
  have h := appOut_loop E staleE out BW W hE hW
  have hm := h.mask (cap := cap) ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    (try fin_cases k) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
