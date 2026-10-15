import Proof.Wire_3_5.CompilerMachineKit3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The table -/

/-- One atom's children as a stream: its entries, then the terminator. -/
def atomStream (E : List (List Bool)) : List Bool := E.flatMap frame ++ [false]

/-- The table: atom after atom, each atom's children stream, then stale cells. -/
def tableTape (Es : List (List (List Bool))) (stale : List Bool) : List Bool := Es.flatMap atomStream ++ stale

/-- The streams of the first `a` atoms. -/
def streamsBefore (Es : List (List (List Bool))) (a : ℕ) : List Bool := (Es.take a).flatMap atomStream

theorem tableTape_split (Es : List (List (List Bool))) (stale : List Bool) (a : ℕ) (ha : a < Es.length) :
    tableTape Es stale = streamsBefore Es a ++ streamTape Es[a] ((Es.drop (a + 1)).flatMap atomStream ++ stale) := by
  have e : Es = Es.take a ++ Es[a] :: Es.drop (a + 1) := by
    rw [← List.drop_eq_getElem_cons ha, List.take_append_drop]
  have h : Es.flatMap atomStream =
      (Es.take a).flatMap atomStream ++ atomStream Es[a] ++ (Es.drop (a + 1)).flatMap atomStream := by
    conv_lhs => rw [e]
    rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  unfold tableTape streamsBefore
  rw [h]
  simp only [atomStream, streamTape, List.append_assoc]
  rfl

theorem streamsBefore_succ_length (Es : List (List (List Bool))) (a : ℕ) (ha : a < Es.length) :
    (streamsBefore Es (a + 1)).length = (streamsBefore Es a).length + ((Es[a]).flatMap frame).length + 1 := by
  unfold streamsBefore
  rw [List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some, List.flatMap_append, List.length_append]
  simp [atomStream]
  omega

/-! ## The machines (tape 0 the code, 1 the table, 2 the copy of the children stream) -/

def kT : Fin 1 → Fin 3 := ![1]
def kM : Fin 1 → Fin 3 := ![0]
def kTE : Fin 2 → Fin 3 := ![1, 2]
def kE : Fin 1 → Fin 3 := ![2]

noncomputable def skipTD := RecoveryFocus.machine kT skipM
noncomputable def skipLoopTD := StreamController.machine skipTD 1
noncomputable def nudgeTD := RecoveryFocus.machine kT nudgeM
/-- Skip one children stream, terminator included. -/
noncomputable def skipStreamM := Composition.machine skipLoopTD nudgeTD
noncomputable def nudgeMD := RecoveryFocus.machine kM nudgeM
/-- One unit of the code: skip a stream, step to the next unit's bit. -/
noncomputable def lookBodyM := Composition.machine (Composition.machine skipStreamM nudgeMD) nudgeMD
noncomputable def lookLoopM := StreamController.machine lookBodyM 0
noncomputable def copyTED := RecoveryFocus.machine kTE CopyO.machine
noncomputable def copyEBodyM := Composition.machine copyTED nudgeTD
noncomputable def copyELoopM := StreamController.machine copyEBodyM 1
noncomputable def putED := RecoveryFocus.machine kE (putM false)
/-- Skip `a` streams, copy stream `a`, terminate the copy. -/
noncomputable def lookupM := Composition.machine (Composition.machine lookLoopM copyELoopM) putED
/-- The lookup with the table's and the copy's heads returned to cell 0 (log on tape 3). -/
noncomputable def lookupResetM := MaskedReset.machine lookupM ![false, true, true]

theorem kT_inj : Function.Injective kT := by decide

theorem install_kT (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install kT A v = ![A 0, v 0, A 2] := by
  funext i
  fin_cases i
  · exact install_other kT A v 0 (by decide)
  · exact install_slot kT kT_inj A v 0
  · exact install_other kT A v 2 (by decide)

theorem dockH_kT (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH kT H v = ![H 0, v 0, H 2] := by
  funext i
  fin_cases i
  · exact dockH_other kT H v 0 (by decide)
  · exact dockH_slot kT kT_inj H v 0
  · exact dockH_other kT H v 2 (by decide)

theorem kM_inj : Function.Injective kM := by decide

theorem install_kM (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install kM A v = ![v 0, A 1, A 2] := by
  funext i
  fin_cases i
  · exact install_slot kM kM_inj A v 0
  · exact install_other kM A v 1 (by decide)
  · exact install_other kM A v 2 (by decide)

theorem dockH_kM (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH kM H v = ![v 0, H 1, H 2] := by
  funext i
  fin_cases i
  · exact dockH_slot kM kM_inj H v 0
  · exact dockH_other kM H v 1 (by decide)
  · exact dockH_other kM H v 2 (by decide)

theorem kTE_inj : Function.Injective kTE := by decide

theorem install_kTE (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    install kTE A v = ![A 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact install_other kTE A v 0 (by decide)
  · exact install_slot kTE kTE_inj A v 0
  · exact install_slot kTE kTE_inj A v 1

theorem dockH_kTE (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH kTE H v = ![H 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other kTE H v 0 (by decide)
  · exact dockH_slot kTE kTE_inj H v 0
  · exact dockH_slot kTE kTE_inj H v 1

theorem kE_inj : Function.Injective kE := by decide

theorem install_kE (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install kE A v = ![A 0, A 1, v 0] := by
  funext i
  fin_cases i
  · exact install_other kE A v 0 (by decide)
  · exact install_other kE A v 1 (by decide)
  · exact install_slot kE kE_inj A v 0

theorem dockH_kE (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH kE H v = ![H 0, H 1, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other kE H v 0 (by decide)
  · exact dockH_other kE H v 1 (by decide)
  · exact dockH_slot kE kE_inj H v 0

/-! ## Skipping one stream -/

theorem skipT_step (Mt Et pre w post : List Bool) (m e : ℕ) :
    Step skipTD (2 * w.length + 1) ![m, pre.length, e] ![Mt, pre ++ frame w ++ post, Et]
      ![m, pre.length + 2 * w.length + 1, e] ![Mt, pre ++ frame w ++ post, Et] := by
  have e1 := dockRun (skipStep pre w post) kT kT_inj ![m, pre.length, e] ![Mt, pre ++ frame w ++ post, Et]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_kT, dockH_kT] at e1
  exact e1

theorem nudgeT_step (Mt Tt Et : List Bool) (m t e : ℕ) :
    Step nudgeTD 1 ![m, t, e] ![Mt, Tt, Et] ![m, t + 1, e] ![Mt, Tt, Et] := by
  have e1 := dockRun (nudge_run Tt t) kT kT_inj ![m, t, e] ![Mt, Tt, Et] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_kT, dockH_kT] at e1
  exact e1

theorem nudgeM_step (Mt Tt Et : List Bool) (m t e : ℕ) :
    Step nudgeMD 1 ![m, t, e] ![Mt, Tt, Et] ![m + 1, t, e] ![Mt, Tt, Et] := by
  have e1 := dockRun (nudge_run Mt m) kM kM_inj ![m, t, e] ![Mt, Tt, Et] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_kM, dockH_kM] at e1
  exact e1

/-- **Skip one children stream** (all entries of width `L`). -/
theorem skipStream_run (PS : List Bool) (E : List (List Bool)) (rest Mt Et : List Bool) (m e L : ℕ)
    (hE : ∀ r ∈ E, r.length = L) (hL : 1 ≤ L) :
    Step skipStreamM (E.length * (2 * L + 1 + 2) + 1 + 1 + 1) ![m, PS.length, e] ![Mt, PS ++ streamTape E rest, Et]
      ![m, PS.length + (E.flatMap frame).length + 1, e] ![Mt, PS ++ streamTape E rest, Et] := by
  have h := streamRunAt skipTD 1 PS E rest (fun r hr h => by have := hE r hr; rw [h] at this; simp at this; omega)
    (fun (u : Unit) _ => u) () (fun _ p => ![m, p, e]) (fun _ => ![Mt, PS ++ streamTape E rest, Et])
    (fun _ => rfl) (fun _ _ => rfl) (2 * L + 1) (by
      intro j hj
      have hs := skipT_step Mt Et (PS ++ (E.take j).flatMap frame) E[j]
        ((E.drop (j + 1)).flatMap frame ++ false :: rest) m e
      have hsplit : PS ++ (E.take j).flatMap frame ++ frame E[j] ++ ((E.drop (j + 1)).flatMap frame ++ false :: rest) =
          PS ++ streamTape E rest := by
        rw [streamTape_split E rest j hj]; simp [List.append_assoc]
      rw [hsplit, hE _ (List.getElem_mem hj)] at hs
      rw [off_succ E j hj, hE _ (List.getElem_mem hj)]
      refine (hs.congr_in ?_ rfl).congr ?_ rfl
      · funext i; fin_cases i <;> simp [off]
      · funext i; fin_cases i <;> simp [off]
        all_goals omega)
  exact h.seq (nudgeT_step Mt (PS ++ streamTape E rest) Et m (PS.length + (E.flatMap frame).length) e)

/-! ## The lookup loop over the code's units -/

/-- The uniform cost of one unit of the lookup, for streams of at most `K` entries of width `L`. -/
def lookUnitCost (K L : ℕ) : ℕ := K * (2 * L + 1 + 2) + 1 + 1 + 1 + 1 + 1 + 1 + 1

theorem look_loop (P post : List Bool) (a : ℕ) (Es : List (List (List Bool))) (staleT Et : List Bool) (K L : ℕ)
    (ha : a ≤ Es.length) (hEs : ∀ E ∈ Es, (∀ r ∈ E, r.length = L) ∧ E.length ≤ K) (hL : 1 ≤ L) :
    Step lookLoopM (a * (lookUnitCost K L + 2) + 1) ![P.length + 2 * 0 + 1, (streamsBefore Es 0).length, 0]
      ![P ++ pairsTape a ++ post, tableTape Es staleT, Et]
      ![P.length + 2 * a + 1, (streamsBefore Es a).length, 0] ![P ++ pairsTape a ++ post, tableTape Es staleT, Et] := by
  refine unaryRun lookBodyM 0 P post a (fun j => ![P.length + 2 * j + 1, (streamsBefore Es j).length, 0])
    (fun _ => ![P ++ pairsTape a ++ post, tableTape Es staleT, Et]) (fun _ => rfl) (fun _ => rfl) (lookUnitCost K L) ?_
  intro j hj
  have hjE : j < Es.length := by omega
  obtain ⟨hw, hk⟩ := hEs _ (List.getElem_mem hjE)
  have s1 := skipStream_run (streamsBefore Es j) Es[j] ((Es.drop (j + 1)).flatMap atomStream ++ staleT)
    (P ++ pairsTape a ++ post) Et (P.length + 2 * j + 1) 0 L hw hL
  rw [← tableTape_split Es staleT j hjE] at s1
  have s2 := nudgeM_step (P ++ pairsTape a ++ post) (tableTape Es staleT) Et (P.length + 2 * j + 1)
    ((streamsBefore Es j).length + (Es[j].flatMap frame).length + 1) 0
  have s3 := nudgeM_step (P ++ pairsTape a ++ post) (tableTape Es staleT) Et (P.length + 2 * j + 1 + 1)
    ((streamsBefore Es j).length + (Es[j].flatMap frame).length + 1) 0
  have hall := (s1.seq s2).seq s3
  have hc : Es[j].length * (2 * L + 1 + 2) ≤ K * (2 * L + 1 + 2) := Nat.mul_le_mul_right _ hk
  refine (hall.enlarge (by unfold lookUnitCost; omega)).congr ?_ rfl
  funext i; fin_cases i
  · show P.length + 2 * j + 1 + 1 + 1 = P.length + 2 * (j + 1) + 1
    omega
  · show (streamsBefore Es j).length + (Es[j].flatMap frame).length + 1 = (streamsBefore Es (j + 1)).length
    rw [streamsBefore_succ_length Es j hjE]
  · rfl

/-! ## Copying the children stream -/

theorem copyTE_step (Mt pre w post out BW : List Bool) (m : ℕ) :
    Step copyTED (2 * w.length + 1) ![m, pre.length, out.length] ![Mt, pre ++ frame w ++ post, overlay out BW]
      ![m, pre.length + 2 * w.length, out.length + (2 * w.length + 1)]
      ![Mt, pre ++ frame w ++ post, overlay (out ++ frame w) BW] := by
  have e1 := dockRun (copyStep pre w post out BW) kTE kTE_inj ![m, pre.length, out.length]
    ![Mt, pre ++ frame w ++ post, overlay out BW] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_kTE, dockH_kTE] at e1
  exact e1

theorem copyE_loop (PS : List Bool) (E : List (List Bool)) (rest Mt EaOld : List Bool) (m L : ℕ)
    (hE : ∀ r ∈ E, r.length = L) (hL : 1 ≤ L) :
    Step copyELoopM (E.length * (2 * L + 1 + 1 + 1 + 2) + 1) ![m, PS.length, 0]
      ![Mt, PS ++ streamTape E rest, EaOld]
      ![m, PS.length + (E.flatMap frame).length, (E.flatMap frame).length]
      ![Mt, PS ++ streamTape E rest, overlay (E.flatMap frame) EaOld] := by
  have h := streamRunAt copyEBodyM 1 PS E rest (fun r hr h => by have := hE r hr; rw [h] at this; simp at this; omega)
    (fun acc r => acc ++ [r]) ([] : List (List Bool)) (fun st p => ![m, p, (st.flatMap frame).length])
    (fun st => ![Mt, PS ++ streamTape E rest, overlay (st.flatMap frame) EaOld]) (fun _ => rfl) (fun _ _ => rfl)
    (2 * L + 1 + 1 + 1) (by
      intro j hj
      have hlen := hE _ (List.getElem_mem hj)
      have hst : (E.take (j + 1)).foldl (fun acc r => acc ++ [r]) [] = (E.take j).foldl (fun acc r => acc ++ [r]) [] ++ [E[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
        rfl
      rw [hst, off_succ E j hj]
      set wr := (E.take j).foldl (fun acc r => acc ++ [r]) []
      have s1 := copyTE_step Mt (PS ++ (E.take j).flatMap frame) E[j] ((E.drop (j + 1)).flatMap frame ++ false :: rest)
        (wr.flatMap frame) EaOld m
      have hsplit : PS ++ (E.take j).flatMap frame ++ frame E[j] ++ ((E.drop (j + 1)).flatMap frame ++ false :: rest) =
          PS ++ streamTape E rest := by
        rw [streamTape_split E rest j hj]; simp [List.append_assoc]
      rw [hsplit] at s1
      have s2 := nudgeT_step Mt (PS ++ streamTape E rest) (overlay (wr.flatMap frame ++ frame E[j]) EaOld) m
        ((PS ++ (E.take j).flatMap frame).length + 2 * E[j].length) ((wr.flatMap frame).length + (2 * E[j].length + 1))
      refine (((s1.seq s2).enlarge (m := 2 * L + 1 + 1 + 1) (by rw [hlen])).congr_in ?_ rfl).congr ?_ ?_
      · funext i; fin_cases i <;> simp [off]
      · funext i; fin_cases i <;> simp [off, frame_length]
        all_goals omega
      · funext i; fin_cases i <;> simp)
  have e0 : (E.foldl (fun acc r => acc ++ [r]) []) = E := by simpa using foldl_snoc E []
  rw [e0] at h
  refine h.congr_in ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [overlay]

/-! ## The lookup -/

/-- The cost of the lookup of an atom below `P` before the reset, streams of at most `K` entries of width `L`. -/
def lookupCost (P K L : ℕ) : ℕ :=
  P * (lookUnitCost K L + 2) + 1 + 1 + (K * (2 * L + 1 + 1 + 1 + 2) + 1) + 1 + 1

theorem lookup_run (P post : List Bool) (a : ℕ) (Es : List (List (List Bool))) (staleT EaOld : List Bool) (K L cap : ℕ)
    (ha : a < Es.length) (hEs : ∀ E ∈ Es, (∀ r ∈ E, r.length = L) ∧ E.length ≤ K) (hL : 1 ≤ L)
    (hcap : lookupCost Es.length K L ≤ cap) :
    Step lookupResetM (2 * lookupCost Es.length K L + 2) ![P.length + 1, 0, 0, 0]
      ![P ++ pairsTape a ++ post, tableTape Es staleT, EaOld, List.replicate cap false]
      ![P.length + 2 * a + 1, 0, 0, 0]
      ![P ++ pairsTape a ++ post, tableTape Es staleT,
        streamTape Es[a] (EaOld.drop ((Es[a].flatMap frame).length + 1)), List.replicate cap false] := by
  obtain ⟨hw, hk⟩ := hEs _ (List.getElem_mem ha)
  have s1 := look_loop P post a Es staleT EaOld K L ha.le hEs hL
  have s2 := copyE_loop (streamsBefore Es a) Es[a] ((Es.drop (a + 1)).flatMap atomStream ++ staleT)
    (P ++ pairsTape a ++ post) EaOld (P.length + 2 * a + 1) L hw hL
  rw [← tableTape_split Es staleT a ha] at s2
  have s3 := dockRun (putStep false (overlay (Es[a].flatMap frame) EaOld) (Es[a].flatMap frame).length) kE kE_inj
    ![P.length + 2 * a + 1, (streamsBefore Es a).length + (Es[a].flatMap frame).length, (Es[a].flatMap frame).length]
    ![P ++ pairsTape a ++ post, tableTape Es staleT, overlay (Es[a].flatMap frame) EaOld]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_kE, dockH_kE, overlay_write, overlay_stream] at s3
  have hall := (s1.seq s2).seq s3
  have hc : a * (lookUnitCost K L + 2) + 1 + 1 + (Es[a].length * (2 * L + 1 + 1 + 1 + 2) + 1) + 1 + 1 ≤
      lookupCost Es.length K L := by
    unfold lookupCost
    have h1 := Nat.mul_le_mul_right (lookUnitCost K L + 2) ha.le
    have h2 := Nat.mul_le_mul_right (2 * L + 1 + 1 + 1 + 2) hk
    omega
  have hm := (hall.enlarge hc).mask (cap := cap) ![false, true, true]
    (by intro i hi; fin_cases i <;> simp_all [streamsBefore]) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Masks
