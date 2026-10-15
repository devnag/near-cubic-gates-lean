import Proof.Wire_3_5.CompilerMachinePoolTable

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The loop over the gates of one flip pattern, driven by the count words (tape 0). -/
noncomputable def gatesM := StreamController.machine atomM 0

theorem natWord_head (v : ℕ) : ∃ l, natWord v = true :: l := by
  obtain ⟨k, hk⟩ : ∃ k, natBitLength v = k + 1 := ⟨natBitLength v - 1, by unfold natBitLength; omega⟩
  rw [natWord_eq, hk, List.replicate_succ, List.cons_append]
  exact ⟨_, rfl⟩

theorem tableOf_append {β : Type} (ent : ℕ → β) : ∀ (c0 : ℕ) (xs ys : List ℕ),
    tableOf ent c0 (xs ++ ys) = tableOf ent c0 xs ++ tableOf ent (c0 + xs.sum) ys
  | c0, [], ys => by simp [tableOf]
  | c0, x :: xs, ys => by
    simp only [List.cons_append, tableOf, List.sum_cons]
    rw [tableOf_append ent (c0 + x) xs ys, Nat.add_assoc]

/-- The gate loop's state: the label offset, the last count, the table written so far. -/
structure GSt where
  c : ℕ
  last : ℕ
  tbl : List Bool

def gnext (Q W : ℕ) (st : GSt) (v : ℕ) : GSt :=
  ⟨st.c + v, v, st.tbl ++ atomStream ((List.range' st.c v).map (entC Q W))⟩

theorem gfold_c (Q W : ℕ) : ∀ (cs : List ℕ) (st : GSt), (cs.foldl (gnext Q W) st).c = st.c + cs.sum
  | [], st => by simp
  | v :: cs, st => by
    rw [List.foldl_cons, gfold_c Q W cs, List.sum_cons]
    simp [gnext, Nat.add_assoc]

theorem gfold_tbl (Q W : ℕ) : ∀ (cs : List ℕ) (st : GSt),
    (cs.foldl (gnext Q W) st).tbl = st.tbl ++ (tableOf (entC Q W) st.c cs).flatMap atomStream
  | [], st => by simp [tableOf]
  | v :: cs, st => by
    rw [List.foldl_cons, gfold_tbl Q W cs]
    simp [gnext, tableOf, List.append_assoc]

/-- The gate loop's bank. -/
def gBank (CN K ZW MK : List Bool) (Q W Wc : ℕ) (BW : List Bool) (cap : ℕ) (st : GSt) : Fin 12 → List Bool :=
  tA CN K (frame (binary Wc st.last)) ZW (frame (binary Wc st.last)) [false] [true] (frame (entC Q W st.c)) MK
    (frame (entC Q W st.c)) (overlay st.tbl BW) (List.replicate cap false)

/-- **The atom streams of one flip pattern's gates**. -/
theorem gates_run (Q W Wc V : ℕ) (cs : List ℕ) (post K ZW MK BW : List Bool) (st0 : GSt) (capK cap : ℕ) (h1 : 1 ≤ Wc)
    (hcs : ∀ v ∈ cs, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK) (hK : K = false :: List.replicate capK true)
    (hZW : ZW = frame (binary Wc 0)) (hMK : MK = frame (shiftMask Q W)) (hc1 : 2 * (Q + W + 1) + 1 ≤ cap)
    (hc2 : 2 * Wc + 2 ≤ cap) (hc3 : 3 * Wc + 2 ≤ cap) :
    Step gatesM (cs.length * (atomCost Q W Wc V + 2) + 1) (tH 0 st0.tbl.length)
      (gBank (cs.flatMap natWord ++ false :: post) K ZW MK Q W Wc BW cap st0)
      (tH (cs.flatMap natWord).length (cs.foldl (gnext Q W) st0).tbl.length)
      (gBank (cs.flatMap natWord ++ false :: post) K ZW MK Q W Wc BW cap (cs.foldl (gnext Q W) st0)) := by
  set CN := cs.flatMap natWord ++ false :: post
  subst hK hZW hMK
  have hr := encRun natWord natWord_head atomM 0 [] cs post (gnext Q W) st0
    (fun st p => tH p st.tbl.length) (fun st => gBank CN (false :: List.replicate capK true) (frame (binary Wc 0))
      (frame (shiftMask Q W)) Q W Wc BW cap st) (fun st => rfl) (fun st p => rfl) (atomCost Q W Wc V) (by
      intro j hj
      set st := (cs.take j).foldl (gnext Q W) st0
      obtain ⟨hv, hV, hKv⟩ := hcs cs[j] (List.getElem_mem hj)
      have hS : CN = ((cs.take j).flatMap natWord) ++ natWord cs[j] ++ ((cs.drop (j + 1)).flatMap natWord ++ false :: post) := by
        simp only [CN]
        rw [enc_split natWord cs j hj]
        simp [List.append_assoc]
      have b := atom_run Q W Wc st.c cs[j] V st.last st.last false ((cs.take j).flatMap natWord)
        ((cs.drop (j + 1)).flatMap natWord ++ false :: post) st.tbl BW capK cap h1 hv hV hKv hc1 hc2 hc3
      rw [← hS] at b
      have ht : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (cs.take (j + 1)).foldl (gnext Q W) st0 = gnext Q W st cs[j] := by
        rw [ht, List.foldl_append]; rfl
      have hpos : ([] : List Bool).length + ((cs.take (j + 1)).flatMap natWord).length =
          ((cs.take j).flatMap natWord ++ natWord cs[j]).length := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_nil,
          Nat.zero_add]
      rw [hst, hpos]
      refine b.congr_in ?_ rfl
      simp)
  simp only [List.length_nil, Nat.zero_add] at hr
  exact hr

/-! ## Every flip pattern (tapes 0-11 as above, 12 the count cursor's log, 13 the flip stream) -/

/-- The gate loop with the count cursor returned to `0` (log on tape 12). -/
noncomputable def gatesR := MaskedReset.machine gatesM (fun i => decide (i = 0))

def uSkip : Fin 1 → Fin 14 := ![13]
def uGates : Fin 13 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem uSkip_inj : Function.Injective uSkip := by decide

theorem install_uSkip (A : Fin 14 → List Bool) (v : Fin 1 → List Bool) :
    install uSkip A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, v 0] := by
  funext i
  fin_cases i
  · exact install_other uSkip A v 0 (by decide)
  · exact install_other uSkip A v 1 (by decide)
  · exact install_other uSkip A v 2 (by decide)
  · exact install_other uSkip A v 3 (by decide)
  · exact install_other uSkip A v 4 (by decide)
  · exact install_other uSkip A v 5 (by decide)
  · exact install_other uSkip A v 6 (by decide)
  · exact install_other uSkip A v 7 (by decide)
  · exact install_other uSkip A v 8 (by decide)
  · exact install_other uSkip A v 9 (by decide)
  · exact install_other uSkip A v 10 (by decide)
  · exact install_other uSkip A v 11 (by decide)
  · exact install_other uSkip A v 12 (by decide)
  · exact install_slot uSkip uSkip_inj A v 0

theorem dockH_uSkip (H : Fin 14 → ℕ) (v : Fin 1 → ℕ) :
    dockH uSkip H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other uSkip H v 0 (by decide)
  · exact dockH_other uSkip H v 1 (by decide)
  · exact dockH_other uSkip H v 2 (by decide)
  · exact dockH_other uSkip H v 3 (by decide)
  · exact dockH_other uSkip H v 4 (by decide)
  · exact dockH_other uSkip H v 5 (by decide)
  · exact dockH_other uSkip H v 6 (by decide)
  · exact dockH_other uSkip H v 7 (by decide)
  · exact dockH_other uSkip H v 8 (by decide)
  · exact dockH_other uSkip H v 9 (by decide)
  · exact dockH_other uSkip H v 10 (by decide)
  · exact dockH_other uSkip H v 11 (by decide)
  · exact dockH_other uSkip H v 12 (by decide)
  · exact dockH_slot uSkip uSkip_inj H v 0

theorem uGates_inj : Function.Injective uGates := by decide

theorem install_uGates (A : Fin 14 → List Bool) (v : Fin 13 → List Bool) :
    install uGates A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, A 13] := by
  funext i
  fin_cases i
  · exact install_slot uGates uGates_inj A v 0
  · exact install_slot uGates uGates_inj A v 1
  · exact install_slot uGates uGates_inj A v 2
  · exact install_slot uGates uGates_inj A v 3
  · exact install_slot uGates uGates_inj A v 4
  · exact install_slot uGates uGates_inj A v 5
  · exact install_slot uGates uGates_inj A v 6
  · exact install_slot uGates uGates_inj A v 7
  · exact install_slot uGates uGates_inj A v 8
  · exact install_slot uGates uGates_inj A v 9
  · exact install_slot uGates uGates_inj A v 10
  · exact install_slot uGates uGates_inj A v 11
  · exact install_slot uGates uGates_inj A v 12
  · exact install_other uGates A v 13 (by decide)

theorem dockH_uGates (H : Fin 14 → ℕ) (v : Fin 13 → ℕ) :
    dockH uGates H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, H 13] := by
  funext i
  fin_cases i
  · exact dockH_slot uGates uGates_inj H v 0
  · exact dockH_slot uGates uGates_inj H v 1
  · exact dockH_slot uGates uGates_inj H v 2
  · exact dockH_slot uGates uGates_inj H v 3
  · exact dockH_slot uGates uGates_inj H v 4
  · exact dockH_slot uGates uGates_inj H v 5
  · exact dockH_slot uGates uGates_inj H v 6
  · exact dockH_slot uGates uGates_inj H v 7
  · exact dockH_slot uGates uGates_inj H v 8
  · exact dockH_slot uGates uGates_inj H v 9
  · exact dockH_slot uGates uGates_inj H v 10
  · exact dockH_slot uGates uGates_inj H v 11
  · exact dockH_slot uGates uGates_inj H v 12
  · exact dockH_other uGates H v 13 (by decide)

/-- One flip pattern of the table: step over its record, run the gate loop. -/
noncomputable def tflipBody := Composition.machine (RecoveryFocus.machine uSkip skipM) (RecoveryFocus.machine uGates gatesR)
/-- The table's flips loop over the flip stream (tape 13). -/
noncomputable def tflipsM := StreamController.machine tflipBody 13

def uH (o q : ℕ) : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, q]

def uBank (CN K ZW MK : List Bool) (Q W Wc : ℕ) (BW : List Bool) (cap cap5 : ℕ) (FL : List Bool) (st : GSt) :
    Fin 14 → List Bool :=
  ![CN, K, frame (binary Wc st.last), ZW, frame (binary Wc st.last), [false], [true], frame (entC Q W st.c), MK,
    frame (entC Q W st.c), overlay st.tbl BW, List.replicate cap false, List.replicate cap5 false, FL]

def gatesCost (Q W Wc V B : ℕ) : ℕ := B * (atomCost Q W Wc V + 2) + 1

def tflipCost (n Q W Wc V B : ℕ) : ℕ := (2 * n + 1) + 1 + (2 * gatesCost Q W Wc V B + 2)

theorem tflips_run (Q W Wc V n : ℕ) (cs : List ℕ) (flips : List (List Bool)) (post K ZW MK BW staleF : List Bool)
    (st0 : GSt) (capK cap cap5 : ℕ) (h1 : 1 ≤ Wc) (hfl : ∀ f ∈ flips, f.length = n) (hn : 1 ≤ n)
    (hcs : ∀ v ∈ cs, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK) (hK : K = false :: List.replicate capK true)
    (hZW : ZW = frame (binary Wc 0)) (hMK : MK = frame (shiftMask Q W)) (hc1 : 2 * (Q + W + 1) + 1 ≤ cap)
    (hc2 : 2 * Wc + 2 ≤ cap) (hc3 : 3 * Wc + 2 ≤ cap) (hc5 : gatesCost Q W Wc V cs.length ≤ cap5) :
    Step tflipsM (flips.length * (tflipCost n Q W Wc V cs.length + 2) + 1) (uH st0.tbl.length 0)
      (uBank (cs.flatMap natWord ++ false :: post) K ZW MK Q W Wc BW cap cap5 (streamTape flips staleF) st0)
      (uH (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) st0).tbl.length (flips.flatMap frame).length)
      (uBank (cs.flatMap natWord ++ false :: post) K ZW MK Q W Wc BW cap cap5 (streamTape flips staleF)
        (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) st0)) := by
  set CN := cs.flatMap natWord ++ false :: post
  have hne : ∀ r ∈ flips, r ≠ [] := by
    intro r hr hr0; have := hfl r hr; rw [hr0] at this; simp at this; omega
  have hr := streamRun tflipBody 13 flips staleF hne (fun st _ => cs.foldl (gnext Q W) st) st0
    (fun st p => uH st.tbl.length p)
    (fun st => uBank CN K ZW MK Q W Wc BW cap cap5 (streamTape flips staleF) st)
    (fun st => rfl) (fun st p => rfl) (tflipCost n Q W Wc V cs.length) (by
      intro j hj
      set st := (flips.take j).foldl (fun st _ => cs.foldl (gnext Q W) st) st0
      have hS := streamTape_split flips staleF j hj
      have sk := skipStep ((flips.take j).flatMap frame) flips[j] ((flips.drop (j + 1)).flatMap frame ++ false :: staleF)
      have hFL : (flips.take j).flatMap frame ++ frame flips[j] ++ ((flips.drop (j + 1)).flatMap frame ++ false :: staleF) =
          streamTape flips staleF := by rw [hS]
      rw [hFL] at sk
      have e1 := dockRun sk uSkip uSkip_inj (uH st.tbl.length (off flips j))
        (uBank CN K ZW MK Q W Wc BW cap cap5 (streamTape flips staleF) st)
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_uSkip, dockH_uSkip] at e1
      have g0 := gates_run Q W Wc V cs post K ZW MK BW st capK cap h1 hcs hK hZW hMK hc1 hc2 hc3
      have gm := g0.mask (fun i => decide (i = 0)) (by intro i hi; simp at hi; subst hi; rfl) hc5
      have g1 : Step gatesR (2 * gatesCost Q W Wc V cs.length + 2)
          ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, st.tbl.length, 0, 0]
          ![CN, K, frame (binary Wc st.last), ZW, frame (binary Wc st.last), [false], [true], frame (entC Q W st.c), MK,
            frame (entC Q W st.c), overlay st.tbl BW, List.replicate cap false, List.replicate cap5 false]
          ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (cs.foldl (gnext Q W) st).tbl.length, 0, 0]
          ![CN, K, frame (binary Wc (cs.foldl (gnext Q W) st).last), ZW, frame (binary Wc (cs.foldl (gnext Q W) st).last),
            [false], [true], frame (entC Q W (cs.foldl (gnext Q W) st).c), MK, frame (entC Q W (cs.foldl (gnext Q W) st).c),
            overlay (cs.foldl (gnext Q W) st).tbl BW, List.replicate cap false, List.replicate cap5 false] := by
        refine (gm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          (try fin_cases j) <;> rfl
      have e2 := dockRun g1 uGates uGates_inj
        (uH st.tbl.length (((flips.take j).flatMap frame).length + 2 * flips[j].length + 1))
        (uBank CN K ZW MK Q W Wc BW cap cap5 (streamTape flips staleF) st)
        (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
      rw [install_uGates, dockH_uGates] at e2
      have ht : flips.take (j + 1) = flips.take j ++ [flips[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (flips.take (j + 1)).foldl (fun st _ => cs.foldl (gnext Q W) st) st0 = cs.foldl (gnext Q W) st := by
        rw [ht, List.foldl_append]; rfl
      have ho : off flips (j + 1) = ((flips.take j).flatMap frame).length + 2 * flips[j].length + 1 := by
        rw [off_succ flips j hj]; simp [off]; omega
      rw [hst, ho]
      have j2 := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq e2
      have hlen : flips[j].length = n := hfl _ (List.getElem_mem hj)
      refine (j2.congr ?_ ?_).enlarge (le_of_eq ?_)
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
      · simp [tflipCost, hlen])
  exact hr

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
