import Proof.Wire_3_5.CompilerMachineMasksAtom
import Proof.Wire_3_5.CompilerMachineStream

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The monomial's frame -/

def atomCodeW (a : ℕ) : List Bool := List.replicate a true ++ [false]

/-- The bits of a monomial: its atoms' codes. -/
def codeBits (mono : List ℕ) : List Bool := mono.flatMap atomCodeW

theorem frame_append_bits (l r : List Bool) : frame (l ++ r) = l.flatMap (fun b => [true, b]) ++ frame r := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame, ih]

theorem pairs_atomCode (a : ℕ) : (atomCodeW a).flatMap (fun b => [true, b]) = pairsTape a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [atomCodeW, pairsTape] at ih ⊢
    rw [List.replicate_succ, List.cons_append, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]
    rfl

/-- **The monomial's frame is its atoms' pairs, then the terminator.** -/
theorem frame_codeBits (mono : List ℕ) : frame (codeBits mono) = mono.flatMap pairsTape ++ [false] := by
  induction mono with
  | nil => rfl
  | cons a mono ih =>
    simp only [codeBits, List.flatMap_cons] at ih ⊢
    rw [frame_append_bits, ih, pairs_atomCode, List.append_assoc]

/-! ## The table and the bridge to `maskStep` -/

/-- The table of the pool's exact children: for each atom, the size-`0` entries of its child labels. -/
def childTable (Q : ℕ) (pool : List (List SynEq)) : List (List (List Bool)) :=
  (List.range pool.length).map fun a => (labelsOf pool a).map fun c => ew Q pool.flatten.length (0, 2 ^ c)

theorem childTable_getD (Q : ℕ) (pool : List (List SynEq)) (a : ℕ) (ha : a < pool.length) :
    (childTable Q pool).getD a [] = (labelsOf pool a).map fun c => ew Q pool.flatten.length (0, 2 ^ c) := by
  simp [childTable, List.getD_eq_getElem?_getD, ha]

theorem length_getD_le_flatten (pool : List (List SynEq)) (a : ℕ) : (pool.getD a []).length ≤ pool.flatten.length := by
  induction pool generalizing a with
  | nil => simp
  | cons x pool ih =>
    cases a with
    | zero => simp
    | succ a => simp only [List.getD_cons_succ, List.flatten_cons, List.length_append]; have := ih a; omega

theorem childTable_props (Q : ℕ) (pool : List (List SynEq)) :
    ∀ E ∈ childTable Q pool, (∀ r ∈ E, r.length = Q + pool.flatten.length + 1) ∧ E.length ≤ pool.flatten.length + 1 := by
  intro E hE
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hE
  refine ⟨?_, ?_⟩
  · intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    exact entryWord_length Q _ 0 _ (by omega)
  · simp only [List.length_map, labelsOf, List.length_range']
    have := length_getD_le_flatten pool a
    omega

/-- **One atom's expansion is `maskStep` read through the entries.** -/
theorem expandW_map (Q : ℕ) (pool : List (List SynEq)) (Lm : List ℕ) (a : ℕ) (ha : a < pool.length) :
    expandW (Lm.map fun U => ew Q pool.flatten.length (0, U)) ((childTable Q pool).getD a []) =
      (maskStep pool Lm a).map fun U => ew Q pool.flatten.length (0, U) := by
  rw [childTable_getD Q pool a ha]
  unfold expandW maskStep
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro U _
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, ew]
  exact orW_entry Q _ 0 U (2 ^ c) (by omega)

theorem foldl_expandW_map (Q : ℕ) (pool : List (List SynEq)) : ∀ (mono : List ℕ) (Lm : List ℕ),
    (∀ a ∈ mono, a < pool.length) →
      mono.foldl (fun L a => expandW L ((childTable Q pool).getD a [])) (Lm.map fun U => ew Q pool.flatten.length (0, U)) =
        (mono.foldl (maskStep pool) Lm).map fun U => ew Q pool.flatten.length (0, U)
  | [], _, _ => rfl
  | a :: mono, Lm, hm => by
    rw [List.foldl_cons, List.foldl_cons, expandW_map Q pool Lm a (hm a List.mem_cons_self)]
    exact foldl_expandW_map Q pool mono (maskStep pool Lm a) (fun a' h' => hm a' (List.mem_cons_of_mem a h'))

/-! ## The initial running list, and the monomial machine -/

def iEmit : Fin 3 → Fin 3 := ![1, 0, 2]
def iPut : Fin 1 → Fin 3 := ![0]
noncomputable def iEmitD := RecoveryFocus.machine iEmit emitM
noncomputable def iPutD := RecoveryFocus.machine iPut (putM false)
/-- Write the one-record running list `[z]` from the register `Z0`, head back at cell 0 (local tapes: 0 `LA`, 1 `Z0`,
2 the register log, 3 the reset log). -/
noncomputable def initM := MaskedReset.machine (Composition.machine iEmitD iPutD) ![true, false, false]

def nInit : Fin 4 → Fin 12 := ![3, 11, 8, 10]
def nAtoms : Fin 11 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
noncomputable def nInitD := RecoveryFocus.machine nInit initM
noncomputable def nAtomsD := RecoveryFocus.machine nAtoms atomLoopM
/-- **The monomial machine**: the running list `[ew Q W (0, 0)]`, then the atom loop. -/
noncomputable def monoM := Composition.machine nInitD nAtomsD

theorem iEmit_inj : Function.Injective iEmit := by decide

theorem install_iEmit (A : Fin 3 → List Bool) (v : Fin 3 → List Bool) :
    install iEmit A v = ![v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact install_slot iEmit iEmit_inj A v 1
  · exact install_slot iEmit iEmit_inj A v 0
  · exact install_slot iEmit iEmit_inj A v 2

theorem dockH_iEmit (H : Fin 3 → ℕ) (v : Fin 3 → ℕ) :
    dockH iEmit H v = ![v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot iEmit iEmit_inj H v 1
  · exact dockH_slot iEmit iEmit_inj H v 0
  · exact dockH_slot iEmit iEmit_inj H v 2

theorem iPut_inj : Function.Injective iPut := by decide

theorem install_iPut (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install iPut A v = ![v 0, A 1, A 2] := by
  funext i
  fin_cases i
  · exact install_slot iPut iPut_inj A v 0
  · exact install_other iPut A v 1 (by decide)
  · exact install_other iPut A v 2 (by decide)

theorem dockH_iPut (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH iPut H v = ![v 0, H 1, H 2] := by
  funext i
  fin_cases i
  · exact dockH_slot iPut iPut_inj H v 0
  · exact dockH_other iPut H v 1 (by decide)
  · exact dockH_other iPut H v 2 (by decide)

theorem nInit_inj : Function.Injective nInit := by decide

theorem install_nInit (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    install nInit A v = ![A 0, A 1, A 2, v 0, A 4, A 5, A 6, A 7, v 2, A 9, v 3, v 1] := by
  funext i
  fin_cases i
  · exact install_other nInit A v 0 (by decide)
  · exact install_other nInit A v 1 (by decide)
  · exact install_other nInit A v 2 (by decide)
  · exact install_slot nInit nInit_inj A v 0
  · exact install_other nInit A v 4 (by decide)
  · exact install_other nInit A v 5 (by decide)
  · exact install_other nInit A v 6 (by decide)
  · exact install_other nInit A v 7 (by decide)
  · exact install_slot nInit nInit_inj A v 2
  · exact install_other nInit A v 9 (by decide)
  · exact install_slot nInit nInit_inj A v 3
  · exact install_slot nInit nInit_inj A v 1

theorem dockH_nInit (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH nInit H v = ![H 0, H 1, H 2, v 0, H 4, H 5, H 6, H 7, v 2, H 9, v 3, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other nInit H v 0 (by decide)
  · exact dockH_other nInit H v 1 (by decide)
  · exact dockH_other nInit H v 2 (by decide)
  · exact dockH_slot nInit nInit_inj H v 0
  · exact dockH_other nInit H v 4 (by decide)
  · exact dockH_other nInit H v 5 (by decide)
  · exact dockH_other nInit H v 6 (by decide)
  · exact dockH_other nInit H v 7 (by decide)
  · exact dockH_slot nInit nInit_inj H v 2
  · exact dockH_other nInit H v 9 (by decide)
  · exact dockH_slot nInit nInit_inj H v 3
  · exact dockH_slot nInit nInit_inj H v 1

theorem nAtoms_inj : Function.Injective nAtoms := by decide

theorem install_nAtoms (A : Fin 12 → List Bool) (v : Fin 11 → List Bool) :
    install nAtoms A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, A 11] := by
  funext i
  fin_cases i
  · exact install_slot nAtoms nAtoms_inj A v 0
  · exact install_slot nAtoms nAtoms_inj A v 1
  · exact install_slot nAtoms nAtoms_inj A v 2
  · exact install_slot nAtoms nAtoms_inj A v 3
  · exact install_slot nAtoms nAtoms_inj A v 4
  · exact install_slot nAtoms nAtoms_inj A v 5
  · exact install_slot nAtoms nAtoms_inj A v 6
  · exact install_slot nAtoms nAtoms_inj A v 7
  · exact install_slot nAtoms nAtoms_inj A v 8
  · exact install_slot nAtoms nAtoms_inj A v 9
  · exact install_slot nAtoms nAtoms_inj A v 10
  · exact install_other nAtoms A v 11 (by decide)

theorem dockH_nAtoms (H : Fin 12 → ℕ) (v : Fin 11 → ℕ) :
    dockH nAtoms H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_slot nAtoms nAtoms_inj H v 0
  · exact dockH_slot nAtoms nAtoms_inj H v 1
  · exact dockH_slot nAtoms nAtoms_inj H v 2
  · exact dockH_slot nAtoms nAtoms_inj H v 3
  · exact dockH_slot nAtoms nAtoms_inj H v 4
  · exact dockH_slot nAtoms nAtoms_inj H v 5
  · exact dockH_slot nAtoms nAtoms_inj H v 6
  · exact dockH_slot nAtoms nAtoms_inj H v 7
  · exact dockH_slot nAtoms nAtoms_inj H v 8
  · exact dockH_slot nAtoms nAtoms_inj H v 9
  · exact dockH_slot nAtoms nAtoms_inj H v 10
  · exact dockH_other nAtoms H v 11 (by decide)

theorem zeroHeads4m : (![0, 0, 0, 0] : Fin 4 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

theorem init_run (BWA z : List Bool) (cap cap3 : ℕ) (hcap : 2 * z.length + 1 ≤ cap)
    (hcap3 : 2 * (2 * z.length + 1) + 2 + 1 + 1 ≤ cap3) :
    Step initM (2 * (2 * (2 * z.length + 1) + 2 + 1 + 1) + 2) (fun _ => 0)
      ![BWA, frame z, List.replicate cap false, List.replicate cap3 false] (fun _ => 0)
      ![streamTape [z] (BWA.drop ((frame z).length + 1)), frame z, List.replicate cap false, List.replicate cap3 false] := by
  have e1 := dockRun (emitStep z [] BWA cap hcap) iEmit iEmit_inj ![0, 0, 0] ![overlay [] BWA, frame z, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iEmit, dockH_iEmit] at e1
  have e2 := dockRun (putStep false (overlay ([] ++ frame z) BWA) ([] ++ frame z).length) iPut iPut_inj
    ![([] ++ frame z).length, 0, 0] ![overlay ([] ++ frame z) BWA, frame z, List.replicate cap false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_iPut, dockH_iPut, overlay_write] at e2
  have e1' := e1.congr (hout' := ![([] ++ frame z).length, 0, 0]) (tout' := ![overlay ([] ++ frame z) BWA, frame z,
    List.replicate cap false]) (by funext i; fin_cases i <;> simp) rfl
  have hall := e1'.seq e2
  have hm := hall.mask (cap := cap3) ![true, false, false] (by intro i hi; fin_cases i <;> simp_all) hcap3
  have hz : overlay ([] ++ frame z ++ [false]) BWA = streamTape [z] (BWA.drop ((frame z).length + 1)) := by
    simp [overlay, streamTape]
  rw [hz] at hm
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- The cost of one monomial of `n` atoms: pool of `P` atoms, `W` labels, size field `Q`. -/
def monoCost (n P Q W : ℕ) : ℕ :=
  (2 * (2 * (2 * (Q + W + 1) + 1) + 2 + 1 + 1) + 2) + 1 + atomsCost n P (W + 1) (Q + W + 1)

theorem monomial_run (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (P post staleT BWA LB Ea R R2 R3 : List Bool)
    (cap cap2 cap3 : ℕ) (hmono : ∀ a ∈ mono, a < pool.length)
    (h1 : R.length = Q + pool.flatten.length + 1) (h2 : R2.length = Q + pool.flatten.length + 1)
    (h3 : R3.length = Q + pool.flatten.length + 1) (hcap : 2 * (Q + pool.flatten.length + 1) + 1 ≤ cap)
    (hcap2 : (pool.flatten.length + 1) * (innerCost (Q + pool.flatten.length + 1) + 2) + 1 ≤ cap2)
    (hcap3 : max (lookupCost pool.length (pool.flatten.length + 1) (Q + pool.flatten.length + 1))
      (max (expandLoopCost ((pool.flatten.length + 1) ^ mono.length) (pool.flatten.length + 1) (Q + pool.flatten.length + 1))
        (copyLoopCost ((pool.flatten.length + 1) ^ mono.length) (Q + pool.flatten.length + 1))) ≤ cap3)
    (hcap3' : 2 * (2 * (Q + pool.flatten.length + 1) + 1) + 2 + 1 + 1 ≤ cap3) :
    ∃ st : MState, st.L = (monoMasks pool mono).map (fun U => ew Q pool.flatten.length (0, U)) ∧
      Step monoM (monoCost mono.length pool.length Q pool.flatten.length) ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, Ea, BWA, LB, frame R, frame R2,
          frame R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false,
          frame (ew Q pool.flatten.length (0, 0))]
        ![P.length + (mono.flatMap pairsTape).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, st.Ea, streamTape st.L st.staleA,
          st.LB, frame st.R, frame st.R2, frame st.R3, List.replicate cap false, List.replicate cap2 false,
          List.replicate cap3 false, frame (ew Q pool.flatten.length (0, 0))] := by
  set W := pool.flatten.length
  set L := Q + W + 1
  set z := ew Q W (0, 0)
  have hz : z.length = L := entryWord_length Q W 0 0 (by omega)
  have hM : P ++ frame (codeBits mono) ++ post = P ++ mono.flatMap pairsTape ++ false :: post := by
    rw [frame_codeBits]; simp [List.append_assoc]
  -- the initial running list
  have e1 := init_run BWA z cap cap3 (by rw [hz]; exact hcap) (by rw [hz]; exact hcap3')
  have s1 := dockKeep e1 nInit nInit_inj ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, Ea, BWA, LB, frame R, frame R2,
      frame R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame z]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_nInit] at s1
  -- the atom loop
  let st0 : MState := ⟨[z], BWA.drop ((frame z).length + 1), LB, Ea, R, R2, R3⟩
  have h0 : MInv L st0 := ⟨by intro U hU; simp [st0] at hU; rw [hU, hz], h1, h2, h3⟩
  have hTab : (childTable Q pool).length = pool.length := by simp [childTable]
  have e2 := atoms_run P post mono (childTable Q pool) staleT cap cap2 cap3 (W + 1) L st0
    (by intro a ha; rw [hTab]; exact hmono a ha) (childTable_props Q pool) (by omega) (by omega) h0 rfl hcap hcap2
    (by rw [hTab]; exact hcap3)
  rw [← hM] at e2
  have s2 := dockRun e2 nAtoms nAtoms_inj ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, Ea,
      streamTape [z] (BWA.drop ((frame z).length + 1)), LB, frame R, frame R2, frame R3, List.replicate cap false,
      List.replicate cap2 false, List.replicate cap3 false, frame z]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_nAtoms, dockH_nAtoms] at s2
  refine ⟨mono.foldl (mstep (childTable Q pool)) st0, ?_, ?_⟩
  · rw [foldl_mstep_L]
    show mono.foldl (fun L a => expandW L ((childTable Q pool).getD a [])) ([0].map fun U => ew Q W (0, U)) = _
    rw [foldl_expandW_map Q pool mono [0] hmono, monoMasks_foldl]
  · have hall := s1.seq s2
    refine (hall.enlarge (by unfold monoCost; rw [hTab, hz])).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

/-! ## Twins -/

/-- The monomial `x₀x₁` of the twin pool (atom 0 with labels 0, 1; atom 1 with label 2): the machine's fold of
`expandW` over the children table is `monoMasks` read through the entries. -/
theorem masks_twin :
    ([0, 1] : List ℕ).foldl (fun L a => expandW L ((childTable 1 twinPool).getD a [])) [ew 1 3 (0, 0)] =
      (monoMasks twinPool [0, 1]).map (fun U => ew 1 3 (0, U)) := by
  decide

theorem codeBits_twin : frame (codeBits [2, 0]) = ([2, 0] : List ℕ).flatMap pairsTape ++ [false] := by decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Masks
