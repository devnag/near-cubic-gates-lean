import Proof.Wire_3_5.PrimAsmDataTabs
import Proof.Wire_3_5.UnionMachineFrontFill
import Proof.Wire_3_5.ListMachineRowLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Stages
variable (cap : ℕ) {n : ℕ} (L : ℕ)

/-- A SYM slot's stage cost. -/
noncomputable def symCostO : Option (NormalizedSymmetricThresholdCircuit n) → ℕ
  | some C => PrimT.SymTab.symTableCost C L + 2
  | none => 2

/-- A carrier slot's stage cost. -/
noncomputable def carCostO : Option (Stars.Carrier n) → ℕ
  | some X => PrimT.CarTable.carTableCost X L + 2
  | none => 2

/-- A SYM slot's entry condition. -/
def symPre (σ : WState DS DR) (i : Fin 4) : Option (NormalizedSymmetricThresholdCircuit n) → Prop
  | some C => Done σ (symTrip i) (encodeNormalizedSymmetricThresholdCircuit C) n L
  | none => Blank σ (symTrip i)

/-- A SYM slot's exit facts (the collection reads the first cell of `0` and the count on `5`). -/
def symPost (σ : WState DS DR) (i : Fin 4) : Option (NormalizedSymmetricThresholdCircuit n) → Prop
  | some C => readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = true ∧
      σ.st (sSym i 5) = List.replicate (Stars.symGates C).length true ∧ σ.sh (sSym i 5) = 0 ∧
      σ.st (sSym i 3) = FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates C)) (Stars.symGates C)
  | none => readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = false

def carPre (σ : WState DS DR) (k : Fin 2) : Option (Stars.Carrier n) → Prop
  | some X => Done σ (carTrip k) X.code n L
  | none => Blank σ (carTrip k)

def carPost (σ : WState DS DR) (k : Fin 2) : Option (Stars.Carrier n) → Prop
  | some X => readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = true ∧
      σ.st (sCar k 5) = List.replicate X.length true ∧ σ.sh (sCar k 5) = 0 ∧
      σ.st (sCar k 3) = FinalPass.Corner.gatesW (PrimT.tabH X) (FinalPass.Corner.maskGates X)
  | none => readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false

/-- **One SYM slot's stage**, filled or empty. -/
theorem symT_stage (i : Fin 4) (oc : Option (NormalizedSymmetricThresholdCircuit n)) (σ : WState DS DR)
    (hpre : symPre L σ i oc) (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hL : ∀ C, oc = some C → C.descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step (symT i) (symCostO L oc) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      symPost σ' i oc ∧ (∀ s, (∀ j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell := by
  cases oc with
  | none =>
    refine ⟨σ, symT_off cap i σ hpre, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
    obtain ⟨b1, b2, _, _, _, _⟩ := hpre
    simp only [symTrip] at b1 b2
    show readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = false
    rw [b1]
    rfl
  | some C =>
    obtain ⟨tout, hs, t0, t3, t5⟩ := symT_on cap i C L (hL C rfl) h2 σ hpre hb
    refine ⟨updS (sSym i) σ (fun _ => 0) tout, hs, ?_, fun s hs' => ⟨updS_st_other _ _ _ _ s hs',
      updS_sh_other _ _ _ _ s hs'⟩, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [updS_st_slot _ (sSym_inj i), updS_sh_slot _ (sSym_inj i), t0]
      exact frame_natWord_head _
    · rw [updS_st_slot _ (sSym_inj i), t5]
    · rw [updS_sh_slot _ (sSym_inj i)]
    · rw [updS_st_slot _ (sSym_inj i), t3]

/-- **One carrier slot's stage**, filled or empty. -/
theorem carT_stage (k : Fin 2) (ox : Option (Stars.Carrier n)) (σ : WState DS DR)
    (hpre : carPre L σ k ox) (hb : ∀ j : Fin 1357, 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0)
    (hL : ∀ X, ox = some X → ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step (carT k) (carCostO L ox) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      carPost σ' k ox ∧ (∀ s, (∀ j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell := by
  cases ox with
  | none =>
    refine ⟨σ, carT_off cap k σ hpre, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
    obtain ⟨b1, b2, _, _, _, _⟩ := hpre
    simp only [carTrip] at b1 b2
    show readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false
    rw [b1]
    rfl
  | some X =>
    obtain ⟨tout, hs, t0, t3, t5⟩ := carT_on cap k X L (hL X rfl) h2 σ hpre hb
    refine ⟨updS (sCar k) σ (fun _ => 0) tout, hs, ?_, fun s hs' => ⟨updS_st_other _ _ _ _ s hs',
      updS_sh_other _ _ _ _ s hs'⟩, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [updS_st_slot _ (sCar_inj k), updS_sh_slot _ (sCar_inj k), t0]
      exact frame_natWord_head _
    · rw [updS_st_slot _ (sCar_inj k), t5]
    · rw [updS_sh_slot _ (sCar_inj k)]
    · rw [updS_st_slot _ (sCar_inj k), t3]

end Stages

/-! ## The six table stages -/

/-- T's machines on the six slots, in order. -/
noncomputable def tabsM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (symT 0) (symT 1)) (symT 2)) (symT 3)) (carT 0)) (carT 1)

section Chain
variable {n : ℕ} (L : ℕ)

/-- The six stages' cost. -/
noncomputable def tabsCost (oc : Fin 4 → Option (NormalizedSymmetricThresholdCircuit n))
    (ox : Fin 2 → Option (Stars.Carrier n)) : ℕ :=
  symCostO L (oc 0) + 1 + symCostO L (oc 1) + 1 + symCostO L (oc 2) + 1 + symCostO L (oc 3) + 1 +
    carCostO L (ox 0) + 1 + carCostO L (ox 1)

/-- The same on slot `i`'s streams. -/
def SameSym (σ σ' : WState DS DR) (i : Fin 4) : Prop :=
  ∀ j, σ'.st (sSym i j) = σ.st (sSym i j) ∧ σ'.sh (sSym i j) = σ.sh (sSym i j)

def SameCar (σ σ' : WState DS DR) (k : Fin 2) : Prop :=
  ∀ j, σ'.st (sCar k j) = σ.st (sCar k j) ∧ σ'.sh (sCar k j) = σ.sh (sCar k j)

theorem symPre_tr {σ σ' : WState DS DR} {i : Fin 4} (h : SameSym σ σ' i) (oc : Option (NormalizedSymmetricThresholdCircuit n)) :
    symPre L σ i oc → symPre L σ' i oc := by
  cases oc with
  | none =>
    intro ⟨b1, b2, b3, b4, b5, b6⟩
    simp only [symTrip] at b1 b2 b3 b4 b5 b6
    exact ⟨by simp only [symTrip]; rw [(h 0).1, b1], by simp only [symTrip]; rw [(h 0).2, b2],
      by simp only [symTrip]; rw [(h 1).1, b3], by simp only [symTrip]; rw [(h 1).2, b4],
      by simp only [symTrip]; rw [(h 2).1, b5], by simp only [symTrip]; rw [(h 2).2, b6]⟩
  | some C =>
    intro ⟨b1, b2, b3, b4, b5, b6⟩
    simp only [symTrip] at b1 b2 b3 b4 b5 b6
    exact ⟨by simp only [symTrip]; rw [(h 0).1, b1], by simp only [symTrip]; rw [(h 0).2, b2],
      by simp only [symTrip]; rw [(h 1).1, b3], by simp only [symTrip]; rw [(h 1).2, b4],
      by simp only [symTrip]; rw [(h 2).1, b5], by simp only [symTrip]; rw [(h 2).2, b6]⟩

theorem symPost_tr {σ σ' : WState DS DR} {i : Fin 4} (h : SameSym σ σ' i) (oc : Option (NormalizedSymmetricThresholdCircuit n)) :
    symPost σ i oc → symPost σ' i oc := by
  cases oc with
  | none =>
    intro b
    show readTapeBit (σ'.st (sSym i 0)) (σ'.sh (sSym i 0)) = false
    rw [(h 0).1, (h 0).2]
    exact b
  | some C =>
    intro ⟨b1, b2, b3, b4⟩
    exact ⟨by rw [(h 0).1, (h 0).2]; exact b1, by rw [(h 5).1, b2], by rw [(h 5).2, b3], by rw [(h 3).1, b4]⟩

theorem carPre_tr {σ σ' : WState DS DR} {k : Fin 2} (h : SameCar σ σ' k) (ox : Option (Stars.Carrier n)) :
    carPre L σ k ox → carPre L σ' k ox := by
  cases ox with
  | none =>
    intro ⟨b1, b2, b3, b4, b5, b6⟩
    simp only [carTrip] at b1 b2 b3 b4 b5 b6
    exact ⟨by simp only [carTrip]; rw [(h 0).1, b1], by simp only [carTrip]; rw [(h 0).2, b2],
      by simp only [carTrip]; rw [(h 1).1, b3], by simp only [carTrip]; rw [(h 1).2, b4],
      by simp only [carTrip]; rw [(h 2).1, b5], by simp only [carTrip]; rw [(h 2).2, b6]⟩
  | some X =>
    intro ⟨b1, b2, b3, b4, b5, b6⟩
    simp only [carTrip] at b1 b2 b3 b4 b5 b6
    exact ⟨by simp only [carTrip]; rw [(h 0).1, b1], by simp only [carTrip]; rw [(h 0).2, b2],
      by simp only [carTrip]; rw [(h 1).1, b3], by simp only [carTrip]; rw [(h 1).2, b4],
      by simp only [carTrip]; rw [(h 2).1, b5], by simp only [carTrip]; rw [(h 2).2, b6]⟩

theorem carPost_tr {σ σ' : WState DS DR} {k : Fin 2} (h : SameCar σ σ' k) (ox : Option (Stars.Carrier n)) :
    carPost σ k ox → carPost σ' k ox := by
  cases ox with
  | none =>
    intro b
    show readTapeBit (σ'.st (sCar k 0)) (σ'.sh (sCar k 0)) = false
    rw [(h 0).1, (h 0).2]
    exact b
  | some X =>
    intro ⟨b1, b2, b3, b4⟩
    exact ⟨by rw [(h 0).1, (h 0).2]; exact b1, by rw [(h 5).1, b2], by rw [(h 5).2, b3], by rw [(h 3).1, b4]⟩

/-- A SYM stage keeps every other slot. -/
theorem sym_keeps_sym {σ σ' : WState DS DR} {i : Fin 4}
    (f : ∀ s, (∀ j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) (i' : Fin 4) (hi : i ≠ i') :
    SameSym σ σ' i' := fun j => f (sSym i' j) (fun j' e => hi ((sSym_eq_iff i i' j' j).mp e).1)

theorem sym_keeps_car {σ σ' : WState DS DR} {i : Fin 4}
    (f : ∀ s, (∀ j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) (k : Fin 2) : SameCar σ σ' k :=
  fun j => f (sCar k j) (fun j' => sSym_ne_sCar i j' k j)

theorem car_keeps_sym {σ σ' : WState DS DR} {k : Fin 2}
    (f : ∀ s, (∀ j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) (i : Fin 4) : SameSym σ σ' i :=
  fun j => f (sSym i j) (fun j' e => sSym_ne_sCar i j k j' e.symm)

theorem car_keeps_car {σ σ' : WState DS DR} {k : Fin 2}
    (f : ∀ s, (∀ j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) (k' : Fin 2) (hk : k ≠ k') :
    SameCar σ σ' k' := fun j => f (sCar k' j) (fun j' e => hk ((sCar_eq_iff k k' j' j).mp e).1)

theorem SameSym.trans {σ σ' σ'' : WState DS DR} {i : Fin 4} (h1 : SameSym σ σ' i) (h2 : SameSym σ' σ'' i) :
    SameSym σ σ'' i := fun j => ⟨(h2 j).1.trans (h1 j).1, (h2 j).2.trans (h1 j).2⟩

theorem SameCar.trans {σ σ' σ'' : WState DS DR} {k : Fin 2} (h1 : SameCar σ σ' k) (h2 : SameCar σ' σ'' k) :
    SameCar σ σ'' k := fun j => ⟨(h2 j).1.trans (h1 j).1, (h2 j).2.trans (h1 j).2⟩

theorem blankSym_tr {σ σ' : WState DS DR} {i : Fin 4} (h : SameSym σ σ' i)
    (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    ∀ j : Fin 1789, 3 ≤ j.val → σ'.st (sSym i j) = [] ∧ σ'.sh (sSym i j) = 0 :=
  fun j hj => ⟨(h j).1.trans (hb j hj).1, (h j).2.trans (hb j hj).2⟩

theorem blankCar_tr {σ σ' : WState DS DR} {k : Fin 2} (h : SameCar σ σ' k)
    (hb : ∀ j : Fin 1357, 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0) :
    ∀ j : Fin 1357, 3 ≤ j.val → σ'.st (sCar k j) = [] ∧ σ'.sh (sCar k j) = 0 :=
  fun j hj => ⟨(h j).1.trans (hb j hj).1, (h j).2.trans (hb j hj).2⟩

variable (cap : ℕ)

/-- **The six table stages**: every filled slot's table and count, every empty slot skipped, nothing else changed. -/
theorem tabs_step (oc : Fin 4 → Option (NormalizedSymmetricThresholdCircuit n)) (ox : Fin 2 → Option (Stars.Carrier n))
    (σ : WState DS DR) (hpre : ∀ i, symPre L σ i (oc i)) (hpreX : ∀ k, carPre L σ k (ox k))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hbX : ∀ k (j : Fin 1357), 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0)
    (hL : ∀ i C, oc i = some C → C.descriptionBits ≤ L)
    (hLX : ∀ k X, ox k = some X → ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step tabsM (tabsCost L oc ox) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      (∀ i, symPost σ' i (oc i)) ∧ (∀ k, carPost σ' k (ox k)) ∧
      (∀ s, (∀ i j, sSym i j ≠ s) → (∀ k j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧
      σ'.val = σ.val ∧ σ'.cell = σ.cell := by
  obtain ⟨σ1, s1, p1, f1, v1, c1⟩ := symT_stage cap L 0 (oc 0) σ (hpre 0) (hb 0) (hL 0) h2
  obtain ⟨σ2, s2, p2, f2, v2, c2⟩ := symT_stage cap L 1 (oc 1) σ1
    (symPre_tr L (sym_keeps_sym f1 1 (by decide)) _ (hpre 1)) (blankSym_tr (sym_keeps_sym f1 1 (by decide)) (hb 1))
    (hL 1) h2
  obtain ⟨σ3, s3, p3, f3, v3, c3⟩ := symT_stage cap L 2 (oc 2) σ2
    (symPre_tr L ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) _ (hpre 2))
    (blankSym_tr ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) (hb 2)) (hL 2) h2
  obtain ⟨σ4, s4, p4, f4, v4, c4⟩ := symT_stage cap L 3 (oc 3) σ3
    (symPre_tr L (((sym_keeps_sym f1 3 (by decide)).trans (sym_keeps_sym f2 3 (by decide))).trans
      (sym_keeps_sym f3 3 (by decide))) _ (hpre 3))
    (blankSym_tr (((sym_keeps_sym f1 3 (by decide)).trans (sym_keeps_sym f2 3 (by decide))).trans
      (sym_keeps_sym f3 3 (by decide))) (hb 3)) (hL 3) h2
  have kc : ∀ k, SameCar σ σ4 k := fun k =>
    (((sym_keeps_car f1 k).trans (sym_keeps_car f2 k)).trans (sym_keeps_car f3 k)).trans (sym_keeps_car f4 k)
  obtain ⟨σ5, s5, p5, f5, v5, c5⟩ := carT_stage cap L 0 (ox 0) σ4 (carPre_tr L (kc 0) _ (hpreX 0))
    (blankCar_tr (kc 0) (hbX 0)) (hLX 0) h2
  obtain ⟨σ6, s6, p6, f6, v6, c6⟩ := carT_stage cap L 1 (ox 1) σ5
    (carPre_tr L ((kc 1).trans (car_keeps_car f5 1 (by decide))) _ (hpreX 1))
    (blankCar_tr ((kc 1).trans (car_keeps_car f5 1 (by decide))) (hbX 1)) (hLX 1) h2
  refine ⟨σ6, ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have t56 : ∀ i, SameSym σ4 σ6 i := fun i => (car_keeps_sym f5 i).trans (car_keeps_sym f6 i)
    fin_cases i
    · exact symPost_tr (((sym_keeps_sym f2 0 (by decide)).trans (sym_keeps_sym f3 0 (by decide))).trans
        ((sym_keeps_sym f4 0 (by decide)).trans (t56 0))) _ p1
    · exact symPost_tr ((sym_keeps_sym f3 1 (by decide)).trans ((sym_keeps_sym f4 1 (by decide)).trans (t56 1))) _ p2
    · exact symPost_tr ((sym_keeps_sym f4 2 (by decide)).trans (t56 2)) _ p3
    · exact symPost_tr (t56 3) _ p4
  · intro k
    fin_cases k
    · exact carPost_tr (car_keeps_car f6 0 (by decide)) _ p5
    · exact p6
  · intro s hs hs'
    have e1 := f1 s (fun j => hs 0 j)
    have e2 := f2 s (fun j => hs 1 j)
    have e3 := f3 s (fun j => hs 2 j)
    have e4 := f4 s (fun j => hs 3 j)
    have e5 := f5 s (fun j => hs' 0 j)
    have e6 := f6 s (fun j => hs' 1 j)
    exact ⟨e6.1.trans (e5.1.trans (e4.1.trans (e3.1.trans (e2.1.trans e1.1)))),
      e6.2.trans (e5.2.trans (e4.2.trans (e3.2.trans (e2.2.trans e1.2))))⟩
  · rw [v6, v5, v4, v3, v2, v1]
  · rw [c6, c5, c4, c3, c2, c1]

end Chain

/-! ## The registers and the cell -/

/-- The register tapes (the fill's targets). -/
def regSel (j : Fin (DS + 2 + DR)) : Bool := decide (DS + 2 ≤ j.val)

/-- The stage's entry bank: the framed request, `1^n`, `1^L`, `1^W`, everything else blank. -/
def rawIn (w : List Bool) (n L W : ℕ) : Fin (DS + 2 + DR) → List Bool := fun j =>
  if j = sTape sIN then RepairOrdinary.frame w else if j = sTape sNT then List.replicate n true
  else if j = sTape sLT then List.replicate L true else if j = sTape sCT then List.replicate W true else []

/-- The fill and the cell. -/
def fillAct : Prog (DS + 2 + DR) :=
  .seq (UnionMachine.FrontFill.fillP (sTape sCT) (sTape sAUX) regSel) (.act (writeAt cTape false) (fun _ => .stay))

/-- The register-language state after the fill: registers `0` at capacity `2W + 2`, the cell `0`, the inputs and the
fill's marker tape on their streams, every head at `0`. -/
def σ0 (w : List Bool) (n L W : ℕ) : WState DS DR :=
  ⟨fun _ => 0, fun s => if s = sIN then RepairOrdinary.frame w else if s = sNT then List.replicate n true
    else if s = sLT then List.replicate L true else if s = sCT then List.replicate W true
    else if s = sAUX then List.replicate (2 * W + 3) false else [], fun _ => 0, false⟩

theorem sTape_val' (s : Fin (DS + 1)) : (sTape (nr := DR) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

theorem sTape_eq_iff' (a b : Fin (DS + 1)) : sTape (nr := DR) a = sTape b ↔ a = b :=
  ⟨fun h => sTape_inj h, fun h => h ▸ rfl⟩

theorem regSel_s (s : Fin (DS + 1)) : regSel (sTape (nr := DR) s) = false := by
  have := s.isLt
  simp only [regSel, sTape_val', decide_eq_false_iff_not, not_le]
  split <;> omega

theorem regSel_c : regSel (cTape (ns := DS) (nr := DR)) = false := by
  unfold regSel
  rw [show (cTape (ns := DS) (nr := DR)).val = 1 from rfl]
  decide

theorem regSel_r (r : Fin DR) : regSel (rTape (ns := DS) r) = true := by simp [regSel, rTape]

theorem rawIn_c (w : List Bool) (n L W : ℕ) : rawIn w n L W cTape = [] := by
  simp [rawIn, fun s => (sTape_ne_c (nr := DR) (ns := DS) s).symm]

theorem rawIn_r (w : List Bool) (n L W : ℕ) (r : Fin DR) : rawIn w n L W (rTape r) = [] := by
  simp [rawIn, fun s => (sTape_ne_r (nr := DR) (ns := DS) s r).symm]

theorem rawIn_s (w : List Bool) (n L W : ℕ) (s : Fin (DS + 1)) : rawIn w n L W (sTape s) =
    if s = sIN then RepairOrdinary.frame w else if s = sNT then List.replicate n true
    else if s = sLT then List.replicate L true else if s = sCT then List.replicate W true else [] := by
  simp only [rawIn, sTape_eq_iff']

/-- **The fill and the cell**: from the entry bank to the register-language state `σ0` at capacity `2W + 2`. -/
theorem fillAct_exec (w : List Bool) (n L W : ℕ) :
    Exec fillAct ⟨fun _ => 0, rawIn w n L W⟩ (wenc (2 * W + 2) (σ0 w n L W)) (11 * W + 20 + 1 + 1) := by
  have hca : sTape (nr := DR) sCT ≠ sTape sAUX := fun h => absurd (sTape_inj h) (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (sTape (nr := DR) sAUX) regSel i → rawIn w n L W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSel_s] at hi; exact absurd hi (by decide)
      · rw [regSel_c] at hi; exact absurd hi (by decide)
      · exact rawIn_r w n L W r
    · subst hi
      rw [rawIn_s]
      simp [sIN, sNT, sLT, sCT, sAUX]
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape sCT) (sTape sAUX) regSel (fun _ => 0) (rawIn w n L W) hca
    (regSel_s _) (regSel_s _) W (by rw [rawIn_s]; simp [sIN, sNT, sLT, sCT]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape sCT) (sTape sAUX) regSel (fun _ => 0) (rawIn w n L W) W 0)
    (writeAt (cTape (ns := DS) (nr := DR)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape sCT) (sTape sAUX) regSel (fun _ => 0) (rawIn w n L W) W 0).act
      (writeAt (cTape (ns := DS) (nr := DR)) false) (fun _ => .stay) = wenc (2 * W + 2) (σ0 w n L W) := by
    apply Bank.ext'
    · intro j
      simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_H_s]
        split_ifs <;> simp [σ0] <;> omega
      · rw [wenc_H_c]
        split_ifs <;> omega
      · rw [wenc_H_r]
        split_ifs <;> simp [σ0] <;> omega
    · intro j
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSel_s, Bool.false_eq_true,
          sTape_eq_iff', rawIn_s, σ0]
        by_cases hx : s = sAUX
        · subst hx; simp [sIN, sNT, sLT, sCT, sAUX]
        · simp [hx]
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSel_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := DR) (ns := DS) s).symm, rawIn_c]
        simp [σ0, UnionMachine.FrontFill.side, regSel_c, fun s => (sTape_ne_c (nr := DR) (ns := DS) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSel_r, if_true, σ0]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

/-! ## The collection -/

def carC : List (Fin (DS + 1) × Fin (DS + 1)) := [(sCar 0 0, sCar 0 5), (sCar 1 0, sCar 1 5)]
def symC : List (Fin (DS + 1) × Fin (DS + 1)) :=
  [(sSym 0 0, sSym 0 5), (sSym 1 0, sSym 1 5), (sSym 2 0, sSym 2 5), (sSym 3 0, sSym 3 5)]

/-- **The collection**: the leading `0`, the carriers' counts, the circuits' counts, the closing `0`. -/
def collectW : WM DS DR :=
  .seq (.wr sOUT false) (.seq (.fwd sOUT) (.seq (slotsC carC) (.seq (slotsC symC) (.wr sOUT false))))

def collectCost (cx cy : List ℕ) : ℕ :=
  1 + 1 + (1 + 1 + (slotsCost carC cx + 1 + (slotsCost symC cy + 1 + 1)))

theorem carC_get (i : ℕ) (hl : i < carC.length) :
    carC.get ⟨i, hl⟩ = (sCar ⟨i, by simpa [carC] using hl⟩ 0, sCar ⟨i, by simpa [carC] using hl⟩ 5) := by
  have : i < 2 := by simpa [carC] using hl
  interval_cases i <;> rfl

theorem symC_get (i : ℕ) (hl : i < symC.length) :
    symC.get ⟨i, hl⟩ = (sSym ⟨i, by simpa [symC] using hl⟩ 0, sSym ⟨i, by simpa [symC] using hl⟩ 5) := by
  have : i < 4 := by simpa [symC] using hl
  interval_cases i <;> rfl

theorem sOUT_low : sOUT.val < 14 := by decide

theorem carC_no : ∀ t ∈ carC, t.1 ≠ sOUT ∧ t.2 ≠ sOUT := by
  intro t ht
  simp only [carC, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact ⟨sCar_ne_low _ _ _ sOUT_low, sCar_ne_low _ _ _ sOUT_low⟩

theorem symC_no : ∀ t ∈ symC, t.1 ≠ sOUT ∧ t.2 ≠ sOUT := by
  intro t ht
  simp only [symC, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨sSym_ne_low _ _ _ sOUT_low, sSym_ne_low _ _ _ sOUT_low⟩

theorem carC_pw : carC.Pairwise (fun t t' => t.2 ≠ t'.1 ∧ t.2 ≠ t'.2) := by
  unfold carC
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    simp [sCar_eq_iff]
  · intro t ht
    simp at ht

theorem symC_pw : symC.Pairwise (fun t t' => t.2 ≠ t'.1 ∧ t.2 ≠ t'.2) := by
  unfold symC
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)))
  all_goals
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  · rcases ht with rfl | rfl | rfl <;> simp [sSym_eq_iff]
  · rcases ht with rfl | rfl <;> simp [sSym_eq_iff]
  · subst ht; simp [sSym_eq_iff]

theorem unaryList_append (a b : List ℕ) : unaryList (a ++ b) = unaryList a ++ unaryList b := by
  simp [unaryList]

section Col
variable (cap : ℕ)

/-- **The collection's spec**: the output stream holds `dataWord (cx ++ cy)`. -/
theorem collect_spec (σ : WState DS DR) (cx cy : List ℕ) (hx : cx.length ≤ 2) (hy : cy.length ≤ 4)
    (hcx : ∀ k : Fin 2, ∀ h : k.val < cx.length, readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = true ∧
      σ.st (sCar k 5) = List.replicate (cx.get ⟨k.val, h⟩) true ∧ σ.sh (sCar k 5) = 0)
    (hcx' : ∀ k : Fin 2, cx.length ≤ k.val → readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false)
    (hcy : ∀ i : Fin 4, ∀ h : i.val < cy.length, readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = true ∧
      σ.st (sSym i 5) = List.replicate (cy.get ⟨i.val, h⟩) true ∧ σ.sh (sSym i 5) = 0)
    (hcy' : ∀ i : Fin 4, cy.length ≤ i.val → readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = false)
    (hO : σ.st sOUT = []) (hOh : σ.sh sOUT = 0) (hOP : σ.val rOP = 0)
    (hcap : 2 * (unaryList cx).length + 2 * (unaryList cy).length + 2 ≤ cap) :
    ∃ τ : WState DS DR, WExec cap collectW σ τ (collectCost cx cy) ∧ τ.st sOUT = dataWord (cx ++ cy) ∧
      (∀ s, s ≠ sOUT → τ.st s = σ.st s) ∧ (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have w1 := WExec.wr (cap := cap) sOUT false σ
  set σ1 := σ.sets sOUT (writeTapeBit (σ.st sOUT) (σ.sh sOUT) false) with hσ1
  have f1 := WExec.fwd (cap := cap) sOUT σ1
  set σ2 := σ1.seth sOUT (σ1.sh sOUT + 1) with hσ2
  have st2 : ∀ s, s ≠ sOUT → σ2.st s = σ.st s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  have sh2 : ∀ s, s ≠ sOUT → σ2.sh s = σ.sh s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  have o2 : σ2.st sOUT = [false] := by simp [hσ2, hσ1, hO, hOh, writeTapeBit]
  obtain ⟨τ1, q1, a1, b1, c1, d1, e1, g1, i1⟩ := slotsC_spec cap carC cx σ2 (by simpa [carC] using hx)
    (fun k h hl => by
      rw [carC_get]
      obtain ⟨x1, x2, x3⟩ := hcx ⟨k, by simpa [carC] using hl⟩ h
      exact ⟨by rw [st2 _ (sCar_ne_low _ _ _ sOUT_low), sh2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x1,
        by rw [st2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x2, by rw [sh2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x3⟩)
    (fun k hl hk => by
      rw [carC_get]
      rw [st2 _ (sCar_ne_low _ _ _ sOUT_low), sh2 _ (sCar_ne_low _ _ _ sOUT_low)]
      exact hcx' ⟨k, by simpa [carC] using hl⟩ hk)
    carC_no carC_pw (by rw [o2]; simp [hσ2, hσ1, hOh]) (by simp [hσ2, hσ1, hOP]; omega)
  have csh : ∀ i : Fin 4, ∀ j, τ1.sh (sSym i j) = σ.sh (sSym i j) := by
    intro i j
    rw [e1 _ (sSym_ne_low _ _ _ sOUT_low) (fun t ht => by
      simp only [carC, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact sSym_ne_sCar _ _ _ _), sh2 _ (sSym_ne_low _ _ _ sOUT_low)]
  have cst : ∀ i : Fin 4, ∀ j, τ1.st (sSym i j) = σ.st (sSym i j) := by
    intro i j
    rw [d1 _ (sSym_ne_low _ _ _ sOUT_low), st2 _ (sSym_ne_low _ _ _ sOUT_low)]
  obtain ⟨τ2, q2, a2, b2, c2, d2, e2, g2, i2⟩ := slotsC_spec cap symC cy τ1 (by simpa [symC] using hy)
    (fun i h hl => by
      rw [symC_get]
      obtain ⟨x1, x2, x3⟩ := hcy ⟨i, by simpa [symC] using hl⟩ h
      exact ⟨by rw [cst, csh]; exact x1, by rw [cst]; exact x2, by rw [csh]; exact x3⟩)
    (fun i hl hi => by
      rw [symC_get, cst, csh]
      exact hcy' ⟨i, by simpa [symC] using hl⟩ hi)
    symC_no symC_pw b1 (by rw [c1]; simp [hσ2, hσ1, hOP]; omega)
  have w3 := WExec.wr (cap := cap) sOUT false τ2
  refine ⟨τ2.sets sOUT (writeTapeBit (τ2.st sOUT) (τ2.sh sOUT) false), ?_, ?_, ?_, ?_, ?_⟩
  · exact WExec.cast cap (WExec.seq w1 (WExec.seq f1 (WExec.seq q1 (WExec.seq q2 w3)))) rfl
      (by unfold collectCost; omega)
  · simp only [WState.sets_st, Function.update_apply, if_pos rfl]
    rw [b2, wtb_end, a2, a1, o2, dataWord, unaryList_append, ← RankBody.marks_frame, marks_append]
    simp [List.append_assoc]
  · intro s hs
    simp only [WState.sets_st, Function.update_apply, if_neg hs]
    rw [d2 s hs, d1 s hs, st2 s hs]
  · intro r hr
    simp only [WState.sets_val]
    rw [g2 r hr, g1 r hr]
    simp [hσ2, hσ1]
  · simp only [WState.sets_cell]
    rw [i2, i1]
    simp [hσ2, hσ1]

end Col

/-! ## The stage as one run -/

/-- The stage before its teardown: the fill, the inputs, the tables, the collection. -/
noncomputable def coreM := Composition.machine (Composition.machine (Composition.machine fillAct.compile
  setupW.toProg.compile) tabsM) collectW.toProg.compile

/-- **The per-call data stage** (every head back at `0`). -/
noncomputable def dataM := MaskedReset.machine coreM (fun _ => true)

section Run
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- The circuits' codes. -/
def symCodes : List ℕ := List.ofFn fun i => encodeNormalizedSymmetricThresholdCircuit (Cs i)

/-- **The call's counts**: the carriers' sizes, then the circuits' bottom counts. -/
def symCounts : List ℕ := carriers.map (·.length) ++ List.ofFn fun i => (Stars.symGates (Cs i)).length

/-- The SYM slot inputs. -/
def ocOf (i : Fin 4) : Option (NormalizedSymmetricThresholdCircuit n) :=
  if h : i.val < a' then some (Cs ⟨i.val, h⟩) else none

/-- The carrier slot inputs. -/
def oxOf (k : Fin 2) : Option (Stars.Carrier n) := carriers[k.val]?

/-- The stage's cost before the teardown. -/
noncomputable def coreCost (L W : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + setupCost n L (symCodes a' Cs) (carriers.map Stars.Carrier.code) + 1 +
    tabsCost L (ocOf a' Cs) (oxOf carriers) + 1 +
    collectCost (carriers.map (·.length)) (List.ofFn fun i => (Stars.symGates (Cs i)).length)

theorem σ0_sym (w : List Bool) (L W : ℕ) (i : Fin 4) (j : Fin 1789) :
    (σ0 w n L W).st (sSym i j) = [] := by
  have h1 := sSym_ne_low i j sIN (by decide)
  have h2 := sSym_ne_low i j sNT (by decide)
  have h3 := sSym_ne_low i j sLT (by decide)
  have h4 := sSym_ne_low i j sCT (by decide)
  have h5 := sSym_ne_low i j sAUX (by decide)
  simp [σ0, h1, h2, h3, h4, h5]

theorem σ0_car (w : List Bool) (L W : ℕ) (k : Fin 2) (j : Fin 1357) :
    (σ0 w n L W).st (sCar k j) = [] := by
  have h1 := sCar_ne_low k j sIN (by decide)
  have h2 := sCar_ne_low k j sNT (by decide)
  have h3 := sCar_ne_low k j sLT (by decide)
  have h4 := sCar_ne_low k j sCT (by decide)
  have h5 := sCar_ne_low k j sAUX (by decide)
  simp [σ0, h1, h2, h3, h4, h5]

/-- **The per-call data stage** (SYM): from `frame w` (`w` the request's word shape, circuits' and carriers' codes),
`1^n`, `1^L`, `1^W`, in `2·coreCost + 2` steps, every head back at `0`: the output stream holds
`dataWord (symCounts …)`, the request stays, and each filled slot holds T's table. -/
theorem data_step (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2) :
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun _ => 0)
        (Fin.addCases (rawIn (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (symCounts a' Cs carriers) ∧
      tout (sTape sIN) = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (sTape (sSym i 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) := by
  set w := reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl with hw
  set cap := 2 * W + 2 with hcap
  have hcl : (symCodes a' Cs).length = a' := by simp [symCodes]
  have h4 : 4 ≤ cap := by
    have hb : 1 ≤ natBitLength a' := by unfold natBitLength; omega
    have : 2 ^ 2 ≤ 2 ^ (natBitLength a' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- 0: the fill and the cell
  have s0 := Exec.step (fillAct_exec w n L W)
  -- 1: the slots' inputs
  obtain ⟨τ1, q1, d1, b1, dx1, bx1, f1, i1, v1, c1⟩ := setup_spec cap n L false (symCodes a' Cs)
    (carriers.map Stars.Carrier.code) tl (σ0 w n L W) (by rw [hcl]; exact ha) (by simpa using hk)
    (by simp [σ0, hw]) rfl (by simp [σ0, sNT, sIN]) rfl (by simp [σ0, sLT, sIN, sNT]) rfl
    (fun i => ⟨σ0_sym w L W i 0, rfl, σ0_sym w L W i 1, rfl, σ0_sym w L W i 2, rfl⟩)
    (fun k => ⟨σ0_car w L W k 0, rfl, σ0_car w L W k 1, rfl, σ0_car w L W k 2, rfl⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl hcN (by rw [hcl]; exact hcA) (by simpa using hcK) hcx hcy h4
  have s1 := Exec.step (WExec.exec cap q1)
  -- 2: the tables
  have keepS : ∀ i : Fin 4, ∀ j : Fin 1789, 3 ≤ j.val → τ1.st (sSym i j) = [] ∧ τ1.sh (sSym i j) = 0 := by
    intro i j hj
    have hnot : ∀ i', ¬ tmem (sSym i j) (symTrip i') := by
      intro i' hm
      simp only [symTrip, tmem, sSym_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sSym i j) hnot (fun k => not_tmem_carTrip_of_sym _ _ _) (sSym_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_sym w L W i j), this.2⟩
  have keepC : ∀ k : Fin 2, ∀ j : Fin 1357, 3 ≤ j.val → τ1.st (sCar k j) = [] ∧ τ1.sh (sCar k j) = 0 := by
    intro k j hj
    have hnot : ∀ k', ¬ tmem (sCar k j) (carTrip k') := by
      intro k' hm
      simp only [carTrip, tmem, sCar_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sCar k j) (fun i => not_tmem_symTrip_of_car _ _ _) hnot (sCar_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_car w L W k j), this.2⟩
  obtain ⟨σ2, s2, p2, px2, f2, v2, c2⟩ := tabs_step L cap (ocOf a' Cs) (oxOf carriers) τ1
    (fun i => by
      unfold ocOf
      split
      · next h =>
        have := d1 i (by rw [hcl]; exact h)
        simpa [symPre, symCodes] using this
      · next h => exact b1 i (by rw [hcl]; omega))
    (fun k => by
      unfold oxOf
      by_cases hk' : k.val < carriers.length
      · rw [List.getElem?_eq_getElem hk']
        have := dx1 k (by simpa using hk')
        simpa [carPre] using this
      · rw [List.getElem?_eq_none (by omega)]
        exact bx1 k (by simpa using (by omega : carriers.length ≤ k.val)))
    keepS keepC
    (fun i C hC => by
      unfold ocOf at hC
      split at hC
      · cases hC; exact hL _
      · cases hC)
    (fun k X hX => by
      unfold oxOf at hX
      exact hLX X (List.mem_of_getElem? hX))
    h2
  -- 3: the collection
  have oOUT : σ2.st sOUT = [] ∧ σ2.sh sOUT = 0 := by
    have a := f2 sOUT (fun i j => sSym_ne_low _ _ _ sOUT_low) (fun k j => sCar_ne_low _ _ _ sOUT_low)
    have b := f1 sOUT (fun i => low_not_tmem_sym _ sOUT_low i) (fun k => low_not_tmem_car _ sOUT_low k) (by decide)
    refine ⟨by rw [a.1, b.1]; simp [σ0, sOUT, sIN, sNT, sLT, sCT, sAUX], by rw [a.2, b.2]; rfl⟩
  obtain ⟨τ3, q3, o3, f3, v3, c3⟩ := collect_spec cap σ2 (carriers.map (·.length))
    (List.ofFn fun i => (Stars.symGates (Cs i)).length) (by simpa using hk) (by simpa using ha)
    (fun k h => by
      have hk' : k.val < carriers.length := by simpa using h
      have := px2 k
      simp only [oxOf, List.getElem?_eq_getElem hk', carPost] at this
      obtain ⟨x1, x2, x3, _⟩ := this
      exact ⟨x1, by simpa using x2, x3⟩)
    (fun k h => by
      have hk' : carriers.length ≤ k.val := by simpa using h
      have := px2 k
      simp only [oxOf, List.getElem?_eq_none hk', carPost] at this
      exact this)
    (fun i h => by
      have hi : i.val < a' := by simpa using h
      have := p2 i
      simp only [ocOf, dif_pos hi, symPost] at this
      obtain ⟨x1, x2, x3, _⟩ := this
      exact ⟨x1, by simpa using x2, x3⟩)
    (fun i h => by
      have hi : a' ≤ i.val := by simpa using h
      have := p2 i
      simp only [ocOf, dif_neg (by omega : ¬ i.val < a'), symPost] at this
      exact this)
    oOUT.1 oOUT.2 (by rw [v2, v1 rOP (by decide) (by decide)]; rfl) hcu
  have s3 := Exec.step (WExec.exec cap q3)
  have core : Step coreM (coreCost a' Cs carriers L W) (fun _ => 0) (rawIn w n L W) (wenc cap τ3).H (wenc cap τ3).A :=
    ((s0.seq s1).seq s2).seq s3
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc cap τ3).H i)
      (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc cap τ3).A, m, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hm.congr_in eh rfl).congr eh' rfl
  · rw [wenc_A_s, o3]
    simp [symCounts]
  · rw [wenc_A_s, f3 _ (by decide)]
    have a := f2 sIN (fun i j => sSym_ne_low _ _ _ (by decide)) (fun k j => sCar_ne_low _ _ _ (by decide))
    rw [a.1, i1]
    simp [σ0, hw]
  · intro i h
    rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low)]
    have := p2 i
    simp only [ocOf, dif_pos h, symPost] at this
    exact this.2.2.2
  · intro k h
    rw [wenc_A_s, f3 _ (sCar_ne_low _ _ _ sOUT_low)]
    have := px2 k
    simp only [oxOf, List.getElem?_eq_getElem h, carPost] at this
    exact this.2.2.2

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.Data
