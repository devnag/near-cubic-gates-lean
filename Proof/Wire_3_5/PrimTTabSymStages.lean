import Proof.Wire_3_5.PrimTTabSymLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Corner

/-! ## The preparation -/

/-- The preparation's entry bank. -/
def prepIn (code n L : ℕ) : Fin 13 → List Bool :=
  Fin.addCases (m := 10 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σP code n L)).A (fun _ => [])

theorem prepIn_val (code n L : ℕ) (j : Fin 13) :
    prepIn code n L j = if j.val = 0 then frame (natWord code) else if j.val = 1 then [false]
      else if j.val = 2 then List.replicate n true else if j.val = 3 then List.replicate L true else [] := by
  fin_cases j <;> rfl

theorem prepStage (code n L : ℕ) : ∃ o : Fin 13 → List Bool,
    Step (Rewind.machine (prepW (nr := 0) spP).toProg.compile) (2 * prepCost (natBitLength code) n L + 2)
      (fun _ => 0) (prepIn code n L) (fun _ => 0) o ∧
    o 0 = frame (natWord code) ∧ o 1 = [false] ∧ o 2 = List.replicate n true ∧ o 3 = List.replicate L true ∧
    o 4 = frame (binary (natBitLength code) code) ∧ o 5 = List.replicate (natBitLength code + 1) true ∧
    o 6 = UnaryTemplate.tape n ∧ o 7 = List.replicate L true ∧ o 8 = List.replicate L true ∧
    o 9 = List.replicate (n + L + 1) false ∧ o 10 = List.replicate (n + L + 1) false ∧
    o 11 = List.replicate (n + L + 1) false := by
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, e5, e6, e7, R, -, -, ec⟩ := prepW_spec 0 spP code n L (σP code n L) rfl rfl rfl rfl
    rfl rfl (fun i hi => ⟨by
      show (if i.val = 0 then _ else if i.val = 1 then _ else if i.val = 2 then _ else []) = []
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)], rfl⟩)
  obtain ⟨o, st, ho⟩ := wm_step 0 (prepW spP) (σP code n L) τ _ hw
    (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 13) = Fin.castAdd 1 (0 : Fin 12) from rfl, ho]; exact e0
  · rw [show (1 : Fin 13) = Fin.castAdd 1 (1 : Fin 12) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 13) = Fin.castAdd 1 (2 : Fin 12) from rfl, ho]; exact e1
  · rw [show (3 : Fin 13) = Fin.castAdd 1 (3 : Fin 12) from rfl, ho]; exact e2
  · rw [show (4 : Fin 13) = Fin.castAdd 1 (4 : Fin 12) from rfl, ho]; exact e3
  · rw [show (5 : Fin 13) = Fin.castAdd 1 (5 : Fin 12) from rfl, ho]; exact e4
  · rw [show (6 : Fin 13) = Fin.castAdd 1 (6 : Fin 12) from rfl, ho]; exact e5
  · rw [show (7 : Fin 13) = Fin.castAdd 1 (7 : Fin 12) from rfl, ho]; exact e6
  · rw [show (8 : Fin 13) = Fin.castAdd 1 (8 : Fin 12) from rfl, ho]; exact e7
  · rw [show (9 : Fin 13) = Fin.castAdd 1 (9 : Fin 12) from rfl, ho]; exact R.1.1
  · rw [show (10 : Fin 13) = Fin.castAdd 1 (10 : Fin 12) from rfl, ho]; exact R.2.1.1
  · rw [show (11 : Fin 13) = Fin.castAdd 1 (11 : Fin 12) from rfl, ho]; exact R.2.2.1

/-! ## The scan -/

/-- The scan's entry bank at register capacity `cap`. -/
def scanIn (cap : ℕ) (w : List Bool) : Fin 9 → List Bool :=
  Fin.addCases (m := 5 + 2 + 1) (n := 1) (motive := fun _ => List Bool) (wenc cap (σS w)).A (fun _ => [])

theorem scanIn_val (cap : ℕ) (w : List Bool) (j : Fin 9) :
    scanIn cap w j = if j.val = 0 then w else if j.val = 1 then [false] else if j.val = 7 then
      List.replicate (cap + 1) false else [] := by
  fin_cases j <;> simp [scanIn, σS, wenc, role, regTape] <;> rfl

theorem scanStage {n : ℕ} (cap x : ℕ) (y : List Bool) (G : List (NormalizedThresholdGate n)) (w : List Bool)
    (hw : w = natWord x ++ (frame y ++ tabSeg G)) (hk : natBitLength x ≤ cap) : ∃ o : Fin 9 → List Bool,
    Step (Rewind.machine (scanW scS rgS).toProg.compile) (2 * (scanCost x y (tabH G) + 4) + 2) (fun _ => 0)
      (scanIn cap w) (fun _ => 0) o ∧
    o 0 = w ∧ o 1 = [false] ∧ o 2 = tabSeg G ∧ o 3 = tabSeg G ∧ o 4 = false :: List.replicate (tabH G) true ∧
    o 5 = List.replicate G.length true ∧ o 6 = [] ∧ o 7 = List.replicate (cap + 1) false := by
  obtain ⟨τ, hwx, ⟨hA, -, hB, -, hH, -, hG, -⟩, h0, hv, hc, oth⟩ := scan_spec cap scS rgS x y G (σS w)
    (by simp [σS, scS, hw]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hk
  obtain ⟨o, st, ho⟩ := wm_step cap (scanW scS rgS) (σS w) τ _ hwx (wenc_H_zero cap _ (fun _ => rfl) (fun _ => rfl))
  have h5 := oth 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 9) = Fin.castAdd 1 (0 : Fin 8) from rfl, ho]; exact h0
  · rw [show (1 : Fin 9) = Fin.castAdd 1 (1 : Fin 8) from rfl, ho]; show [τ.cell] = [false]; rw [hc]; rfl
  · rw [show (2 : Fin 9) = Fin.castAdd 1 (2 : Fin 8) from rfl, ho]; exact hA
  · rw [show (3 : Fin 9) = Fin.castAdd 1 (3 : Fin 8) from rfl, ho]; exact hB
  · rw [show (4 : Fin 9) = Fin.castAdd 1 (4 : Fin 8) from rfl, ho]; exact hH
  · rw [show (5 : Fin 9) = Fin.castAdd 1 (5 : Fin 8) from rfl, ho]; exact hG
  · rw [show (6 : Fin 9) = Fin.castAdd 1 (6 : Fin 8) from rfl, ho]; exact h5.1
  · rw [show (7 : Fin 9) = Fin.castAdd 1 (7 : Fin 8) from rfl, ho]
    show regTape cap (τ.val 0) = _; rw [hv]; simp [σS, regTape, List.replicate_succ]

/-! ## The unary width and the table -/

/-- The table's entry bank at register capacity `cap`. -/
def tabIn (cap : ℕ) (seg : List Bool) (n h : ℕ) : Fin 11 → List Bool :=
  Fin.addCases (m := 5 + 2 + 3) (n := 1) (motive := fun _ => List Bool) (wenc cap (σT seg n h)).A (fun _ => [])

theorem tabIn_val (cap : ℕ) (seg : List Bool) (n h : ℕ) (j : Fin 11) :
    tabIn cap seg n h j = if j.val = 0 then seg else if j.val = 1 then [false] else if j.val = 2 then seg
      else if j.val = 3 then List.replicate n true else if j.val = 4 then false :: List.replicate h true
      else if 7 ≤ j.val ∧ j.val ≤ 9 then List.replicate (cap + 1) false else [] := by
  fin_cases j <;> simp [tabIn, σT, wenc, role, regTape] <;> rfl

def tabCost (n h m : ℕ) : ℕ := 10 * h + 7 + 1 + (m * (gateCost n h + 2) + 5)

theorem tabStage {n : ℕ} (cap h : ℕ) (G : List (NormalizedThresholdGate n)) (hok : ∀ g ∈ G, GateOk cap h g) :
    ∃ o : Fin 11 → List Bool,
    Step (Rewind.machine tabW2.toProg.compile) (2 * tabCost n h G.length + 2) (fun _ => 0)
      (tabIn cap (tabSeg G) n h) (fun _ => 0) o ∧
    o 3 = List.replicate n true ∧ o 5 = gatesW h G ∧ o 6 = List.replicate h true := by
  obtain ⟨τ1, s1, eO, -, eR, eRh, oth1, v1, c1⟩ := onesW_spec cap scS h (σT (tabSeg G) n h) (by simp [σT, scS])
    rfl rfl
  have hs1 : Std smT rgT τ1 h n := by
    have o2 := oth1 2 (by decide) (by decide); have o4 := oth1 4 (by decide) (by decide)
    refine ⟨?_, ?_, ?_, eRh, ?_, ?_, ?_, ?_⟩
    · show τ1.st 2 = _; rw [o2.1]; rfl
    · show τ1.sh 2 = _; rw [o2.2]; rfl
    · show τ1.st 3 = _; exact eR
    · show τ1.sh 4 = (τ1.st 4).length; rw [o4.1, o4.2]; rfl
    · show τ1.val 0 = 0; rw [v1]; rfl
    · show τ1.val 1 = 0; rw [v1]; rfl
    · show τ1.val 2 = 0; rw [v1]; rfl
  have o0 := oth1 0 (by decide) (by decide); have o1 := oth1 1 (by decide) (by decide)
  obtain ⟨τ, s2, eT, eA, eB, eN, eH, -, -, -, fr⟩ := tableW_spec cap smT rgT h n G τ1 hs1
    (by show τ1.st 0 = _; rw [o0.1]; rfl) (by show τ1.sh 0 = _; rw [o0.2]; rfl)
    (by show τ1.st 1 = _; rw [o1.1]; rfl) (by show τ1.sh 1 = _; rw [o1.2]; rfl) hok
  have run : WExec cap tabW2 (σT (tabSeg G) n h) τ (tabCost n h G.length) :=
    WExec.mono (WExec.seq s1 s2) (by unfold tabCost; omega)
  obtain ⟨o, st, ho⟩ := wm_step cap tabW2 (σT (tabSeg G) n h) τ _ run
    (wenc_H_zero cap _ (fun _ => rfl) (fun _ => rfl))
  have o5 := fr.1 5 (by decide)
  have o4 := oth1 4 (by decide) (by decide)
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (3 : Fin 11) = Fin.castAdd 1 (3 : Fin 10) from rfl, ho]; show τ.st 2 = _
    exact eN.trans hs1.1
  · rw [show (5 : Fin 11) = Fin.castAdd 1 (5 : Fin 10) from rfl, ho]; show τ.st 4 = _
    have e4 : τ.st 4 = τ1.st 4 ++ gatesW h G := eT
    rw [e4, o4.1]; rfl
  · rw [show (6 : Fin 11) = Fin.castAdd 1 (6 : Fin 10) from rfl, ho]; show τ.st 5 = _
    rw [o5.1]; exact eO.trans (by simp [σT, scS])

end NearCubicWires.WireExponent3_5.PrimT.SymTab
