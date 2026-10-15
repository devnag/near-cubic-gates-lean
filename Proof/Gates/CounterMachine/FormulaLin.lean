import Proof.Gates.CounterMachine.FormulaTok

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)
open NearCubicGates.Close.Tabulator

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Value level -/

theorem toks_sumList {V : ℕ} : ∀ fs : List (Formula V),
    toks (Formula.sumList fs) = (fs.map toks).flatten ++ [Tok.const 0] ++ List.replicate fs.length Tok.add
  | [] => rfl
  | f :: fs => by
    simp only [Formula.sumList, toks, toks_sumList fs, List.map_cons, List.flatten_cons, List.length_cons,
      List.replicate_succ', List.append_assoc]

/-- The tokens of `Σ_{t<m} a_t x_{o+t}`. -/
def linToks (o : ℕ) (as : List ℤ) : List Tok :=
  ((List.range as.length).map fun t => [Tok.const (as.getD t 0), Tok.var (o + t), Tok.mul]).flatten ++
    [Tok.const 0] ++ List.replicate as.length Tok.add

theorem toks_linF {V : ℕ} (o : ℕ) (as : List ℤ) (hV : o + as.length ≤ V) :
    toks (linF (V := V) o as.length as) = linToks o as := by
  unfold linF linToks
  rw [toks_sumList, List.length_map, List.length_range, List.map_map]
  congr 3
  apply List.map_congr_left
  intro t ht
  simp only [List.mem_range] at ht
  simp only [Function.comp_apply, toks, varN, dif_pos (show o + t < V by omega)]
  rfl

/-! ## The printer -/

section Lin
variable (O I : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr)

def linBody : WM ns nr :=
  .seq (tokConstIn O I Rg) (.seq (tokTagReg O Rg 1 (Rg 9)) (.seq (tokLit O Rg .mul) (.inc (Rg 9))))

def linBodyCost (z : ℤ) (x : ℕ) : ℕ :=
  16 * (natWord 0).length + 1 + (60 * (NearCubicGates.Close.Interfaces.intWord z).length + 121) + 1 +
    (16 * (natWord 1).length + 1 + printCost x + 1 + (16 * (tokWord .mul).length + 1 + 3))

theorem linBody_spec (hIO : I ≠ O) (o t : ℕ) (z : ℤ) (pre rest : List Bool) (σ : WState ns nr) (h : PrRest O Rg σ)
    (hst : σ.st I = pre ++ enc true (NearCubicGates.Close.Interfaces.intWord z) ++ rest) (hsh : σ.sh I = pre.length)
    (hX : σ.val (Rg 9) = o + t) (V : ℕ)
    (hV : σ.val (Rg 7) + (marks (tokWord (.const z) ++ tokWord (.var (o + t)) ++ tokWord .mul)).length ≤ V)
    (hcap : V + 7 * (o + t) + 20 ≤ cap) :
    WExec cap (linBody O I Rg) σ (((appendO σ O (Rg 7) (marks (tokWord (.const z) ++ tokWord (.var (o + t)) ++
      tokWord .mul))).seth I (pre.length + (enc true (NearCubicGates.Close.Interfaces.intWord z)).length)).setv (Rg 9)
      (o + t + 1)) (linBodyCost z (o + t)) := by
  have hrn : ∀ {a b : Fin 16}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  have hml : ∀ w : List Bool, (marks w).length = 2 * w.length := marks_length
  simp only [marksApp, List.length_append, hml] at hV
  have hc0 : (tokWord (.const z)).length = (natWord 0).length + (NearCubicGates.Close.Interfaces.intWord z).length := by
    simp [tokWord]
  have hcv : (tokWord (.var (o + t))).length = (natWord 1).length + (natWord (o + t)).length := by simp [tokWord]
  have h1 := tokConstIn_spec cap O I Rg hIO z pre rest σ h hst hsh (by omega)
  set σ1 := (appendO σ O (Rg 7) (marks (tokWord (.const z)))).seth I
    (pre.length + 2 * (NearCubicGates.Close.Interfaces.intWord z).length) with hσ1
  have h1r : PrRest O Rg σ1 := ⟨by simp [hσ1, appendO, Function.update_of_ne hIO.symm, h.out], fun i hi => by
    simp [hσ1, appendO, Function.update_of_ne (hrn (show i ≠ 7 by revert i; decide))]; exact h.zero i hi⟩
  have v1 : σ1.val (Rg 9) = o + t := by
    simp [hσ1, appendO, Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 7 by decide)), hX]
  have v17 : σ1.val (Rg 7) = σ.val (Rg 7) + 2 * (tokWord (.const z)).length := by
    simp [hσ1, appendO, marks_length]
  have hv9 : ∀ i : Fin 16, i.val ≤ 8 → Rg i ≠ Rg 9 := fun i hi => hrn (by intro e; subst e; simp at hi)
  have h2 := tokTagReg_spec cap O Rg 1 (Rg 9) hv9 σ1 h1r (by rw [v17, v1]; omega)
  rw [v1] at h2
  set σ2 := appendO σ1 O (Rg 7) (marks (natWord 1 ++ natWord (o + t))) with hσ2
  have h2r : PrRest O Rg σ2 := h1r.append O Rg _
  have h3 := tokLit_spec cap O Rg .mul σ2 h2r (by
    simp only [hσ2, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_self, v17,
      marks_length, List.length_append]
    omega)
  set σ3 := appendO σ2 O (Rg 7) (marks (tokWord .mul)) with hσ3
  have v3 : σ3.val (Rg 9) = o + t := by
    simp [hσ3, hσ2, appendO, Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 7 by decide)), v1]
  have h4 := WExec.inc (cap := cap) (Rg 9) σ3 (by rw [v3]; omega)
  rw [v3] at h4
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by unfold linBodyCost; omega)
  have htv : tokWord (.var (o + t)) = natWord 1 ++ natWord (o + t) := rfl
  rw [hσ3, hσ2, appendO_append, htv]
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hIO.symm, marksApp]; ring
    · by_cases hjI : j = I
      · subst hjI; simp [hσ1, appendO, Function.update_of_ne hj, enc_length, stp]
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjI]
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hIO.symm, marksApp]
    · simp [hσ1, appendO, Function.update_of_ne hj]
  · funext r; by_cases c9 : r = Rg 9
    · subst c9; simp [hσ1, appendO, Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 7 by decide))]
    · by_cases c7 : r = Rg 7
      · subst c7; simp [hσ1, appendO, Function.update_of_ne c9, marksApp]; ring
      · simp [hσ1, appendO, Function.update_of_ne c9, Function.update_of_ne c7]
  · simp [hσ1, appendO]

theorem map_eq_range {α β : Type} (f : α → β) (d : α) (as : List α) :
    as.map f = (List.range as.length).map fun i => f (as.getD i d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem flatMap_tok (ts : List (List Tok)) :
    (ts.flatten).flatMap tokWord = (ts.map fun l => l.flatMap tokWord).flatten := by
  induction ts with
  | nil => rfl
  | cons l ts ih => simp [List.flatten_cons, List.flatMap_append, ih]

theorem flatMap_rep (t : Tok) (m : ℕ) :
    (List.replicate m t).flatMap tokWord = (List.replicate m (tokWord t)).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ih]

theorem linToks_words (o : ℕ) (as : List ℤ) :
    (linToks o as).flatMap tokWord = ((List.range as.length).map fun t => tokWord (.const (as.getD t 0)) ++
      tokWord (.var (o + t)) ++ tokWord .mul).flatten ++ tokWord (.const 0) ++
      (List.replicate as.length (tokWord .add)).flatten := by
  unfold linToks
  rw [List.flatMap_append, List.flatMap_append, flatMap_tok, flatMap_rep, List.map_map]
  congr 3
  apply List.map_congr_left; intro t _; simp [List.append_assoc]

/-- **The linear-form printer**: `M` holds the number of coefficients, `Rg 9` the first variable index. -/
def linP (M : Fin nr) : WM ns nr :=
  .seq (copyR M (Rg 10) (Rg 8))
  (.seq (listLoop (Rg 10) (linBody O I Rg))
  (.seq (tokLit O Rg (.const 0))
  (.seq (copyR M (Rg 10) (Rg 8)) (listLoop (Rg 10) (tokLit O Rg .add)))))

def linCost (o : ℕ) (as : List ℤ) : ℕ :=
  18 * as.length + 3 + 1 + (((List.range as.length).map fun i => linBodyCost (as.getD (0 + i) 0) (o + (0 + i)) + 4).sum
    + 1 + 1 + (16 * (tokWord (.const 0)).length + 1 + (18 * as.length + 3 + 1 +
    (as.length * (16 * (tokWord .add).length + 4) + 1))))

theorem linP_spec (hIO : I ≠ O) (M : Fin nr) (hM : ∀ i : Fin 16, i.val ≤ 10 → Rg i ≠ M) (o : ℕ) (as : List ℤ)
    (pre rest : List Bool) (σ : WState ns nr) (h : PrRest O Rg σ)
    (hst : σ.st I = pre ++ (as.map fun a => enc true (NearCubicGates.Close.Interfaces.intWord a)).flatten ++ rest)
    (hsh : σ.sh I = pre.length) (hX : σ.val (Rg 9) = o) (hK : σ.val (Rg 10) = 0) (hMv : σ.val M = as.length)
    (V : ℕ) (hV : σ.val (Rg 7) + (marks ((linToks o as).flatMap tokWord)).length ≤ V)
    (hcap : V + 7 * (o + as.length) + 40 ≤ cap) :
    WExec cap (linP O I Rg M) σ (((appendO σ O (Rg 7) (marks ((linToks o as).flatMap tokWord))).seth I
      (pre.length + (as.map fun a => enc true (NearCubicGates.Close.Interfaces.intWord a)).flatten.length)).setv (Rg 9)
      (o + as.length)) (linCost o as) := by
  have hrn : ∀ {a b : Fin 16}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  set m := as.length with hm
  have hml : ∀ w : List Bool, (marks w).length = 2 * w.length := marks_length
  rw [linToks_words, hml] at hV
  simp only [List.length_append] at hV
  rw [← hm] at hV
  -- copy the count
  have e1 := copyR_spec cap (v := M) (d := Rg 10) (t := Rg 8) (hM 10 (by decide)).symm (hM 8 (by decide)).symm
    (hrn (by decide)) σ (h.zero 8 (by decide)) (by rw [hK, hMv]; omega)
  rw [hK, hMv, Nat.zero_add] at e1
  set σ1 := σ.setv (Rg 10) m with hσ1
  have h1r : PrRest O Rg σ1 := ⟨by simp [hσ1, h.out], fun i hi => by
    simp [hσ1, Function.update_of_ne (hrn (show i ≠ 10 by revert i; decide))]; exact h.zero i hi⟩
  -- the terms
  have hin : (as.map fun a => enc true (NearCubicGates.Close.Interfaces.intWord a)).flatten =
      ((List.range m).map fun i => enc true (NearCubicGates.Close.Interfaces.intWord (as.getD (0 + i) 0))).flatten := by
    rw [map_eq_range _ 0, hm]; simp only [Nat.zero_add]
  have e2 := idxLoop_spec cap I O hIO (Rg 10) (Rg 9) (Rg 7) (hrn (by decide)) (hrn (by decide)) (hrn (by decide))
    (linBody O I Rg) (fun t => enc true (NearCubicGates.Close.Interfaces.intWord (as.getD t 0)))
    (fun t => tokWord (.const (as.getD t 0)) ++ tokWord (.var (o + t)) ++ tokWord .mul)
    (fun t => linBodyCost (as.getD t 0) (o + t)) (PrRest O Rg) o m V
    (fun σ x hσ => ⟨by simp [hσ.out, Function.update_of_ne hIO.symm], fun i hi => by simpa using hσ.zero i hi⟩)
    (fun σ x hσ => ⟨by simp [hσ.out], fun i hi => by
      simp [Function.update_of_ne (hrn (show i ≠ 10 by revert i; decide))]; exact hσ.zero i hi⟩)
    (fun σ x hσ => ⟨by simp [hσ.out], fun i hi => by
      simp [Function.update_of_ne (hrn (show i ≠ 9 by revert i; decide))]; exact hσ.zero i hi⟩)
    (fun σ w hσ => hσ.append O Rg w)
    (fun t ht pre' rest' σ' hσ' hst' hsh' ho' hX' hV' =>
      linBody_spec cap O I Rg hIO o t (as.getD t 0) pre' rest' σ' hσ' hst' hsh' hX' V hV' (by omega))
    m 0 pre rest σ1 (by omega) h1r (by simp only [hσ1, WState.setv_st]; rw [hst, hin])
    (by simp [hσ1, hsh]) (by simp [hσ1, h.out])
    (by simp [hσ1]) (by omega) (by simp [hσ1, Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 10 by decide)), hX])
    (by
      have e : σ1.val (Rg 7) = σ.val (Rg 7) := by
        simp [hσ1, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 10 by decide))]
      rw [e, hml]; simp only [Nat.zero_add]; omega)
  set G := ((List.range m).map fun i => enc true (NearCubicGates.Close.Interfaces.intWord (as.getD (0 + i) 0))).flatten
    with hG
  set U := ((List.range m).map fun i => tokWord (.const (as.getD (0 + i) 0)) ++ tokWord (.var (o + (0 + i))) ++
    tokWord .mul).flatten with hU
  set σ2 := (((appendO σ1 O (Rg 7) (marks U)).setv (Rg 10) 0).seth I (pre.length + G.length)).setv (Rg 9) (o + 0 + m)
    with hσ2
  have h2r : PrRest O Rg σ2 := ⟨by simp [hσ2, appendO, Function.update_of_ne hIO.symm, h1r.out], fun i hi => by
    simp [hσ2, appendO, Function.update_of_ne (hrn (show i ≠ 9 by revert i; decide)),
      Function.update_of_ne (hrn (show i ≠ 10 by revert i; decide)),
      Function.update_of_ne (hrn (show i ≠ 7 by revert i; decide))]; exact h1r.zero i hi⟩
  have hUl : (marks U).length = 2 * U.length := hml U
  have hU0 : U = ((List.range m).map fun t => tokWord (.const (as.getD t 0)) ++ tokWord (.var (o + t)) ++
      tokWord .mul).flatten := by simp [hU]
  have v27 : σ2.val (Rg 7) = σ.val (Rg 7) + 2 * U.length := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 10 by decide)),
      Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 9 by decide)), hml]
  have e3 := tokLit_spec cap O Rg (.const 0) σ2 h2r (by rw [v27, hU0]; omega)
  set σ3 := appendO σ2 O (Rg 7) (marks (tokWord (.const 0))) with hσ3
  have hMne : ∀ i : Fin 16, i.val ≤ 10 → M ≠ Rg i := fun i hi => (hM i hi).symm
  have v3M : σ3.val M = m := by
    simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (hMne 7 (by decide)), Function.update_of_ne (hMne 9 (by decide)),
      Function.update_of_ne (hMne 10 (by decide)), hMv]
  have v3K : σ3.val (Rg 10) = 0 := by
    simp [hσ3, hσ2, appendO, Function.update_of_ne (hrn (show (10 : Fin 16) ≠ 7 by decide)),
      Function.update_of_ne (hrn (show (10 : Fin 16) ≠ 9 by decide))]
  have e4 := copyR_spec cap (v := M) (d := Rg 10) (t := Rg 8) (hM 10 (by decide)).symm (hM 8 (by decide)).symm
    (hrn (by decide)) σ3 ((h2r.append O Rg _).zero 8 (by decide)) (by rw [v3K, v3M]; omega)
  rw [v3K, v3M, Nat.zero_add] at e4
  set σ4 := σ3.setv (Rg 10) m with hσ4
  have v47 : σ4.val (Rg 7) = σ.val (Rg 7) + 2 * U.length + 2 * (tokWord (.const 0)).length := by
    simp [hσ4, hσ3, appendO, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 10 by decide)), v27, hml]
  have e5 := constLoop_spec cap O (Rg 10) (Rg 7) (hrn (by decide)) (tokLit O Rg .add) (tokWord .add)
    (16 * (tokWord .add).length) V (fun σ' ho hb => emitMarks_spec cap O (Rg 7) (tokWord .add) σ' ho (by
      rw [hml] at hb; omega)) m σ4 (by simp [hσ4, hσ3, appendO, h2r.out]) (by simp [hσ4]) (by omega)
    (by
      have hrep : (List.replicate m (tokWord Tok.add)).flatten.length = m * (tokWord Tok.add).length := by simp
      have hadd : (tokWord Tok.add).length = 5 := by decide
      have hUeq : U.length = ((List.range m).map fun t => tokWord (.const (as.getD t 0)) ++ tokWord (.var (o + t)) ++
          tokWord .mul).flatten.length := by rw [hU0]
      rw [v47, hml, hUeq, hadd]; rw [hrep, hadd] at hV; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by unfold linCost; rw [← hm])
  have hw := linToks_words o as
  rw [← hm, ← hU0] at hw
  have hGl : G.length = (as.map fun a => enc true (NearCubicGates.Close.Interfaces.intWord a)).flatten.length := by
    rw [hin]
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj
      simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hIO.symm, hw, marksApp, hml]; ring
    · by_cases hjI : j = I
      · subst hjI; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, hGl]
      · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjI]
  · funext j; by_cases hj : j = O
    · subst hj
      simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hIO.symm, hw, marksApp]
    · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
  · funext r
    by_cases c10 : r = Rg 10
    · subst c10; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne (hrn (show (10 : Fin 16) ≠ 9 by decide)),
        Function.update_of_ne (hrn (show (10 : Fin 16) ≠ 7 by decide)), hK]
    · by_cases c9 : r = Rg 9
      · subst c9; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 10 by decide)),
          Function.update_of_ne (hrn (show (9 : Fin 16) ≠ 7 by decide))]
      · by_cases c7 : r = Rg 7
        · subst c7
          simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 10 by decide)),
            Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 9 by decide)), hw, marksApp, hml]; ring
        · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne c10, Function.update_of_ne c9,
            Function.update_of_ne c7]
  · simp [hσ4, hσ3, hσ2, hσ1, appendO]
