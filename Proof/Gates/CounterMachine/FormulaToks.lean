import Proof.Gates.CounterMachine.ReqMom
import Proof.Gates.CounterMachine.ReqCond
import Proof.Gates.CounterMachine.FormulaStage

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-! ## Generic token lists -/

/-- Digit `j` of the stage lists `A s` (offset `o`, rates `rate`). -/
def digToks (o : ℕ) (A : ℕ → List ℤ) (rate : ℕ → ℤ) : ℕ → List Tok
  | 0 => linToks o (A 0)
  | j + 1 => linToks o (A (j + 1)) ++ [Tok.const (rate j)] ++ linToks o (A j) ++ [Tok.mul, Tok.sub]

/-- One Fermat factor `1 − (f − ρ)^{q−1}`. -/
def facToks (f : List Tok) (ρ : ℤ) (q : ℕ) : List Tok :=
  [Tok.const 1] ++ f ++ [Tok.const ρ, Tok.sub, Tok.pow (q - 1), Tok.sub]

/-- A product (`prodList`). -/
def prodToks (fs : List (List Tok)) : List Tok := fs.flatten ++ [Tok.const 1] ++ List.replicate fs.length Tok.mul

/-- The binomial constants of `Amp_e`. -/
def binom (e j : ℕ) : ℕ := (e - 1 + j).choose j

/-- `Amp_e(t)`. -/
def ampToks (e : ℕ) (t : List Tok) : List Tok :=
  [Tok.const 1, Tok.const 1] ++ t ++ [Tok.sub, Tok.pow e] ++
    ((List.range e).map fun j => [Tok.const (binom e j : ℤ)] ++ t ++ [Tok.pow j, Tok.mul]).flatten ++
    [Tok.const 0] ++ List.replicate e Tok.add ++ [Tok.mul, Tok.sub]

section Gen
variable {V : ℕ}

theorem toks_prodList : ∀ fs : List (Formula V), toks (Formula.prodList fs) = prodToks (fs.map toks)
  | [] => rfl
  | f :: fs => by
    simp only [Formula.prodList, toks, toks_prodList fs, prodToks, List.map_cons, List.flatten_cons,
      List.length_cons, List.length_map, List.replicate_succ', List.append_assoc]

theorem toks_amp (e : ℕ) (t : Formula V) : toks (Formula.amp e t) = ampToks e (toks t) := by
  simp only [Formula.amp, toks, toks_sumList, List.map_map, List.length_map, List.length_range, ampToks]
  have : (List.map (toks ∘ fun j => Formula.mul (Formula.const ((e - 1 + j).choose j : ℤ)) (Formula.pow t j))
      (List.range e)) = (List.range e).map fun j => [Tok.const (binom e j : ℤ)] ++ toks t ++ [Tok.pow j, Tok.mul] := by
    apply List.map_congr_left; intro j _; simp [toks, binom]
  rw [this]; simp [List.append_assoc]

theorem toks_fac (f : Formula V) (ρ : ℤ) (q : ℕ) :
    toks (Formula.sub (Formula.const 1) (Formula.pow (Formula.sub f (Formula.const ρ)) (q - 1))) =
      facToks (toks f) ρ q := by
  simp [toks, facToks, List.append_assoc]

theorem toks_resF (q e R : ℕ) (f : Fin R → Formula V) (ρ : Fin R → ℤ) :
    toks (resF q e f ρ) = ampToks e (prodToks ((List.finRange R).map fun i => facToks (toks (f i)) (ρ i) q)) := by
  unfold resF
  rw [toks_amp, toks_prodList, List.map_map]
  congr 2
  apply List.map_congr_left; intro i _; exact toks_fac _ _ _

end Gen

/-! ## The coefficient lists of a decoded witness -/

theorem readBlock_length (bits : List Bool) (ws : List ℕ) : (readBlock bits ws).1.length = ws.length := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih => simp [readBlock, ih]

theorem readSegments_getD (bits : List Bool) (segs : List (List ℕ)) (i : ℕ) (hi : i < segs.length) :
    ((readSegments bits segs).1.getD i []).length = (segs.getD i []).length := by
  induction segs generalizing bits i with
  | nil => simp at hi
  | cons sg segs ih =>
    cases i with
    | zero => simp [readSegments, readBlock_length]
    | succ i =>
      simp only [readSegments, List.getD_cons_succ]
      exact ih _ i (by simpa using hi)

theorem segmentWidths_getD (c : Call) (p : Params) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    (segmentWidths c p).getD (segmentIndex c s r) [] = (circ c r).coeffs.map coefWidth := by
  have hlen : ∀ m, ((List.range m).flatMap fun _ => (List.range (roleCount c.kind)).map fun r =>
      (circ c r).coeffs.map coefWidth).length = m * roleCount c.kind := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring
  have key : ∀ m, s < m → ((List.range m).flatMap fun _ => (List.range (roleCount c.kind)).map fun r =>
      (circ c r).coeffs.map coefWidth).getD (s * roleCount c.kind + r) [] = (circ c r).coeffs.map coefWidth := by
    intro m; induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h
      rw [List.range_succ, List.flatMap_append]
      by_cases hsm : s < m
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]; exact ih hsm
      · have hsm' : s = m := by omega
        subst hsm'
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
        simp [hr]
  exact key p.J hs

/-- **Coefficient lists of a decoded witness have one entry per top coefficient.** -/
theorem coef_length_of_decode (c : Call) (p : Params) (w : List Bool) (wt : Wit c.n)
    (hw : decodeWitness c p w = some wt) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    (wt.coef s r).length = (circ c r).coeffs.length := by
  unfold decodeWitness at hw
  simp only at hw
  split_ifs at hw with hok
  cases hw
  simp only [List.length_map, List.length_zip]
  have hidx : segmentIndex c s r < (segmentWidths c p).length := by
    have hl : (segmentWidths c p).length = p.J * roleCount c.kind := by
      unfold segmentWidths
      induction p.J with
      | zero => simp
      | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring
    rw [hl]; unfold segmentIndex; nlinarith
  rw [readSegments_getD _ _ _ hidx, segmentWidths_getD c p s r hs hr, List.length_map, min_self]

/-! ## The forms of a call -/

theorem finRange_map_val {β : Type} (n : ℕ) (h : ℕ → β) :
    (List.finRange n).map (fun i => h i.val) = (List.range n).map h := by
  apply List.ext_getElem <;> simp

theorem range_mul_map {β : Type} (a J : ℕ) (h : ℕ → β) :
    (List.range (a * J)).map h = (List.range a).flatMap fun r => (List.range J).map fun j => h (r * J + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show (a + 1) * J = a * J + J by ring, List.range_add, List.map_append, ih, List.range_succ,
      List.flatMap_append, List.map_map]
    simp [Function.comp_def]

section Call
variable (c : Call) (p : Params) (wt : Wit c.n)

/-- Every coefficient list has one entry per gate of its role. -/
def CoefOK : Prop :=
  (∀ r < roleCount c.kind, (circ c r).coeffs.length = (circ c r).gates.length) ∧
    ∀ s < p.J, ∀ r < roleCount c.kind, (wt.coef s r).length = (circ c r).gates.length

theorem toks_stageF {V : ℕ} (r s : ℕ) (hlen : (wt.coef s r).length = (circ c r).gates.length)
    (hV : offR c r + (circ c r).gates.length ≤ V) :
    toks (stageF (V := V) c wt r s) = linToks (offR c r) (wt.coef s r) := by
  unfold stageF; rw [← hlen]; exact toks_linF _ _ (by omega)

theorem toks_scoreF {V : ℕ} (r : ℕ) (hlen : (circ c r).coeffs.length = (circ c r).gates.length)
    (hV : offR c r + (circ c r).gates.length ≤ V) :
    toks (scoreF (V := V) c r) = linToks (offR c r) (circ c r).coeffs := by
  unfold scoreF; rw [← hlen]; exact toks_linF _ _ (by omega)

theorem toks_digF {V : ℕ} (r j : ℕ) (hlen : ∀ s ≤ j, (wt.coef s r).length = (circ c r).gates.length)
    (hV : offR c r + (circ c r).gates.length ≤ V) :
    toks (digF (V := V) c p wt r j) = digToks (offR c r) (fun s => wt.coef s r) (rateOf p) j := by
  cases j with
  | zero => exact toks_stageF c wt r 0 (hlen 0 le_rfl) hV
  | succ j =>
    simp only [digF, toks, digToks]
    rw [toks_stageF c wt r (j + 1) (hlen _ le_rfl) hV, toks_stageF c wt r j (hlen _ (by omega)) hV]
    simp [List.append_assoc]

/-- The Fermat factors of table (a), in printing order: the digits of role 0, of role 1, then the scores. -/
def resFacs (q : ℕ) (ρs : List ℕ) : List (List Tok) :=
  ((List.range (roleCount c.kind)).flatMap fun r => (List.range p.J).map fun j =>
      facToks (digToks (offR c r) (fun s => wt.coef s r) (rateOf p) j) (ρs.getD (r * p.J + j) 0 : ℤ) q) ++
    ((List.range (roleCount c.kind)).map fun r =>
      facToks (linToks (offR c r) (circ c r).coeffs) (ρs.getD (roleCount c.kind * p.J + r) 0 : ℤ) q)

theorem offR_le (r : ℕ) (hr : r < roleCount c.kind) :
    offR c r + (circ c r).gates.length ≤ (resGates c).length := by
  unfold offR circ resGates
  by_cases hp : c.kind = .pair
  · simp only [hp, if_true, List.length_append]; split_ifs <;> omega
  · have : r = 0 := by
      have : roleCount c.kind = 1 := by unfold roleCount; split <;> simp_all
      omega
    subst this; simp [hp]

/-- **The residue formula's tokens** (table (a), lem:residue-count). -/
theorem toks_resFormula (q : ℕ) (κ σ : List ℕ) (hκ : κ.length = roleCount c.kind * p.J) (hok : CoefOK c p wt) :
    toks (resFormula c p wt q κ σ) = ampToks p.e (prodToks (resFacs c p wt q (κ ++ σ))) := by
  unfold resFormula
  rw [toks_resF]
  congr 2
  rw [finRange_map_val (roleCount c.kind * p.J + roleCount c.kind)
    (fun i => facToks (toks (resForm (V := (resGates c).length) c p wt i)) (resRho c p κ σ i) q),
    List.range_add, List.map_append, range_mul_map, List.map_map]
  unfold resFacs
  congr 1
  · apply List.flatMap_congr; intro r hr; simp only [List.mem_range] at hr
    apply List.map_congr_left; intro j hj; simp only [List.mem_range] at hj
    have hi : r * p.J + j < roleCount c.kind * p.J := by nlinarith
    have hdiv : (r * p.J + j) / p.J = r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (r * p.J + j) % p.J = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [resForm, resRho, if_pos hi, hdiv, hmod]
    rw [toks_digF c p wt r j (fun s hs => hok.2 s (by omega) r hr) (offR_le c r hr)]
    rw [List.getD_append _ _ _ _ (by omega)]
  · apply List.map_congr_left; intro r hr; simp only [List.mem_range] at hr
    simp only [Function.comp_apply, resForm, resRho, if_neg (show ¬ (roleCount c.kind * p.J + r <
      roleCount c.kind * p.J) by omega), Nat.add_sub_cancel_left]
    rw [toks_scoreF c r (hok.1 r hr) (offR_le c r hr)]
    rw [List.getD_append_right _ _ _ _ (by omega), hκ, Nat.add_sub_cancel_left]

/-! ## Table (b) -/

/-- `Φ = M₁ K_J − A X` on the variables from `o`. -/
def phiToks (o r : ℕ) : List Tok :=
  [Tok.const (p.M1 : ℤ)] ++ linToks o (wt.coef (p.J - 1) r) ++ [Tok.mul, Tok.const (p.A : ℤ)] ++
    linToks o (circ c r).coeffs ++ [Tok.mul, Tok.sub]

/-- The moment tokens of `digitMoment r j` (`some j`) or `phiMoment r` (`none`). -/
def momToks (r : ℕ) : Option ℕ → List Tok
  | some j => digToks 0 (fun s => wt.coef s r) (rateOf p) j ++
      digToks (circ c r).gates.length (fun s => wt.coef s r) (rateOf p) j ++ [Tok.sub, Tok.pow (2 * p.k)]
  | none => phiToks c p wt 0 r ++ phiToks c p wt (circ c r).gates.length r ++ [Tok.sub, Tok.pow (2 * p.k)]

theorem toks_stO {V : ℕ} (o r s : ℕ) (hlen : (wt.coef s r).length = (circ c r).gates.length)
    (hV : o + (circ c r).gates.length ≤ V) : toks (stO (V := V) c wt o r s) = linToks o (wt.coef s r) := by
  unfold stO; rw [← hlen]; exact toks_linF _ _ (by omega)

theorem toks_digO {V : ℕ} (o r j : ℕ) (hlen : ∀ s ≤ j, (wt.coef s r).length = (circ c r).gates.length)
    (hV : o + (circ c r).gates.length ≤ V) :
    toks (digO (V := V) c p wt o r j) = digToks o (fun s => wt.coef s r) (rateOf p) j := by
  cases j with
  | zero => exact toks_stO c wt o r 0 (hlen 0 le_rfl) hV
  | succ j =>
    simp only [digO, toks, digToks]
    rw [toks_stO c wt o r (j + 1) (hlen _ le_rfl) hV, toks_stO c wt o r j (hlen _ (by omega)) hV]
    simp [List.append_assoc]

/-- **The moment formulas' tokens** (table (b)). -/
theorem toks_momF (r : ℕ) (hr : r < roleCount c.kind) (j : Option ℕ) (hj : ∀ i, j = some i → i < p.J)
    (hJ : 1 ≤ p.J) (hok : CoefOK c p wt) :
    toks (momF (V := 2 * (circ c r).gates.length) c p wt r j) = momToks c p wt r j := by
  cases j with
  | some j =>
    have hjJ := hj j rfl
    simp only [momF, toks, momToks]
    rw [toks_digO c p wt 0 r j (fun s hs => hok.2 s (by omega) r hr) (by omega),
      toks_digO c p wt _ r j (fun s hs => hok.2 s (by omega) r hr) (by omega)]
    simp [List.append_assoc]
  | none =>
    have hJ1 : p.J - 1 < p.J := by omega
    have hsc : ∀ o, o + (circ c r).gates.length ≤ 2 * (circ c r).gates.length →
        toks (scO (V := 2 * (circ c r).gates.length) c o r) = linToks o (circ c r).coeffs := by
      intro o ho; unfold scO; rw [← hok.1 r hr]; exact toks_linF _ _ (by rw [hok.1 r hr]; exact ho)
    simp only [momF, phiO, toks, momToks, phiToks]
    rw [toks_stO c wt 0 r (p.J - 1) (hok.2 _ hJ1 r hr) (by omega),
      toks_stO c wt _ r (p.J - 1) (hok.2 _ hJ1 r hr) (by omega), hsc 0 (by omega), hsc _ (by omega)]
    simp [List.append_assoc]

end Call

end NearCubicGates.Close.CounterMachine
