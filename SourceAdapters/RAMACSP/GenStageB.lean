import SourceAdapters.RAMACSP.GenBank

/-!
# The generator's printing stages around the constraint circuit

Paper: `def:acsp` (the fields after `irr`: "an affine subspace `H ⊆ F` of dimension `m_H`, neighbors
`N_ν(X) = a_ν X + b_ν` … and an affine subspace `I ⊆ H` of dimension `m`", each given by a basis and an offset);
`app:affine-embedding`, "`H` be their span, with offset `0`" (basis masks `2^b`, `b < m_H`), "Neighbors" and
"Input subspace" ("Let `I` have offset `E(T,0,0,0,0)` and the basis `e_{k_N+ℓ_S}, …, e_{k_N+ℓ_S+ω−1}`,
`e_0, …, e_{m−ω−1}`, in this order"); `lem:generator` ("outputs `x̄` and the instance").

- `stageB1` prints `natWord irr ++ listWord natWord hBasis ++ natWord 0 ++ listWord pairWord nbr` (`irr` in program
  variable `37`);
- `stageB2` prints `listWord natWord iBasis ++ natWord iOffset`: `natWord m`, the `ω` column masks
  `2^(k_N+ℓ_S+j)`, the `m − ω` lane masks `2^j`, and the offset `2^τ`.

**Totality** (`cor:short-pcp-clock`: "The construction does not test the promise"). Both stages print their words on
every clock request, including `n < 2` and `n > t`. The input dimension `m` is not bounded by `t` alone: the
bound is `m ≤ n + ω` (`inExp_le`), so every printed number of `stageB2` has at most `n + f + 1` bits. The run
constant `G.K` exceeds `n + f + |bits t|` on every request (`ParamFit`, the condition under which `paramsP` computes
the numbers at all), and the loop bounds `ω`, `m − ω` are below `G.K ≤ G.N`. No invalid-request branch exists.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-! ## Loops printing `natWord`s -/

theorem loopNat (lv : Var) (hlv : lv.val = 50 ∨ lv.val = 51) (s : FS) (lenE : E) (n : ℕ)
    (hn : min (evalE G s lenE) G.N = n) (g : E) (fv : ℕ → ℕ)
    (hg : ∀ j < n, ∀ t : FS, (∀ i : Var, i ∉ LW → t.env i = s.env i) → t.env lv = j → t.fl = s.fl → t.fp = s.fp →
      evalE G t g = fv j)
    (hb : ∀ j < n, natBitLength (fv j) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Em (lv :: SW) s (evalS G (.loop lv lenE (emitNatE g)) s) ((List.range n).flatMap (fun j => natWord (fv j))) := by
  have hlvW : lv ∈ LW := mem_LW.mpr (Or.inr (by omega))
  have hlvS : lv ∉ SW := not_mem_SW (by omega)
  refine (Em_loop lv lenE (emitNatE g) (lv :: SW) (by simp) s n hn (fun _ => True) trivial
    (fun j => natWord (fv j)) (fun j hj t _ te => ⟨trivial, ?_⟩)).2
  have hv : evalE G (t.setv lv j) g = fv j := hg j hj _ (fun i hi => by
      simp only [FS.setv_env, Function.update_apply]
      rw [if_neg (show i ≠ lv from fun e => hi (e ▸ hlvW))]
      exact te.env i (fun hm => by
        simp only [List.mem_cons] at hm; rcases hm with hm | hm
        · exact hi (hm ▸ hlvW)
        · exact hi (SW_sub_LW i hm))) (by simp) te.fl te.fp
  have := emitNatE_spec (G := G) (t.setv lv j) g (by rw [hv]; exact hb j hj) hN
  rw [hv] at this
  exact this.mono (fun x hx => List.mem_cons_of_mem _ hx)

theorem lvSW_sub (lv : Var) (hlv : lv.val = 50 ∨ lv.val = 51) : ∀ x ∈ lv :: SW, x ∈ LW := fun x hx => by
  simp only [List.mem_cons] at hx; rcases hx with rfl | hx
  · exact mem_LW.mpr (Or.inr (by omega))
  · exact SW_sub_LW x hx

theorem emitNatE_val (s : FS) (e : E) (v : ℕ) (hv : evalE G s e = v) (hL : natBitLength v + 2 ≤ G.K)
    (hN : G.K ≤ G.N) : Em LW s (evalS G (emitNatE e) s) (natWord v) := by
  have := emitNatE_spec (G := G) s e (by rw [hv]; exact hL) hN
  rw [hv] at this; exact this.mono SW_sub_LW

theorem listWord_nat_range (n : ℕ) (fv : ℕ → ℕ) :
    listWord natWord ((List.range n).map fv) = natWord n ++ (List.range n).flatMap (fun j => natWord (fv j)) := by
  simp [listWord, List.flatMap, Function.comp_def]

/-! ## Stage B1 -/

variable (V : Verifier)

/-- **Stage B1**: `natWord irr`, the basis of `H`, its offset `0`, the neighbor pairs. -/
def stageB1 : S :=
  .seq (emitNatE (.v 37)) (.seq (emitNatE (.v 35)) (.seq (.loop 50 (.v 35) (emitNatE (two (.v 50))))
    (.seq (emitNatE (.k 0)) bankPairP)))

/-- The size condition of the printing stages. -/
def BFit (t : ℕ) (G : Glob) : Prop :=
  fieldExp V t + 8 ≤ G.K ∧ 16 * 2 ^ colExp V t + 2 * laneExp V t + 2 * tau V t + 2 ≤ G.N ∧ G.K ≤ G.N

theorem lv_own {r : ClockRequest} {s : FS} (h : PV V r s) : LV (ownLayout V r.2) s := ⟨h.k, h.ell, h.q⟩

theorem stageB1_spec (r : ClockRequest) (s : FS) (h : PV V r s) (irr : ℕ) (h37 : s.env 37 = irr)
    (hirr : irr < 2 ^ (fieldExp V r.2 + 1)) (hfit : BFit V r.2 G) :
    Em LW s (evalS G (stageB1) s) (natWord irr ++ listWord natWord ((List.range (domExp V r.2)).map (2 ^ ·)) ++
      natWord 0 ++ listWord ACSP.Affine.Instance.pairWord
        ((Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b)))) := by
  obtain ⟨hK, hN, hKN⟩ := hfit
  have hmf := domExp_add_two_le_fieldExp V r.2
  have hm : (ownLayout V r.2).m = domExp V r.2 := rfl
  have hcap := cap_add G
  have hmK : 2 ^ domExp V r.2 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnb : ∀ x, x < 2 ^ (fieldExp V r.2 + 1) → natBitLength x + 2 ≤ G.K := fun x hx => by
    have := natBitLength_le_of_lt (by omega) hx; omega
  have hnbm : ∀ x, x < 2 ^ domExp V r.2 → natBitLength x + 2 ≤ G.K := fun x hx => hnb x (lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [listWord_nat_range]
  simp only [List.append_assoc]
  unfold stageB1
  refine Em_acc (emitNatE_val (G := G) s (.v 37) irr (by rw [eE_v, h37]) (hnb irr hirr) hKN) (fun t1 a1 => ?_)
  have u1 : ∀ i : Var, i ∉ LW → t1.env i = s.env i := a1.env
  have h35 : t1.env 35 = domExp V r.2 := by rw [u1 35 (by decide), h.mH]
  refine Em_acc (emitNatE_val (G := G) t1 (.v 35) _ (by rw [eE_v, h35]) (hnbm _ Nat.lt_two_pow_self) hKN)
    (fun t2 a2 => ?_)
  have u2 : ∀ i : Var, i ∉ LW → t2.env i = s.env i := fun i hi => (a2.env i hi).trans (u1 i hi)
  refine Em_acc ((loopNat 50 (Or.inl rfl) t2 (.v 35) (domExp V r.2) (by
      rw [eE_v, u2 35 (by decide), h.mH]; exact min_eq_left (by omega))
    (two (.v 50)) (2 ^ ·) (fun j hj u hu h50 _ _ => eE_two (by rw [eE_v, h50]) (by omega))
    (fun j hj => hnbm _ (Nat.pow_lt_pow_right (by norm_num) hj)) hKN).mono (lvSW_sub 50 (Or.inl rfl)))
    (fun t3 a3 => ?_)
  have u3 : ∀ i : Var, i ∉ LW → t3.env i = s.env i := fun i hi => (a3.env i hi).trans (u2 i hi)
  refine Em_acc ((emitNatK_spec (G := G) t3 0 (by omega) (by simp [natBitLength]; omega) hKN).mono SW_sub_LW)
    (fun t4 a4 => ?_)
  have u4 : ∀ i : Var, i ∉ LW → t4.env i = s.env i := fun i hi => (a4.env i hi).trans (u3 i hi)
  exact bankPairP_spec (ownLayout V r.2) t4 (lv_of (lv_own V h) u4) (by rw [hm]; omega) hKN
    (by show 16 * 2 ^ colExp V r.2 + 2 * laneExp V r.2 ≤ G.N; omega)

/-! ## Stage B2: the input subspace -/

/-- The input dimension is at most `n + ω`, on every request. -/
theorem inExp_le (r : ClockRequest) : inExp V r ≤ r.1.1 + wordExp V r.2 := by
  rw [inExp_eq]; apply Nat.clog_le_of_le_pow
  have h1 : r.1.1 + 1 ≤ 2 ^ (r.1.1 + wordExp V r.2) := by
    have := Nat.lt_two_pow_self (n := r.1.1)
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show r.1.1 ≤ r.1.1 + wordExp V r.2 by omega); omega
  have h2 : wordW V r.2 ≤ 2 ^ (r.1.1 + wordExp V r.2) := by
    rw [show wordW V r.2 = 2 ^ wordExp V r.2 from rfl]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact max_le h1 h2

/-- The basis of the input subspace (`app:affine-embedding`, "Input subspace"): the `ω` column coordinates
`e_{k_N+ℓ_S+j}`, then the `m − ω` lane coordinates `e_j`. -/
def inBasis (r : ClockRequest) : List ℕ :=
  (List.range (wordExp V r.2)).map (fun j => 2 ^ (laneExp V r.2 + stageExp V r.2 + j)) ++
    (List.range (inExp V r - wordExp V r.2)).map (fun j => 2 ^ j)

/-- **Stage B2**: `natWord m`, the basis masks, the offset `2^τ`. -/
def stageB2 : S :=
  .seq (emitNatE (.v 29)) (.seq (.loop 50 (.v 25) (emitNatE (two (.add (.add (.v 31) (.v 32)) (.v 50)))))
    (.seq (.loop 50 (.sub (.v 29) (.v 25)) (emitNatE (two (.v 50)))) (emitNatE (.v 28))))

theorem inBasis_word (r : ClockRequest) :
    listWord natWord (inBasis V r) = natWord (inExp V r) ++
      ((List.range (wordExp V r.2)).flatMap (fun j => natWord (2 ^ (laneExp V r.2 + stageExp V r.2 + j))) ++
        (List.range (inExp V r - wordExp V r.2)).flatMap (fun j => natWord (2 ^ j))) := by
  have hω := wordExp_le_inExp V r
  have hl : (inBasis V r).length = inExp V r := by
    simp only [inBasis, List.length_append, List.length_map, List.length_range]; omega
  unfold listWord
  rw [hl]
  congr 1
  simp [inBasis, List.flatMap, Function.comp_def]

/-- **The input subspace is printed** on every request (the bounds are `n`-aware: `AFit`). -/
theorem stageB2_spec (r : ClockRequest) (s : FS) (h : PV V r s) (hfit : BFit V r.2 G) (hA : AFit V r G) :
    Em LW s (evalS G stageB2 s) (listWord natWord (inBasis V r) ++ natWord (2 ^ tau V r.2)) := by
  obtain ⟨hK, hN, hKN⟩ := hfit
  obtain ⟨⟨hKn, -⟩, -⟩ := hA
  have hτm := tau_lt_domExp V r.2
  have hmf := domExp_add_two_le_fieldExp V r.2
  have hωτ := wordExp_le_tau V r.2
  have hmn := inExp_le V r
  have hcap := cap_add G
  have hKl : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have hdm : domExp V r.2 = laneExp V r.2 + stageExp V r.2 + colExp V r.2 + 4 := rfl
  have hq : colExp V r.2 = tagExp V + wordExp V r.2 := rfl
  have hnbm : ∀ x, x < 2 ^ domExp V r.2 → natBitLength x + 2 ≤ G.K := fun x hx => by
    have := natBitLength_le_of_lt (show 1 ≤ domExp V r.2 by omega) hx; omega
  have hpm : ∀ x, x < domExp V r.2 → 2 ^ x < 2 ^ domExp V r.2 := fun x hx => Nat.pow_lt_pow_right (by norm_num) hx
  have hωN : wordExp V r.2 ≤ G.N := by omega
  rw [inBasis_word]
  simp only [List.append_assoc]
  unfold stageB2
  -- `natWord m`
  refine Em_acc (emitNatE_val (G := G) s (.v 29) _ (by rw [eE_v, h.m]) (by have := natBitLength_le (inExp V r); omega)
    hKN) (fun t1 a1 => ?_)
  have u1 : ∀ i : Var, i ∉ LW → t1.env i = s.env i := a1.env
  -- the column coordinates
  have L1 := loopNat 50 (Or.inl rfl) t1 (.v 25) (wordExp V r.2)
    (by rw [eE_v, u1 25 (by decide), h.om]; exact min_eq_left hωN)
    (two (.add (.add (.v 31) (.v 32)) (.v 50))) (fun i => 2 ^ (laneExp V r.2 + stageExp V r.2 + i))
    (fun i hi v hv h50 _ _ => eE_two (eE_add (eE_add (by rw [eE_v, hv 31 (by decide), u1 31 (by decide), h.k])
      (by rw [eE_v, hv 32 (by decide), u1 32 (by decide), h.ell]) (by
        have := Nat.lt_two_pow_self (n := domExp V r.2); omega)) (by rw [eE_v, h50]) (by
        have := Nat.lt_two_pow_self (n := domExp V r.2); omega)) (by omega))
    (fun i hi => hnbm _ (hpm _ (by omega))) hKN
  refine Em_acc (L1.mono (lvSW_sub 50 (Or.inl rfl))) (fun t2 a2 => ?_)
  have u2 : ∀ i : Var, i ∉ LW → t2.env i = s.env i := fun i hi => (a2.env i hi).trans (u1 i hi)
  -- the lane coordinates (`m − ω ≤ n` of them, each below `2^(n + ω)`)
  refine Em_acc ((loopNat 50 (Or.inl rfl) t2 (.sub (.v 29) (.v 25)) (inExp V r - wordExp V r.2)
    (by rw [eE_sub (by rw [eE_v, u2 29 (by decide), h.m]) (by rw [eE_v, u2 25 (by decide), h.om])]
        exact min_eq_left (by omega))
    (two (.v 50)) (2 ^ ·) (fun i hi v hv h50 _ _ => eE_two (by rw [eE_v, h50]) (by omega))
    (fun i hi => by
      show natBitLength (2 ^ i) + 2 ≤ G.K
      have := natBitLength_le_of_lt (show 1 ≤ i + 1 by omega) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self i))
      omega) hKN).mono (lvSW_sub 50 (Or.inl rfl))) (fun t3 a3 => ?_)
  have u3 : ∀ i : Var, i ∉ LW → t3.env i = s.env i := fun i hi => (a3.env i hi).trans (u2 i hi)
  -- the offset `2^τ`
  exact emitNatE_val (G := G) t3 (.v 28) _ (by rw [eE_v, u3 28 (by decide), h.T]) (hnbm _ (hpm _ hτm)) hKN

end NearCubicGates.Adapters.RAMACSP.Gen
