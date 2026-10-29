import SourceAdapters.Amplification.ReconstructionSize
import SourceAdapters.Amplification.SlotOracle
import SourceAdapters.Amplification.GateAReconstruct
import SourceAdapters.Amplification.CoinFixing
import SourceAdapters.Amplification.Regimes

/-!
# A02: the reconstruction bound from STV Theorem 29

`app:sources`, "Full-range amplification interface": "The reconstruction in [STV, Theorem 24], using the binary code family of its Lemma 28, gives
absolute constants `A ≥ 1` and an integer `a ≥ 1` with the following consequence. An `s'`-node circuit agreeing
with the encoded function on more than a `1/2 + δ` fraction yields an exact circuit for the original `n`-input
function with at most `A(n/δ)^a s' + n + 2` nodes. The polynomial reconstruction overhead includes fixing the
decoder's randomness and conversion to our fan-in-two basis."

STV's proof of Theorem 24 (fix the coins, express `M_j^B` as a circuit) and Remark 21 (majority vote over
`O(log|X|)` runs, then fixed coins as in [Adl78]), carried out non-uniformly in the target basis:

1. `gateA_reconstruct` (from the leaf): a slot `j0` and an oracle machine `M` whose run with the slot oracle of `B`
   computes `innerPoly` at every point (STV Definition 20), within time, description and coins
   `≤ K(m + d + t + 1/δ³)^e`;
2. `real_slot`: the slot oracle from `2^t` copies of `B`; `real_run`: `T = ⌊K(…)^e⌋` steps of `M` on the grid point
   of the input `i` (input word wired from `i`, `ptWord`) with fixed coins;
3. `exists_majority_coins`: `2(3n+3)` coin strings on which, for every `i ∈ {0,1}^n`, most runs are correct;
4. a majority count (`Real.count`); bit `0` of the output word (`word_zero_of_fieldElt`: the word of `0` or `1`)
   is `msg i` by `innerPoly_recovers`;
5. `reconSize_bound`: at most `A·(n·2^(k+2))^a·|B|` nodes.

`reconstructionObligation : ReconstructionObligation` closes A02.
-/

set_option autoImplicit false
namespace NearCubicGates.Adapters.Amplification
open Finset Polynomial NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.Bindings.CLW20Lemma39
open NearCubicGates.Published.STV

/-- The bit `0` of a word denoting `0` or `1`. -/
theorem word_zero_of_fieldElt {q : (ZMod 2)[X]} {t : ℕ} (hq : q.Monic) (ht : q.natDegree = t) (h1 : 1 ≤ t)
    (w : Fin t → Bool) (bit : Bool) (h : fieldElt q w = if bit then 1 else 0) : w ⟨0, h1⟩ = bit := by
  have hinj := (fieldElt_bijective hq ht).1
  have he1 : fieldElt q (fun s : Fin t => decide (s.val = 0)) = 1 := by
    unfold fieldElt wordPoly
    rw [Finset.sum_eq_single ⟨0, h1⟩]
    · simp
    · intro s _ hs
      have : s.val ≠ 0 := fun h0 => hs (Fin.ext h0)
      simp [this]
    · simp
  have he0 : fieldElt q (fun _ : Fin t => false) = 0 := by
    unfold fieldElt wordPoly; simp
  cases bit
  · rw [if_neg (by simp), ← he0] at h
    rw [hinj h]
  · rw [if_pos rfl, ← he1] at h
    rw [hinj h]; simp

/-- The threshold of the slot oracle as an integer. -/
theorem slot_threshold (k t : ℕ) (h : k + 3 ≤ t) :
    (1 / 2 + dyadicAcc k / 2) * 2 ^ t = ((2 ^ (t - 1) + 2 ^ (t - (k + 3)) : ℕ) : ℝ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show k + 3 + r - 1 = k + 2 + r by omega, show k + 3 + r - (k + 3) = r by omega]
  unfold dyadicAcc
  push_cast
  rw [pow_add, pow_add, pow_add, pow_add]
  field_simp
  ring

/-- The input leaves of the grid point of `i`. -/
def ptLeaf (n m h t : ℕ) (j : Fin m) (s : Fin t) : Bool ⊕ Fin n :=
  if s.val < h then (if hp : j.val * h + s.val < n then Sum.inr ⟨j.val * h + s.val, hp⟩ else Sum.inl false)
  else Sum.inl false

/-- The input word (the grid point of `i`) as leaves. -/
def ptWord (n m h t : ℕ) : List (Bool ⊕ Fin n) := (List.ofFn fun j : Fin m => List.ofFn (ptLeaf n m h t j)).flatten

theorem ptWord_map (n m h t : ℕ) (i : Fin n → Bool) :
    (ptWord n m h t).map (Real.leafEval i) = pointWord (fun j => hWord (t := t) (grid (m := m) (h := h) i j)) := by
  unfold ptWord pointWord
  rw [List.map_flatten, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  simp only [Function.comp_apply, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext s
  simp only [Function.comp_apply, ptLeaf, hWord, grid]
  split_ifs <;> rfl

/-- **A02, logical part**: from the leaf, a circuit for the message whose node count is `reconSize` of the
reconstruction's parameters (time `T`, description `Q·2^τ`, slot `j0`) and the adversary's size. -/
theorem reconstruct (h29 : Theorem29) :
    ∃ (C : ℕ) (K : ℝ) (e : ℕ), ∀ (n k : ℕ) (q : (ZMod 2)[X]) [Fact (Irreducible q)] (hq : q.Monic)
      (ht : q.natDegree = tParam C n k) (msg : BoolFunction n)
      (B : BooleanCircuit ((mParam n k + 1) * tParam C n k)),
      (1 / 2 + dyadicAcc k) * 2 ^ ((mParam n k + 1) * tParam C n k) <
        ((univ.filter fun w => B.eval w = stvEncode C n k hq ht msg w).card : ℝ) →
      ∃ T Q τ j0 : ℕ, 1 ≤ Q ∧
        (T : ℝ) ≤ K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e ∧
        ((Q * 2 ^ τ : ℕ) : ℝ) ≤ K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e ∧
        j0 < ⌊1 / dyadicAcc k ^ 2⌋₊ ∧
        HasCircuitOfSize msg (reconSize n (mParam n k) (tParam C n k) ((mParam n k + 1) * tParam C n k)
          (2 ^ (tParam C n k - 1) + 2 ^ (tParam C n k - (k + 3))) T Q τ j0 B.size) := by
  classical
  obtain ⟨C, K, e, hrec⟩ := gateA_reconstruct h29
  refine ⟨C, K, e, fun n k q _ hq ht msg B hB => ?_⟩
  obtain ⟨j0, hj0, M, hdesc, _, hhalt, hcomp⟩ := hrec n k q hq ht msg B.eval hB
  have ht3 : k + 3 ≤ tParam C n k := by unfold tParam hParam; omega
  have hO := real_slot (mParam n k) (tParam C n k) (2 ^ (tParam C n k - 1) + 2 ^ (tParam C n k - (k + 3))) j0
    (dyadicAcc k / 2) (slot_threshold k _ ht3) B
  have hb : M.stateCount ≤ 2 ^ (Nat.log 2 M.stateCount + 1) := (Nat.lt_pow_succ_log_self (by norm_num) _).le
  set Kb := K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e with hKb
  set T := ⌊Kb⌋₊ with hT
  set f : (Fin (mParam n k) → Fin (tParam C n k) → Bool) → Fin (tParam C n k) → Bool :=
    fun z => slot (dyadicAcc k / 2) j0 (fun u => B.eval (layoutEquiv _ _ (z, u))) with hf
  have hrun := fun r : Fin M.randomBits → Bool => real_run M f _ hO (Nat.log 2 M.stateCount + 1)
    (T + mParam n k * tParam C n k + 1) T hb (by omega) (by omega) (ptWord n (mParam n k) (hParam n k) (tParam C n k))
    (List.ofFn r)
  let good : (Fin n → Bool) → (Fin M.randomBits → Bool) → Prop := fun i r =>
    M.OutputsValue q f (fun j => hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j)) r
      (evalAt q (innerPoly C n k q msg) (fun j => hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j)))
  have hgood : ∀ i, 3 * Fintype.card (Fin M.randomBits → Bool) ≤ 4 * (univ.filter (good i)).card := by
    intro i
    have := hcomp (fun j => hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j))
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] at this
    simpa [Fintype.card_fun] using this
  obtain ⟨rs, hrs⟩ := exists_majority_coins good n (by simp) hgood
  have hbit : ∀ i r, good i r → readTapeBit (((tstep M (fieldOracle f))^[T]
      (M.initial ((ptWord n (mParam n k) (hParam n k) (tParam C n k)).map (Real.leafEval i)) (List.ofFn r))).tapes
        M.outputTape) 0 = msg i := by
    intro i r hg
    obtain ⟨fuel, c, hc, hv⟩ := hg
    obtain ⟨fuel0, hf0, hs0⟩ := hhalt (fun j => hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j)) r
    obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.mp hs0
    have hfT : fuel0 ≤ T := Nat.le_floor hf0
    have e1 := oracleRun_eq_iterate M _ fuel0 T hfT _ _ hc1
    have e2 := oracleRun_eq_iterate M _ fuel (max fuel T) (le_max_left _ _) _ _ hc
    have e3 := oracleRun_eq_iterate M _ fuel0 (max fuel T) (hfT.trans (le_max_right _ _)) _ _ hc1
    rw [ptWord_map, e1, ← e2.symm.trans e3]
    rw [innerPoly_recovers C n k hq ht msg i] at hv
    exact word_zero_of_fieldElt hq ht (by unfold tParam; omega) _ _ hv
  have hpi := Real.pi (β := Fin (2 * (3 * n + 3)))
    (fun (i : Fin n → Bool) j => readTapeBit (((tstep M (fieldOracle f))^[T]
      (M.initial ((ptWord n (mParam n k) (hParam n k) (tParam C n k)).map (Real.leafEval i))
        (List.ofFn (rs j)))).tapes M.outputTape) 0) (fun j => hrun (rs j))
  have hcnt := Real.count (α := Fin (2 * (3 * n + 3))) (3 * n + 4) (List.finRange _) id (fun _ b => b)
  rw [List.length_finRange] at hcnt
  have hmaj := ((Real.comp hpi hcnt).reindex (fun _ : Unit => Fin.last (3 * n + 4))).congr
    (G := fun i (_ : Unit) => msg i) (fun i _ => by
      simp only [Function.comp_apply, cntState, Fin.val_last, id]
      rw [length_filter_eq_card _ (List.nodup_finRange _) (List.mem_finRange)]
      have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * (3 * n + 3)))))
        (fun j => good i (rs j))
      rw [card_univ, Fintype.card_fin] at hsplit
      have hbad := hrs i
      cases hm : msg i
      · rw [decide_eq_false_iff_not, not_le]
        have hsub : (univ.filter fun j => readTapeBit (((tstep M (fieldOracle f))^[T]
            (M.initial ((ptWord n (mParam n k) (hParam n k) (tParam C n k)).map (Real.leafEval i))
              (List.ofFn (rs j)))).tapes M.outputTape) 0 = true) ⊆ univ.filter fun j => ¬ good i (rs j) := by
          intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj ⊢
          intro hg
          rw [hbit i (rs j) hg, hm] at hj
          exact Bool.false_ne_true hj
        have := card_le_card hsub
        omega
      · rw [decide_eq_true_iff]
        have hsub : (univ.filter fun j => good i (rs j)) ⊆ univ.filter fun j => readTapeBit
            (((tstep M (fieldOracle f))^[T] (M.initial ((ptWord n (mParam n k) (hParam n k) (tParam C n k)).map
              (Real.leafEval i)) (List.ofFn (rs j)))).tapes M.outputTape) 0 = true := by
          intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj ⊢
          rw [hbit i (rs j) hj, hm]
        have := card_le_card hsub
        omega)
  refine ⟨T, M.stateCount, M.tapeCount, j0, Fin.pos M.machine.start, Nat.floor_le (le_trans ?_ hdesc), ?_,
    hj0, ?_⟩
  · positivity
  · exact hdesc
  · have hc := hasCircuitOfSize_of_real hmaj
    rw [Fintype.card_fin] at hc
    exact hc

/-- **A02**: the reconstruction bound from the published Theorem 29. -/
theorem reconstructionObligation : ReconstructionObligation := by
  intro h29
  obtain ⟨C, K, e, hrec⟩ := reconstruct h29
  obtain ⟨A, a, hA⟩ := reconSize_bound C K e
  refine ⟨C, A, a, fun n k q _ hq ht msg B hB => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : Real 1 (fun (x : Fin 0 → Bool) (_ : Unit) => msg x) := by
      have := Real.leaves (α := Fin 0) (fun _ : Fin 1 => (Sum.inl (msg Fin.elim0) : Bool ⊕ Fin 0))
      refine (this.reindex (fun _ => (0 : Fin 1))).congr fun x _ => ?_
      simp only [Function.comp_apply, Real.leafEval, Sum.elim_inl, id]
      congr 1; funext i; exact i.elim0
    exact NearCubicGates.Close.Amplifier.hasCircuitOfSize_mono (hasCircuitOfSize_of_real h1) (by omega)
  · obtain ⟨T, Q, τ, j0, hQ, hT, hD, hj0, hcirc⟩ := hrec n k q hq ht msg B hB
    have hBs : 1 ≤ B.size := Fin.pos B.output
    exact NearCubicGates.Close.Amplifier.hasCircuitOfSize_mono hcirc
      ((hA n k T Q τ j0 B.size hn hQ hBs hT hD hj0).trans (by omega))

end NearCubicGates.Adapters.Amplification
