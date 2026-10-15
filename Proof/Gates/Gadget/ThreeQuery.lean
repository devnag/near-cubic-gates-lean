import Proof.Gates.Gadget.Checked

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

/-- The accepted input `(checkedCircuit code D, sysEnc code x)` when `D` accepts `x`. -/
noncomputable def acceptedInput (code : LinearCodeFamily) (D : Circuit) (x : BitInput D.n)
    (h : D.D.eval x = true) : AcceptedCircuitInput :=
  ⟨checkedCircuit code D, ⟨sysEnc code D.n x,
    (checkedCircuit_accepts_iff code D _).2 ⟨by rw [prefixOf_sysEnc]; exact h, by rw [prefixOf_sysEnc]⟩⟩⟩

structure ThreeQueryPCPP where
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_lt_one : gamma < 1
  code : LinearCodeFamily
  output : (C : Circuit) → RawThreeQueryPCPP C.n
  outputPoly : Nonempty (Turing.TM2ComputableInPolyTime (fun C : Circuit => C.word)
    (fun word : List Bool => word) (fun C => (output C).word))
  outputSize : ∃ K e : ℕ, ∀ C : Circuit,
    (output C).proofBits ≤ K * (C.m + 1) ^ e ∧ 2 ^ (output C).randomBits ≤ K * (C.m + 1) ^ e
  honest : (p : AcceptedCircuitInput) → BitInput (output p.1).proofBits
  honestPoly : Nonempty (Turing.TM2ComputableInPolyTime acceptedCircuitInputWord
    (fun word : List Bool => word) (fun p => List.ofFn (honest p)))
  codeLength : ∃ K : ℕ, ∀ n, 2 ≤ n → code.length n ≤ K * (n + 1)
  /-- "a polynomial-time computable linear encoding Enc" (v2 line 2100). -/
  encPoly : Nonempty (Turing.TM2ComputableInPolyTime messageWord (fun word : List Bool => word)
    (fun p => List.ofFn (code.enc p.1 p.2.val)))
  /-- "If D(x) = 1, an auxiliary assignment computable in polynomial time satisfies every clause." -/
  complete : ∀ (D : Circuit) (x : BitInput D.n) (h : D.D.eval x = true) coins,
    (output (checkedCircuit code D)).accepts (sysEnc code D.n x) (honest (acceptedInput code D x h)) coins = true

  sound : ∀ (D : Circuit) (x : BitInput D.n), 2 ≤ D.n → D.D.eval x = false →
    ∀ proof, (output (checkedCircuit code D)).fraction (sysEnc code D.n x) proof ≤ 1 - (gamma : ℝ)

/-- The relative distance of two systematic codewords is at least half the code distance. -/
theorem sysEnc_far (E : LinearCodeFamily) (q : ℕ) (hq : 0 < q) (hL : q ≤ E.length q) (dist : ℝ)
    (x x' : BitInput q) (hd : dist ≤ relativeHamming (E.enc q x) (E.enc q x')) :
    dist / 2 ≤ relativeHamming (sysEnc E q x) (sysEnc E q x') := by
  set L := E.length q
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le hq hL)
  have hcard : ((Finset.univ.filter fun j : Fin L => E.enc q x j ≠ E.enc q x' j).card : ℝ) ≤
      ((Finset.univ.filter fun i : Fin (q + L) => sysEnc E q x i ≠ sysEnc E q x' i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun j => Fin.natAdd q j)
      (fun j hj => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
        rw [sysEnc_natAdd, sysEnc_natAdd]; exact hj)
      (fun a _ b _ hab => by simpa [Fin.ext_iff] using hab)
  unfold relativeHamming at hd ⊢
  have hqL : ((q + L : ℕ) : ℝ) ≤ 2 * L := by push_cast; exact_mod_cast (by omega : q + L ≤ 2 * L)
  have hqLpos : (0 : ℝ) < ((q + L : ℕ) : ℝ) := by push_cast; linarith
  rw [div_le_div_iff₀ (by norm_num) hqLpos]
  have h1 : dist * L ≤ ((Finset.univ.filter fun j : Fin L => E.enc q x j ≠ E.enc q x' j).card : ℝ) := by
    rwa [le_div_iff₀ hLpos] at hd
  have hnn : 0 ≤ dist ∨ dist < 0 := le_or_gt 0 dist
  rcases hnn with hnn | hneg
  · nlinarith
  · have : 0 ≤ ((Finset.univ.filter fun i : Fin (q + L) => sysEnc E q x i ≠ sysEnc E q x' i).card : ℝ) :=
      by positivity
    nlinarith

theorem threeQuery_of_source (h : ThreeQuerySourceGroup) : Nonempty ThreeQueryPCPP := by
  obtain ⟨hpcpp, E, dist, rad, hrad, hrad_lt, hdist_lt, hlen, -, hdistance, -, hencTM, -⟩ := h
  have hd0 : 0 < dist := hrad.trans hrad_lt
  obtain ⟨s, hs0, hs1, output, hTM, hsize, hsound, honest, hhonest, hhonestTM⟩ :=
    hpcpp (dist / 2) (by linarith) (by linarith)
  obtain ⟨γ, hγ0, hγ1⟩ := exists_rat_btwn (show (0 : ℝ) < 1 - s by linarith)
  refine ⟨{ gamma := γ, gamma_pos := by exact_mod_cast hγ0,
            gamma_lt_one := by
              have : (γ : ℝ) < 1 := by linarith
              exact_mod_cast this,
            code := E, output := output, outputPoly := hTM, outputSize := hsize,
            honest := honest, honestPoly := hhonestTM, codeLength := hlen, encPoly := hencTM,
            complete := fun D x h coins => hhonest (acceptedInput E D x h) coins,
            sound := ?_ }⟩
  intro D x hn hx proof
  have hfar : ProximityFar (dist / 2) (checkedCircuit E D) (sysEnc E D.n x) := by
    intro y hy
    obtain ⟨hDy, hyenc⟩ := (checkedCircuit_accepts_iff E D y).1 hy
    have hne : x ≠ prefixOf y := by
      intro hxy; rw [hxy] at hx; rw [hx] at hDy; exact Bool.false_ne_true hDy
    -- the code is injective, hence `q ≤ L`
    have hinj : Function.Injective (E.enc D.n) := by
      intro a b hab
      by_contra hne'
      have := hdistance D.n hn a b hne'
      rw [hab] at this
      have hz : relativeHamming (E.enc D.n b) (E.enc D.n b) = 0 := by
        simp [relativeHamming]
      linarith
    have hL : D.n ≤ E.length D.n := by
      have := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have := sysEnc_far E D.n (by omega) hL dist x (prefixOf y) (hdistance D.n hn x (prefixOf y) hne)
    rw [hyenc]; exact this
  have := hsound (checkedCircuit E D) (sysEnc E D.n x) hfar proof
  have hγ : (1 : ℝ) - s ≥ γ := le_of_lt hγ1
  linarith

end NearCubicGates.Close.Gadget
