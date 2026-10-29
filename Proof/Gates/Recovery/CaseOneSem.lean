import Proof.Gates.Recovery.CaseOneRuns

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.CaseOneSem

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces NearCubicGates.Close.Transfer NearCubicGates.Close.Recovery
open NearCubicGates.Close.Gadget

/-- The cyclic list: `K` entries, entry `i` is `wl[i mod |wl|]`. -/
def cycList (wl : List Bool) (K : ℕ) : List Bool := (List.range K).map fun i => wl.getD (i % wl.length) false

theorem cycList_length (wl : List Bool) (K : ℕ) : (cycList wl K).length = K := by simp [cycList]

theorem cycList_succ (wl : List Bool) (K : ℕ) :
    cycList wl (K + 1) = cycList wl K ++ [wl.getD (K % wl.length) false] := by
  simp [cycList, List.range_succ]

/-- The address bits of `i < 2^q` restricted to `a` bits (`false` past `q`) encode `i mod 2^a`. -/
theorem address_mod (a q i : ℕ) (hi : i < 2 ^ q) :
    binaryAddress (fun j : Fin a => if h : j.val < q then (fun k : Fin q => i.testBit k.val) ⟨j.val, h⟩ else false) =
      ⟨i % 2 ^ a, Nat.mod_lt _ (by positivity)⟩ := by
  have hfun : (fun j : Fin a => if h : j.val < q then (fun k : Fin q => i.testBit k.val) ⟨j.val, h⟩ else false) =
      fun j : Fin a => (i % 2 ^ a).testBit j.val := by
    funext j
    rw [Nat.testBit_mod_two_pow]
    simp only [decide_eq_true j.isLt, Bool.true_and]
    split_ifs with h
    · rfl
    · symm
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hfun, binaryAddress_testBit (Nat.mod_lt _ (by positivity))]

/-- **The truth table of `cycFn`** is the cyclic list of `w`. -/
theorem table_cycFn (a q : ℕ) (w : BitInput (2 ^ a)) :
    boolFunctionTable (cycFn a w q) = cycList (List.ofFn w) (2 ^ q) := by
  apply List.ext_getElem
  · simp [boolFunctionTable, cycList]
  · intro i h1 h2
    have hi : i < 2 ^ q := by simpa [cycList] using h2
    simp only [boolFunctionTable, cycList, List.getElem_map, List.getElem_range, cycFn]
    rw [address_mod a q i hi]
    simp only [List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; exact Nat.mod_lt _ (by positivity)), List.getElem_ofFn]

/-- Case 1 (i): `X_z` is the cyclic function of `z`. -/
theorem srcFn_eq (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν)) :
    g.srcFn s ν z = cycFn ν z (g.width s ν) := by
  funext r
  unfold GateParams.srcFn cycFn
  congr 2
  funext j
  rw [dif_pos (lt_of_lt_of_le j.isLt (g.nu_lt_width s ν).le)]
  rfl

/-- Case 1 (iii): `O*` as a function of `q` bits is the cyclic function of its table. -/
theorem pfFn_eq {q ℓ : ℕ} (t : BitInput (2 ^ ℓ)) : (GateParams.pfFn t : BoolFunction q) = cycFn ℓ t q := rfl

/-- **Case 1 (i)** (`sec:gadget-extract`, case (NoSource); `sec:all-lengths`): without a CHECK-passing source
circuit, the gate core is the amplified
padded cyclic function of the source input `z`. -/
theorem gateCore_caseOne_i (s : GateSources) (g : GateParams) (P : ThreeQueryPCPP) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h : ¬g.SrcExists s ν z) :
    g.gateCore s P amplifier ν z cl pl target =
      GateParams.amplified amplifier (g.width s ν) (cycFn ν z (g.width s ν)) target := by
  unfold GateParams.gateCore
  rw [dif_neg h, srcFn_eq]

/-- **Case 1 (iii)** (`sec:gadget-extract`, case (NoProof); `sec:all-lengths`): with `B*_src` and `O*` but no
`q^G`-gate circuit answering as `O*`, the gate
core is the amplified padded cyclic function of the first honest table `O*`. -/
theorem gateCore_caseOne_iii (s : GateSources) (g : GateParams) (P : ThreeQueryPCPP) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h1 : g.SrcExists s ν z) (h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t)
    (h : ¬g.IsCaseTwo s ν z) :
    g.gateCore s P amplifier ν z cl pl target =
      GateParams.amplified amplifier (g.width s ν)
        (cycFn _ (Classical.choice (existsFirstTable _ h2)).table (g.width s ν)) target := by
  unfold GateParams.gateCore
  rw [dif_pos h1, dif_pos h2]
  simp only []
  rw [dif_neg h]
  rfl

/-- **The Case 1 fit** (`sec:all-lengths`: "pad the function in either case to exactly `m(q) = K_amp q₀(q)` inputs"):
with `K_amp ≥ a_G` (`GateParamsReady.ampLarge`), the amplified function on `q = q(N_ν)` inputs has at most `m(q)`
(`GateParams.coreArity`) inputs, so it fits every final length `n ≥ m(q)`. -/
theorem arity_fit (s : GateSources) (g : GateParams) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (hK : amplifier.arityCoefficient ≤ g.ampFactor) (ν : ℕ) (f : BoolFunction (g.width s ν)) :
    (amplifier.output (g.width s ν) f).arity ≤ g.coreArity s ν := by
  have hq : 1 ≤ g.width s ν := by have := g.nu_lt_width s ν; omega
  refine (amplifier.arityBound _ f hq).trans ?_
  unfold GateParams.coreArity GateParams.tableArity
  exact Nat.mul_le_mul hK (by omega)

end NearCubicGates.Close.Recovery.CaseOneSem
