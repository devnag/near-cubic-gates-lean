import Proof.Wire_3_5.SeedFixTable

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

/-! ## `XorAnd`: tapes 0 the prefix word (at a marker), 1 the bit cell `B`, 2 the accumulator cell `F` -/

namespace XorAnd
open Three (act cfg)

def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none none none .right .stay .stay)
    else if q.val = 1 then some (act 2 none none (some (xor (sc 2) (sc 1 && sc 0))) .right .stay .stay)
    else none

theorem run (T : List Bool) (h : ℕ) (a f : Bool) :
    Step machine 2 ![h, 0, 0] ![T, [a], [f]] ![h + 2, 0, 0] ![T, [a], [xor f (a && readTapeBit T (h + 1))]] := by
  have s1 : step machine (cfg 0 T [a] [f] h 0 0) = some (cfg 1 T [a] [f] (h + 1) 0 0) := by
    rw [Three.step_cfg machine 0 1 T [a] [f] h 0 0 none none none .right .stay .stay (by simp [machine])]
    rfl
  have s2 : step machine (cfg 1 T [a] [f] (h + 1) 0 0) =
      some (cfg 2 T [a] [xor f (a && readTapeBit T (h + 1))] (h + 2) 0 0) := by
    rw [Three.step_cfg machine 1 2 T [a] [f] (h + 1) 0 0 none none (some (xor f (a && readTapeBit T (h + 1))))
      .right .stay .stay (by simp [machine, readTapeBit])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]
  have t1 := RecoveryExecution.Timed.single (p := machine) rfl s1
  have t2 := RecoveryExecution.Timed.single (p := machine) rfl s2
  obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end XorAnd

/-! ## `AppendBit`: tapes 0 the bit cell `B`, 1 the rows tape (at its end) -/

namespace AppendBit
open Two (act cfg)

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none (some true) .stay .right)
    else if q.val = 1 then some (act 2 none (some (sc 0)) .stay .right)
    else none

theorem run (a : Bool) (out backing : List Bool) :
    Step machine 2 ![0, out.length] ![[a], overlay out backing] ![0, out.length + 2]
      ![[a], overlay (out ++ [true, a]) backing] := by
  have s1 : step machine (cfg 0 [a] (overlay out backing) 0 out.length) =
      some (cfg 1 [a] (overlay (out ++ [true]) backing) 0 (out.length + 1)) := by
    rw [Two.step_cfg machine 0 1 [a] (overlay out backing) 0 out.length none (some true) .stay .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    rw [overlay_write]
  have s2 : step machine (cfg 1 [a] (overlay (out ++ [true]) backing) 0 (out.length + 1)) =
      some (cfg 2 [a] (overlay (out ++ [true, a]) backing) 0 (out.length + 2)) := by
    rw [Two.step_cfg machine 1 2 [a] (overlay (out ++ [true]) backing) 0 (out.length + 1) none (some a) .stay .right
      (by simp [machine, readTapeBit])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (out ++ [true]) backing a
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  have t1 := RecoveryExecution.Timed.single (p := machine) rfl s1
  have t2 := RecoveryExecution.Timed.single (p := machine) rfl s2
  obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end AppendBit

/-! ## `AppendRhs`: tapes 0 the target word (at a marker), 1 the accumulator cell `F`, 2 the rows tape (at its end) -/

namespace AppendRhs
open Three (act cfg)

def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none none none .right .stay .stay)
    else if q.val = 1 then some (act 2 none none (some true) .stay .stay .right)
    else if q.val = 2 then some (act 3 none none (some (xor (sc 0) (sc 1))) .right .stay .right)
    else if q.val = 3 then some (act 4 none none (some false) .stay .stay .right)
    else none

theorem run (T : List Bool) (h : ℕ) (f : Bool) (out backing : List Bool) :
    Step machine 4 ![h, 0, out.length] ![T, [f], overlay out backing] ![h + 2, 0, out.length + 3]
      ![T, [f], overlay (out ++ [true, xor (readTapeBit T (h + 1)) f, false]) backing] := by
  set v := readTapeBit T (h + 1)
  have s1 : step machine (cfg 0 T [f] (overlay out backing) h 0 out.length) =
      some (cfg 1 T [f] (overlay out backing) (h + 1) 0 out.length) := by
    rw [Three.step_cfg machine 0 1 T [f] (overlay out backing) h 0 out.length none none none .right .stay .stay
      (by simp [machine])]
    rfl
  have s2 : step machine (cfg 1 T [f] (overlay out backing) (h + 1) 0 out.length) =
      some (cfg 2 T [f] (overlay (out ++ [true]) backing) (h + 1) 0 (out.length + 1)) := by
    rw [Three.step_cfg machine 1 2 T [f] (overlay out backing) (h + 1) 0 out.length none none (some true)
      .stay .stay .right (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    rw [overlay_write]
  have s3 : step machine (cfg 2 T [f] (overlay (out ++ [true]) backing) (h + 1) 0 (out.length + 1)) =
      some (cfg 3 T [f] (overlay (out ++ [true, xor v f]) backing) (h + 2) 0 (out.length + 2)) := by
    rw [Three.step_cfg machine 2 3 T [f] (overlay (out ++ [true]) backing) (h + 1) 0 (out.length + 1) none none
      (some (xor v f)) .right .stay .right (by simp [machine, readTapeBit, v])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (out ++ [true]) backing (xor v f)
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  have s4 : step machine (cfg 3 T [f] (overlay (out ++ [true, xor v f]) backing) (h + 2) 0 (out.length + 2)) =
      some (cfg 4 T [f] (overlay (out ++ [true, xor v f, false]) backing) (h + 2) 0 (out.length + 3)) := by
    rw [Three.step_cfg machine 3 4 T [f] (overlay (out ++ [true, xor v f]) backing) (h + 2) 0 (out.length + 2) none
      none (some false) .stay .stay .right (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (out ++ [true, xor v f]) backing false
    rw [List.length_append] at this
    simp only [List.length_cons, List.length_nil] at this
    rw [this, List.append_assoc]
    rfl
  have t1 := RecoveryExecution.Timed.single (p := machine) rfl s1
  have t2 := RecoveryExecution.Timed.single (p := machine) rfl s2
  have t3 := RecoveryExecution.Timed.single (p := machine) rfl s3
  have t4 := RecoveryExecution.Timed.single (p := machine) rfl s4
  obtain ⟨r, hr, hf, hs⟩ := (((t1.trans t2).trans t3).trans t4).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end AppendRhs

/-! ## Helpers: the fold of a one-hot mask reads one bit; the stream with a tail -/

theorem foldBits_eq_fold (f : Bool → Bool → Bool → Bool) :
    ∀ (s : Bool) (u v : List Bool), foldBits f s u v = ZipFold.fold f u v s
  | s, [], v => by cases v <;> rfl
  | s, a :: u, [] => rfl
  | s, a :: u, b :: v => by simp only [foldBits, ZipFold.fold]; exact foldBits_eq_fold f _ u v

theorem parityMasked_two_pow (c a ℓ : ℕ) (hc : c < ℓ) :
    parityMasked (2 ^ c) a ℓ = if a.testBit c then 1 else 0 := by
  unfold parityMasked
  have hf : (List.range ℓ).filter (fun b => (2 ^ c).testBit b && a.testBit b) =
      if a.testBit c then [c] else [] := by
    induction ℓ with
    | zero => omega
    | succ n ih =>
      rw [List.range_succ, List.filter_append]
      by_cases hcn : c < n
      · rw [ih hcn]
        have : (2 ^ c).testBit n = false := by rw [Nat.testBit_two_pow]; simp; omega
        simp [this]
      · have hcn' : c = n := by omega
        subst hcn'
        have h0 : (List.range c).filter (fun b => (2 ^ c).testBit b && a.testBit b) = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb
          have := List.mem_range.mp hb
          rw [Nat.testBit_two_pow]; simp; omega
        rw [h0]
        cases h : a.testBit c <;> simp [Nat.testBit_two_pow, h]
  rw [hf]
  cases a.testBit c <;> simp

/-- **The fold of the one-hot mask `2^c` with a record is its bit `c`.** -/
theorem foldBits_onehot (ℓ c t : ℕ) (hc : c < ℓ) :
    foldBits parityStep false (binary ℓ (2 ^ c)) (binary ℓ t) = t.testBit c := by
  rw [foldBits_eq_fold, parity_bit, parityMasked_two_pow c t ℓ hc]
  cases t.testBit c <;> simp

theorem read_append_left (a b : List Bool) (i : ℕ) (hi : i < a.length) : readTapeBit (a ++ b) i = readTapeBit a i := by
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ hi]

theorem pre_le (L : List (List Bool)) (k : ℕ) : pre L k ≤ (L.flatMap frame).length := by
  unfold pre
  conv_rhs => rw [← List.take_append_drop k L]
  rw [List.flatMap_append, List.length_append]
  omega

/-- The stream with a tail reads as the stream at record boundaries. -/
theorem read_pre_tail (L : List (List Bool)) (tail : List Bool) (k : ℕ) (hne : ∀ w ∈ L, w ≠ []) :
    readTapeBit (streamOf L ++ tail) (pre L k) = decide (k < L.length) := by
  have h1 := pre_le L k
  have h2 : (streamOf L).length = (L.flatMap frame).length + 1 := by
    unfold streamOf; rw [List.length_append]; rfl
  rw [read_append_left _ _ _ (by omega), read_pre L k hne]

theorem streamOf_tail_split (L : List (List Bool)) (tail : List Bool) (k : ℕ) (hk : k < L.length) :
    streamOf L ++ tail =
      (L.take k).flatMap frame ++ frame L[k] ++ ((L.drop (k + 1)).flatMap frame ++ [false] ++ tail) := by
  rw [streamOf_split L k hk]
  simp only [List.append_assoc]

/-! ## Phase A: the prefix columns into the right-hand side (tapes 0 the prefix word, 1 the table stream, 2 the mask
`2^c`, 3 the record register, 4 the bit cell, 5 the accumulator cell, 6 the capacity tape) -/

def a7Copy : Fin 3 → Fin 7 := ![1, 3, 6]

theorem install_a7Copy (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install a7Copy A v = ![A 0, v 0, A 2, v 1, A 4, A 5, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_a7Copy (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH a7Copy H v = ![H 0, v 0, H 2, v 1, H 4, H 5, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def a7Nudge : Fin 1 → Fin 7 := ![1]

theorem install_a7Nudge (A : Fin 7 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install a7Nudge A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_a7Nudge (H : Fin 7 → ℕ) (v : Fin 1 → ℕ) :
    dockH a7Nudge H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def a7Fold : Fin 4 → Fin 7 := ![2, 3, 4, 6]

theorem install_a7Fold (A : Fin 7 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install a7Fold A v = ![A 0, A 1, v 0, v 1, v 2, A 5, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_a7Fold (H : Fin 7 → ℕ) (v : Fin 4 → ℕ) :
    dockH a7Fold H v = ![H 0, H 1, v 0, v 1, v 2, H 5, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def a7Xor : Fin 3 → Fin 7 := ![0, 4, 5]

theorem install_a7Xor (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install a7Xor A v = ![v 0, A 1, A 2, A 3, v 1, v 2, A 6] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_a7Xor (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH a7Xor H v = ![v 0, H 1, H 2, H 3, v 1, v 2, H 6] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)
def selRec : Fin 2 → Bool := ![false, true]

noncomputable def phABody :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine a7Copy (MaskedReset.machine CopyO.machine selRec)) (RecoveryFocus.machine a7Nudge nudgeM))
    (RecoveryFocus.machine a7Fold (MaskedReset.machine (FoldCell.machine parityStep false) sel3)))
    (RecoveryFocus.machine a7Xor XorAnd.machine)

/-- **Phase A**: one pass per prefix bit. -/
noncomputable def phAM := StreamController.machine phABody 0

/-- The right-hand side's accumulated part after `j` prefix columns: `Σ_{j'<j} col_{j'}[c]·pre_{j'}`. -/
def fixAcc (tab : List ℕ) (pfx c j : ℕ) : Bool :=
  (List.range j).foldl (fun acc j' => xor acc ((tab.getD j' 0).testBit c && pfx.testBit j')) false

/-- The register and bit cell after `j` records (the given initial contents before the first). -/
def regAt (ℓ : ℕ) (tab : List ℕ) (r0 : List Bool) : ℕ → List Bool
  | 0 => r0
  | j + 1 => frame (binary ℓ (tab.getD j 0))

def bitAt (tab : List ℕ) (c : ℕ) (b0 : Bool) : ℕ → Bool
  | 0 => b0
  | j + 1 => (tab.getD j 0).testBit c

def phAH (ℓ : ℕ) (tab : List ℕ) (j : ℕ) : Fin 7 → ℕ := ![2 * j, pre (tab.map (binary ℓ)) j, 0, 0, 0, 0, 0]

def phAA (ℓ plen pfx c cap : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool) (j : ℕ) : Fin 7 → List Bool :=
  ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), regAt ℓ tab r0 j,
    [bitAt tab c b0 j], [fixAcc tab pfx c j], List.replicate cap false]

theorem fixAcc_succ (tab : List ℕ) (pfx c j : ℕ) :
    fixAcc tab pfx c (j + 1) = xor (fixAcc tab pfx c j) ((tab.getD j 0).testBit c && pfx.testBit j) := by
  unfold fixAcc
  rw [List.range_succ, List.foldl_append]
  rfl

def phACost (ℓ : ℕ) : ℕ := 2 * (2 * ℓ + 1) + 2 + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 2

theorem regAt_length (ℓ : ℕ) (tab : List ℕ) (r0 : List Bool) (hr0 : r0.length ≤ 2 * ℓ + 1) :
    ∀ j, (regAt ℓ tab r0 j).length ≤ 2 * ℓ + 1
  | 0 => hr0
  | j + 1 => by simp [regAt, frame_length]

theorem phA_step (ℓ plen pfx c cap : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool) (hc : c < ℓ)
    (hr0 : r0.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 1 ≤ cap) (j : ℕ) (hj : j < plen) (hjt : j < tab.length) :
    Step phABody (phACost ℓ) (phAH ℓ tab j) (phAA ℓ plen pfx c cap tab tail r0 b0 j)
      (phAH ℓ tab (j + 1)) (phAA ℓ plen pfx c cap tab tail r0 b0 (j + 1)) := by
  set W := tab.map (binary ℓ) with hW
  have hjW : j < W.length := by simpa [hW] using hjt
  have hWj : W[j] = binary ℓ (tab.getD j 0) := by
    simp [hW, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
  set t := tab.getD j 0 with ht
  set S := streamOf W ++ tail with hS
  -- 1: the record into the register
  obtain ⟨cr, hcr, hcrf⟩ := CopyO.copy_run ((W.take j).flatMap frame) W[j]
    ((W.drop (j + 1)).flatMap frame ++ [false] ++ tail) [] (regAt ℓ tab r0 j)
  rw [← streamOf_tail_split W tail j hjW] at hcr hcrf
  have hlen : W[j].length = ℓ := by rw [hWj, binary_length]
  have hcs : Step CopyO.machine (2 * W[j].length + 1) ![pre W j, 0] ![S, regAt ℓ tab r0 j]
      ![pre W j + 2 * W[j].length, 2 * W[j].length + 1] ![S, frame W[j]] := by
    refine ⟨cr, hcr, ?_, ?_, runFrom_steps_le _ _ _ _ hcr⟩
    · rw [hcrf]; funext i; fin_cases i <;> simp [CopyO.config, pre, frame_length]
    · rw [hcrf]
      funext i; fin_cases i
      · rfl
      · show overlay ([] ++ frame W[j]) (regAt ℓ tab r0 j) = frame W[j]
        exact overlay_exact _ _ (by rw [List.nil_append, frame_length, hlen]; exact regAt_length ℓ tab r0 hr0 j)
  rw [hlen, hWj] at hcs
  have hm := hcs.mask (cap := cap) selRec (by intro i hi; fin_cases i <;> first | rfl | simp [selRec] at hi) hcap
  have hm' : Step (MaskedReset.machine CopyO.machine selRec) (2 * (2 * ℓ + 1) + 2)
      ![pre W j, 0, 0] ![S, regAt ℓ tab r0 j, List.replicate cap false]
      ![pre W j + 2 * ℓ, 0, 0] ![S, frame (binary ℓ t), List.replicate cap false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s1 := dockRun hm' a7Copy (by decide) (phAH ℓ tab j) (phAA ℓ plen pfx c cap tab tail r0 b0 j)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_a7Copy, install_a7Copy] at s1
  -- 2: past the record's end marker
  have s2 := dockRun (nudge_run S (pre W j + 2 * ℓ)) a7Nudge (by decide) ![2 * j, pre W j + 2 * ℓ, 0, 0, 0, 0, 0]
    ![frame (binary plen pfx), S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitAt tab c b0 j],
      [fixAcc tab pfx c j], List.replicate cap false]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_a7Nudge, install_a7Nudge] at s2
  -- 3: the record's bit `c`
  have hf := FoldCell.run parityStep false (binary ℓ (2 ^ c)) (binary ℓ t) (bitAt tab c b0 j) (by simp)
  rw [foldBits_onehot ℓ c t hc, binary_length] at hf
  have hf' : Step (FoldCell.machine parityStep false) (2 * ℓ + 1) (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitAt tab c b0 j]] ![2 * ℓ, 2 * ℓ, 0]
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c]] :=
    hf.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hfm := maskZero hf' sel3 (by intro i hi; fin_cases i <;> first | rfl | simp [sel3] at hi) hcap
  have hfm' : Step (MaskedReset.machine (FoldCell.machine parityStep false) sel3) (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitAt tab c b0 j], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c], List.replicate cap false] := by
    refine (hfm.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have s3 := dockKeep hfm' a7Fold (by decide) ![2 * j, pre W j + 2 * ℓ + 1, 0, 0, 0, 0, 0]
    ![frame (binary plen pfx), S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitAt tab c b0 j],
      [fixAcc tab pfx c j], List.replicate cap false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_a7Fold] at s3
  -- 4: the prefix bit's contribution
  have hx := XorAnd.run (frame (binary plen pfx)) (2 * j) (t.testBit c) (fixAcc tab pfx c j)
  have hpb : readTapeBit (frame (binary plen pfx)) (2 * j + 1) = pfx.testBit j := by
    rw [read_frame_bit _ j (by simpa using hj), binary_getElem]
  rw [hpb] at hx
  have s4 := dockRun hx a7Xor (by decide) ![2 * j, pre W j + 2 * ℓ + 1, 0, 0, 0, 0, 0]
    ![frame (binary plen pfx), S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c],
      [fixAcc tab pfx c j], List.replicate cap false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_a7Xor, install_a7Xor] at s4
  have hall := (((s1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq
    (s3.congr rfl (by funext i; fin_cases i <;> rfl))).seq s4
  have ep : pre W (j + 1) = pre W j + 2 * ℓ + 1 := by rw [pre_succ W j hjW, hlen]; omega
  have eH : phAH ℓ tab (j + 1) = ![2 * j + 2, pre W j + 2 * ℓ + 1, 0, 0, 0, 0, 0] := by
    funext i; fin_cases i
    · show 2 * (j + 1) = 2 * j + 2; ring
    · exact ep
    all_goals rfl
  have eA : phAA ℓ plen pfx c cap tab tail r0 b0 (j + 1) =
      ![frame (binary plen pfx), S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c],
        [xor (fixAcc tab pfx c j) (t.testBit c && pfx.testBit j)], List.replicate cap false] := by
    funext i; fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · show [fixAcc tab pfx c (j + 1)] = _
      rw [fixAcc_succ, ← ht]
      rfl
    · rfl
  rw [eH, eA]
  exact hall.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- **Phase A as one `Step`**: the `plen` prefix columns folded into the right-hand side. -/
theorem phA_run (ℓ plen pfx c cap : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool) (hc : c < ℓ)
    (hr0 : r0.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 1 ≤ cap) (hplen : plen ≤ tab.length) :
    Step phAM (plen * (phACost ℓ + 2) + 1) (phAH ℓ tab 0) (phAA ℓ plen pfx c cap tab tail r0 b0 0)
      (phAH ℓ tab plen) (phAA ℓ plen pfx c cap tab tail r0 b0 plen) := by
  let W : WhileBody 7 _ :=
    { body := phABody
      tape := 0
      bound := plen
      H := phAH ℓ tab
      A := phAA ℓ plen pfx c cap tab tail r0 b0
      cost := fun _ => phACost ℓ
      step := fun j hj => phA_step ℓ plen pfx c cap tab tail r0 b0 hc hr0 hcap j hj (by omega)
      cont := fun j hj => by
        show readTapeBit (frame (binary plen pfx)) (2 * j) = true
        exact read_frame_mark _ j (by simpa using hj)
      halt := by
        show readTapeBit (frame (binary plen pfx)) (2 * plen) = false
        have := read_frame_end (binary plen pfx)
        rwa [binary_length] at this }
  have h := W.run
  rw [W.rest_const (phACost ℓ) (fun _ => rfl)] at h
  exact h

/-! ## Phase B: the remaining columns as mask bits (tapes 0 the table stream, 1 the mask `2^c`, 2 the record register,
3 the bit cell, 4 the rows tape, 5 the capacity tape) -/

def b6Copy : Fin 3 → Fin 6 := ![0, 2, 5]

theorem install_b6Copy (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install b6Copy A v = ![v 0, A 1, v 1, A 3, A 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_b6Copy (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH b6Copy H v = ![v 0, H 1, v 1, H 3, H 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def b6Nudge : Fin 1 → Fin 6 := ![0]

theorem install_b6Nudge (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install b6Nudge A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_b6Nudge (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH b6Nudge H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def b6Fold : Fin 4 → Fin 6 := ![1, 2, 3, 5]

theorem install_b6Fold (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install b6Fold A v = ![A 0, v 0, v 1, v 2, A 4, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_b6Fold (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH b6Fold H v = ![H 0, v 0, v 1, v 2, H 4, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def b6App : Fin 2 → Fin 6 := ![3, 4]

theorem install_b6App (A : Fin 6 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install b6App A v = ![A 0, A 1, A 2, v 0, v 1, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_b6App (H : Fin 6 → ℕ) (v : Fin 2 → ℕ) :
    dockH b6App H v = ![H 0, H 1, H 2, v 0, v 1, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)
noncomputable def phBBody :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine b6Copy (MaskedReset.machine CopyO.machine selRec)) (RecoveryFocus.machine b6Nudge nudgeM))
    (RecoveryFocus.machine b6Fold (MaskedReset.machine (FoldCell.machine parityStep false) sel3)))
    (RecoveryFocus.machine b6App AppendBit.machine)

/-- **Phase B**: one pass per remaining record of the table stream. -/
noncomputable def phBM := StreamController.machine phBBody 0

/-- The mask bits written after the records `plen, …, plen + j − 1`. -/
def maskBits (tab : List ℕ) (plen c j : ℕ) : List Bool :=
  ((List.range j).map fun j' => (tab.getD (plen + j') 0).testBit c).flatMap fun b => [true, b]

theorem maskBits_succ (tab : List ℕ) (plen c j : ℕ) :
    maskBits tab plen c (j + 1) = maskBits tab plen c j ++ [true, (tab.getD (plen + j) 0).testBit c] := by
  unfold maskBits
  rw [List.range_succ, List.map_append, List.flatMap_append]
  rfl

theorem maskBits_length (tab : List ℕ) (plen c : ℕ) : ∀ j, (maskBits tab plen c j).length = 2 * j
  | 0 => rfl
  | j + 1 => by rw [maskBits_succ, List.length_append, maskBits_length tab plen c j]; simp; ring

/-- The register and bit cell after `j` records of phase B (phase A's last contents before the first). -/
def regB (ℓ : ℕ) (tab : List ℕ) (plen : ℕ) (r1 : List Bool) : ℕ → List Bool
  | 0 => r1
  | j + 1 => frame (binary ℓ (tab.getD (plen + j) 0))

def bitB (tab : List ℕ) (c plen : ℕ) (b1 : Bool) : ℕ → Bool
  | 0 => b1
  | j + 1 => (tab.getD (plen + j) 0).testBit c

def phBH (ℓ : ℕ) (tab : List ℕ) (plen n0 j : ℕ) : Fin 6 → ℕ :=
  ![pre (tab.map (binary ℓ)) (plen + j), 0, 0, 0, n0 + 2 * j, 0]

def phBA (ℓ c cap plen : ℕ) (tab : List ℕ) (tail r1 : List Bool) (b1 : Bool) (out backing : List Bool) (j : ℕ) :
    Fin 6 → List Bool :=
  ![streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), regB ℓ tab plen r1 j, [bitB tab c plen b1 j],
    overlay (out ++ maskBits tab plen c j) backing, List.replicate cap false]

theorem regB_length (ℓ : ℕ) (tab : List ℕ) (plen : ℕ) (r1 : List Bool) (hr1 : r1.length ≤ 2 * ℓ + 1) :
    ∀ j, (regB ℓ tab plen r1 j).length ≤ 2 * ℓ + 1
  | 0 => hr1
  | j + 1 => by simp [regB, frame_length]

def phBCost (ℓ : ℕ) : ℕ := 2 * (2 * ℓ + 1) + 2 + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 2

theorem phB_step (ℓ c cap plen : ℕ) (tab : List ℕ) (tail r1 : List Bool) (b1 : Bool) (out backing : List Bool)
    (hc : c < ℓ) (hr1 : r1.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 1 ≤ cap) (j : ℕ) (hjt : plen + j < tab.length) :
    Step phBBody (phBCost ℓ) (phBH ℓ tab plen out.length j) (phBA ℓ c cap plen tab tail r1 b1 out backing j)
      (phBH ℓ tab plen out.length (j + 1)) (phBA ℓ c cap plen tab tail r1 b1 out backing (j + 1)) := by
  set W := tab.map (binary ℓ) with hW
  set k := plen + j with hk
  have hkW : k < W.length := by simpa [hW] using hjt
  set t := tab.getD k 0 with ht
  have hWk : W[k] = binary ℓ t := by
    simp [hW, t, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
  set S := streamOf W ++ tail with hS
  set M := out ++ maskBits tab plen c j with hM
  have hMl : M.length = out.length + 2 * j := by rw [hM, List.length_append, maskBits_length]
  -- 1: the record into the register
  obtain ⟨cr, hcr, hcrf⟩ := CopyO.copy_run ((W.take k).flatMap frame) W[k]
    ((W.drop (k + 1)).flatMap frame ++ [false] ++ tail) [] (regB ℓ tab plen r1 j)
  rw [← streamOf_tail_split W tail k hkW] at hcr hcrf
  have hlen : W[k].length = ℓ := by rw [hWk, binary_length]
  have hcs : Step CopyO.machine (2 * W[k].length + 1) ![pre W k, 0] ![S, regB ℓ tab plen r1 j]
      ![pre W k + 2 * W[k].length, 2 * W[k].length + 1] ![S, frame W[k]] := by
    refine ⟨cr, hcr, ?_, ?_, runFrom_steps_le _ _ _ _ hcr⟩
    · rw [hcrf]; funext i; fin_cases i <;> simp [CopyO.config, pre, frame_length]
    · rw [hcrf]
      funext i; fin_cases i
      · rfl
      · show overlay ([] ++ frame W[k]) (regB ℓ tab plen r1 j) = frame W[k]
        exact overlay_exact _ _ (by rw [List.nil_append, frame_length, hlen]; exact regB_length ℓ tab plen r1 hr1 j)
  rw [hlen, hWk] at hcs
  have hm := hcs.mask (cap := cap) selRec (by intro i hi; fin_cases i <;> first | rfl | simp [selRec] at hi) hcap
  have hm' : Step (MaskedReset.machine CopyO.machine selRec) (2 * (2 * ℓ + 1) + 2)
      ![pre W k, 0, 0] ![S, regB ℓ tab plen r1 j, List.replicate cap false]
      ![pre W k + 2 * ℓ, 0, 0] ![S, frame (binary ℓ t), List.replicate cap false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s1 := dockRun hm' b6Copy (by decide) (phBH ℓ tab plen out.length j)
    (phBA ℓ c cap plen tab tail r1 b1 out backing j)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_b6Copy, install_b6Copy] at s1
  -- 2: past the record's end marker
  have s2 := dockRun (nudge_run S (pre W k + 2 * ℓ)) b6Nudge (by decide) ![pre W k + 2 * ℓ, 0, 0, 0, M.length, 0]
    ![S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitB tab c plen b1 j], overlay M backing,
      List.replicate cap false]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_b6Nudge, install_b6Nudge] at s2
  -- 3: the record's bit `c`
  have hf := FoldCell.run parityStep false (binary ℓ (2 ^ c)) (binary ℓ t) (bitB tab c plen b1 j) (by simp)
  rw [foldBits_onehot ℓ c t hc, binary_length] at hf
  have hf' : Step (FoldCell.machine parityStep false) (2 * ℓ + 1) (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitB tab c plen b1 j]] ![2 * ℓ, 2 * ℓ, 0]
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c]] :=
    hf.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hfm := maskZero hf' sel3 (by intro i hi; fin_cases i <;> first | rfl | simp [sel3] at hi) hcap
  have hfm' : Step (MaskedReset.machine (FoldCell.machine parityStep false) sel3) (2 * (2 * ℓ + 1) + 2) (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitB tab c plen b1 j], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c], List.replicate cap false] := by
    refine (hfm.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  have s3 := dockKeep hfm' b6Fold (by decide) ![pre W k + 2 * ℓ + 1, 0, 0, 0, M.length, 0]
    ![S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitB tab c plen b1 j], overlay M backing,
      List.replicate cap false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_b6Fold] at s3
  -- 4: the mask bit appended
  have s4 := dockRun (AppendBit.run (t.testBit c) M backing) b6App (by decide)
    ![pre W k + 2 * ℓ + 1, 0, 0, 0, M.length, 0]
    ![S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c], overlay M backing, List.replicate cap false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_b6App, install_b6App] at s4
  have s1' := s1.congr (hout' := ![pre W k + 2 * ℓ, 0, 0, 0, M.length, 0])
    (tout' := ![S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [bitB tab c plen b1 j], overlay M backing,
      List.replicate cap false])
    (by
      funext i; fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · show out.length + 2 * j = M.length
        rw [hMl]
      · rfl)
    (by funext i; fin_cases i <;> rfl)
  have hall := ((s1'.seq
    (s2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq
    (s3.congr rfl (by funext i; fin_cases i <;> rfl))).seq s4
  have ep : pre W (plen + (j + 1)) = pre W k + 2 * ℓ + 1 := by
    rw [show plen + (j + 1) = k + 1 by omega, pre_succ W k hkW, hlen]; omega
  have eH : phBH ℓ tab plen out.length (j + 1) = ![pre W k + 2 * ℓ + 1, 0, 0, 0, M.length + 2, 0] := by
    funext i; fin_cases i
    · exact ep
    · rfl
    · rfl
    · rfl
    · show out.length + 2 * (j + 1) = M.length + 2
      rw [hMl]; ring
    · rfl
  have eA : phBA ℓ c cap plen tab tail r1 b1 out backing (j + 1) =
      ![S, frame (binary ℓ (2 ^ c)), frame (binary ℓ t), [t.testBit c], overlay (M ++ [true, t.testBit c]) backing,
        List.replicate cap false] := by
    funext i; fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · show overlay (out ++ maskBits tab plen c (j + 1)) backing = _
      rw [maskBits_succ, hM, List.append_assoc, ← hk, ← ht]
      rfl
    · rfl
  rw [eH, eA]
  exact hall.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- **Phase B as one `Step`**: the remaining `|tab| − plen` columns' bits `c` appended as mask pairs. -/
theorem phB_run (ℓ c cap plen : ℕ) (tab : List ℕ) (tail r1 : List Bool) (b1 : Bool) (out backing : List Bool)
    (hℓ : 1 ≤ ℓ) (hc : c < ℓ) (hr1 : r1.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 1 ≤ cap) (hplen : plen ≤ tab.length) :
    Step phBM ((tab.length - plen) * (phBCost ℓ + 2) + 1) (phBH ℓ tab plen out.length 0)
      (phBA ℓ c cap plen tab tail r1 b1 out backing 0) (phBH ℓ tab plen out.length (tab.length - plen))
      (phBA ℓ c cap plen tab tail r1 b1 out backing (tab.length - plen)) := by
  have hne : ∀ w ∈ tab.map (binary ℓ), w ≠ [] := by
    intro w hw
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw
    intro h
    have := congrArg List.length h
    simp at this
    omega
  let W : WhileBody 6 _ :=
    { body := phBBody
      tape := 0
      bound := tab.length - plen
      H := phBH ℓ tab plen out.length
      A := phBA ℓ c cap plen tab tail r1 b1 out backing
      cost := fun _ => phBCost ℓ
      step := fun j hj => phB_step ℓ c cap plen tab tail r1 b1 out backing hc hr1 hcap j (by omega)
      cont := fun j hj => by
        show readTapeBit (streamOf (tab.map (binary ℓ)) ++ tail) (pre (tab.map (binary ℓ)) (plen + j)) = true
        rw [read_pre_tail _ _ _ hne]
        simp only [List.length_map, decide_eq_true_eq]
        omega
      halt := by
        show readTapeBit (streamOf (tab.map (binary ℓ)) ++ tail)
          (pre (tab.map (binary ℓ)) (plen + (tab.length - plen))) = false
        rw [read_pre_tail _ _ _ hne]
        simp only [List.length_map, decide_eq_false_iff_not]
        omega }
  have h := W.run
  rw [W.rest_const (phBCost ℓ) (fun _ => rfl)] at h
  exact h

/-! ## One row's passes (tapes 0 the prefix word, 1 the table stream, 2 the mask, 3 the register, 4 the bit cell, 5 the
accumulator cell, 6 the rows tape, 7 the capacity tape, 8 the rewind log) -/

def p9A : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 7, 8]

theorem install_p9A (A : Fin 9 → List Bool) (v : Fin 8 → List Bool) :
    RecoveryRootRound.install p9A A v = ![v 0, v 1, v 2, v 3, v 4, v 5, A 6, v 6, v 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_p9A (H : Fin 9 → ℕ) (v : Fin 8 → ℕ) :
    dockH p9A H v = ![v 0, v 1, v 2, v 3, v 4, v 5, H 6, v 6, v 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_other _ _ _ _ (by decide)

def p9B : Fin 6 → Fin 9 := ![1, 2, 3, 4, 6, 7]

theorem install_p9B (A : Fin 9 → List Bool) (v : Fin 6 → List Bool) :
    RecoveryRootRound.install p9B A v = ![A 0, v 0, v 1, v 2, v 3, A 5, v 4, v 5, A 8] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_p9B (H : Fin 9 → ℕ) (v : Fin 6 → ℕ) :
    dockH p9B H v = ![H 0, v 0, v 1, v 2, v 3, H 5, v 4, v 5, H 8] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_other _ _ _ _ (by decide)
def selPre : Fin 7 → Bool := ![true, false, false, false, false, false, false]

noncomputable def passesM :=
  Composition.machine (RecoveryFocus.machine p9A (MaskedReset.machine phAM selPre)) (RecoveryFocus.machine p9B phBM)

def passesCost (ℓ plen n : ℕ) : ℕ :=
  2 * (plen * (phACost ℓ + 2) + 1) + 2 + 1 + ((n - plen) * (phBCost ℓ + 2) + 1)

/-- **One row's passes**: phase A (prefix columns into the accumulator, the prefix word rewound), then phase B (the
remaining columns' bits `c` appended). -/
theorem passes_run (ℓ plen pfx c cap cap2 : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool) (out backing : List Bool)
    (hℓ : 1 ≤ ℓ) (hc : c < ℓ) (hr0 : r0.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 1 ≤ cap)
    (hcap2 : plen * (phACost ℓ + 2) + 1 ≤ cap2) (hplen : plen ≤ tab.length) :
    Step passesM (passesCost ℓ plen tab.length) ![0, 0, 0, 0, 0, 0, out.length, 0, 0]
      ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), r0, [b0], [false],
        overlay out backing, List.replicate cap false, List.replicate cap2 false]
      ![0, pre (tab.map (binary ℓ)) (plen + (tab.length - plen)), 0, 0, 0, 0, out.length + 2 * (tab.length - plen), 0, 0]
      ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)),
        regB ℓ tab plen (regAt ℓ tab r0 plen) (tab.length - plen),
        [bitB tab c plen (bitAt tab c b0 plen) (tab.length - plen)], [fixAcc tab pfx c plen],
        overlay (out ++ maskBits tab plen c (tab.length - plen)) backing, List.replicate cap false,
        List.replicate cap2 false] := by
  -- phase A, its prefix head rewound
  have hA := phA_run ℓ plen pfx c cap tab tail r0 b0 hc hr0 hcap hplen
  have hfix0 : fixAcc tab pfx c 0 = false := rfl
  have hAm := hA.mask (cap := cap2) selPre (by intro i _; fin_cases i <;> rfl) hcap2
  have hAm' : Step (MaskedReset.machine phAM selPre) (2 * (plen * (phACost ℓ + 2) + 1) + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), r0, [b0], [false],
        List.replicate cap false, List.replicate cap2 false]
      ![0, pre (tab.map (binary ℓ)) plen, 0, 0, 0, 0, 0, 0]
      ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), regAt ℓ tab r0 plen,
        [bitAt tab c b0 plen], [fixAcc tab pfx c plen], List.replicate cap false, List.replicate cap2 false] := by
    refine (hAm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s1 := dockRun hAm' p9A (by decide) ![0, 0, 0, 0, 0, 0, out.length, 0, 0]
    ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), r0, [b0], [false],
      overlay out backing, List.replicate cap false, List.replicate cap2 false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_p9A, install_p9A] at s1
  -- phase B
  have hB := phB_run ℓ c cap plen tab tail (regAt ℓ tab r0 plen) (bitAt tab c b0 plen) out backing hℓ hc
    (regAt_length ℓ tab r0 hr0 plen) hcap hplen
  have hB' : Step phBM ((tab.length - plen) * (phBCost ℓ + 2) + 1)
      ![pre (tab.map (binary ℓ)) plen, 0, 0, 0, out.length, 0]
      ![streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), regAt ℓ tab r0 plen, [bitAt tab c b0 plen],
        overlay out backing, List.replicate cap false]
      ![pre (tab.map (binary ℓ)) (plen + (tab.length - plen)), 0, 0, 0, out.length + 2 * (tab.length - plen), 0]
      ![streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)),
        regB ℓ tab plen (regAt ℓ tab r0 plen) (tab.length - plen),
        [bitB tab c plen (bitAt tab c b0 plen) (tab.length - plen)],
        overlay (out ++ maskBits tab plen c (tab.length - plen)) backing, List.replicate cap false] := by
    refine (hB.congr_in ?_ ?_).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · have e : maskBits tab plen c 0 = [] := rfl
      funext i; fin_cases i <;> simp only [phBA, e, List.append_nil] <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have s2 := dockRun hB' p9B (by decide) ![0, pre (tab.map (binary ℓ)) plen, 0, 0, 0, 0, out.length, 0, 0]
    ![frame (binary plen pfx), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary ℓ (2 ^ c)), regAt ℓ tab r0 plen,
      [bitAt tab c b0 plen], [fixAcc tab pfx c plen], overlay out backing, List.replicate cap false,
      List.replicate cap2 false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_p9B, install_p9B] at s2
  have hall := (s1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq s2
  exact hall.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

end NearCubicWires.WireExponent3_5.SeedFix
