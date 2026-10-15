import Proof.Wire_3_5.CompilerMachinePolyTerms

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The machines: the term pass with the expression's head reset, then the counter -/

noncomputable def termsLoopM := StreamController.machine termM 0
def selVT : Fin 33 → Bool := fun i => decide (i = 0)
/-- The pass over all terms, the expression's head returned to cell 0 (log on tape 33). -/
noncomputable def termsRM := MaskedReset.machine termsLoopM selVT

def sTerms : Fin 34 → Fin 37 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31, 32, 33]
def sNeq : Fin 4 → Fin 37 := ![18, 34, 35, 8]
def sInc : Fin 3 → Fin 37 := ![18, 36, 8]
noncomputable def sTermsD := RecoveryFocus.machine sTerms termsRM
noncomputable def sNeqD := RecoveryFocus.machine sNeq neqM
noncomputable def sIncD := RecoveryFocus.machine sInc incM
/-- One counter value: the term pass, then `C := [J ≠ 1^m]`, then `J := J + 1`. -/
noncomputable def subsetBodyM := Composition.machine (Composition.machine sTermsD sNeqD) sIncD
/-- **The counter loop**, while `C` (tape 35) is set. -/
noncomputable def subsetLoopM := StreamController.machine subsetBodyM 35

theorem sTerms_inj : Function.Injective sTerms := by decide

theorem install_sTerms (A : Fin 37 → List Bool) (v : Fin 34 → List Bool) :
    install sTerms A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, A 34, A 35, A 36] := by
  funext i
  fin_cases i
  · exact install_slot sTerms sTerms_inj A v 0
  · exact install_slot sTerms sTerms_inj A v 1
  · exact install_slot sTerms sTerms_inj A v 2
  · exact install_slot sTerms sTerms_inj A v 3
  · exact install_slot sTerms sTerms_inj A v 4
  · exact install_slot sTerms sTerms_inj A v 5
  · exact install_slot sTerms sTerms_inj A v 6
  · exact install_slot sTerms sTerms_inj A v 7
  · exact install_slot sTerms sTerms_inj A v 8
  · exact install_slot sTerms sTerms_inj A v 9
  · exact install_slot sTerms sTerms_inj A v 10
  · exact install_slot sTerms sTerms_inj A v 11
  · exact install_slot sTerms sTerms_inj A v 12
  · exact install_slot sTerms sTerms_inj A v 13
  · exact install_slot sTerms sTerms_inj A v 14
  · exact install_slot sTerms sTerms_inj A v 15
  · exact install_slot sTerms sTerms_inj A v 16
  · exact install_slot sTerms sTerms_inj A v 17
  · exact install_slot sTerms sTerms_inj A v 18
  · exact install_slot sTerms sTerms_inj A v 19
  · exact install_slot sTerms sTerms_inj A v 20
  · exact install_slot sTerms sTerms_inj A v 21
  · exact install_slot sTerms sTerms_inj A v 22
  · exact install_slot sTerms sTerms_inj A v 23
  · exact install_slot sTerms sTerms_inj A v 24
  · exact install_slot sTerms sTerms_inj A v 25
  · exact install_slot sTerms sTerms_inj A v 26
  · exact install_slot sTerms sTerms_inj A v 27
  · exact install_slot sTerms sTerms_inj A v 28
  · exact install_slot sTerms sTerms_inj A v 29
  · exact install_slot sTerms sTerms_inj A v 30
  · exact install_slot sTerms sTerms_inj A v 31
  · exact install_slot sTerms sTerms_inj A v 32
  · exact install_slot sTerms sTerms_inj A v 33
  · exact install_other sTerms A v 34 (by decide)
  · exact install_other sTerms A v 35 (by decide)
  · exact install_other sTerms A v 36 (by decide)

theorem dockH_sTerms (H : Fin 37 → ℕ) (v : Fin 34 → ℕ) :
    dockH sTerms H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, H 34, H 35, H 36] := by
  funext i
  fin_cases i
  · exact dockH_slot sTerms sTerms_inj H v 0
  · exact dockH_slot sTerms sTerms_inj H v 1
  · exact dockH_slot sTerms sTerms_inj H v 2
  · exact dockH_slot sTerms sTerms_inj H v 3
  · exact dockH_slot sTerms sTerms_inj H v 4
  · exact dockH_slot sTerms sTerms_inj H v 5
  · exact dockH_slot sTerms sTerms_inj H v 6
  · exact dockH_slot sTerms sTerms_inj H v 7
  · exact dockH_slot sTerms sTerms_inj H v 8
  · exact dockH_slot sTerms sTerms_inj H v 9
  · exact dockH_slot sTerms sTerms_inj H v 10
  · exact dockH_slot sTerms sTerms_inj H v 11
  · exact dockH_slot sTerms sTerms_inj H v 12
  · exact dockH_slot sTerms sTerms_inj H v 13
  · exact dockH_slot sTerms sTerms_inj H v 14
  · exact dockH_slot sTerms sTerms_inj H v 15
  · exact dockH_slot sTerms sTerms_inj H v 16
  · exact dockH_slot sTerms sTerms_inj H v 17
  · exact dockH_slot sTerms sTerms_inj H v 18
  · exact dockH_slot sTerms sTerms_inj H v 19
  · exact dockH_slot sTerms sTerms_inj H v 20
  · exact dockH_slot sTerms sTerms_inj H v 21
  · exact dockH_slot sTerms sTerms_inj H v 22
  · exact dockH_slot sTerms sTerms_inj H v 23
  · exact dockH_slot sTerms sTerms_inj H v 24
  · exact dockH_slot sTerms sTerms_inj H v 25
  · exact dockH_slot sTerms sTerms_inj H v 26
  · exact dockH_slot sTerms sTerms_inj H v 27
  · exact dockH_slot sTerms sTerms_inj H v 28
  · exact dockH_slot sTerms sTerms_inj H v 29
  · exact dockH_slot sTerms sTerms_inj H v 30
  · exact dockH_slot sTerms sTerms_inj H v 31
  · exact dockH_slot sTerms sTerms_inj H v 32
  · exact dockH_slot sTerms sTerms_inj H v 33
  · exact dockH_other sTerms H v 34 (by decide)
  · exact dockH_other sTerms H v 35 (by decide)
  · exact dockH_other sTerms H v 36 (by decide)

theorem sNeq_inj : Function.Injective sNeq := by decide

theorem install_sNeq (A : Fin 37 → List Bool) (v : Fin 4 → List Bool) :
    install sNeq A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 3, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, v 1, v 2, A 36] := by
  funext i
  fin_cases i
  · exact install_other sNeq A v 0 (by decide)
  · exact install_other sNeq A v 1 (by decide)
  · exact install_other sNeq A v 2 (by decide)
  · exact install_other sNeq A v 3 (by decide)
  · exact install_other sNeq A v 4 (by decide)
  · exact install_other sNeq A v 5 (by decide)
  · exact install_other sNeq A v 6 (by decide)
  · exact install_other sNeq A v 7 (by decide)
  · exact install_slot sNeq sNeq_inj A v 3
  · exact install_other sNeq A v 9 (by decide)
  · exact install_other sNeq A v 10 (by decide)
  · exact install_other sNeq A v 11 (by decide)
  · exact install_other sNeq A v 12 (by decide)
  · exact install_other sNeq A v 13 (by decide)
  · exact install_other sNeq A v 14 (by decide)
  · exact install_other sNeq A v 15 (by decide)
  · exact install_other sNeq A v 16 (by decide)
  · exact install_other sNeq A v 17 (by decide)
  · exact install_slot sNeq sNeq_inj A v 0
  · exact install_other sNeq A v 19 (by decide)
  · exact install_other sNeq A v 20 (by decide)
  · exact install_other sNeq A v 21 (by decide)
  · exact install_other sNeq A v 22 (by decide)
  · exact install_other sNeq A v 23 (by decide)
  · exact install_other sNeq A v 24 (by decide)
  · exact install_other sNeq A v 25 (by decide)
  · exact install_other sNeq A v 26 (by decide)
  · exact install_other sNeq A v 27 (by decide)
  · exact install_other sNeq A v 28 (by decide)
  · exact install_other sNeq A v 29 (by decide)
  · exact install_other sNeq A v 30 (by decide)
  · exact install_other sNeq A v 31 (by decide)
  · exact install_other sNeq A v 32 (by decide)
  · exact install_other sNeq A v 33 (by decide)
  · exact install_slot sNeq sNeq_inj A v 1
  · exact install_slot sNeq sNeq_inj A v 2
  · exact install_other sNeq A v 36 (by decide)

theorem dockH_sNeq (H : Fin 37 → ℕ) (v : Fin 4 → ℕ) :
    dockH sNeq H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 3, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, v 1, v 2, H 36] := by
  funext i
  fin_cases i
  · exact dockH_other sNeq H v 0 (by decide)
  · exact dockH_other sNeq H v 1 (by decide)
  · exact dockH_other sNeq H v 2 (by decide)
  · exact dockH_other sNeq H v 3 (by decide)
  · exact dockH_other sNeq H v 4 (by decide)
  · exact dockH_other sNeq H v 5 (by decide)
  · exact dockH_other sNeq H v 6 (by decide)
  · exact dockH_other sNeq H v 7 (by decide)
  · exact dockH_slot sNeq sNeq_inj H v 3
  · exact dockH_other sNeq H v 9 (by decide)
  · exact dockH_other sNeq H v 10 (by decide)
  · exact dockH_other sNeq H v 11 (by decide)
  · exact dockH_other sNeq H v 12 (by decide)
  · exact dockH_other sNeq H v 13 (by decide)
  · exact dockH_other sNeq H v 14 (by decide)
  · exact dockH_other sNeq H v 15 (by decide)
  · exact dockH_other sNeq H v 16 (by decide)
  · exact dockH_other sNeq H v 17 (by decide)
  · exact dockH_slot sNeq sNeq_inj H v 0
  · exact dockH_other sNeq H v 19 (by decide)
  · exact dockH_other sNeq H v 20 (by decide)
  · exact dockH_other sNeq H v 21 (by decide)
  · exact dockH_other sNeq H v 22 (by decide)
  · exact dockH_other sNeq H v 23 (by decide)
  · exact dockH_other sNeq H v 24 (by decide)
  · exact dockH_other sNeq H v 25 (by decide)
  · exact dockH_other sNeq H v 26 (by decide)
  · exact dockH_other sNeq H v 27 (by decide)
  · exact dockH_other sNeq H v 28 (by decide)
  · exact dockH_other sNeq H v 29 (by decide)
  · exact dockH_other sNeq H v 30 (by decide)
  · exact dockH_other sNeq H v 31 (by decide)
  · exact dockH_other sNeq H v 32 (by decide)
  · exact dockH_other sNeq H v 33 (by decide)
  · exact dockH_slot sNeq sNeq_inj H v 1
  · exact dockH_slot sNeq sNeq_inj H v 2
  · exact dockH_other sNeq H v 36 (by decide)

theorem sInc_inj : Function.Injective sInc := by decide

theorem install_sInc (A : Fin 37 → List Bool) (v : Fin 3 → List Bool) :
    install sInc A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 2, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, v 1] := by
  funext i
  fin_cases i
  · exact install_other sInc A v 0 (by decide)
  · exact install_other sInc A v 1 (by decide)
  · exact install_other sInc A v 2 (by decide)
  · exact install_other sInc A v 3 (by decide)
  · exact install_other sInc A v 4 (by decide)
  · exact install_other sInc A v 5 (by decide)
  · exact install_other sInc A v 6 (by decide)
  · exact install_other sInc A v 7 (by decide)
  · exact install_slot sInc sInc_inj A v 2
  · exact install_other sInc A v 9 (by decide)
  · exact install_other sInc A v 10 (by decide)
  · exact install_other sInc A v 11 (by decide)
  · exact install_other sInc A v 12 (by decide)
  · exact install_other sInc A v 13 (by decide)
  · exact install_other sInc A v 14 (by decide)
  · exact install_other sInc A v 15 (by decide)
  · exact install_other sInc A v 16 (by decide)
  · exact install_other sInc A v 17 (by decide)
  · exact install_slot sInc sInc_inj A v 0
  · exact install_other sInc A v 19 (by decide)
  · exact install_other sInc A v 20 (by decide)
  · exact install_other sInc A v 21 (by decide)
  · exact install_other sInc A v 22 (by decide)
  · exact install_other sInc A v 23 (by decide)
  · exact install_other sInc A v 24 (by decide)
  · exact install_other sInc A v 25 (by decide)
  · exact install_other sInc A v 26 (by decide)
  · exact install_other sInc A v 27 (by decide)
  · exact install_other sInc A v 28 (by decide)
  · exact install_other sInc A v 29 (by decide)
  · exact install_other sInc A v 30 (by decide)
  · exact install_other sInc A v 31 (by decide)
  · exact install_other sInc A v 32 (by decide)
  · exact install_other sInc A v 33 (by decide)
  · exact install_other sInc A v 34 (by decide)
  · exact install_other sInc A v 35 (by decide)
  · exact install_slot sInc sInc_inj A v 1

theorem dockH_sInc (H : Fin 37 → ℕ) (v : Fin 3 → ℕ) :
    dockH sInc H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 2, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, H 34, H 35, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other sInc H v 0 (by decide)
  · exact dockH_other sInc H v 1 (by decide)
  · exact dockH_other sInc H v 2 (by decide)
  · exact dockH_other sInc H v 3 (by decide)
  · exact dockH_other sInc H v 4 (by decide)
  · exact dockH_other sInc H v 5 (by decide)
  · exact dockH_other sInc H v 6 (by decide)
  · exact dockH_other sInc H v 7 (by decide)
  · exact dockH_slot sInc sInc_inj H v 2
  · exact dockH_other sInc H v 9 (by decide)
  · exact dockH_other sInc H v 10 (by decide)
  · exact dockH_other sInc H v 11 (by decide)
  · exact dockH_other sInc H v 12 (by decide)
  · exact dockH_other sInc H v 13 (by decide)
  · exact dockH_other sInc H v 14 (by decide)
  · exact dockH_other sInc H v 15 (by decide)
  · exact dockH_other sInc H v 16 (by decide)
  · exact dockH_other sInc H v 17 (by decide)
  · exact dockH_slot sInc sInc_inj H v 0
  · exact dockH_other sInc H v 19 (by decide)
  · exact dockH_other sInc H v 20 (by decide)
  · exact dockH_other sInc H v 21 (by decide)
  · exact dockH_other sInc H v 22 (by decide)
  · exact dockH_other sInc H v 23 (by decide)
  · exact dockH_other sInc H v 24 (by decide)
  · exact dockH_other sInc H v 25 (by decide)
  · exact dockH_other sInc H v 26 (by decide)
  · exact dockH_other sInc H v 27 (by decide)
  · exact dockH_other sInc H v 28 (by decide)
  · exact dockH_other sInc H v 29 (by decide)
  · exact dockH_other sInc H v 30 (by decide)
  · exact dockH_other sInc H v 31 (by decide)
  · exact dockH_other sInc H v 32 (by decide)
  · exact dockH_other sInc H v 33 (by decide)
  · exact dockH_other sInc H v 34 (by decide)
  · exact dockH_other sInc H v 35 (by decide)
  · exact dockH_slot sInc sInc_inj H v 1

/-! ## The counter's last value -/

theorem value_replicate_true : ∀ m : ℕ, RadixSemantics.value (List.replicate m true) + 1 = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, RadixSemantics.value, pow_succ]
    have := value_replicate_true m
    simp only [Bool.toNat_true]
    omega

theorem binary_eq_ones_iff (m k : ℕ) (hk : k < 2 ^ m) : binary m k = List.replicate m true ↔ k + 1 = 2 ^ m := by
  constructor
  · intro h
    have h1 := congrArg RadixSemantics.value h
    rw [binary_value m k hk] at h1
    rw [h1]
    exact value_replicate_true m
  · intro h
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [binary_getElem, List.getElem_replicate]
      have e : k = 2 ^ m - 1 := by omega
      rw [e, Nat.testBit_two_pow_sub_one]
      simp only [binary_length] at h1
      simp [h1]

/-! ## Banks of the counter loop -/

def sHead (o : ℕ) : Fin 37 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, 0, 0, 0]

/-- The counter loop's tapes at counter value `k`, state `st`, loop cell `cont`. -/
def sBank (x : TFix) (m k : ℕ) (st : TS) (cap5 : ℕ) (cont : Bool) : Fin 37 → List Bool :=
  ![x.VT, x.TT, st.ps.Ea, st.ps.LA, st.ps.LB, frame st.ps.R, frame st.ps.R2, frame st.ps.R3, List.replicate x.cap false,
    List.replicate x.cap2 false, List.replicate x.cap3 false, frame x.z, streamTape st.ps.G st.ps.staleG, st.ps.O,
    frame st.ps.X, frame st.ps.Y, [st.ps.Ec], [false], frame (binary m k), [st.PJ], st.CW, st.Sp, st.Op, frame st.Gw,
    frame st.Rp, frame st.Zu, frame st.Z2u, frame x.T1, frame x.T2, frame x.ZT, [st.Cu], overlay st.outs x.BWO,
    List.replicate x.cap4 false, List.replicate cap5 false, frame (List.replicate m true), [cont], [true]]

/-- The state after the counter values `0, …, k−1`. -/
def stAt (Q : ℕ) (pool : List (List SynEq)) (V : IntExpression ℕ) (st0 : TS) (k : ℕ) : TS :=
  (List.range k).foldl (fun st j => V.foldl (termNext Q pool j) st) st0

theorem stAt_succ (Q : ℕ) (pool : List (List SynEq)) (V : IntExpression ℕ) (st0 : TS) (k : ℕ) :
    stAt Q pool V st0 (k + 1) = V.foldl (termNext Q pool k) (stAt Q pool V st0 k) := by
  simp [stAt, List.range_succ, List.foldl_append]

theorem stAt_inv (Q : ℕ) (pool : List (List SynEq)) (V : IntExpression ℕ) (st0 : TS) (hQ : 1 ≤ Q)
    (hp : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (h0 : TSInv (Q + pool.flatten.length + 1) st0) :
    ∀ k, TSInv (Q + pool.flatten.length + 1) (stAt Q pool V st0 k)
  | 0 => h0
  | k + 1 => by
    rw [stAt_succ]
    exact foldl_termNext_inv Q pool k hQ V _ hp (stAt_inv Q pool V st0 hQ hp h0 k)

/-- The cost of one counter value. -/
def subsetCost (Vn CBW m NF CB d P Q W B NG NU : ℕ) : ℕ :=
  (2 * (Vn * (termCost CBW m NF CB d P Q W B NG NU + 2) + 1) + 2) + 1 + (2 * (2 * m + 1) + 2) + 1 + (2 * (2 * m + 2) + 2)

/-- The hypotheses of the term pass that do not depend on the counter value, bundled. -/
structure SubsetPre (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) (post staleT : List Bool)
    (x : TFix) (cap5 d B NF CB CBW NG NU : ℕ) : Prop where
  hVT : x.VT = V.flatMap termRec ++ false :: post
  hTT : x.TT = tableTape (childTable Q pool) staleT
  hz : x.z = z0 Q pool.flatten.length
  hT1 : x.T1 = lastT Q pool.flatten.length
  hT2 : x.T2 = levelT Q pool.flatten.length
  hZT : x.ZT = zeroT Q pool.flatten.length
  hQ : 1 ≤ Q
  hm : Padded m V
  hp : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length
  hd : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, mono.length ≤ d
  hNF : ∀ t ∈ V, ∀ f ∈ t.2, f.length ≤ NF
  hCB : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, (codeBits mono).length ≤ CB
  hB : ∀ t ∈ V, (t.2.flatten.flatMap (monoMasks pool)).length ≤ B
  hcw : ∀ t ∈ V, (cbits t.1).length ≤ CBW
  hNG : ∀ j, ∀ t ∈ V, (oddMasksM pool (selectBits t.2 j).flatten).length ≤ NG
  hNU : ∀ j, ∀ t ∈ V, (unionsM Q (oddMasksM pool (selectBits t.2 j).flatten)).length ≤ NU
  hc : Caps d pool.length Q pool.flatten.length B x.cap x.cap2 x.cap3
  hcap4 : 1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1) ≤ x.cap4
  hcwc : 2 * CBW + 1 ≤ x.cap
  hcap2u : pass1Cost NU (Q + pool.flatten.length + 1) ≤ x.cap2 ∧
    appendCost NU (NU + 1) (Q + pool.flatten.length + 1) ≤ x.cap2
  hcap3u : NG * (aCost NU (Q + pool.flatten.length + 1) + 2) + 1 ≤ x.cap3
  hcap3o : NU * (2 * (Q + pool.flatten.length + 1) + 1 + 1 + 1 + 2) + 1 ≤ x.cap3
  hcapm : 2 * m + 2 ≤ x.cap
  hcap5 : V.length * (termCost CBW m NF CB d pool.length Q pool.flatten.length B NG NU + 2) + 1 ≤ cap5

/-- **One counter value**: the pass over all terms, then the loop cell and the counter. -/
theorem subset_step (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) (post staleT : List Bool)
    (x : TFix) (st : TS) (k cap5 d B NF CB CBW NG NU : ℕ)
    (h : SubsetPre Q pool m V post staleT x cap5 d B NF CB CBW NG NU) (hk : k < 2 ^ m)
    (hinv : TSInv (Q + pool.flatten.length + 1) st) :
    Step subsetBodyM (subsetCost V.length CBW m NF CB d pool.length Q pool.flatten.length B NG NU)
      (sHead st.outs.length) (sBank x m k st cap5 true)
      (sHead (V.foldl (termNext Q pool k) st).outs.length)
      (sBank x m (k + 1) (V.foldl (termNext Q pool k) st) cap5 (decide (k + 1 < 2 ^ m))) := by
  set x' : TFix := { x with Jt := frame (binary m k) }
  have e1 := terms_run Q pool k m V [] post staleT x' st d B NF CB CBW NG NU (by simpa [x'] using h.hVT) h.hTT h.hz rfl
    h.hT1 h.hT2 h.hZT h.hQ h.hm h.hp h.hd h.hNF h.hCB h.hB h.hcw (h.hNG k) (h.hNU k) h.hc h.hcap4 h.hcwc h.hcap2u
    h.hcap3u h.hcap3o hinv
  simp only [List.length_nil, Nat.zero_add] at e1
  have e2 := e1.mask (cap := cap5) selVT (by intro i hi; fin_cases i <;> simp_all [selVT, tHead]) h.hcap5
  have s1 := dockRun e2 sTerms sTerms_inj (sHead st.outs.length) (sBank x m k st cap5 true)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_sTerms, dockH_sTerms] at s1
  set st' := V.foldl (termNext Q pool k) st
  have s1' := s1.congr (hout' := sHead st'.outs.length) (tout' := sBank x m k st' cap5 true)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have hbl : (binary m k).length = (List.replicate m true).length := by simp
  have e4 := neqStep (binary m k) (List.replicate m true) true hbl x.cap (by rw [binary_length]; have := h.hcapm; omega)
  rw [zeroHeads4] at e4
  have s2 := dockKeep e4 sNeq sNeq_inj (sHead st'.outs.length) (sBank x m k st' cap5 true)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_sNeq] at s2
  have e5 := incStep m k true x.cap h.hcapm
  rw [zeroHeads3] at e5
  have s3 := dockKeep e5 sInc sInc_inj (sHead st'.outs.length)
    (sBank x m k st' cap5 (!decide (binary m k = List.replicate m true)))
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_sInc] at s3
  have s2' := s2.congr (hout' := sHead st'.outs.length)
    (tout' := sBank x m k st' cap5 (!decide (binary m k = List.replicate m true)))
    rfl (by funext i; fin_cases i <;> rfl)
  have hall := (s1'.seq s2').seq s3
  have hcont : (!decide (binary m k = List.replicate m true)) = decide (k + 1 < 2 ^ m) := by
    by_cases he : k + 1 = 2 ^ m
    · have := (binary_eq_ones_iff m k hk).mpr he
      simp [this, he]
    · have hne : binary m k ≠ List.replicate m true := fun e => he ((binary_eq_ones_iff m k hk).mp e)
      simp [hne]
      omega
  refine (hall.enlarge (by unfold subsetCost; simp only [binary_length]; omega)).congr rfl ?_
  funext i; fin_cases i <;> simp [sBank, hcont]

/-! ## The counter loop -/

theorem subsets_run (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) (post staleT : List Bool)
    (x : TFix) (st0 : TS) (cap5 d B NF CB CBW NG NU : ℕ)
    (h : SubsetPre Q pool m V post staleT x cap5 d B NF CB CBW NG NU)
    (hinv : TSInv (Q + pool.flatten.length + 1) st0) :
    Step subsetLoopM (2 ^ m * (subsetCost V.length CBW m NF CB d pool.length Q pool.flatten.length B NG NU + 2) + 1)
      (sHead st0.outs.length) (sBank x m 0 st0 cap5 true)
      (sHead (stAt Q pool V st0 (2 ^ m)).outs.length) (sBank x m (2 ^ m) (stAt Q pool V st0 (2 ^ m)) cap5 false) := by
  let W : WhileBody 37 _ :=
    { body := subsetBodyM
      tape := 35
      bound := 2 ^ m
      H := fun k => sHead (stAt Q pool V st0 k).outs.length
      A := fun k => sBank x m k (stAt Q pool V st0 k) cap5 (decide (k < 2 ^ m))
      cost := fun _ => subsetCost V.length CBW m NF CB d pool.length Q pool.flatten.length B NG NU
      step := fun k hk => by
        have e := subset_step Q pool m V post staleT x (stAt Q pool V st0 k) k cap5 d B NF CB CBW NG NU h hk
          (stAt_inv Q pool V st0 h.hQ h.hp hinv k)
        rw [← stAt_succ] at e
        have hdk : decide (k < 2 ^ m) = true := decide_eq_true hk
        show Step subsetBodyM _ (sHead (stAt Q pool V st0 k).outs.length)
          (sBank x m k (stAt Q pool V st0 k) cap5 (decide (k < 2 ^ m))) _ _
        rw [hdk]
        exact e
      cont := fun k hk => by
        show readTapeBit [decide (k < 2 ^ m)] 0 = true
        simp [hk]; rfl
      halt := by
        show readTapeBit [decide (2 ^ m < 2 ^ m)] 0 = false
        simp; rfl }
  have hW := W.run
  rw [W.rest_const _ (fun _ => rfl)] at hW
  have e0 : W.A 0 = sBank x m 0 st0 cap5 true := by
    show sBank x m 0 (stAt Q pool V st0 0) cap5 (decide (0 < 2 ^ m)) = _
    simp [stAt]
  have e1 : W.A W.bound = sBank x m (2 ^ m) (stAt Q pool V st0 (2 ^ m)) cap5 false := by
    show sBank x m (2 ^ m) (stAt Q pool V st0 (2 ^ m)) cap5 (decide (2 ^ m < 2 ^ m)) = _
    simp
  have e2 : W.H 0 = sHead st0.outs.length := by show sHead (stAt Q pool V st0 0).outs.length = _; simp [stAt]
  rw [e0, e1, e2] at hW
  exact hW

/-! ## The output -/

/-- The group of one term and one counter value. -/
def groupOf (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (t : ℤ × List (F2Poly ℕ)) : List Bool :=
  groupWord (cbits t.1) (decide ((selectBits t.2 j).length % 2 = 1))
    ((unionsM Q (oddMasksM pool (selectBits t.2 j).flatten)).map (ew Q pool.flatten.length))

/-- **The compiler stages' output before stacking**: for each counter value, for each term, its group. -/
def groupsRef (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) : List Bool :=
  (List.range (2 ^ m)).flatMap fun j => V.flatMap (groupOf Q pool j)

theorem foldl_termNext_outs (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (hQ : 1 ≤ Q) : ∀ (V : IntExpression ℕ) (st : TS),
    (∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) →
      (V.foldl (termNext Q pool j) st).outs = st.outs ++ V.flatMap (groupOf Q pool j)
  | [], _, _ => by simp
  | t :: V, st, hp => by
    rw [List.foldl_cons, foldl_termNext_outs Q pool j hQ V _ (fun t' ht' => hp t' (List.mem_cons_of_mem t ht')),
      termNext_outs, termNext_E Q pool j st t hQ (hp t List.mem_cons_self)]
    have hpar : (psAfter Q pool j t st).2.1 = decide ((selectBits t.2 j).length % 2 = 1) :=
      factors_PJ Q pool t.2 j _
    rw [hpar]
    simp [groupOf, List.append_assoc]

/-- **The output after the counter loop is `groupsRef`** (after the output's initial content). -/
theorem subsets_outs (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) (st0 : TS) (hQ : 1 ≤ Q)
    (hp : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) :
    (stAt Q pool V st0 (2 ^ m)).outs = st0.outs ++ groupsRef Q pool m V := by
  have : ∀ k, (stAt Q pool V st0 k).outs = st0.outs ++ (List.range k).flatMap fun j => V.flatMap (groupOf Q pool j) := by
    intro k
    induction k with
    | zero => simp [stAt]
    | succ k ih =>
      rw [stAt_succ, foldl_termNext_outs Q pool k hQ V _ hp, ih, List.range_succ, List.flatMap_append]
      simp [List.append_assoc]
  exact this (2 ^ m)

/-! ## Twins -/

/-- The counter order of the sub-lists of three factors. -/
theorem sublists_twin : ([1, 2, 3] : List ℕ).sublists = (List.range 8).map (selectBits [1, 2, 3]) := by decide

/-- The twin pool's two-factor term `x₀ · x₁` under counter value `3` (both factors): the cancelled polynomial has the
masks of `x₀ ⊕ x₁`, and its parity bit is `0`. -/
theorem group_twin :
    selectBits ([[[0]], [[1]]] : List (F2Poly ℕ)) 3 = [[[0]], [[1]]] ∧
      oddMasksM twinPool ([[[0]], [[1]]] : List (F2Poly ℕ)).flatten = [1, 2, 4] ∧
      decide ((selectBits ([[[0]], [[1]]] : List (F2Poly ℕ)) 3).length % 2 = 1) = false := by
  decide

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
