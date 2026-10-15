import Proof.Wire_3_5.SeedFixFields

/-! # C4.Sb, machine part 9: the counter split into the sign word and the label and digit streams

The builder's counter `j` (`binary (W+1) j` for `W = 8 + 8ℓ + 8kh`) carries the signs `β` in its low 8 bits, the
eight labels in the next `8ℓ` bits and the eight walk digits in the top `8kh` bits (`sampTermsT_flat`). The split
writes the sign word, the stream of the eight label words, the stream of the eight digit words, and the rotated digit
stream `d₁ … d₇ d₀` that the cell words read beside the digit stream.

Paper quantities of the main type: the fields of the counter (`split_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

namespace Split

theorem binary_add_split : ∀ (a b n : ℕ), binary (a + b) n = binary a n ++ binary b (n / 2 ^ a)
  | 0, b, n => by simp [binary]
  | a + 1, b, n => by
    rw [show a + 1 + b = (a + b) + 1 by omega, binary, binary, binary_add_split a b (n / 2), Nat.div_div_eq_div_mul,
      pow_succ']
    rfl

theorem binary_mul_split (r : ℕ) : ∀ (m n : ℕ),
    binary (m * r) n = ((List.range m).map fun k => binary r (n / 2 ^ (k * r))).flatten
  | 0, n => by simp [binary]
  | m + 1, n => by
    rw [show (m + 1) * r = m * r + r by ring, binary_add_split, binary_mul_split r m n, List.range_succ,
      List.map_append, List.flatten_append]
    simp

/-- The eight fields of width `r` of `n`. -/
def fields8 (r n : ℕ) : List (List Bool) := (List.range 8).map fun k => binary r (n / 2 ^ (k * r))

theorem fields8_flatten (r n : ℕ) : (fields8 r n).flatten = binary (8 * r) n := (binary_mul_split r 8 n).symm

theorem fields8_length (r n : ℕ) : (fields8 r n).length = 8 := by simp [fields8]

theorem fields8_width (r n : ℕ) : ∀ f ∈ fields8 r n, f.length = r := by
  intro f hf
  simp only [fields8, List.mem_map] at hf
  obtain ⟨k, _, rfl⟩ := hf
  simp

/-- The counter's words: the signs, the labels, the digits. -/
theorem counter_split (ℓ kh j : ℕ) :
    binary (8 + 8 * ℓ + 8 * kh + 1) j = binary 8 j ++ (fields8 ℓ (j / 2 ^ 8)).flatten ++
      ((fields8 kh (j / 2 ^ (8 + 8 * ℓ))).flatten ++ binary 1 (j / 2 ^ (8 + 8 * ℓ + 8 * kh))) := by
  rw [binary_add_split, binary_add_split, binary_add_split, fields8_flatten, fields8_flatten]
  simp only [List.append_assoc]

/-! ## A stream of fields with its terminator, the count ruler rewound (tapes 0 the count ruler, 1 the width ruler,
2 the source, 3 the output, 4 the fields' log, then the ruler's log) -/

def s12A : Fin 5 → Fin 12 := ![8, 5, 0, 1, 10]

theorem install_s12A (A : Fin 12 → List Bool) (v : Fin 5 → List Bool) :
    RecoveryRootRound.install s12A A v = ![v 2, v 3, A 2, A 3, A 4, v 1, A 6, A 7, v 0, A 9, v 4, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12A (H : Fin 12 → ℕ) (v : Fin 5 → ℕ) :
    dockH s12A H v = ![v 2, v 3, H 2, H 3, H 4, v 1, H 6, H 7, v 0, H 9, v 4, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_other _ _ _ _ (by decide)

def s12B : Fin 6 → Fin 12 := ![5, 6, 0, 2, 10, 11]

theorem install_s12B (A : Fin 12 → List Bool) (v : Fin 6 → List Bool) :
    RecoveryRootRound.install s12B A v = ![v 2, A 1, v 3, A 3, A 4, v 0, v 1, A 7, A 8, A 9, v 4, v 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12B (H : Fin 12 → ℕ) (v : Fin 6 → ℕ) :
    dockH s12B H v = ![v 2, H 1, v 3, H 3, H 4, v 0, v 1, H 7, H 8, H 9, v 4, v 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_other _ _ _ _ (by decide)

def s12C : Fin 6 → Fin 12 := ![5, 7, 0, 3, 10, 11]

theorem install_s12C (A : Fin 12 → List Bool) (v : Fin 6 → List Bool) :
    RecoveryRootRound.install s12C A v = ![v 2, A 1, A 2, v 3, A 4, v 0, A 6, v 1, A 8, A 9, v 4, v 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12C (H : Fin 12 → ℕ) (v : Fin 6 → ℕ) :
    dockH s12C H v = ![v 2, H 1, H 2, v 3, H 4, v 0, H 6, v 1, H 8, H 9, v 4, v 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_other _ _ _ _ (by decide)

def s12D : Fin 4 → Fin 12 := ![9, 3, 4, 11]

theorem install_s12D (A : Fin 12 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install s12D A v = ![A 0, A 1, A 2, v 1, v 2, A 5, A 6, A 7, A 8, v 0, A 10, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12D (H : Fin 12 → ℕ) (v : Fin 4 → ℕ) :
    dockH s12D H v = ![H 0, H 1, H 2, v 1, v 2, H 5, H 6, H 7, H 8, v 0, H 10, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def s12T : Fin 2 → Fin 12 := ![3, 4]

theorem install_s12T (A : Fin 12 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install s12T A v = ![A 0, A 1, A 2, v 0, v 1, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12T (H : Fin 12 → ℕ) (v : Fin 2 → ℕ) :
    dockH s12T H v = ![H 0, H 1, H 2, v 0, v 1, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def s12E : Fin 1 → Fin 12 := ![4]

theorem install_s12E (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install s12E A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_s12E (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH s12E H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def l5E : Fin 1 → Fin 5 := ![3]

theorem install_l5E (A : Fin 5 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install l5E A v = ![A 0, A 1, A 2, v 0, A 4] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_l5E (H : Fin 5 → ℕ) (v : Fin 1 → ℕ) :
    dockH l5E H v = ![H 0, H 1, H 2, v 0, H 4] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def l3P : Fin 2 → Fin 3 := ![1, 2]

theorem install_l3P (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install l3P A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_l3P (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH l3P H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def selMR : Fin 5 → Bool := ![true, false, false, false, false]

noncomputable def fieldsTermM :=
  MaskedReset.machine (Composition.machine fieldsLoopM (RecoveryFocus.machine l5E EndF.machine)) selMR

def fieldsTermCost (m r : ℕ) : ℕ := 2 * (m * (fieldCost r + 2) + 1 + 1 + 1) + 2

theorem fieldsTerm_run (r : ℕ) (mus rus pre post o B : List Bool) (fs : List (List Bool)) (cL cL2 : ℕ)
    (hfs : ∀ f ∈ fs, f.length = r) (hcL : r * (2 + 2) + 1 ≤ cL) (hcL2 : fs.length * (fieldCost r + 2) + 1 + 1 + 1 ≤ cL2) :
    Step fieldsTermM (fieldsTermCost fs.length r) ![0, 0, pre.length, o.length, 0, 0]
      ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post,
        overlay o B, List.replicate cL false, List.replicate cL2 false]
      ![0, 0, pre.length + fs.length * r, (o ++ fs.flatMap frame).length + 1, 0, 0]
      ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post,
        overlay (o ++ fs.flatMap frame ++ [false]) B, List.replicate cL false, List.replicate cL2 false] := by
  have h1 := fieldsLoop_run r mus rus pre post o B fs cL hfs hcL
  have h2 := dockRun (EndF.run (o ++ fs.flatMap frame) B) l5E (by decide)
    ![fs.length, 0, pre.length + fs.length * r, (o ++ fs.flatMap frame).length, 0]
    ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus, pre ++ fs.flatten ++ post,
      overlay (o ++ fs.flatMap frame) B, List.replicate cL false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_l5E, install_l5E] at h2
  have hs := h1.seq (h2.congr (hout' := ![fs.length, 0, pre.length + fs.length * r, (o ++ fs.flatMap frame).length + 1, 0])
    (tout' := ![List.replicate fs.length true ++ false :: mus, List.replicate r true ++ false :: rus,
      pre ++ fs.flatten ++ post, overlay (o ++ fs.flatMap frame ++ [false]) B, List.replicate cL false])
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have hm := hs.mask (cap := cL2) selMR (by intro j hj; fin_cases j <;> first | rfl | simp [selMR] at hj) hcL2
  unfold fieldsTermCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

/-! ## The rotated digit stream (tapes 0 the count ruler, 1 the digit stream, 2 the rotated stream, then a log) -/

def selRD : Fin 3 → Bool := ![true, true, false]

noncomputable def rotM :=
  MaskedReset.machine (Composition.machine (RecoveryFocus.machine l3P frameP) framesLoopM) selRD

theorem rot_run (mus post B : List Bool) (d0 : List Bool) (ds : List (List Bool)) (cL2 n : ℕ)
    (hn : 2 * d0.length + 1 + 1 + 1 + 1 + (((List.range (ds.length - 0)).map
      (fun i => 2 * (ds.getD (0 + i) []).length + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ cL2)
    (hN : n = 2 * (2 * d0.length + 1 + 1 + 1 + 1 + (((List.range (ds.length - 0)).map
      (fun i => 2 * (ds.getD (0 + i) []).length + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1)) + 2) :
    Step rotM n ![0, 0, 0, 0]
      ![List.replicate ds.length true ++ false :: mus, (d0 :: ds).flatMap frame ++ post, B, List.replicate cL2 false]
      ![0, 0, (ds.flatMap frame).length, 0]
      ![List.replicate ds.length true ++ false :: mus, (d0 :: ds).flatMap frame ++ post, overlay (ds.flatMap frame) B,
        List.replicate cL2 false] := by
  set S := (d0 :: ds).flatMap frame ++ post
  have eS : S = [] ++ frame d0 ++ (ds.flatMap frame ++ post) := by simp [S]
  have h1 := frameP_run [] d0 (ds.flatMap frame ++ post) [] B
  rw [← eS] at h1
  have h1' := dockRun h1 l3P (by decide) ![0, 0, 0] ![List.replicate ds.length true ++ false :: mus, S, B]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_l3P, install_l3P] at h1'
  have eS2 : S = frame d0 ++ ds.flatMap frame ++ post := by simp [S]
  have h2 := framesLoop_run mus (frame d0) post [] B ds
  rw [← eS2] at h2
  have hs := (h1'.congr (hout' := ![0, (frame d0).length, 0]) (tout' := ![List.replicate ds.length true ++ false :: mus, S, B])
    (by funext j; fin_cases j <;> simp) (by funext j; fin_cases j <;> rfl)).seq
    (h2.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have hs' : Step (Composition.machine (RecoveryFocus.machine l3P frameP) framesLoopM)
      (2 * d0.length + 1 + 1 + 1 + 1 + (((List.range (ds.length - 0)).map
        (fun i => 2 * (ds.getD (0 + i) []).length + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1))
      ![0, 0, 0] ![List.replicate ds.length true ++ false :: mus, S, B]
      ![ds.length, (frame d0).length + (ds.flatMap frame).length, (ds.flatMap frame).length]
      ![List.replicate ds.length true ++ false :: mus, S, overlay (ds.flatMap frame) B] := by
    refine hs.congr ?_ ?_
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp [overlay]
  have hm := hs'.mask (cap := cL2) selRD (by intro j _; fin_cases j <;> rfl) hn
  subst hN
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

/-! ## The split (tapes 0 the counter, 1 the sign word, 2 the label stream, 3 the digit stream, 4 the rotated digit
stream, 5–9 unit rulers of 8, ℓ, kh, 1 and 7 cells, 10 and 11 logs) -/

def bank12 (C BT AL DG DN R8 RL RK R1 R7 : List Bool) (cL cL2 : ℕ) : Fin 12 → List Bool :=
  ![C, BT, AL, DG, DN, R8, RL, RK, R1, R7, List.replicate cL false, List.replicate cL2 false]

/-- The fields: the sign word, the label stream, the digit stream. -/
noncomputable def splitFieldsM :=
  Composition.machine (Composition.machine (RecoveryFocus.machine s12A fieldsLoopM) (RecoveryFocus.machine s12B fieldsTermM))
    (RecoveryFocus.machine s12C fieldsTermM)

/-- The rotated digit stream. -/
noncomputable def splitRotM :=
  Composition.machine (Composition.machine (RecoveryFocus.machine s12D rotM) (RecoveryFocus.machine s12T frameT))
    (RecoveryFocus.machine s12E EndF.machine)

/-- The split: the sign word, the label stream, the digit stream, the rotated digit stream. -/
noncomputable def splitBody := Composition.machine splitFieldsM splitRotM

def rotCost (kh : ℕ) : ℕ :=
  2 * (2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1)) + 2

def splitFieldsCost (ℓ kh : ℕ) : ℕ := (1 * (fieldCost 8 + 2) + 1) + 1 + fieldsTermCost 8 ℓ + 1 + fieldsTermCost 8 kh
def splitRotCost (kh : ℕ) : ℕ := rotCost kh + 1 + (2 * kh + 1 + 1 + 1) + 1 + 1

/-- The label words, the digit words, the digit head and tail of counter `j`. -/
def alphasOf (ℓ j : ℕ) : List (List Bool) := fields8 ℓ (j / 2 ^ 8)
def digsOf (ℓ kh j : ℕ) : List (List Bool) := fields8 kh (j / 2 ^ (8 + 8 * ℓ))

theorem alphasOf_length (ℓ j : ℕ) : (alphasOf ℓ j).length = 8 := fields8_length ℓ _
theorem digsOf_length (ℓ kh j : ℕ) : (digsOf ℓ kh j).length = 8 := fields8_length kh _

theorem split_A (j : ℕ) (C BTo ALo DGo DNo RL RK R7 r8s r1s rest : List Bool) (cL cL2 : ℕ)
    (hC : C = binary 8 j ++ rest) (hℓ : 8 * (2 + 2) + 1 ≤ cL) :
    Step (RecoveryFocus.machine s12A fieldsLoopM) (1 * (fieldCost 8 + 2) + 1) (fun _ => 0)
      (bank12 C BTo ALo DGo DNo (List.replicate 8 true ++ false :: r8s) RL RK (List.replicate 1 true ++ false :: r1s) R7 cL cL2)
      ![8, (frame (binary 8 j)).length, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C (overlay (frame (binary 8 j)) BTo) ALo DGo DNo (List.replicate 8 true ++ false :: r8s) RL RK
        (List.replicate 1 true ++ false :: r1s) R7 cL cL2) := by
  have hA := fieldsLoop_run 8 r1s r8s [] rest [] BTo [binary 8 j] cL (by intro f hf; simp at hf; subst hf; simp) hℓ
  have eCA : [] ++ [binary 8 j].flatten ++ rest = C := by rw [hC]; simp
  have e1 : ([] : List Bool) ++ [binary 8 j].flatMap frame = frame (binary 8 j) := by simp
  rw [eCA, e1] at hA
  have sA := dockRun hA s12A (by decide) (fun _ => 0)
    (bank12 C BTo ALo DGo DNo (List.replicate 8 true ++ false :: r8s) RL RK (List.replicate 1 true ++ false :: r1s) R7 cL cL2)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s12A, install_s12A] at sA
  refine sA.congr ?_ ?_
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> rfl

theorem split_B (ℓ j h1 : ℕ) (C BT ALo DGo DNo RK R1 R7 r8s rls post : List Bool) (cL cL2 : ℕ)
    (hC : C = binary 8 j ++ (alphasOf ℓ j).flatten ++ post)
    (hl : ℓ * (2 + 2) + 1 ≤ cL) (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) :
    Step (RecoveryFocus.machine s12B fieldsTermM) (fieldsTermCost 8 ℓ) ![8, h1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT ALo DGo DNo (List.replicate 8 true ++ false :: r8s) (List.replicate ℓ true ++ false :: rls) RK R1 R7 cL cL2)
      ![8 + 8 * ℓ, h1, ((alphasOf ℓ j).flatMap frame).length + 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT (overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo) DGo DNo (List.replicate 8 true ++ false :: r8s)
        (List.replicate ℓ true ++ false :: rls) RK R1 R7 cL cL2) := by
  have hB := fieldsTerm_run ℓ r8s rls (binary 8 j) post [] ALo (alphasOf ℓ j) cL cL2 (fields8_width ℓ _) hl
    (by rw [alphasOf_length]; exact hl2)
  have e1 : ([] : List Bool) ++ (alphasOf ℓ j).flatMap frame ++ [false] = (alphasOf ℓ j).flatMap frame ++ [false] := by simp
  have e2 : (([] : List Bool) ++ (alphasOf ℓ j).flatMap frame).length = ((alphasOf ℓ j).flatMap frame).length := by simp
  rw [← hC, alphasOf_length, e1, e2, binary_length] at hB
  have sB := dockRun hB s12B (by decide) ![8, h1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    (bank12 C BT ALo DGo DNo (List.replicate 8 true ++ false :: r8s) (List.replicate ℓ true ++ false :: rls) RK R1 R7 cL cL2)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s12B, install_s12B] at sB
  exact sB.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem split_C (ℓ kh j h1 h2 : ℕ) (C BT AL DGo DNo RL R1 R7 r8s rks post : List Bool) (cL cL2 : ℕ)
    (hC : C = binary 8 j ++ (alphasOf ℓ j).flatten ++ (digsOf ℓ kh j).flatten ++ post)
    (hk : kh * (2 + 2) + 1 ≤ cL) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2) :
    Step (RecoveryFocus.machine s12C fieldsTermM) (fieldsTermCost 8 kh) ![8 + 8 * ℓ, h1, h2, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT AL DGo DNo (List.replicate 8 true ++ false :: r8s) RL (List.replicate kh true ++ false :: rks) R1 R7 cL cL2)
      ![8 + 8 * ℓ + 8 * kh, h1, h2, ((digsOf ℓ kh j).flatMap frame).length + 1, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT AL (overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo) DNo (List.replicate 8 true ++ false :: r8s)
        RL (List.replicate kh true ++ false :: rks) R1 R7 cL cL2) := by
  have hCC := fieldsTerm_run kh r8s rks (binary 8 j ++ (alphasOf ℓ j).flatten) post [] DGo (digsOf ℓ kh j) cL cL2
    (fields8_width kh _) hk (by rw [digsOf_length]; exact hk2)
  have e1 : ([] : List Bool) ++ (digsOf ℓ kh j).flatMap frame ++ [false] = (digsOf ℓ kh j).flatMap frame ++ [false] := by simp
  have e2 : (([] : List Bool) ++ (digsOf ℓ kh j).flatMap frame).length = ((digsOf ℓ kh j).flatMap frame).length := by simp
  have e3 : (binary 8 j ++ (alphasOf ℓ j).flatten).length = 8 + 8 * ℓ := by
    simp [alphasOf, fields8_flatten]
  rw [← hC, digsOf_length, e1, e2, e3] at hCC
  have sC := dockRun hCC s12C (by decide) ![8 + 8 * ℓ, h1, h2, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    (bank12 C BT AL DGo DNo (List.replicate 8 true ++ false :: r8s) RL (List.replicate kh true ++ false :: rks) R1 R7 cL cL2)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s12C, install_s12C] at sC
  exact sC.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem split_fields (ℓ kh j : ℕ) (r8s rls rks r1s r7s BTo ALo DGo DNo : List Bool) (cL cL2 : ℕ)
    (hℓ : 8 * (2 + 2) + 1 ≤ cL) (hl : ℓ * (2 + 2) + 1 ≤ cL) (hk : kh * (2 + 2) + 1 ≤ cL)
    (hl2 : 8 * (fieldCost ℓ + 2) + 1 + 1 + 1 ≤ cL2) (hk2 : 8 * (fieldCost kh + 2) + 1 + 1 + 1 ≤ cL2) :
    Step splitFieldsM (splitFieldsCost ℓ kh) (fun _ => 0)
      (bank12 (binary (8 + 8 * ℓ + 8 * kh + 1) j) BTo ALo DGo DNo (List.replicate 8 true ++ false :: r8s)
        (List.replicate ℓ true ++ false :: rls) (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2)
      ![8 + 8 * ℓ + 8 * kh, (frame (binary 8 j)).length, ((alphasOf ℓ j).flatMap frame).length + 1,
        ((digsOf ℓ kh j).flatMap frame).length + 1, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 (binary (8 + 8 * ℓ + 8 * kh + 1) j) (overlay (frame (binary 8 j)) BTo)
        (overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo) (overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo) DNo
        (List.replicate 8 true ++ false :: r8s) (List.replicate ℓ true ++ false :: rls)
        (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2) := by
  have eC := counter_split ℓ kh j
  set tl := binary 1 (j / 2 ^ (8 + 8 * ℓ + 8 * kh))
  have sA := split_A j (binary (8 + 8 * ℓ + 8 * kh + 1) j) BTo ALo DGo DNo (List.replicate ℓ true ++ false :: rls)
    (List.replicate kh true ++ false :: rks) (List.replicate 7 true ++ false :: r7s) r8s r1s
    ((alphasOf ℓ j).flatten ++ ((digsOf ℓ kh j).flatten ++ tl)) cL cL2
    (by rw [eC]; simp [alphasOf, digsOf, List.append_assoc]) hℓ
  have sB := split_B ℓ j (frame (binary 8 j)).length (binary (8 + 8 * ℓ + 8 * kh + 1) j) (overlay (frame (binary 8 j)) BTo)
    ALo DGo DNo (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
    (List.replicate 7 true ++ false :: r7s) r8s rls ((digsOf ℓ kh j).flatten ++ tl) cL cL2
    (by rw [eC]; simp [alphasOf, digsOf, List.append_assoc]) hl hl2
  have sC := split_C ℓ kh j (frame (binary 8 j)).length (((alphasOf ℓ j).flatMap frame).length + 1)
    (binary (8 + 8 * ℓ + 8 * kh + 1) j) (overlay (frame (binary 8 j)) BTo)
    (overlay ((alphasOf ℓ j).flatMap frame ++ [false]) ALo) DGo DNo (List.replicate ℓ true ++ false :: rls)
    (List.replicate 1 true ++ false :: r1s) (List.replicate 7 true ++ false :: r7s) r8s rks tl cL cL2
    (by rw [eC]; simp [alphasOf, digsOf, List.append_assoc]) hk hk2
  exact (sA.seq sB).seq sC

theorem split_rot (ℓ kh j : ℕ) (r8s rls rks r1s r7s BT1 AL1 DGo DNo C : List Bool) (cL cL2 : ℕ) (h0 h1 h2 : ℕ)
    (hr2 : 2 * kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1) ≤ cL2) :
    Step splitRotM (splitRotCost kh) ![h0, h1, h2, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT1 AL1 (overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo) DNo (List.replicate 8 true ++ false :: r8s)
        (List.replicate ℓ true ++ false :: rls) (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2)
      ![h0, h1, h2, (frame ((digsOf ℓ kh j).headD [])).length,
        (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame).length + 1, 0, 0, 0, 1, 0, 0, 0]
      (bank12 C BT1 AL1 (overlay ((digsOf ℓ kh j).flatMap frame ++ [false]) DGo)
        (overlay (((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).flatMap frame ++ [false]) DNo)
        (List.replicate 8 true ++ false :: r8s) (List.replicate ℓ true ++ false :: rls)
        (List.replicate kh true ++ false :: rks) (List.replicate 1 true ++ false :: r1s)
        (List.replicate 7 true ++ false :: r7s) cL cL2) := by
  set DG := digsOf ℓ kh j
  set R8 := List.replicate 8 true ++ false :: r8s
  set RL := List.replicate ℓ true ++ false :: rls
  set RK := List.replicate kh true ++ false :: rks
  set R1 := List.replicate 1 true ++ false :: r1s
  set R7 := List.replicate 7 true ++ false :: r7s
  have hDG : DG = DG.headD [] :: DG.tail := by
    have hl : DG.length = 8 := fields8_length kh _
    clear_value DG
    cases DG with
    | nil => simp at hl
    | cons a l => rfl
  set d0 := DG.headD []
  set ds := DG.tail
  have hds : ∀ d ∈ ds, d.length = kh := fun d hd => fields8_width kh _ d (List.mem_of_mem_tail hd)
  have hdl : ds.length = 7 := by simp [ds, DG, digsOf, fields8_length]
  have hd0 : d0.length = kh := by
    have hm : d0 ∈ DG := by rw [hDG]; exact List.mem_cons_self
    exact fields8_width kh (j / 2 ^ (8 + 8 * ℓ)) d0 hm
  set DG1 := overlay (DG.flatMap frame ++ [false]) DGo
  set post := false :: DGo.drop (DG.flatMap frame ++ [false]).length
  have eDG : DG1 = (d0 :: ds).flatMap frame ++ post := by
    simp only [DG1, overlay, post]; rw [← hDG]; simp [List.append_assoc]
  have hsum : ((List.range (ds.length - 0)).map (fun i => 2 * (ds.getD (0 + i) []).length + 1 + 1 + 1 + 1 + 1 + 2)).sum =
      ((List.range (7 - 0)).map (fun _ => 2 * kh + 1 + 1 + 1 + 1 + 1 + 2)).sum := by
    rw [hdl]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < ds.length := by rw [hdl]; simpa using hi
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
      hds _ (List.getElem_mem hi')]
  have hD := rot_run r7s post DNo d0 ds cL2 (rotCost kh) (by rw [hsum, hd0]; exact hr2)
    (by unfold rotCost; rw [hsum, hd0])
  rw [hdl, ← eDG] at hD
  have sD := dockRun hD s12D (by decide) ![h0, h1, h2, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    (bank12 C BT1 AL1 DG1 DNo R8 RL RK R1 R7 cL cL2) (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s12D, install_s12D] at sD
  have hT := frameT_run [] d0 (ds.flatMap frame ++ post) (ds.flatMap frame) DNo
  have eT : [] ++ frame d0 ++ (ds.flatMap frame ++ post) = DG1 := by rw [eDG]; simp
  rw [eT] at hT
  have sT := dockRun hT s12T (by decide) ![h0, h1, h2, 0, (ds.flatMap frame).length, 0, 0, 0, 1, 0, 0, 0]
    (bank12 C BT1 AL1 DG1 (overlay (ds.flatMap frame) DNo) R8 RL RK R1 R7 cL cL2)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_s12T, install_s12T] at sT
  have hE := EndF.run (ds.flatMap frame ++ frame d0) DNo
  have sE := dockRun hE s12E (by decide)
    ![h0, h1, h2, (frame d0).length, (ds.flatMap frame ++ frame d0).length, 0, 0, 0, 1, 0, 0, 0]
    (bank12 C BT1 AL1 DG1 (overlay (ds.flatMap frame ++ frame d0) DNo) R8 RL RK R1 R7 cL cL2)
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_s12E, install_s12E] at sE
  have hall := ((sD.congr (hout' := ![h0, h1, h2, 0, (ds.flatMap frame).length, 0, 0, 0, 1, 0, 0, 0])
      (tout' := bank12 C BT1 AL1 DG1 (overlay (ds.flatMap frame) DNo) R8 RL RK R1 R7 cL cL2)
      (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    (sT.congr (hout' := ![h0, h1, h2, (frame d0).length, (ds.flatMap frame ++ frame d0).length, 0, 0, 0, 1, 0, 0, 0])
      (tout' := bank12 C BT1 AL1 DG1 (overlay (ds.flatMap frame ++ frame d0) DNo) R8 RL RK R1 R7 cL cL2)
      (by funext i; fin_cases i <;> simp) (by funext i; fin_cases i <;> rfl))).seq sE
  unfold splitRotCost
  rw [hd0] at hall
  refine hall.congr ?_ ?_
  · funext i; fin_cases i <;> simp [ds, d0]
  · funext i; fin_cases i <;> simp [bank12, ds, d0]

end Split

end NearCubicWires.WireExponent3_5.SeedFix
