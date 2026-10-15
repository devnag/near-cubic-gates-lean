import Proof.Gates.Expand.Fam3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem famUpTo_length (Wb V j : ℕ) : (famUpTo Wb V j).length = (fam V j).length * (2 * Wb + 1) := by
  rw [famUpTo_eq, len_frames, famRecs_length]

theorem se_restore {σ τ : WState ns nr} {S : List (Fin (ns + 1))} {Rg : List (Fin nr)} {x : Fin nr}
    (h : SameExcept σ τ S (x :: Rg)) (hx : τ.val x = σ.val x) : SameExcept σ τ S Rg :=
  ⟨h.1, fun r hr => by
    by_cases e : r = x
    · subst e; exact hx
    · exact h.2.1 r (by simp [e, hr]), h.2.2⟩

theorem se_sub {σ τ : WState ns nr} {S S' : List (Fin (ns + 1))} {Rg Rg' : List (Fin nr)}
    (h : SameExcept σ τ S Rg) (hS : S ⊆ S') (hR : Rg ⊆ Rg') : SameExcept σ τ S' Rg' :=
  h.weaken (fun _ hx => hS hx) (fun _ hr => hR hr)

section PhaseSpec
variable {UF : Fin 12 ↪ Fin (ns + 1)} {RF : Fin 14 ↪ Fin nr}

/-- The family phase's end. -/
structure FDone (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr) (Wb V D : ℕ) (σ0 σ : WState ns nr) : Prop where
  fam : ∃ junk, σ.st (UF 2) = recStream ((famRecs V D).map (binary Wb)) ++ junk
  famh : σ.sh (UF 2) = 0
  wkh : σ.sh (UF 3) = 0
  wkl : (σ.st (UF 3)).length ≤ 2 * Wb + 1
  S : ∃ x, NumOn σ (UF 4) Wb x
  P : ∃ x, NumOn σ (UF 5) Wb x
  E : ∃ x, NumOn σ (UF 6) Wb x
  one : NumOn σ (UF 7) Wb 1
  T : NumOn σ (UF 8) Wb (2 ^ V)
  DT : ∃ x, NumOn σ (UF 9) Wb x
  mask : NumOn σ (UF 10) Wb (2 ^ V - 1)
  regs : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13] : List (Fin 14)) → σ.val (RF k) = 0
  rv : σ.val (RF 10) = V
  fr : SameExcept σ0 σ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9]
    [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13]
  curh : σ.sh (UF 0) = 0
  nxth : σ.sh (UF 1) = 0

def famPhaseCost (Wb V D N : ℕ) : ℕ :=
  famInitCost Wb + 1 + ((D * ((famLoopCost Wb V N + 1 + famTailCost Wb N) + 8) + 7 * D + 3) + 1 +
    (5 * (N * (2 * Wb + 1)) + 3))

theorem famPhase_spec (cap Wb V D : ℕ) (σ : WState ns nr) (h : FS0 UF RF Wb V σ) (hRD : σ.val (RF 8) = D)
    (hRD2 : σ.val (RF 9) = 0) (hVW : V + 1 < Wb) (hDW : (D + 3) * 2 ^ V < 2 ^ Wb) (hcap : 4 * Wb + 4 ≤ cap)
    (hcapV : 2 * V ≤ cap) (hcapD : 2 * D ≤ cap)
    (hcapA : ((fam V D).length + 2) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (famPhase UF RF) σ (famPhaseCost Wb V D (fam V D).length)
      (fun τ => FDone UF RF Wb V D σ τ ∧ τ.val (RF 8) = D ∧ τ.val (RF 9) = 0) := by
  set N := (fam V D).length with hN
  set L0F := σ.st (UF 2) with hL0F
  refine Runs.seq (famInit_spec cap Wb V σ h (by omega) hcap) (fun σ1 h1 => ?_)
  let Inv : ℕ → WState ns nr → Prop := fun j τ => FLS UF RF Wb V j [] L0F τ τ ∧
    SameExcept σ τ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9]
      (RF 8 :: RF 9 :: [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13])
  have hrep := Runs.rep (cap := cap) (K := RF 8) (K2 := RF 9) (body := famLevel UF RF) (rfN (by decide))
    (famLoopCost Wb V N + 1 + famTailCost Wb N) D Inv hcapD
    (fun j τ v ⟨hF, hfr⟩ => ⟨hF.setv 8 (Or.inl rfl) v, SameExcept.trans hfr (sameExcept_setv τ (by simp) v)⟩)
    (fun j τ v ⟨hF, hfr⟩ => ⟨hF.setv 9 (Or.inr rfl) v, SameExcept.trans hfr (sameExcept_setv τ (by simp) v)⟩)
    (fun j hj τ ⟨hF, hfr⟩ => by
      have hjD : j + 1 ≤ D := hj
      have hl := famLevel_spec cap Wb V j [] L0F τ τ hF hVW
        (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hDW) (by omega) hcapV
        (by have := level2_le_fam V D j hjD; nlinarith)
        (by rw [List.nil_append, famUpTo_length]; have := fam_mono V (j + 1) D hjD; nlinarith)
      refine (hl.mono ?_ (fun τ' hF' => ⟨⟨hF'.self, SameExcept.trans hfr (se_sub hF'.fr
        (by simp [List.cons_subset]) (by simp [List.cons_subset]))⟩,
        hF'.fr.val (by simp [rfN]), hF'.fr.val (by simp [rfN])⟩))
      have h1 : (level V j).length ≤ N := level_le_fam V D j (by omega)
      have h2 : (level V (j + 1)).length ≤ N := level_le_fam V D (j + 1) hjD
      unfold famLoopCost famTailCost
      have e1 := Nat.mul_le_mul_right (famBodyCost Wb V + (50 * Wb + 30)) h1
      have e2 := Nat.mul_le_mul_right (2 * Wb + 1) h2
      have e3 := Nat.mul_le_mul_right (40 * Wb + 11 + (50 * Wb + 30)) h2
      omega)
  have hInv0 : Inv 0 σ1 := ⟨h1.self, se_sub h1.fr (by simp [List.cons_subset]) (by simp [List.cons_subset])⟩
  have hRD1 : σ1.val (RF 8) = D := by rw [h1.fr.val (by simp [rfN])]; exact hRD
  have hRD21 : σ1.val (RF 9) = 0 := by rw [h1.fr.val (by simp [rfN])]; exact hRD2
  refine Runs.seq (hrep σ1 hInv0 hRD1 hRD21) (fun τ ⟨⟨hF, hfr⟩, hK, hK2⟩ => ?_)
  -- close FAM
  have hO := hF.fam
  rw [List.nil_append] at hO
  refine (closeNum cap τ _ _ hO (by rw [famUpTo_length]; nlinarith)).mono (by rw [famUpTo_length])
    (fun ρ ⟨hst, hsh, hcf, f⟩ => ⟨?_, ?_, ?_⟩)
  · have nin2 : ∀ k : Fin 12, k ≠ 2 → UF k ∉ [UF 2] := by
      intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (UF.injective hm)
    have rin6 : ∀ k : Fin 14, k ≠ 6 → RF k ∉ [RF 6] := by
      intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (RF.injective hm)
    refine ⟨?_, hsh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨junk, hj⟩ := overlay_rec (famUpTo Wb V D) L0F
      exact ⟨junk, by rw [hst, hj, famUpTo_eq, ← NearCubicGates.Close.Expand.flatMap_frame_binary]; rfl⟩
    · rw [f.sh (nin2 3 (by decide))]; exact hF.wkh
    · rw [f.st (nin2 3 (by decide))]; exact hF.wkl
    · obtain ⟨x, hx⟩ := hF.S; exact ⟨x, f.numOn (nin2 4 (by decide)) hx⟩
    · obtain ⟨x, hx⟩ := hF.P; exact ⟨x, f.numOn (nin2 5 (by decide)) hx⟩
    · obtain ⟨x, hx⟩ := hF.E; exact ⟨x, f.numOn (nin2 6 (by decide)) hx⟩
    · exact f.numOn (nin2 7 (by decide)) hF.one
    · exact f.numOn (nin2 8 (by decide)) hF.T
    · exact ⟨_, f.numOn (nin2 9 (by decide)) hF.dtn⟩
    · exact f.numOn (nin2 10 (by decide)) hF.mask
    · intro k hk
      by_cases h6 : k = 6
      · subst h6; exact hcf
      · rw [f.val (rin6 k h6)]
        exact hF.regs k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; tauto)
    · rw [f.val (rin6 10 (by decide))]; exact hF.rv
    · have hall : SameExcept σ ρ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9]
          (RF 8 :: RF 9 :: [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13]) :=
        SameExcept.trans hfr (se_sub f (by simp [List.cons_subset]) (by simp [List.cons_subset]))
      refine se_restore (se_restore hall ?_) ?_
      · rw [f.val (by simp [rfN]), hK, hRD]
      · rw [f.val (by simp [rfN]), hK2, hRD2]
    · rw [f.sh (nin2 0 (by decide))]; exact hF.curh
    · rw [f.sh (nin2 1 (by decide))]; exact hF.nxth
  · rw [f.val (by simp [rfN])]; exact hK
  · rw [f.val (by simp [rfN])]; exact hK2

end PhaseSpec

end NearCubicGates.Close.Expand
