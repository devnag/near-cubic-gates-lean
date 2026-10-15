import Proof.Wire_3_5.PrimAsmPopCellNum
import Proof.Wire_3_5.PrimAsmPopLink

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopCellW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW
open NearCubicWires.WireExponent3_5.PrimAsm.PopRecW NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.PopCellNum
open NearCubicWires.WireExponent3_5.PrimAsm.PopParams NearCubicWires.WireExponent3_5.PrimAsm.LevelW
open NearCubicWires.WireExponent3_5.PrimAsm.Arith

section Cell
variable {ns nr : ℕ} (cap : ℕ) (P : Fin 200 ↪ Fin nr)

/-- The record's registers `X = P 0 … P 63`. -/
def Xe : PReg nr := ⟨fun i => P (Fin.castLE (by norm_num) i), fun a b h => Fin.castLE_injective _ (P.injective h)⟩

theorem Xe_apply (k : Fin 64) : Xe P k = P (Fin.castLE (by norm_num) k) := rfl

theorem Xe_lit (k : Fin 64) (j : Fin 200) (h : k.val = j.val) : Xe P k = P j := by
  rw [Xe_apply]
  exact congrArg P (Fin.ext h)

/-- **The POP cell's word program**: the numbers, the record, the record stream rewound. -/
def popCellW (O S D : Fin (ns + 1)) : WM ns nr :=
  .seq (popNumW P D) (.seq (popRecW O S (Xe P) cwOne cwNeg) (WM.rewind O (Xe P 0)))

theorem numX (σ τ : WState ns nr) (L d c R Lg cp J n : ℕ)
    (hr : ∀ i : Fin 200, i.val < 64 → τ.val (P i) = xNew L d c R Lg cp J n i.val (σ.val (P i))) (k : Fin 64) :
    τ.val (Xe P k) = xNew L d c R Lg cp J n k.val (σ.val (Xe P k)) := by
  rw [Xe_apply]
  exact hr _ (by simp)

theorem xNew_of (L d c R Lg cp J n i old : ℕ)
    (h : i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 51 ∧ i ≠ 54 ∧ i ≠ 55 ∧ i ≠ 56 ∧ i ≠ 57 ∧ i ≠ 58) :
    xNew L d c R Lg cp J n i old = old := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  simp [xNew, a1, a2, a3, a4, a5, a6, a7, a8]

theorem xNew_13 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 13 old = 4 * L := by
  simp [xNew]

theorem xNew_14 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 14 old = d := by
  simp [xNew]

theorem xNew_51 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 51 old = c + 1 := by
  simp [xNew]

theorem xNew_54 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 54 old = R := by
  simp [xNew]

theorem xNew_55 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 55 old = Lg := by
  simp [xNew]

theorem xNew_56 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 56 old = cp := by
  simp [xNew]

theorem xNew_57 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 57 old = (J + 1) * (2 * L + 1) := by
  simp [xNew]

theorem xNew_58 (L d c R Lg cp J n old : ℕ) : xNew L d c R Lg cp J n 58 old = n * ((J + 1) * (2 * L + 1) + 1) := by
  simp [xNew]

/-- **The record writer's registers after the numbers stage** (`PopBlockW.BlockRegs` at `s' = 0`). -/
theorem blockRegs_num (σ τ : WState ns nr) (L d c R Lg cp J n r4 G off Sv M : ℕ) (sgn : Bool)
    (hr : ∀ i : Fin 200, i.val < 64 → τ.val (P i) = xNew L d c R Lg cp J n i.val (σ.val (P i)))
    (h1 : σ.val (Xe P 1) = r4) (h2 : σ.val (Xe P 2) = G) (h3 : σ.val (Xe P 3) = off) (h4 : σ.val (Xe P 4) = L)
    (h20 : σ.val (Xe P 20) = Sv) (h21 : σ.val (Xe P 21) = J) (h44 : σ.val (Xe P 44) = M)
    (h45 : σ.val (Xe P 45) = L) (h50 : σ.val (Xe P 50) = if sgn then 1 else 0)
    (hzA : ∀ k : Fin 64, (5 ≤ k.val ∧ k.val ≤ 19) ∨ (22 ≤ k.val ∧ k.val ≤ 43) ∨ (46 ≤ k.val ∧ k.val ≤ 49) ∨
      k.val = 51 ∨ (54 ≤ k.val ∧ k.val ≤ 62) → σ.val (Xe P k) = 0) :
    BlockRegs (Xe P) τ (4 * L) d r4 G off L Sv J M L 0 c ((J + 1) * (2 * L + 1)) sgn where
  h1 := (numX P σ τ L d c R Lg cp J n hr 1).trans ((xNew_of L d c R Lg cp J n 1 _ (by decide)).trans h1)
  h2 := (numX P σ τ L d c R Lg cp J n hr 2).trans ((xNew_of L d c R Lg cp J n 2 _ (by decide)).trans h2)
  h3 := (numX P σ τ L d c R Lg cp J n hr 3).trans ((xNew_of L d c R Lg cp J n 3 _ (by decide)).trans h3)
  h4 := (numX P σ τ L d c R Lg cp J n hr 4).trans ((xNew_of L d c R Lg cp J n 4 _ (by decide)).trans h4)
  hz1 := fun i a b => (numX P σ τ L d c R Lg cp J n hr i).trans
    ((xNew_of L d c R Lg cp J n i.val _ ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩).trans (hzA i (Or.inl ⟨by omega, by omega⟩)))
  h13 := (numX P σ τ L d c R Lg cp J n hr 13).trans (xNew_13 L d c R Lg cp J n _)
  h14 := (numX P σ τ L d c R Lg cp J n hr 14).trans (xNew_14 L d c R Lg cp J n _)
  h19 := (numX P σ τ L d c R Lg cp J n hr 19).trans
    ((xNew_of L d c R Lg cp J n 19 _ (by decide)).trans (hzA 19 (by decide)))
  h20 := (numX P σ τ L d c R Lg cp J n hr 20).trans ((xNew_of L d c R Lg cp J n 20 _ (by decide)).trans h20)
  h21 := (numX P σ τ L d c R Lg cp J n hr 21).trans ((xNew_of L d c R Lg cp J n 21 _ (by decide)).trans h21)
  hz2 := fun i a b => (numX P σ τ L d c R Lg cp J n hr i).trans
    ((xNew_of L d c R Lg cp J n i.val _ ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩).trans (hzA i (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  h44 := (numX P σ τ L d c R Lg cp J n hr 44).trans ((xNew_of L d c R Lg cp J n 44 _ (by decide)).trans h44)
  h45 := (numX P σ τ L d c R Lg cp J n hr 45).trans ((xNew_of L d c R Lg cp J n 45 _ (by decide)).trans h45)
  h46 := (numX P σ τ L d c R Lg cp J n hr 46).trans
    ((xNew_of L d c R Lg cp J n 46 _ (by decide)).trans (hzA 46 (by decide)))
  h47 := (numX P σ τ L d c R Lg cp J n hr 47).trans
    ((xNew_of L d c R Lg cp J n 47 _ (by decide)).trans (hzA 47 (by decide)))
  h48 := (numX P σ τ L d c R Lg cp J n hr 48).trans
    ((xNew_of L d c R Lg cp J n 48 _ (by decide)).trans (hzA 48 (by decide)))
  h49 := (numX P σ τ L d c R Lg cp J n hr 49).trans
    ((xNew_of L d c R Lg cp J n 49 _ (by decide)).trans (hzA 49 (by decide)))
  h50 := (numX P σ τ L d c R Lg cp J n hr 50).trans ((xNew_of L d c R Lg cp J n 50 _ (by decide)).trans h50)
  h51 := (numX P σ τ L d c R Lg cp J n hr 51).trans (xNew_51 L d c R Lg cp J n _)
  h57 := (numX P σ τ L d c R Lg cp J n hr 57).trans (xNew_57 L d c R Lg cp J n _)
  h61 := (numX P σ τ L d c R Lg cp J n hr 61).trans
    ((xNew_of L d c R Lg cp J n 61 _ (by decide)).trans (hzA 61 (by decide)))
  h62 := (numX P σ τ L d c R Lg cp J n hr 62).trans
    ((xNew_of L d c R Lg cp J n 62 _ (by decide)).trans (hzA 62 (by decide)))

/-- A bound on the POP cell's word program. -/
def popCellBound (cap Sv J M L r4 G off n d Mlab lw θ R cp c ulen : ℕ) : ℕ :=
  numABound cap Sv J M L r4 G off L + 1 + numBBound cap J L n d M Mlab lw + 1 +
    (popRecBound cap n θ R (R + 1) cp J M c (4 * L) d r4 G off L (cwOne.length + cwNeg.length) + 1 + (5 * ulen + 1))

/-- **The POP cell's word program**: from the list's numbers in `X`, an empty record stream `O` and the list walk's
table on `S`, the record stream holds C2's POP row record at Route B's capacities, its head at `0`; every stream but
`O` and the dummy `D` is kept. -/
theorem popCellW_spec (O S D : Fin (ns + 1)) (hOS : O ≠ S) (hOD : O ≠ D) (hSD : S ≠ D) (σ : WState ns nr)
    (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off Mlab θ lw CAP LL R cp : ℕ) (sgn : Bool)
    (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) (hlen : (sliceLabs r4 G off L).length = 4 * L)
    (hlw : lw = lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L + Pl.M + 2)
    (hCAP : CAP = labSum (sliceLabs r4 G off L)) (hLL : LL = ((sliceLabs r4 G off L).flatMap labE).length)
    (hR : R = PopCap.popKc L (3 * lbP Pl) (capP Pl L) CAP (PopNums.blF L (3 * lbP Pl) (capP Pl L) CAP LL lw Pl.M) + 1)
    (hcp : cp = PopCap.popCapB Pl.walkLen R (PopCap.popPW L (3 * lbP Pl) Mlab))
    (h0 : σ.val (Xe P 0) = 0) (h1 : σ.val (Xe P 1) = r4) (h2 : σ.val (Xe P 2) = G) (h3 : σ.val (Xe P 3) = off)
    (h4 : σ.val (Xe P 4) = L) (h20 : σ.val (Xe P 20) = CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B))
    (h21 : σ.val (Xe P 21) = Pl.base.J) (h44 : σ.val (Xe P 44) = Pl.M) (h45 : σ.val (Xe P 45) = L)
    (h50 : σ.val (Xe P 50) = if sgn then 1 else 0) (h52 : σ.val (Xe P 52) = Pl.walkLen) (h53 : σ.val (Xe P 53) = θ)
    (h63 : σ.val (Xe P 63) = s.val)
    (hzA : ∀ k : Fin 64, (5 ≤ k.val ∧ k.val ≤ 19) ∨ (22 ≤ k.val ∧ k.val ≤ 43) ∨ (46 ≤ k.val ∧ k.val ≤ 49) ∨
      k.val = 51 ∨ (54 ≤ k.val ∧ k.val ≤ 62) → σ.val (Xe P k) = 0)
    (hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 170 → σ.val (P j) = 0) (h180 : σ.val (P 180) = Mlab)
    (hO0 : σ.st O = []) (hO1 : σ.sh O = 0) (hD : σ.sh D = (σ.st D).length)
    (hS : ∀ i < (tableW Pl.walkLen Pl.base.J (rowKP Pl e L)).length,
      readTapeBit (σ.st S) (σ.sh S + i) = (tableW Pl.walkLen Pl.base.J (rowKP Pl e L)).getD i false)
    (hM : off + L + (r4 + 4) * G ≤ Mlab)
    (hcap : lvCap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.base.J ≤ cap)
    (hdc : 3 * lbP Pl ≤ cap) (hJc : Pl.base.J + 1 ≤ cap)
    (hSc : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ cap) (hlwc : lw ≤ cap) (hMc : Pl.M ≤ cap)
    (hcL : 4 * L ≤ cap)
    (hcap3 : L * (4 * (4 * Mlab + 4)) + 5 + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) +
      4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + L + 20 ≤ cap) (hac3 : CAP + LL ≤ cap)
    (hQc : (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) + 2 ≤ cap) (hc4 : capP Pl L + 8 ≤ cap)
    (hin : L + capP Pl L + Pl.M + Mlab + Pl.walkLen ≤ cap)
    (hnum : ∀ i, evalL (vIn L (3 * lbP Pl) (capP Pl L) CAP LL Pl.M Mlab Pl.walkLen lw ((8 * L + 2) ^ (3 * lbP Pl)))
      PopNums.numOps i ≤ cap)
    (h2c : 2 ≤ cap) (hcV : (Pl.base.J + 1) * (2 * L + 1) + 1 ≤ cap)
    (hcT : Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤ cap)
    (hθc : θ ≤ cap) (hRc1 : R + 1 ≤ cap) (hcpc : cp ≤ cap)
    (hbig : (frame (popRowRec Pl.walkLen θ R (R + 1) cp (oneWC Pl s)
      (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s))).length + 2 + labCapA (4 * L) (3 * lbP Pl) +
      (pieceA (4 * L) (3 * lbP Pl)).length + labCapB r4 G off L Mlab ≤ cap) :
    ∃ m τ, WExec cap (popCellW P O S D) σ τ m ∧
      τ.st O = frame (popRowRec Pl.walkLen θ R (R + 1) cp (oneWC Pl s)
        (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s)) ∧ τ.sh O = 0 ∧
      (∀ T, T ≠ O → T ≠ D → τ.st T = σ.st T ∧ τ.sh T = σ.sh T) ∧
      m ≤ popCellBound cap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.M L r4 G off
        Pl.walkLen (3 * lbP Pl) Mlab lw θ R cp (capP Pl L)
        (frame (popRowRec Pl.walkLen θ R (R + 1) cp (oneWC Pl s)
          (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s))).length := by
  have hbM : Pl.base.M = Pl.M := rfl
  obtain ⟨u, hu⟩ : ∃ x, x = frame (popRowRec Pl.walkLen θ R (R + 1) cp (oneWC Pl s)
      (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s)) := ⟨_, rfl⟩
  have hlink := popRec_link Pl e L sgn r4 G off hlen hlabs s θ R (R + 1) cp
  rw [← hu] at hbig hlink ⊢
  obtain ⟨mN, τN, eN, rN, sN, bN⟩ := popNumW_spec cap P D σ
    (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.M L r4 G off L Mlab Pl.walkLen
    (3 * lbP Pl) lw CAP LL (capP Pl L) R (by rw [lbP_eq]) hlw hCAP hLL (by rw [capP_eq, hbM, hlw]) hR
    (by rw [← Xe_lit P 20 20 rfl]; exact h20) (by rw [← Xe_lit P 21 21 rfl]; exact h21)
    (by rw [← Xe_lit P 44 44 rfl]; exact h44) (by rw [← Xe_lit P 45 45 rfl]; exact h45)
    (by rw [← Xe_lit P 1 1 rfl]; exact h1) (by rw [← Xe_lit P 2 2 rfl]; exact h2)
    (by rw [← Xe_lit P 3 3 rfl]; exact h3) (by rw [← Xe_lit P 4 4 rfl]; exact h4)
    (by rw [← Xe_lit P 52 52 rfl]; exact h52) h180
    (fun j hj => by
      obtain ⟨k, hk⟩ : ∃ k : Fin 64, k.val = j.val := ⟨⟨j.val, by omega⟩, rfl⟩
      rw [← Xe_lit P k j hk]
      exact hzA k (by omega))
    hz hD hM hcap hdc hJc hSc hlwc hMc hcL hcap3 hac3 hQc hc4 hin hnum h2c hcV hcT
  rw [← hcp] at rN
  have xv := numX P σ τN L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen rN
  have hB := blockRegs_num P σ τN L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen r4 G off
    (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.M sgn rN h1 h2 h3 h4 h20 h21 h44 h45 h50 hzA
  have hx0 : τN.val (Xe P 0) = 0 :=
    (xv 0).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 0 _ (by decide)).trans h0)
  obtain ⟨mR, eR, bR⟩ := popRecW_spec cap O S (Xe P) hOS cwOne cwNeg τN Pl.walkLen θ R (R + 1) cp s.val (4 * L)
    (3 * lbP Pl) r4 G off L (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.M L
    (capP Pl L) sgn hB
    ((xv 52).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 52 _ (by decide)).trans h52))
    ((xv 53).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 53 _ (by decide)).trans h53))
    ((xv 54).trans (xNew_54 L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen _))
    ((xv 55).trans (xNew_55 L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen _))
    ((xv 56).trans (xNew_56 L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen _))
    ((xv 58).trans ((xNew_58 L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen _).trans (by ring)))
    ((xv 59).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 59 _ (by decide)).trans
      (hzA 59 (by decide))))
    ((xv 60).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 60 _ (by decide)).trans
      (hzA 60 (by decide))))
    ((xv 63).trans ((xNew_of L (3 * lbP Pl) (capP Pl L) R (R + 1) cp Pl.base.J Pl.walkLen 63 _ (by decide)).trans h63))
    (Nat.le_of_lt_succ s.isLt) Mlab hM (rowKP Pl e L) (rowKP_length Pl e L)
    (by simp [(sN O hOD).1, (sN O hOD).2, hO0, hO1])
    (by rw [(sN S hSD).1, (sN S hSD).2]; exact hS)
    hcap hJc (by omega) hMc (by omega) (by omega) (by omega) (by rw [Nat.add_comm 1]; exact hcT) hθc (by omega)
    hRc1 hcpc (by rw [hx0, ← hlink]; omega)
  rw [← hlink] at eR
  have eW := wrewind_spec cap O (Xe P 0) u.length (lSt O S (Xe P 0) τN u (τN.sh S))
    (by simp [lSt_val, hx0]) (by simp [lSt_val, hx0]; omega)
  refine ⟨mN + 1 + (mR + 1 + (5 * u.length + 1)), _, WExec.seq eN (WExec.seq eR eW), ?_, ?_, ?_, ?_⟩
  · simp [lSt_stO, (sN O hOD).2, hO0]
  · simp [lSt_shO hOS, (sN O hOD).1, hO1]
  · intro T hTO hTD
    obtain ⟨s1, s2⟩ := sN T hTD
    refine ⟨?_, ?_⟩
    · simp [lSt, Function.update_apply, hTO, s2]
    · by_cases hTS : T = S
      · rw [hTS]
        simp [lSt, Function.update_apply, Ne.symm hOS, (sN S hSD).1]
      · simp [lSt, Function.update_apply, hTO, hTS, s1]
  · unfold popCellBound
    omega

end Cell

end NearCubicWires.WireExponent3_5.PrimAsm.PopCellW
