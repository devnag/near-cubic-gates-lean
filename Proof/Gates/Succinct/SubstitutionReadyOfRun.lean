import Proof.Gates.Succinct.SubstitutionRunSpec
import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The port tapes of the rewound program. -/
def portT (i : Fin (4 + 1)) : Fin (4 + 2 + nrH + 1) := (sTape (nr := nrH) i).castAdd 1

theorem portT_val (i : Fin (4 + 1)) : (portT i).val = if i.val = 0 then 0 else i.val + 1 := rfl

theorem portT_inj (a b : Fin (4 + 1)) : portT a = portT b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [portT_val, portT_val] at this
    apply Fin.ext
    split_ifs at this <;> omega
  · intro h; rw [h]

/-- The rewound program's cold bank is the port bank of the two words. -/
theorem subst_bank_eq (w d : List Bool) :
    Fin.addCases (m := 4 + 2 + nrH) (n := 1) (motive := fun _ => List Bool)
      (CheckedPCPP.coldBank (start w d)) (fun _ => []) =
    CheckedPCPP.portBank (4 + 2 + nrH + 1) (portT sW) (portT sD) w d := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left]
    rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [CheckedPCPP.coldBank_s]
      unfold CheckedPCPP.portBank start
      change _ = if portT i = portT sW then w else if portT i = portT sD then d else []
      simp only [portT_inj]
    · rw [CheckedPCPP.coldBank_c]
      unfold CheckedPCPP.portBank
      rw [if_neg, if_neg]
      · intro e; have h := congrArg Fin.val e; change 1 = 2 at h; omega
      · intro e; have h := congrArg Fin.val e; change 1 = 0 at h; omega
    · rw [CheckedPCPP.coldBank_r]
      unfold CheckedPCPP.portBank
      rw [if_neg, if_neg]
      · intro e; have h := congrArg Fin.val e; change 4 + 2 + r.val = 2 at h; omega
      · intro e; have h := congrArg Fin.val e; change 4 + 2 + r.val = 0 at h; omega
  · rw [Fin.addCases_right]
    unfold CheckedPCPP.portBank
    rw [if_neg, if_neg]
    · intro e; have h := congrArg Fin.val e; change 4 + 2 + nrH + j.val = 2 at h; omega
    · intro e; have h := congrArg Fin.val e; change 4 + 2 + nrH + j.val = 0 at h; omega

theorem substReady_of_run (h : SubstRunSpec) : SubstReadySpec := by
  refine ⟨4 + 2 + nrH + 1, _, Rewind.machine substProg.compile, portT sW, portT sD, portT sO,
    2 * 10000000000 * 3 ^ 7 + 2, 7, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true, portT_inj]
    exact ⟨⟨sW_ne_sD, sW_ne_sO⟩, sD_ne_sO⟩
  · intro oc q B
    obtain ⟨cap, τ, hx, hO, hW, hD⟩ := h oc B
    obtain ⟨out, hrun, hout⟩ := CheckedPCPP.WXExec.readyRewound hx (fun _ => rfl) (fun _ => rfl) rfl
    refine ⟨out, ?_, (hout sO).trans hO, (hout sW).trans hW, (hout sD).trans hD⟩
    rw [← subst_bank_eq]
    refine ClockJoin.enlarge _ _ _ _ _ hrun ?_
    have hS : 1 ≤ sizeS oc B := by unfold sizeS; omega
    change 2 * substCostClass (sizeS oc B) + 2 ≤ (2 * 10000000000 * 3 ^ 7 + 2) * (sizeS oc B) ^ 7
    unfold substCostClass
    generalize sizeS oc B = S at hS
    have h2 : (S + 2) ^ 7 ≤ 3 ^ 7 * S ^ 7 := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left (by omega) 7
    have h1 : 1 ≤ S ^ 7 := Nat.one_le_pow _ _ (by omega)
    rw [show (3 : ℕ) ^ 7 = 2187 by norm_num] at h2 ⊢
    generalize (S + 2) ^ 7 = A at h2 ⊢
    generalize S ^ 7 = Bv at h1 h2 ⊢
    omega

end NearCubicGates.Close.Succinct.SubstMachine
