import Proof.Gates.Succinct.Verifier

/-!
# 𝒱_G, part 10: the run of the succinct verifier

Paper: lem:succinct-verifier (app:multitape), items (ii)–(iii). **`verifierV_run`**: on every input `u` and witness `y`
(any lengths), `𝒱_G` halts within `bodyCost + 1 + H.time N` steps (`N = 2^{rootOf G |u|}`), and accepts exactly when
the hierarchy verifier accepts the table `bodyTable G u` with the witness `prefixBits y (H.time N)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP (coldBank coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_val cTape_val rTape_val)

variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ)

theorem pick_swap12 (t : ℕ) (ht : 3 ≤ t) (i : Fin t) :
    RecoveryFocus.pick (swap12 t ht) i = some (swap12 t ht i) := by
  have := RecoveryFocus.pick_slot (swap12 t ht) (swap12_inj t ht) (swap12 t ht i)
  rwa [swap12_swap12] at this

/-- The verifier's input bank is the body's cold bank, renamed. -/
theorem bank_swap (u y : List Bool) (i : Fin (vT H)) :
    coldBank (bodyStart (tH H) u y) (swap12 (vT H) (three_le_vT H) i) = (verifierV H G).inputTapes u y i := by
  have hvt := three_le_vT H
  show coldBank (bodyStart (tH H) u y) (swap12 (vT H) (three_le_vT H) i) =
    if i.val = 0 then RepairOrdinary.frame u else if i.val = 1 then RepairOrdinary.frame y else []
  by_cases h1 : i.val = 1
  · have e : swap12 (vT H) (three_le_vT H) i = sTape (nr := nrV) (bs (tH H) 1 (by have := two_le_tH H; omega)) := by
      ext; simp [swap12, h1, sTape, bs]
    rw [e, coldBank_s, if_neg (by omega), if_pos h1]; simp [bodyStart, bs]
  by_cases h2 : i.val = 2
  · have e : swap12 (vT H) (three_le_vT H) i = cTape (ns := tH H + 4) (nr := nrV) := by
      ext; simp [swap12, h1, h2, cTape]
    rw [e, coldBank_c, if_neg (by omega), if_neg h1]
  have e : swap12 (vT H) (three_le_vT H) i = i := by simp [swap12, h1, h2]
  rw [e]
  rcases tape_cases i with ⟨j, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [coldBank_s]
    have hv := sTape_val (nr := nrV) j
    by_cases h0 : j.val = 0
    · have : (sTape (nr := nrV) j).val = 0 := by rw [hv, if_pos h0]
      rw [if_pos this]
      show (if j.val = 0 then _ else if j.val = 1 then _ else []) = _
      rw [if_pos h0]
    · have hj1 : j.val ≠ 1 := by intro h; apply h2; rw [hv, if_neg h0, h]
      have : (sTape (nr := nrV) j).val = j.val + 1 := by rw [hv, if_neg h0]
      rw [if_neg (by omega), if_neg (by omega)]
      show (if j.val = 0 then _ else if j.val = 1 then _ else []) = _
      rw [if_neg h0, if_neg hj1]
  · simp [cTape] at h1
  · rw [coldBank_r]; simp only [rTape_val] at h1 h2 ⊢; rw [if_neg (by omega), if_neg (by omega)]

theorem verifierV_acc (st : Fin (verifierV H G).stateCount) (x : Fin H.verifier.stateCount)
    (h : st.val = (body G H.coefficient k (tH H) (two_le_tH H)).size + x.val) :
    (verifierV H G).accepting st = H.verifier.accepting x := by
  dsimp only [verifierV]
  rw [dif_pos (by rw [h]; exact Nat.le_add_right _ _)]
  exact congrArg H.verifier.accepting (Fin.ext (Nat.sub_eq_of_eq_add (by rw [h, Nat.add_comm])))

/-- **The run of `𝒱_G`** (paper lem:succinct-verifier (ii)–(iii)). -/
theorem verifierV_run (u y : List Bool) :
    ∃ r, run (verifierV H G).machine (bodyCost G H.coefficient k u.length + 1 + H.time (2 ^ rootOf G u.length))
        ((verifierV H G).inputTapes u y) = some r ∧
      ((verifierV H G).accepting r.final.control = true ↔
        H.verifier.accepts (bodyTable G u) (prefixBits y (H.time (2 ^ rootOf G u.length)))) := by
  set N := 2 ^ rootOf G u.length with hN
  set m := H.time N with hm
  have htH := two_le_tH H
  -- the body
  obtain ⟨τ, eb, hTT, hTTh, hWP, hWPh, hrest⟩ := body_spec G H.coefficient k (tH H) htH u y
  obtain ⟨rb, hrb, hbh, hbt⟩ := cold_run eb (fun _ => rfl) (fun _ => rfl) rfl
  -- the hierarchy verifier's run
  have hlenT : (bodyTable G u).length = N := by simp [bodyTable, ttWord_length, hN]
  have hlenW : (prefixBits y (htVal H.coefficient k N)).length = m := by simp [prefixBits_length, hm, htVal,
    OrdinaryHierarchy.time]
  set tt : BitInput N := fun i => (bodyTable G u).getD i.val false with htt
  set w : BitInput (H.coefficient * (N ^ (k + 2) + 1)) := fun i => (prefixBits y m).getD i.val false with hw
  have htt' : List.ofFn tt = bodyTable G u := by
    apply List.ext_getElem (by simp [hlenT])
    intro i h1 h2; simp [tt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hw' : List.ofFn w = prefixBits y m := by
    apply List.ext_getElem (by simp [prefixBits_length, hm, OrdinaryHierarchy.time])
    intro i h1 h2; simp [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  obtain ⟨rh, hrh⟩ := H.halts N tt w
  rw [htt', hw'] at hrh
  have hmt : H.coefficient * (N ^ (k + 2) + 1) = m := rfl
  rw [hmt] at hrh

  set src := initialConfiguration H.verifier.machine (H.verifier.inputTapes (bodyTable G u) (prefixBits y m))
    with hsrc
  obtain ⟨rd, hrd, hrdf, _⟩ := RecoveryFocus.run_config (hmap H) (hmap_inj H) H.verifier.machine rb.final.heads
    rb.final.tapes m src rh hrh
  have hrestart : Composition.restart rb.final (hDock H).start =
      RecoveryFocus.config (hmap H) rb.final.heads rb.final.tapes src := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick (hmap H) i with
      | none => simp [RecoveryFocus.config, hp, Composition.restart]
      | some j =>
        have hji := RecoveryFocus.slot_of_pick _ hp
        subst hji
        simp only [RecoveryFocus.config, hp, Composition.restart, src, initialConfiguration]
        rw [hbh, hmap, wenc_H_s]
        by_cases hj0 : j.val = 0
        · have : bs (tH H) (j.val + 5) (by omega) = bs (tH H) 5 (by omega) := by simp [bs, hj0]
          rw [this, hTTh]
        by_cases hj1 : j.val = 1
        · have : bs (tH H) (j.val + 5) (by omega) = bs (tH H) 6 (by omega) := by simp [bs, hj1]
          rw [this, hWPh]
        exact (hrest _ (by simp [bs]; omega)).2
    · funext i
      cases hp : RecoveryFocus.pick (hmap H) i with
      | none => simp [RecoveryFocus.config, hp, Composition.restart]
      | some j =>
        have hji := RecoveryFocus.slot_of_pick _ hp
        subst hji
        simp only [RecoveryFocus.config, hp, Composition.restart, src, initialConfiguration, Verifier.inputTapes]
        rw [hmap, hbt]
        by_cases hj0 : j.val = 0
        · have : bs (tH H) (j.val + 5) (by omega) = bs (tH H) 5 (by omega) := by simp [bs, hj0]
          rw [this, hTT, if_pos hj0]
        by_cases hj1 : j.val = 1
        · have : bs (tH H) (j.val + 5) (by omega) = bs (tH H) 6 (by omega) := by simp [bs, hj1]
          rw [this, hWP, if_neg hj0, if_pos hj1]
          congr 2
        rw [if_neg hj0, if_neg hj1]
        exact (hrest _ (by simp [bs]; omega)).1
  rw [← hrestart] at hrd
  have hjoin := Composition.run_join (bodyM H G) (hDock H) _ _ _ rb rd hrb hrd
  replace hjoin : runFrom (m0 H G) (bodyCost G H.coefficient k u.length + 1 + m)
      (initialConfiguration (m0 H G) (coldBank (bodyStart (tH H) u y))) = some (Composition.joinedReceipt rb rd) :=
    hjoin
  -- renamed tapes
  have hinit : initialConfiguration (verifierV H G).machine ((verifierV H G).inputTapes u y) =
      RecoveryFocus.config (swap12 (vT H) (three_le_vT H)) (fun _ => 0) ((verifierV H G).inputTapes u y)
        (initialConfiguration (m0 H G) (coldBank (bodyStart (tH H) u y))) := by
    apply configuration_ext
    · rfl
    · funext i; simp [RecoveryFocus.config, pick_swap12, initialConfiguration]
    · funext i; simp only [RecoveryFocus.config, pick_swap12, initialConfiguration]; rw [bank_swap]
  obtain ⟨rV, hrV, hrVf, _⟩ := RecoveryFocus.run_config (swap12 (vT H) (three_le_vT H)) (swap12_inj _ _) (m0 H G)
    (fun _ => 0) ((verifierV H G).inputTapes u y) _ _ _ hjoin
  refine ⟨rV, ?_, ?_⟩
  · show runFrom (verifierV H G).machine _ (initialConfiguration (verifierV H G).machine
      ((verifierV H G).inputTapes u y)) = some rV
    rw [hinit]; exact hrV
  · have h1 : rV.final.control = (Composition.joinedReceipt rb rd).final.control := by rw [hrVf]; rfl
    have h2 : (Composition.joinedReceipt rb rd).final.control =
        Fin.natAdd (body G H.coefficient k (tH H) htH).size rd.final.control := rfl
    have h3 : rd.final.control = rh.final.control := by rw [hrdf]; rfl
    have hctrl : rV.final.control.val = (body G H.coefficient k (tH H) htH).size + rh.final.control.val := by
      rw [h1, h2, Fin.val_natAdd, h3]
    rw [verifierV_acc H G _ _ hctrl]
    constructor
    · intro ha; exact ⟨m, rh, hrh, ha⟩
    · rintro ⟨f, r', hr', ha⟩
      have := UAcceptanceCarrier.run_receipt_unique H.verifier.machine _ f m r' rh hr' hrh
      rw [← this]; exact ha

end NearCubicGates.Close.Succinct
