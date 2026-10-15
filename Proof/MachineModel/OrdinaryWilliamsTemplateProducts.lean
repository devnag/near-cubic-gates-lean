import Proof.MachineModel.OrdinaryWilliamsTemplateDifferences

/-! The three paid product calls of the preparation controller. Their
new banks are cold; every earlier register is physically retained. -/
namespace NearCubicWires.RepairOrdinary.WilliamsTemplates
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem product_ready (slot : Fin 12 → Fin 50) (hinj : Function.Injective slot)
    (lo hi : ℕ) (hnew : ∀ j, j≠0 → j≠5 → lo ≤ (slot j).val)
    (hupper : ∀ j, (slot j).val<hi) (hlohi : lo ≤ hi)
    (a : Fin 50 → List Bool) (d e : ℕ)
    (h0 : a (slot 0)=UnaryTemplate.tape d) (h5 : a (slot 5)=UnaryTemplate.tape e)
    (hb : Blank lo a) :
    ∃ b, ReadyRun (RecoveryFocus.machine slot MatrixTemplateProduct.machine)
      (8*d*e+10*d+28) a b ∧ Old lo a b ∧
      b (slot 10)=UnaryTemplate.tape (d*e) ∧ Blank hi b := by
  obtain ⟨r,hr,hr0,hr5,hr10,hh,hs⟩ := MatrixTemplateProduct.product_run d e
  have ready : ReadyRun MatrixTemplateProduct.machine (8*d*e+10*d+28)
      (MatrixTemplateProduct.input d e) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (slot j)=MatrixTemplateProduct.input d e j := by
    intro j
    by_cases hj0 : j=0
    · subst j; exact h0
    · by_cases hj5 : j=5
      · subst j; exact h5
      · simpa [MatrixTemplateProduct.input,hj0,hj5] using hb (slot j) (hnew j hj0 hj5)
  let b := install slot a r.final.tapes
  refine ⟨b,ready.focus slot hinj a hin,?_,?_,?_⟩
  · apply install_old
    intro j hj
    by_cases hj0 : j=0
    · subst j; exact hr0.trans h0.symm
    · by_cases hj5 : j=5
      · subst j; exact hr5.trans h5.symm
      · have := hnew j hj0 hj5; omega
  · exact (install_slot slot hinj a r.final.tapes 10).trans hr10
  · exact install_blank slot a r.final.tapes hi hupper (hb.later hlohi)

theorem used_ready (a : Fin 50 → List Bool) (u c : ℕ)
    (h0 : a 0=UnaryTemplate.tape u) (h1 : a 1=UnaryTemplate.tape c) (hb : Blank 14 a) :
    ∃ b, ReadyRun (programs 3) (8*u*c+10*u+28) a b ∧ Old 14 a b ∧
      b 22=UnaryTemplate.tape (u*c) ∧ Blank 24 b :=
  product_ready usedSlots (by decide) 14 24 (by decide) (by decide) (by decide) a u c h0 h1 hb

theorem pad_ready (a : Fin 50 → List Bool) (d c : ℕ)
    (h10 : a 10=UnaryTemplate.tape d) (h1 : a 1=UnaryTemplate.tape c) (hb : Blank 24 a) :
    ∃ b, ReadyRun (programs 4) (8*d*c+10*d+28) a b ∧ Old 24 a b ∧
      b 32=UnaryTemplate.tape (d*c) ∧ Blank 34 b :=
  product_ready padSlots (by decide) 24 34 (by decide) (by decide) (by decide) a d c h10 h1 hb

theorem tail_ready (a : Fin 50 → List Bool) (d w : ℕ)
    (h10 : a 10=UnaryTemplate.tape d) (h8 : a 8=UnaryTemplate.tape w) (hb : Blank 34 a) :
    ∃ b, ReadyRun (programs 5) (8*d*w+10*d+28) a b ∧ Old 34 a b ∧
      b 42=UnaryTemplate.tape (d*w) ∧ Blank 44 b :=
  product_ready tailSlots (by decide) 34 44 (by decide) (by decide) (by decide) a d w h10 h8 hb

end NearCubicWires.RepairOrdinary.WilliamsTemplates
