import SourceAdapters.Proximity.TaggedBank

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": a uniform binary dispatcher combines actual ordinary
source programs. The selector bit, payload copy and final head reset are paid. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TaggedCalls

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

def input {A B : Type} (left : A → List Bool) (right : B → List Bool) : A ⊕ B → List Bool :=
  Sum.elim (fun a => false :: left a) (fun b => true :: right b)

def payload {A B : Type} (left : A → List Bool) (right : B → List Bool) : A ⊕ B → List Bool := Sum.elim left right

def selectedBudget {A B : Type} (left : A → ℕ) (right : B → ℕ) : A ⊕ B → ℕ := Sum.elim left right

noncomputable def dispatch (p q : Program) : WMX (max p.tapeCount q.tapeCount + 2) 1 :=
  .seq (.wm (.fwd 0)) (.ifs 0 (branch q _ (le_max_right _ _)) (branch p _ (le_max_left _ _)))

def cost {A B : Type} (left : A → List Bool) (right : B → List Bool) (lb : A → ℕ) (rb : B → ℕ)
    (r : A ⊕ B) : ℕ := 32 * (payload left right r).length + selectedBudget lb rb r + 22

theorem dispatch_run {A B : Type} {ia oa : A → List Bool} {ib ob : B → List Bool} {ba : A → ℕ} {bb : B → ℕ}
    (P : WordFunction A ia oa ba) (Q : WordFunction B ib ob bb) (r : A ⊕ B) :
    ∃ τ : State (max P.program.tapeCount Q.program.tapeCount),
      WXExec (2 * (payload ia ib r).length + 2) (dispatch P.program Q.program)
        (idealStart (max P.program.tapeCount Q.program.tapeCount + 2) 1 (input ia ib r) (fun _ => 0))
        τ (cost ia ib ba bb r) ∧ τ.st 2 = payload oa ob r := by
  let N := max P.program.tapeCount Q.program.tapeCount
  cases r with
  | inl a =>
    obtain ⟨receipt, hr, ho⟩ := P.realizes a
    obtain ⟨τ, he, hout⟩ := branch_run P.program N (le_max_left _ _) false (ia a) (oa a) (ba a) receipt hr ho
    have hf : WExec (2 * (ia a).length + 2) (.fwd 0) (initial N false (ia a)) (atTag N false (ia a)) 1 := by
      simpa [initial, idealStart, atTag] using WExec.fwd (cap := 2 * (ia a).length + 2)
        (0 : Fin (N + 3)) (initial N false (ia a))
    refine ⟨τ, (WXExec.seq (WXExec.wm hf) (WXExec.ifsF (by rfl) he)).cast _ rfl ?_, hout⟩
    simp only [cost, payload, selectedBudget, Sum.elim_inl]
    omega
  | inr b =>
    obtain ⟨receipt, hr, ho⟩ := Q.realizes b
    obtain ⟨τ, he, hout⟩ := branch_run Q.program N (le_max_right _ _) true (ib b) (ob b) (bb b) receipt hr ho
    have hf : WExec (2 * (ib b).length + 2) (.fwd 0) (initial N true (ib b)) (atTag N true (ib b)) 1 := by
      simpa [initial, idealStart, atTag] using WExec.fwd (cap := 2 * (ib b).length + 2)
        (0 : Fin (N + 3)) (initial N true (ib b))
    refine ⟨τ, (WXExec.seq (WXExec.wm hf) (WXExec.ifsT (by rfl) he)).cast _ rfl ?_, hout⟩
    simp only [cost, payload, selectedBudget, Sum.elim_inr]
    omega

noncomputable def wordFunction {A B : Type} {ia oa : A → List Bool} {ib ob : B → List Bool}
    {ba : A → ℕ} {bb : B → ℕ} (P : WordFunction A ia oa ba) (Q : WordFunction B ib ob bb) :
    WordFunction (A ⊕ B) (input ia ib) (payload oa ob) (fun r => 2 * cost ia ib ba bb r + 2) :=
  wordFunction_of_ideal (Request := A ⊕ B) (input := input ia ib) (output := payload oa ob)
    (dispatch P.program Q.program) 2
    (by change 2 % (_ + 3) ≠ 0; rw [Nat.mod_eq_of_lt (by omega)]; omega)
    (fun r => 2 * (payload ia ib r).length + 2) (fun _ _ => 0) (cost ia ib ba bb)
    (fun _ => le_rfl) (fun r => ⟨rfl, dispatch_run P Q r⟩)

end NearCubicGates.Adapters.Proximity.TaggedCalls
