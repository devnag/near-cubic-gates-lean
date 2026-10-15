import Proof.Wire_3_5.FinalPassWords
import Proof.Wire_3_5.ListMachineRecords

/-! # PA (d)-SYM, part 16: docking raw machines onto a register program's streams

The writer's cells run one register-language layout (`WM ns nr`, C5's `wenc` encoding) and dock raw machines — T's
walk-bank producer, C2's row machines — onto its STREAMS: machine tape `j` is stream `tmap j`. A docked run leaves a
state of the same layout (**`dockS`**): the streams `tmap j` hold the machine's exit tapes at its exit heads
(`updS`: `install` / `dockH` over the streams), every register, the cell and every other stream unchanged. So a
register program can run before and after a raw machine on one bank.

* `tape_cases`: every tape is a stream, the cell or a register; `sTape_inj`, `sTape_ne_c`, `sTape_ne_r`, …;
* `install_comp`, `dockH_comp`: docking through an injective map of the ambient positions;
* **`updS_A`**, **`updS_H`**, **`dockS`**.

Paper quantity: none (machine plumbing for the writer's cells; the consumers' types carry the paper's words). -/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.ListMachine.Rec

section Tapes
variable {ns nr : ℕ}

theorem sTape_val (i : Fin (ns + 1)) : (sTape (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl
theorem cTape_val : (cTape (ns := ns) (nr := nr)).val = 1 := rfl
theorem rTape_val (r : Fin nr) : (rTape (ns := ns) r).val = ns + 2 + r.val := rfl

/-- Every tape of the layout is a stream, the cell or a register. -/
theorem tape_cases (j : Fin (ns + 2 + nr)) :
    (∃ i : Fin (ns + 1), j = sTape i) ∨ j = cTape ∨ ∃ r : Fin nr, j = rTape r := by
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · refine Or.inl ⟨⟨0, by omega⟩, Fin.ext ?_⟩
    show j.val = if 0 = 0 then 0 else 0 + 1
    rw [if_pos rfl]
    exact h0
  · by_cases h1 : j.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · by_cases h2 : j.val ≤ ns + 1
      · refine Or.inl ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
        show j.val = if j.val - 1 = 0 then 0 else j.val - 1 + 1
        rw [if_neg (by omega)]
        omega
      · refine Or.inr (Or.inr ⟨⟨j.val - (ns + 2), by omega⟩, Fin.ext ?_⟩)
        show j.val = ns + 2 + (j.val - (ns + 2))
        omega

theorem sTape_inj : Function.Injective (sTape (ns := ns) (nr := nr)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [sTape_val, sTape_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem rTape_inj : Function.Injective (rTape (ns := ns) (nr := nr)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [rTape_val, rTape_val] at hv
  apply Fin.ext
  omega

theorem sTape_ne_c (i : Fin (ns + 1)) : sTape (nr := nr) i ≠ cTape := by
  intro h
  have hv := congrArg Fin.val h
  rw [sTape_val, cTape_val] at hv
  split_ifs at hv <;> omega

theorem sTape_ne_r (i : Fin (ns + 1)) (r : Fin nr) : sTape (nr := nr) i ≠ rTape r := by
  intro h
  have hi := i.isLt
  have hv := congrArg Fin.val h
  rw [sTape_val, rTape_val] at hv
  split_ifs at hv <;> omega

theorem cTape_ne_r (r : Fin nr) : cTape (ns := ns) (nr := nr) ≠ rTape r := by
  intro h
  have hv := congrArg Fin.val h
  rw [cTape_val, rTape_val] at hv
  omega

variable (cap : ℕ)

theorem wenc_A_c (σ : WState ns nr) : (wenc cap σ).A cTape = [σ.cell] := by
  simp [wenc, role_cTape]

theorem wenc_H_c (σ : WState ns nr) : (wenc cap σ).H cTape = 0 := by
  simp [wenc, role_cTape]

end Tapes

/-! ## Docking through an injective map of the ambient positions -/

theorem install_comp {t u v : ℕ} (e : Fin u → Fin v) (he : Function.Injective e) (f : Fin t → Fin u)
    (hf : Function.Injective f) (A : Fin v → List Bool) (X : Fin t → List Bool) (i : Fin u) :
    install (fun j => e (f j)) A X (e i) = install f (fun k => A (e k)) X i := by
  classical
  by_cases h : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := h
    exact (install_slot (fun j => e (f j)) (fun a b hab => hf (he hab)) A X j).trans (install_slot f hf _ X j).symm
  · have h' : ∀ j, f j ≠ i := fun j hj => h ⟨j, hj⟩
    exact (install_other _ A X (e i) (fun j hj => h' j (he hj))).trans (install_other f (fun k => A (e k)) X i h').symm

theorem dockH_comp {t u v : ℕ} (e : Fin u → Fin v) (he : Function.Injective e) (f : Fin t → Fin u)
    (hf : Function.Injective f) (A : Fin v → ℕ) (X : Fin t → ℕ) (i : Fin u) :
    dockH (fun j => e (f j)) A X (e i) = dockH f (fun k => A (e k)) X i := by
  classical
  by_cases h : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := h
    exact (dockH_slot (fun j => e (f j)) (fun a b hab => hf (he hab)) A X j).trans (dockH_slot f hf _ X j).symm
  · have h' : ∀ j, f j ≠ i := fun j hj => h ⟨j, hj⟩
    exact (dockH_other _ A X (e i) (fun j hj => h' j (he hj))).trans (dockH_other f (fun k => A (e k)) X i h').symm

/-! ## A raw machine docked onto streams -/

section Streams
variable {ns nr : ℕ} (cap : ℕ)

/-- The state after a raw machine docked onto the streams `tmap`: those streams hold its exit tapes at its exit
heads; the registers, the cell and the other streams are unchanged. -/
noncomputable def updS {t : ℕ} (tmap : Fin t → Fin (ns + 1)) (σ : WState ns nr) (hout : Fin t → ℕ)
    (tout : Fin t → List Bool) : WState ns nr :=
  ⟨dockH tmap σ.sh hout, install tmap σ.st tout, σ.val, σ.cell⟩

theorem updS_A {t : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) :
    install (fun j => sTape (nr := nr) (tmap j)) (wenc cap σ).A tout = (wenc cap (updS tmap σ hout tout)).A := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [install_comp _ sTape_inj tmap hinj, wenc_A_s,
      show (fun k => (wenc cap σ).A (sTape k)) = σ.st from funext fun k => wenc_A_s cap σ k]
    rfl
  · rw [install_other _ _ _ _ (fun j => sTape_ne_c (tmap j)), wenc_A_c, wenc_A_c]
    rfl
  · rw [install_other _ _ _ _ (fun j => sTape_ne_r (tmap j) r), wenc_A_r, wenc_A_r]
    rfl

theorem updS_H {t : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) :
    dockH (fun j => sTape (nr := nr) (tmap j)) (wenc cap σ).H hout = (wenc cap (updS tmap σ hout tout)).H := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [dockH_comp _ sTape_inj tmap hinj, wenc_H_s,
      show (fun k => (wenc cap σ).H (sTape k)) = σ.sh from funext fun k => wenc_H_s cap σ k]
    rfl
  · rw [dockH_other _ _ _ _ (fun j => sTape_ne_c (tmap j)), wenc_H_c, wenc_H_c]
  · rw [dockH_other _ _ _ _ (fun j => sTape_ne_r (tmap j) r), wenc_H_r, wenc_H_r]
    rfl

/-- **A raw machine docked onto streams** leaves a state of the same layout. -/
theorem dockS {t s n : ℕ} {M : Machine t s} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (σ : WState ns nr) {hout : Fin t → ℕ} {tout : Fin t → List Bool}
    (h : Step M n (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j)) hout tout) :
    Step (RecoveryFocus.machine (fun j => sTape (nr := nr) (tmap j)) M) n (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updS tmap σ hout tout)).H (wenc cap (updS tmap σ hout tout)).A := by
  have hd := dockRun h (fun j => sTape (nr := nr) (tmap j)) (fun a b hab => hinj (sTape_inj hab))
    (wenc cap σ).H (wenc cap σ).A (fun j => wenc_H_s cap σ (tmap j)) (fun j => wenc_A_s cap σ (tmap j))
  rw [updS_H cap tmap hinj σ hout tout, updS_A cap tmap hinj σ hout tout] at hd
  exact hd

end Streams

/-! ## Docking through a factorization of the slots -/

theorem install_fac {t t' u v : ℕ} (slots : Fin t → Fin v) (hs : Function.Injective slots) (e : Fin u → Fin v)
    (he : Function.Injective e) (f : Fin t' → Fin u) (hf : Function.Injective f) (g : Fin t' → Fin t)
    (hg : ∀ x, slots (g x) = e (f x)) (hout : ∀ j, (∀ x, g x ≠ j) → ∀ i, slots j ≠ e i)
    (A : Fin v → List Bool) (X : Fin t → List Bool) (i : Fin u) :
    install slots A X (e i) = install f (fun k => A (e k)) (fun x => X (g x)) i := by
  classical
  by_cases h : ∃ x, f x = i
  · obtain ⟨x, rfl⟩ := h
    rw [← hg x, install_slot slots hs]
    exact (install_slot f hf (fun k => A (e k)) (fun x => X (g x)) x).symm
  · have h' : ∀ x, f x ≠ i := fun x hx => h ⟨x, hx⟩
    have hn : ∀ j, slots j ≠ e i := by
      intro j
      by_cases hj : ∃ x, g x = j
      · obtain ⟨x, rfl⟩ := hj
        rw [hg x]
        exact fun hh => h' x (he hh)
      · exact hout j (fun x hx => hj ⟨x, hx⟩) i
    exact (install_other slots A X (e i) hn).trans (install_other f (fun k => A (e k)) _ i h').symm

theorem dockH_fac {t t' u v : ℕ} (slots : Fin t → Fin v) (hs : Function.Injective slots) (e : Fin u → Fin v)
    (he : Function.Injective e) (f : Fin t' → Fin u) (hf : Function.Injective f) (g : Fin t' → Fin t)
    (hg : ∀ x, slots (g x) = e (f x)) (hout : ∀ j, (∀ x, g x ≠ j) → ∀ i, slots j ≠ e i)
    (A : Fin v → ℕ) (X : Fin t → ℕ) (i : Fin u) :
    dockH slots A X (e i) = dockH f (fun k => A (e k)) (fun x => X (g x)) i := by
  classical
  by_cases h : ∃ x, f x = i
  · obtain ⟨x, rfl⟩ := h
    rw [← hg x, dockH_slot slots hs]
    exact (dockH_slot f hf (fun k => A (e k)) (fun x => X (g x)) x).symm
  · have h' : ∀ x, f x ≠ i := fun x hx => h ⟨x, hx⟩
    have hn : ∀ j, slots j ≠ e i := by
      intro j
      by_cases hj : ∃ x, g x = j
      · obtain ⟨x, rfl⟩ := hj
        rw [hg x]
        exact fun hh => h' x (he hh)
      · exact hout j (fun x hx => hj ⟨x, hx⟩) i
    exact (dockH_other slots A X (e i) hn).trans (dockH_other f (fun k => A (e k)) _ i h').symm

theorem install_reg {t u : ℕ} (f : Fin t → Fin u) (hf : Function.Injective f) (A : Fin u → ℕ) (X : Fin t → ℕ)
    (i : Fin u) (h : ℕ → List Bool) : install f (fun k => h (A k)) (fun x => h (X x)) i = h (dockH f A X i) := by
  classical
  by_cases hx : ∃ x, f x = i
  · obtain ⟨x, rfl⟩ := hx
    rw [install_slot f hf, dockH_slot f hf]
  · have h' : ∀ x, f x ≠ i := fun x hx' => hx ⟨x, hx'⟩
    rw [install_other f _ _ i h', dockH_other f A X i h']

/-! ## A register program of a sub-layout docked with extra streams -/

section Sub
variable {ns nr ns' nr' q : ℕ} (cap : ℕ)

/-- A sub-layout's tape in the big layout: streams by `fs`, registers by `fr`, the cell to the cell. -/
def wslot (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (j : Fin (ns' + 2 + nr')) :
    Fin (ns + 2 + nr) :=
  match role j with
  | .stream i => sTape (fs i)
  | .cell => cTape
  | .reg r => rTape (fr r)

theorem wslot_s (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (i : Fin (ns' + 1)) :
    wslot fs fr (sTape (nr := nr') i) = sTape (nr := nr) (fs i) := by
  simp [wslot, role_sTape]

theorem wslot_c (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) :
    wslot fs fr (cTape (ns := ns') (nr := nr')) = cTape := by
  simp [wslot, role_cTape]

theorem wslot_r (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (r : Fin nr') :
    wslot fs fr (rTape (ns := ns') r) = rTape (ns := ns) (fr r) := by
  simp [wslot, role_rTape]

/-- The combined stream map: the sub-layout's streams, then the extra tapes. -/
def gs (fs : Fin (ns' + 1) → Fin (ns + 1)) (em : Fin q → Fin (ns + 1)) : Fin ((ns' + 1) + q) → Fin (ns + 1) :=
  Fin.addCases (motive := fun _ => Fin (ns + 1)) fs em

/-- The slots of a sub-layout bank with `q` extra tapes. -/
def wq (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1)) :
    Fin ((ns' + 2 + nr') + q) → Fin (ns + 2 + nr) :=
  Fin.addCases (motive := fun _ => Fin (ns + 2 + nr)) (wslot fs fr) (fun k => sTape (em k))

/-- The stream part of the sub bank. -/
def sp : Fin ((ns' + 1) + q) → Fin ((ns' + 2 + nr') + q) :=
  Fin.addCases (motive := fun _ => Fin ((ns' + 2 + nr') + q)) (fun i => Fin.castAdd q (sTape (nr := nr') i))
    (fun k => Fin.natAdd (ns' + 2 + nr') k)

theorem wq_sp (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (x : Fin ((ns' + 1) + q)) : wq fs fr em (sp (nr' := nr') x) = sTape (nr := nr) (gs fs em x) := by
  refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · simp only [sp, gs, wq, Fin.addCases_left, wslot_s]
  · simp only [sp, gs, wq, Fin.addCases_right]

theorem wq_c (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1)) :
    wq fs fr em (Fin.castAdd q (cTape (ns := ns') (nr := nr'))) = cTape := by
  simp only [wq, Fin.addCases_left, wslot_c]

theorem wq_r (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1)) (r : Fin nr') :
    wq fs fr em (Fin.castAdd q (rTape (ns := ns') r)) = rTape (ns := ns) (fr r) := by
  simp only [wq, Fin.addCases_left, wslot_r]

theorem sub_cases (j : Fin ((ns' + 2 + nr') + q)) :
    (∃ x, j = sp (nr' := nr') x) ∨ j = Fin.castAdd q (cTape (ns := ns') (nr := nr')) ∨
      ∃ r : Fin nr', j = Fin.castAdd q (rTape (ns := ns') r) := by
  refine Fin.addCases (fun a => ?_) (fun k => ?_) j
  · rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · exact Or.inl ⟨Fin.castAdd q i, by simp only [sp, Fin.addCases_left]⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨r, rfl⟩)
  · exact Or.inl ⟨Fin.natAdd (ns' + 1) k, by simp only [sp, Fin.addCases_right]⟩

theorem wq_inj (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (hgs : Function.Injective (gs fs em)) (hfr : Function.Injective fr) : Function.Injective (wq fs fr em) := by
  intro a b h
  rcases sub_cases a with ⟨x, rfl⟩ | rfl | ⟨r, rfl⟩
  · rcases sub_cases b with ⟨x', rfl⟩ | rfl | ⟨r', rfl⟩
    · rw [wq_sp, wq_sp] at h
      rw [hgs (sTape_inj h)]
    · rw [wq_sp, wq_c] at h
      exact absurd h (sTape_ne_c _)
    · rw [wq_sp, wq_r] at h
      exact absurd h (sTape_ne_r _ _)
  · rcases sub_cases b with ⟨x', rfl⟩ | rfl | ⟨r', rfl⟩
    · rw [wq_c, wq_sp] at h
      exact absurd h.symm (sTape_ne_c _)
    · rfl
    · rw [wq_c, wq_r] at h
      exact absurd h (cTape_ne_r _)
  · rcases sub_cases b with ⟨x', rfl⟩ | rfl | ⟨r', rfl⟩
    · rw [wq_r, wq_sp] at h
      exact absurd h.symm (sTape_ne_r _ _)
    · rw [wq_r, wq_c] at h
      exact absurd h.symm (cTape_ne_r _)
    · rw [wq_r, wq_r] at h
      rw [hfr (rTape_inj h)]

theorem wq_out_s (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (j : Fin ((ns' + 2 + nr') + q)) (hj : ∀ x, sp (nr' := nr') x ≠ j) (i : Fin (ns + 1)) :
    wq fs fr em j ≠ sTape (nr := nr) i := by
  rcases sub_cases j with ⟨x, rfl⟩ | rfl | ⟨r, rfl⟩
  · exact absurd rfl (hj x)
  · rw [wq_c]
    exact fun h => sTape_ne_c i h.symm
  · rw [wq_r]
    exact fun h => sTape_ne_r i _ h.symm

theorem wq_out_r (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (j : Fin ((ns' + 2 + nr') + q)) (hj : ∀ r, Fin.castAdd q (rTape (ns := ns') r) ≠ j) (r : Fin nr) :
    wq fs fr em j ≠ rTape (ns := ns) r := by
  rcases sub_cases j with ⟨x, rfl⟩ | rfl | ⟨r', rfl⟩
  · rw [wq_sp]
    exact sTape_ne_r _ r
  · rw [wq_c]
    exact cTape_ne_r r
  · exact absurd rfl (hj r')

/-- The state after a sub-layout bank docked with extra streams: the sub-layout's streams and the extra streams hold
the machine's exit, its registers and cell are the sub-layout's; the rest is unchanged. -/
noncomputable def updW (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (σ : WState ns nr) (y : WState ns' nr') (hq : Fin q → ℕ) (tq : Fin q → List Bool) : WState ns nr :=
  ⟨dockH (gs fs em) σ.sh (Fin.addCases (motive := fun _ => ℕ) y.sh hq),
    install (gs fs em) σ.st (Fin.addCases (motive := fun _ => List Bool) y.st tq), dockH fr σ.val y.val, y.cell⟩

theorem updW_A (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (hgs : Function.Injective (gs fs em)) (hfr : Function.Injective fr) (σ : WState ns nr) (y : WState ns' nr')
    (hq : Fin q → ℕ) (tq : Fin q → List Bool) :
    install (wq fs fr em) (wenc cap σ).A (Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq) =
      (wenc cap (updW fs fr em σ y hq tq)).A := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [install_fac (wq fs fr em) (wq_inj fs fr em hgs hfr) sTape sTape_inj (gs fs em) hgs sp (wq_sp fs fr em)
      (wq_out_s fs fr em), wenc_A_s,
      show (fun k => (wenc cap σ).A (sTape k)) = σ.st from funext fun k => wenc_A_s cap σ k]
    have e : (fun x => Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq (sp (nr' := nr') x)) =
        Fin.addCases (motive := fun _ => List Bool) y.st tq := by
      funext x
      refine Fin.addCases (fun i' => ?_) (fun k' => ?_) x
      · simp only [sp, Fin.addCases_left, wenc_A_s]
      · simp only [sp, Fin.addCases_right]
    rw [e]
    rfl
  · have e := install_slot (wq fs fr em) (wq_inj fs fr em hgs hfr) (wenc cap σ).A
      (Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq) (Fin.castAdd q cTape)
    rw [wq_c, Fin.addCases_left, wenc_A_c] at e
    rw [e, wenc_A_c]
    rfl
  · rw [install_fac (wq fs fr em) (wq_inj fs fr em hgs hfr) rTape rTape_inj fr hfr
      (fun r' => Fin.castAdd q (rTape (ns := ns') r')) (wq_r fs fr em) (wq_out_r fs fr em), wenc_A_r,
      show (fun k => (wenc cap σ).A (rTape k)) = fun k => regTape cap (σ.val k) from funext fun k => wenc_A_r cap σ k]
    have e : (fun x => Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq
        (Fin.castAdd q (rTape (ns := ns') x))) = fun x => regTape cap (y.val x) := by
      funext x
      simp only [Fin.addCases_left, wenc_A_r]
    rw [e, install_reg fr hfr σ.val y.val r (regTape cap)]
    rfl

theorem updW_H (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1))
    (hgs : Function.Injective (gs fs em)) (hfr : Function.Injective fr) (σ : WState ns nr) (y : WState ns' nr')
    (hq : Fin q → ℕ) (tq : Fin q → List Bool) :
    dockH (wq fs fr em) (wenc cap σ).H (Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq) =
      (wenc cap (updW fs fr em σ y hq tq)).H := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [dockH_fac (wq fs fr em) (wq_inj fs fr em hgs hfr) sTape sTape_inj (gs fs em) hgs sp (wq_sp fs fr em)
      (wq_out_s fs fr em), wenc_H_s,
      show (fun k => (wenc cap σ).H (sTape k)) = σ.sh from funext fun k => wenc_H_s cap σ k]
    have e : (fun x => Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq (sp (nr' := nr') x)) =
        Fin.addCases (motive := fun _ => ℕ) y.sh hq := by
      funext x
      refine Fin.addCases (fun i' => ?_) (fun k' => ?_) x
      · simp only [sp, Fin.addCases_left, wenc_H_s]
      · simp only [sp, Fin.addCases_right]
    rw [e]
    rfl
  · have e := dockH_slot (wq fs fr em) (wq_inj fs fr em hgs hfr) (wenc cap σ).H
      (Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq) (Fin.castAdd q cTape)
    rw [wq_c, Fin.addCases_left, wenc_H_c] at e
    rw [e, wenc_H_c]
  · rw [dockH_fac (wq fs fr em) (wq_inj fs fr em hgs hfr) rTape rTape_inj fr hfr
      (fun r' => Fin.castAdd q (rTape (ns := ns') r')) (wq_r fs fr em) (wq_out_r fs fr em), wenc_H_r,
      show (fun k => (wenc cap σ).H (rTape k)) = σ.val from funext fun k => wenc_H_r cap σ k]
    have e : (fun x => Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq
        (Fin.castAdd q (rTape (ns := ns') x))) = y.val := by
      funext x
      simp only [Fin.addCases_left, wenc_H_r]
    rw [e]
    rfl

/-- **A sub-layout register bank with extra tapes, docked**: a machine run on `wenc y` and `q` extra tapes, docked onto
the streams `fs`, the registers `fr`, the cell and the streams `em` of a state `σ` that restricts to `y` there, leaves
the state `updW …`. -/
theorem dockW {s n : ℕ} {M : Machine ((ns' + 2 + nr') + q) s} (fs : Fin (ns' + 1) → Fin (ns + 1))
    (fr : Fin nr' → Fin nr) (em : Fin q → Fin (ns + 1)) (hgs : Function.Injective (gs fs em))
    (hfr : Function.Injective fr) (σ : WState ns nr) (y y' : WState ns' nr') (hq0 hq : Fin q → ℕ)
    (tq0 tq : Fin q → List Bool)
    (h : Step M n (Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq0)
      (Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq0)
      (Fin.addCases (motive := fun _ => ℕ) (wenc cap y').H hq)
      (Fin.addCases (motive := fun _ => List Bool) (wenc cap y').A tq))
    (hsh : ∀ i, σ.sh (fs i) = y.sh i) (hst : ∀ i, σ.st (fs i) = y.st i) (hv : ∀ r, σ.val (fr r) = y.val r)
    (hc : σ.cell = y.cell) (hqh : ∀ k, σ.sh (em k) = hq0 k) (hqt : ∀ k, σ.st (em k) = tq0 k) :
    Step (RecoveryFocus.machine (wq fs fr em) M) n (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updW fs fr em σ y' hq tq)).H (wenc cap (updW fs fr em σ y' hq tq)).A := by
  have hH : ∀ j, (wenc cap σ).H (wq fs fr em j) = Fin.addCases (motive := fun _ => ℕ) (wenc cap y).H hq0 j := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun k => ?_) j
    · simp only [wq, Fin.addCases_left]
      rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wslot_s, wenc_H_s, wenc_H_s, hsh]
      · rw [wslot_c, wenc_H_c, wenc_H_c]
      · rw [wslot_r, wenc_H_r, wenc_H_r, hv]
    · simp only [wq, Fin.addCases_right]
      rw [wenc_H_s, hqh]
  have hA : ∀ j, (wenc cap σ).A (wq fs fr em j) = Fin.addCases (motive := fun _ => List Bool) (wenc cap y).A tq0 j := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun k => ?_) j
    · simp only [wq, Fin.addCases_left]
      rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wslot_s, wenc_A_s, wenc_A_s, hst]
      · rw [wslot_c, wenc_A_c, wenc_A_c, hc]
      · rw [wslot_r, wenc_A_r, wenc_A_r, hv]
    · simp only [wq, Fin.addCases_right]
      rw [wenc_A_s, hqt]
  have hd := dockRun h (wq fs fr em) (wq_inj fs fr em hgs hfr) (wenc cap σ).H (wenc cap σ).A hH hA
  rw [updW_H cap fs fr em hgs hfr σ y' hq tq, updW_A cap fs fr em hgs hfr σ y' hq tq] at hd
  exact hd

end Sub

end NearCubicWires.WireExponent3_5.PrimAsm.DockW
