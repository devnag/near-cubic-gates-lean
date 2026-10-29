import SourceAdapters.Compile.BoundedMachine
import SourceAdapters.Compile.OracleChargedRun

/-!
proof of `thm:short-pcp-ours`, Step 4: a finite representation of the actual charged computation.
In addition to finite cells/heads/control, retain every allocated tape length:
OrdinaryOracleRuns requires exact list equality on the output tape. A framed
singleton followed by allocated false cells must not become accepting.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

structure Window (t s width : ℕ) where
  view : MachineWindow t s width
  lengths : Fin t → Fin (width+1)

def Fits {t s : ℕ} (width : ℕ) (c : Configuration t s) : Prop :=
  (∀ tape, c.heads tape < width) ∧ (∀ tape, (c.tapes tape).length ≤ width)

def Window.unpack {t s width : ℕ} (a : Window t s width) : Configuration t s where
  control := a.view.control
  heads := fun tape => (a.view.heads tape).val
  tapes := fun tape => (List.ofFn (a.view.cells tape)).take (a.lengths tape).val

def Window.pack {t s width : ℕ} (c : Configuration t s) (h : Fits width c) : Window t s width where
  view := MachineWindow.ofConfiguration c h.1
  lengths := fun tape => ⟨(c.tapes tape).length,Nat.lt_succ_of_le (h.2 tape)⟩

theorem observed_take (bits : List Bool) (width : ℕ) (h : bits.length ≤ width) :
    (List.ofFn fun i : Fin width => readTapeBit bits i.val).take bits.length=bits := by
  apply List.ext_getElem (by simp; omega)
  intro i hleft hright
  simp only [List.getElem_take,List.getElem_ofFn,readTapeBit]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hright]

theorem Window.unpack_pack {t s width : ℕ} (c : Configuration t s) (h : Fits width c) :
    (Window.pack c h).unpack=c := by
  apply configuration_ext
  · rfl
  · rfl
  · funext tape
    exact observed_take _ _ (h.2 tape)

theorem Window.unpack_fits {t s width : ℕ} (a : Window t s width) : Fits width a.unpack := by
  constructor
  · exact fun tape => (a.view.heads tape).isLt
  · intro tape
    simp [Window.unpack]

/-- Preserve enough head room for all still-available charged steps. -/
theorem step_room {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost budget width : ℕ} {a b : p.Config}
    (hs : OrdinaryOracleStep o p cost a b) (hc : cost ≤ budget)
    (hh : ∀ tape, a.heads tape+budget < width)
    (ht : ∀ tape, (a.tapes tape).length ≤ width) :
    Fits width b ∧ (∀ tape, b.heads tape+(budget-cost) < width) := by
  cases hs with
  | «local» a b _ _ hs =>
    have hb := OrdinaryOracleCompose.local_head_bound hs
    have hl := OrdinaryOracleCompose.local_tape_bound hs
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro tape; have := hh tape; have := hb tape; omega
    · intro tape; have := hh tape; have := hl tape; have := ht tape; omega
    · intro tape; have := hh tape; have := hb tape; omega
  | ask a bits padding rule _ _ _ _ =>
    refine ⟨⟨?_,ht⟩,?_⟩
    · intro tape; exact Nat.lt_of_add_right_lt (hh tape)
    · intro tape; have := hh tape; change a.heads tape+(budget-_) < width; omega

/-- A bounded local/ask step on finite data, retaining its full literal cost. -/
noncomputable def windowStep (o : ℕ → Bool) (p : OrdinaryOracleProgram) (width : ℕ)
    (a : Window p.base.tapeCount p.base.stateCount width) :
    Option (ℕ × Window p.base.tapeCount p.base.stateCount width) := by
  classical
  exact match chargedStep o p a.unpack with
    | none => none
    | some (cost,b) => if h : Fits width b then some (cost,Window.pack b h) else none

theorem windowStep_sound {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cost : ℕ}
    {a b : Window p.base.tapeCount p.base.stateCount width}
    (h : windowStep o p width a=some (cost,b)) :
    OrdinaryOracleStep o p cost a.unpack b.unpack := by
  unfold windowStep at h
  split at h
  · simp at h
  · rename_i pair hs
    obtain ⟨charge,after⟩ := pair
    split at h
    · rename_i hf
      cases h
      rw [Window.unpack_pack]
      exact chargedStep_sound hs
    · simp at h

theorem windowStep_complete {o : ℕ → Bool} {p : OrdinaryOracleProgram} {width cost : ℕ}
    {a : Window p.base.tapeCount p.base.stateCount width} {b : p.Config}
    (h : OrdinaryOracleStep o p cost a.unpack b) (hf : Fits width b) :
    windowStep o p width a=some (cost,Window.pack b hf) := by
  classical
  simp only [windowStep,chargedStep_complete h]
  rw [dif_pos hf]

end NearCubicGates.Adapters.Compile.OracleExecution
