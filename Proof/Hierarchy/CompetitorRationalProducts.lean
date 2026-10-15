import Proof.Hierarchy.HierarchyBinaryMultiply

/-! Four actual cross-products for a signed rational decision. Numerators
and denominators are read from shared retained tapes. Every invocation gets
disjoint blank work tapes, so neither operand duplication nor scratch erasure
is implicit. The two denominator tapes and the unary width are reused at
restored heads by the actual multiplier. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalProducts
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shared (j : Fin 7) : Fin 67 := ⟨j.val,by omega⟩
def privateTape (i : Fin 4) (j : Fin 14) : Fin 67 := ⟨7+14*i.val+j.val,by omega⟩
def productTape (i : Fin 4) : Fin 67 := privateTape i 3
def factorTape (i : Fin 4) : Fin 67 := if i.val<2 then 5 else 4
def slot (i : Fin 4) (j : Fin 14) : Fin 67 :=
  if j.val=0 then factorTape i else if j.val=8 then ⟨i.val,by omega⟩
  else if j.val=9 then 6 else privateTape i j

theorem slot_injective (i : Fin 4) : Function.Injective (slot i) := by
  fin_cases i <;> decide
@[simp] theorem slot_zero (i : Fin 4) : slot i 0=factorTape i := rfl
@[simp] theorem slot_eight (i : Fin 4) : slot i 8=⟨i.val,by omega⟩ := rfl
@[simp] theorem slot_nine (i : Fin 4) : slot i 9=6 := rfl
@[simp] theorem slot_three (i : Fin 4) : slot i 3=productTape i := rfl

def input (w b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) : Fin 67 → List Bool :=
  fun j => if h : j.val<4 then frame (binary w (nums ⟨j.val,h⟩))
    else if j.val=4 then frame (binary b d)
    else if j.val=5 then frame (binary b e)
    else if j.val=6 then List.replicate w true else []
def factor (i : Fin 4) (d e : ℕ) : ℕ := if i.val<2 then e else d

structure Store (w b : ℕ) (nums : Fin 4 → ℕ) (d e done : ℕ)
    (tapes : Fin 67 → List Bool) : Prop where
  shared : ∀ j : Fin 7,tapes (shared j)=input w b nums d e (shared j)
  products : ∀ i : Fin 4,i.val<done →
    tapes (productTape i)=frame (binary w (nums i*factor i d e))
  fresh : ∀ j : Fin 67,7+14*done≤j.val → tapes j=[]

theorem initial_store (w b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) :
    Store w b nums d e 0 (input w b nums d e) := by
  constructor
  · intro j; rfl
  · intro i hi; omega
  · intro j hj
    simp only [input]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · rfl

theorem input14_cases (w a : ℕ) (bits : List Bool) (j : Fin 14) :
    HierarchyMultiplyEntry.input14 w a bits j=
      if j.val=0 then frame bits else if j.val=8 then frame (binary w a)
      else if j.val=9 then List.replicate w true else [] := by
  fin_cases j <;> rfl

theorem store_slot (w b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) (i : Fin 4)
    (tapes : Fin 67 → List Bool) (h : Store w b nums d e i.val tapes) (j : Fin 14) :
    tapes (slot i j)=HierarchyMultiplyEntry.input14 w (nums i) (binary b (factor i d e)) j := by
  rw [input14_cases]
  by_cases h0 : j.val=0
  · have hj : j=0 := Fin.ext h0
    subst j
    simp only [slot_zero]
    by_cases hi : i.val<2
    · simpa [factorTape,hi,input,shared,factor] using h.shared 5
    · simpa [factorTape,hi,input,shared,factor] using h.shared 4
  · by_cases h8 : j.val=8
    · have hj : j=8 := Fin.ext h8
      subst j
      have hs := h.shared ⟨i.val,by omega⟩
      simpa [input,shared,i.isLt] using hs
    · by_cases h9 : j.val=9
      · have hj : j=9 := Fin.ext h9
        subst j
        simpa [input,shared] using h.shared 6
      · simp only [slot,h0,h8,h9,if_false]
        exact h.fresh _ (by simp [privateTape])

theorem bounded_focus {t u s time : ℕ} (slot' : Fin t → Fin u)
    (hi : Function.Injective slot') (p : Machine t s)
    (input' output' : Fin t → List Bool) (h : ClockJoin.ReadyRun p time input' output')
    (ambient : Fin u → List Bool) (hin : ∀ j,ambient (slot' j)=input' j) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slot' p) time ambient (install slot' ambient output') := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot' hi p (fun _ => 0) ambient time
    (initialConfiguration p input') base hr
  have hinit : RecoveryFocus.config slot' (fun _ => 0) ambient (initialConfiguration p input')=
      initialConfiguration (RecoveryFocus.machine slot' p) ambient := by
    apply configuration_ext
    · rfl
    · funext j; cases hp : RecoveryFocus.pick slot' j <;>
        simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing slot' ambient input' hin
  rw [hinit] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    change install slot' ambient base.final.tapes=install slot' ambient output'
    rw [ht]
  · intro j
    cases hp : RecoveryFocus.pick slot' j <;> simp [hf,RecoveryFocus.config,hp,hh]

theorem slot_before (i : Fin 4) (j : Fin 14) : (slot i j).val<7+14*(i.val+1) := by
  simp only [slot]
  split
  · simp only [factorTape]; split <;> simp <;> omega
  · split
    · simp; omega
    · split
      · simp; omega
      · simp [privateTape]; omega

theorem slot_private_distinct (i k : Fin 4) (j l : Fin 14) (hik : i≠k) :
    slot i j≠privateTape k l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [slot] at hv
  split at hv
  · simp only [factorTape] at hv
    split at hv <;> simp only [privateTape] at hv <;> omega
  · split at hv
    · simp only [privateTape] at hv; omega
    · split at hv
      · simp only [privateTape] at hv; omega
      · simp only [privateTape] at hv
        have hn : i.val≠k.val := fun h => hik (Fin.ext h)
        omega

theorem store_after (w b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) (i : Fin 4)
    (tapes : Fin 67 → List Bool) (h : Store w b nums d e i.val tapes)
    (out : Fin 14 → List Bool)
    (hout : out 3=frame (binary w (nums i*factor i d e)))
    (hfactor : out 0=frame (binary b (factor i d e)))
    (hnum : out 8=frame (binary w (nums i)))
    (hwidth : out 9=List.replicate w true) :
    Store w b nums d e (i.val+1) (install (slot i) tapes out) := by
  constructor
  · intro j
    cases hp : RecoveryFocus.pick (slot i) (shared j) with
    | none => simpa [install,hp] using h.shared j
    | some k =>
      have he := RecoveryFocus.slot_of_pick (slot i) hp
      have hv := congrArg Fin.val he
      have hk : k.val=0 ∨ k.val=8 ∨ k.val=9 := by
        by_contra hn
        simp only [not_or] at hn
        simp only [slot,hn.1,hn.2.1,hn.2.2,if_false,privateTape,shared] at hv
        omega
      have hsame : out k=tapes (slot i k) := by
        rw [store_slot w b nums d e i tapes h k,input14_cases]
        rcases hk with hk | hk | hk
        · have heq : k=0 := Fin.ext hk
          subst k
          exact hfactor
        · have heq : k=8 := Fin.ext hk
          subst k
          exact hnum
        · have heq : k=9 := Fin.ext hk
          subst k
          exact hwidth
      simp only [install,hp]
      rw [hsame,he]
      exact h.shared j
  · intro k hk
    by_cases he : k=i
    · subst k
      exact (install_slot (slot i) (slot_injective i) tapes out 3).trans hout
    · rw [install_other (slot i) tapes out (productTape k)
        (fun j => slot_private_distinct i k j 3 (Ne.symm he))]
      exact h.products k (by have hn : k.val≠i.val := fun h => he (Fin.ext h); omega)
  · intro j hj
    rw [install_other (slot i) tapes out j (by
      intro k he
      have hlt := slot_before i k
      rw [he] at hlt
      omega)]
    exact h.fresh j (by omega)

noncomputable def program (i : Fin 4) := RecoveryFocus.machine (slot i) HierarchyMultiplyEntry.machine
def cost (w b : ℕ) := 128*(w+1)*(b+1)

theorem product_run (w b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ) (i : Fin 4)
    (tapes : Fin 67 → List Bool) (h : Store w b nums d e i.val tapes)
    (hfit : nums i*2^b<2^w) (hdenom : factor i d e<2^b) :
    ∃ out,ClockJoin.ReadyRun (program i) (cost w b) tapes out ∧
      Store w b nums d e (i.val+1) out := by
  obtain ⟨r,hr,hout,hfactor,hnum,hwidth,_,hh,hs⟩ :=
    HierarchyMultiplyEntry.multiply_run w (nums i) (binary b (factor i d e)) (by simpa using hfit)
  have hprod : r.final.tapes 3=frame (binary w (nums i*factor i d e)) := by
    simpa only [binary_value b (factor i d e) hdenom] using hout
  have hready : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine (cost w b)
      (HierarchyMultiplyEntry.input14 w (nums i) (binary b (factor i d e))) r.final.tapes := by
    exact ⟨r,by simpa [HierarchyMultiplyEntry.budget,cost] using hr,rfl,hh,
      by simpa [HierarchyMultiplyEntry.budget,cost] using hs⟩
  refine ⟨install (slot i) tapes r.final.tapes,
    bounded_focus (slot i) (slot_injective i) _ _ _ hready tapes (store_slot w b nums d e i tapes h),?_⟩
  exact store_after w b nums d e i tapes h r.final.tapes hprod hfactor hnum hwidth

end NearCubicWires.RepairOrdinary.CompetitorRationalProducts
