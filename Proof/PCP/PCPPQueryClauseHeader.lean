import Proof.PCP.PCPPQueryClauseRows

/-! Physical PCPP metadata preparation for clause queries. The systematic
row count is decoded into its actual unary driver; auxiliary/clause widths
are only skipped. Caller arity and index drivers are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseHeader
open LocalBitMultitape PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 3→Fin 16 := ![0,11,12]
def naturalSlots (i : Fin 11) : Fin 16 := i.castAdd 5
noncomputable def first := RecoveryFocus.machine fieldSlots (PCPPQueryField.machine false)
noncomputable def natural := RecoveryFocus.machine naturalSlots PCPPQueryNatural.machine
noncomputable def last := RecoveryFocus.machine fieldSlots (pair false)
noncomputable def prefixMachine := Composition.machine first natural
noncomputable def machine := Composition.machine prefixMachine last
def heads : Fin 16→ℕ := fun i => if i=13 ∨ i=14 then 1 else 0
def tapes (source : List Bool) (arity index : ℕ) : Fin 16→List Bool := fun i =>
  if i=0 then source else if i=13 then UnaryTemplate.tape arity else if i=14 then UnaryTemplate.tape index else []
noncomputable def entry (source : List Bool) (arity index : ℕ) :=
  (⟨machine.start,heads,tapes source arity index⟩ : Configuration 16 (4+PCPPQueryNatural.states+8))
def budget (a b c : ℕ) := fieldCost 3+PCPPQueryNatural.budget a+pairCost b c+2

theorem field_pick (i : Fin 16) : RecoveryFocus.pick fieldSlots i=
    if i=0 then some 0 else if i=11 then some 1 else if i=12 then some 2 else none := by
  by_cases h0 : i=0
  · subst i; exact RecoveryFocus.pick_slot fieldSlots (by decide) 0
  by_cases h11 : i=11
  · subst i; exact RecoveryFocus.pick_slot fieldSlots (by decide) 1
  by_cases h12 : i=12
  · subst i; exact RecoveryFocus.pick_slot fieldSlots (by decide) 2
  have hn : ¬∃ j,fieldSlots j=i := by
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [fieldSlots] at hj <;> omega
  simp [RecoveryFocus.pick,hn,h0,h11,h12]

theorem header_run (a b c arity index : ℕ) (tail : List Bool) :
    let source := fourBits 3 a b c++tail
    ∃ r,runFrom machine (budget a b c) (entry source arity index)=some r ∧
      r.steps≤budget a b c ∧
      r.final.tapes 0=source ∧ r.final.heads 0=(fourBits 3 a b c).length ∧
      r.final.tapes 10=UnaryTemplate.tape a ∧ r.final.heads 10=1 ∧
      r.final.tapes 11=saved c (saved b (saved 3 [])) ∧ r.final.heads 11=0 ∧
      r.final.tapes 12=[] ∧ r.final.heads 12=0 ∧
      r.final.tapes 13=UnaryTemplate.tape arity ∧ r.final.heads 13=1 ∧
      r.final.tapes 14=UnaryTemplate.tape index ∧ r.final.heads 14=1 ∧
      r.final.tapes 15=[] ∧ r.final.heads 15=0 := by
  dsimp only
  let source := fourBits 3 a b c++tail
  let start : Configuration 16 4 := ⟨first.start,heads,tapes source arity index⟩
  obtain ⟨raw,hr,hrf,hrs⟩ := nat_run false [] (fieldBits a++pairBits b c++tail) [] [] 3
  have hsource : []++RepairRepresentation.natWord 3++(fieldBits a++pairBits b c++tail)=source := by
    simp [source,fourBits,pairBits,fieldBits,List.append_assoc]
  rw [hsource] at hr hrf
  simp only [List.length_nil,Nat.zero_add,selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hr hrf
  obtain ⟨x,hx,hxf,hxs⟩ := RecoveryFocus.run_config fieldSlots (by decide)
    (PCPPQueryField.machine false) start.heads start.tapes _ _ raw hr
  have hxentry : RecoveryFocus.config fieldSlots start.heads start.tapes (cfg 0 source 0 [] 0 [])=start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> simp [start,heads,fieldSlots,cfg]
    · intro i; fin_cases i <;> simp [start,tapes,fieldSlots,cfg]
  rw [hxentry] at hx
  have hnt : ∀ j,x.final.tapes (naturalSlots j)=if j=0 then
      fieldBits 3++RepairRepresentation.natWord a++(pairBits b c++tail) else [] := by
    intro j
    rw [hxf,hrf]
    fin_cases j <;> simp [RecoveryFocus.config,field_pick,naturalSlots,payload,cfg,start,tapes,
      source,fourBits,pairBits,fieldBits,List.append_assoc]
  have hnh : ∀ j,x.final.heads (naturalSlots j)=if j=0 then (fieldBits 3).length else 0 := by
    intro j
    rw [hxf,hrf]
    fin_cases j <;> simp [RecoveryFocus.config,field_pick,naturalSlots,payload,cfg,start,heads]
  obtain ⟨y,hy,hys,hsourceY,hposY,hsys,hsysHead,hyOther⟩ := PCPPQueryNatural.focus_run naturalSlots
    (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 16 => k.val) h)
    x.final (fieldBits 3) (pairBits b c++tail) a hnt hnh
  have hXY := Composition.run_join first natural _ _ _ x y hx hy
  let xy := Composition.joinedReceipt x y
  let pre := pairBits 3 a
  obtain ⟨endRaw,her,herf,hers⟩ := pair_run false pre tail (saved 3 []) [] b c
  have hendSource : pre++pairBits b c++tail=source := rfl
  rw [hendSource] at her herf
  simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at herf
  obtain ⟨z,hz,hzf,hzs⟩ := RecoveryFocus.run_config fieldSlots (by decide) (pair false)
    xy.final.heads xy.final.tapes _ _ endRaw her
  have hzentry : RecoveryFocus.config fieldSlots xy.final.heads xy.final.tapes
      (store (s:=8) 0 source pre.length (saved 3 []) [])=Composition.restart xy.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      change y.final.heads (fieldSlots i)=_
      fin_cases i
      · change y.final.heads 0=pre.length
        have he : (fieldBits 3).length+2*natBitLength a+1=pre.length := by simp [pre,pairBits]; omega
        exact hposY.trans he
      · change y.final.heads 11=0
        rw [(hyOther 11 (by decide)).2,hxf,hrf]
        simp [RecoveryFocus.config,field_pick,payload,cfg]
      · change y.final.heads 12=0
        rw [(hyOther 12 (by decide)).2,hxf,hrf]
        simp [RecoveryFocus.config,field_pick,payload,cfg]
    · intro i
      change y.final.tapes (fieldSlots i)=_
      fin_cases i
      · change y.final.tapes 0=source
        simpa [source,fourBits,pairBits,fieldBits,List.append_assoc,naturalSlots] using hsourceY
      · change y.final.tapes 11=saved 3 []
        rw [(hyOther 11 (by decide)).1,hxf,hrf]
        simp [RecoveryFocus.config,field_pick,payload,cfg,saved]
      · change y.final.tapes 12=[]
        rw [(hyOther 12 (by decide)).1,hxf,hrf]
        simp [RecoveryFocus.config,field_pick,payload,cfg]
  rw [hzentry] at hz
  have hXYZ := Composition.run_join prefixMachine last _ _ _ xy z hXY hz
  have ht : ((2*natBitLength 3+3)+1+PCPPQueryNatural.budget a)+1+pairCost b c=budget a b c := by
    unfold budget fieldCost; omega
  rw [ht] at hXYZ
  have he : Composition.leftConfig 8 (Composition.leftConfig PCPPQueryNatural.states start)=entry source arity index := rfl
  rw [he] at hXYZ
  have hzt (j : Fin 3) : z.final.tapes (fieldSlots j)=endRaw.final.tapes j := by
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot fieldSlots (by decide)]
  have hzh (j : Fin 3) : z.final.heads (fieldSlots j)=endRaw.final.heads j := by
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot fieldSlots (by decide)]
  have hzOther (i : Fin 16) (hi : i≠0 ∧ i≠11 ∧ i≠12) :
      z.final.tapes i=y.final.tapes i ∧ z.final.heads i=y.final.heads i := by
    simp [hzf,RecoveryFocus.config,field_pick,hi,xy,Composition.joinedReceipt,Composition.rightConfig]
  have retained (i : Fin 16) (hi : i=13 ∨ i=14 ∨ i=15) :
      z.final.tapes i=tapes source arity index i ∧ z.final.heads i=heads i := by
    have hnot : i≠0 ∧ i≠11 ∧ i≠12 := by rcases hi with h|h|h <;> subst i <;> decide
    obtain ⟨hzt',hzh'⟩ := hzOther i hnot
    have hn : RecoveryFocus.pick naturalSlots i=none := by rcases hi with h|h|h <;> subst i <;> decide
    rw [hzt',hzh',(hyOther i hn).1,(hyOther i hn).2,hxf,hrf]
    simp [RecoveryFocus.config,field_pick,hnot,start]
  refine ⟨Composition.joinedReceipt xy z,hXYZ,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    (retained 13 (by simp)).1,(retained 13 (by simp)).2,
    (retained 14 (by simp)).1,(retained 14 (by simp)).2,
    (retained 15 (by simp)).1,(retained 15 (by simp)).2⟩
  · change (x.steps+1+y.steps)+1+z.steps≤_
    rw [hxs,hrs,hzs,hers]
    unfold budget fieldCost
    omega
  · exact (hzt 0).trans (by rw [herf]; rfl)
  · exact (hzh 0).trans (by rw [herf]; simp [store,pre,fourBits,List.length_append])
  · exact (hzOther 10 (by decide)).1.trans hsys
  · exact (hzOther 10 (by decide)).2.trans hsysHead
  · exact (hzt 1).trans (by rw [herf]; rfl)
  · exact (hzh 1).trans (by rw [herf]; rfl)
  · exact (hzt 2).trans (by rw [herf]; rfl)
  · exact (hzh 2).trans (by rw [herf]; rfl)

end NearCubicWires.RepairOrdinary.PCPPQueryClauseHeader
