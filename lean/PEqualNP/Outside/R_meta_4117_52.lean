import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A cubic vertex with at most one reader has exactly one reader.
-- Changing that vertex affects the output only through that gate.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4117_52
    (invert : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit) (v : Fin n) (j : ℕ),
      let f := graphFun G A
      let r (i : ℕ) (g : Gate) := (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      let g := gateAt C j
      (∀ w ∉ A, (G.neighborSet w).ncard = 3) → 7 ≤ G.egirth →
      (∀ u w, G.Adj u w → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      (∀ w ∉ A, let R := C.gates.filter (r w.val)
        R.length ≤ 3 ∧ (R.length = 3 → ∀ h ∈ R, h.op = .or)) →
      v ∉ A → j < C.gates.length → r v.val g = true → g.op = GateOp.not →
      (∀ k < C.gates.length, r v.val (gateAt C k) = true → k = j) →
      ((Finset.range C.gates.length).filter fun k => j < k ∧ r (n+j) (gateAt C k) = true).card ≤ 2 →
      ∃ w ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x w false)) t)
    (meet : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit) (v : Fin n) (j : ℕ),
      let f := graphFun G A
      let r (i : ℕ) (g : Gate) := (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      let g := gateAt C j
      (∀ w ∉ A, (G.neighborSet w).ncard = 3) → 7 ≤ G.egirth →
      (∀ u w, G.Adj u w → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      (∀ w ∉ A, let R := C.gates.filter (r w.val)
        R.length ≤ 3 ∧ (R.length = 3 → ∀ h ∈ R, h.op = .or)) →
      v ∉ A → j < C.gates.length → r v.val g = true → g.op = GateOp.and →
      (∀ k < C.gates.length, r v.val (gateAt C k) = true → k = j) →
      ((Finset.range C.gates.length).filter fun k => j < k ∧ r (n+j) (gateAt C k) = true).card ≤ 2 →
      (∀ u : Fin n, u ≠ v → ¬g.inputs.Perm [v.val,u.val]) →
      (∀ x, f (Function.update x v false) ≠ f (Function.update x v true) →
        (C.wires (List.ofFn (Function.update x v false))).getD (n+j) false ≠
          (C.wires (List.ofFn (Function.update x v true))).getD (n+j) false) →
      ∃ w ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x w false)) t)
    (join : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit) (v : Fin n) (j : ℕ),
      let f := graphFun G A
      let r (i : ℕ) (g : Gate) := (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      let g := gateAt C j
      (∀ w ∉ A, (G.neighborSet w).ncard = 3) → 7 ≤ G.egirth →
      (∀ u w, G.Adj u w → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      (∀ w ∉ A, let R := C.gates.filter (r w.val)
        R.length ≤ 3 ∧ (R.length = 3 → ∀ h ∈ R, h.op = .or)) →
      v ∉ A → j < C.gates.length → r v.val g = true → g.op = GateOp.or →
      (∀ k < C.gates.length, r v.val (gateAt C k) = true → k = j) →
      (∀ u : Fin n, u ≠ v → ¬g.inputs.Perm [v.val,u.val]) →
      (∀ x, f (Function.update x v false) ≠ f (Function.update x v true) →
        (C.wires (List.ofFn (Function.update x v false))).getD (n+j) false ≠
          (C.wires (List.ofFn (Function.update x v true))).getD (n+j) false) →
      ∃ w ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x w false)) t) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
  have factor :
      ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ),
      let read (i : ℕ) (g : Gate) :=
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      FanInTwo C → C.output ≠ v.val →
      (∀ k < C.gates.length, read v.val (gateAt C k) = true → k = j) →
      ∀ a b : Fin n → Bool, (∀ w, w ≠ v → a w = b w) →
        (C.wires (List.ofFn a)).getD (n+j) false = (C.wires (List.ofFn b)).getD (n+j) false →
        circuitFun n C a = circuitFun n C b := by
    intro n C v j read fan out readers a b agree common
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let W (x : Fin n → Bool) (k : ℕ) := (C.gates.take k).foldl step (List.ofFn x)
    have foldLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
    have length (x : Fin n → Bool) (k : ℕ) (hk : k ≤ C.gates.length) : (W x k).length = n+k := by
      simp only [W,foldLen,List.length_ofFn,List.length_take,Nat.min_eq_left hk]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have before (x : Fin n → Bool) (k i : ℕ) (hi : i < (W x k).length) :
        (C.wires (List.ofFn x)).getD i false = (W x k).getD i false := by
      change (C.gates.foldl step (List.ofFn x)).getD i false = _
      conv_lhs => rw [← List.take_append_drop k C.gates]
      rw [List.foldl_append]
      exact keep _ _ _ hi
    have equalGate (g : Gate) (hg : g ∈ C.gates) (w z : List Bool)
        (h : ∀ i, read i g = true → w.getD i false = z.getD i false) :
        g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => z.getD i false) := by
      obtain ⟨op,arity⟩ := fan g hg
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using op
      rcases hop with he | he | he
      · have take : g.inputs.take 2 = g.inputs := List.take_of_length_le arity
        have same : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => z.getD i false) := by
          apply List.map_congr_left
          intro i hi
          apply h i
          have e : GateOp.and.eval [false] = false := rfl
          simpa only [read,he,e,Bool.cond_false,take,List.contains_iff_mem] using hi
        rw [same]
      · have take : g.inputs.take 2 = g.inputs := List.take_of_length_le arity
        have same : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => z.getD i false) := by
          apply List.map_congr_left
          intro i hi
          apply h i
          have e : GateOp.or.eval [false] = false := rfl
          simpa only [read,he,e,Bool.cond_false,take,List.contains_iff_mem] using hi
        rw [same]
      · cases e : g.inputs with
        | nil => simp only [he,List.map_nil]
        | cons i rest =>
          have one : GateOp.not.eval [false] = true := rfl
          have m : read i g = true := by
            simp [read,he,one,e]
          rw [he]
          change (!(w.getD i false)) = (!(z.getD i false))
          rw [h i m]
    have same (k : ℕ) (hk : k ≤ C.gates.length) :
        ∀ i, i ≠ v.val → (W a k).getD i false = (W b k).getD i false := by
      induction k with
      | zero =>
        intro i ne
        change (List.ofFn a).getD i false = (List.ofFn b).getD i false
        by_cases hi : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
            List.getElem_ofFn,List.getElem_ofFn]
          exact agree ⟨i,hi⟩ (fun e => ne (congrArg Fin.val e))
        · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi),
            List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]
      | succ k ih =>
        have old : k < C.gates.length := by omega
        have prev := ih (by omega)
        let g := C.gates[k]'old
        have stepW (x : Fin n → Bool) : W x (k+1) = step (W x k) g := by
          simp only [W,List.take_succ_eq_append_getElem old,List.foldl_append,List.foldl_cons,List.foldl_nil,g]
        intro i ne
        by_cases hi : i < n+k
        · rw [stepW,stepW]
          change ((W a k) ++ [_]).getD i false = ((W b k) ++ [_]).getD i false
          rw [List.getD_append _ _ _ _ (by rw [length _ _ (by omega)]; exact hi),
            List.getD_append _ _ _ _ (by rw [length _ _ (by omega)]; exact hi)]
          exact prev i ne
        · by_cases e : i = n+k
          · subst i
            by_cases kj : k = j
            · have ha : n+k < (W a (k+1)).length := by rw [length _ _ hk]; omega
              have hb : n+k < (W b (k+1)).length := by rw [length _ _ hk]; omega
              rw [← before _ _ _ ha, ← before _ _ _ hb,kj]
              exact common
            · have val : g = gateAt C k := (List.getD_eq_getElem _ _ old).symm
              have sameVal := equalGate g (List.getElem_mem old) (W a k) (W b k) (fun pin hr =>
                prev pin (fun e => kj (readers k old (by simpa only [e,val] using hr))))
              rw [stepW,stepW]
              simp only [step,sameVal]
              rw [List.getD_append_right _ _ _ _ (by rw [length _ _ (by omega)]),
                List.getD_append_right _ _ _ _ (by rw [length _ _ (by omega)]),
                length a k (by omega),length b k (by omega)]
          · rw [List.getD_eq_default _ _ (by rw [length _ _ hk]; omega),
              List.getD_eq_default _ _ (by rw [length _ _ hk]; omega)]
    have last := same C.gates.length le_rfl C.output out
    change (C.gates.foldl step (List.ofFn a)).getD C.output false =
      (C.gates.foldl step (List.ofFn b)).getD C.output false
    simpa only [W,List.take_length] using last
  intro n G dec A C f r near R deg girth isolated edge minimal eval sparse rare low
  obtain ⟨v,hv,small,raw⟩ := rare
  have unitFalse (w : Fin n) (hw : w ∉ A) : f (fun u => decide (u=w)) = false := by
    cases e : f (fun u => decide (u=w)) with
    | false => rfl
    | true =>
      change (decide (∃ u ∈ A, decide (u=w) = true) ||
        decide (∃ a b, G.Adj a b ∧ decide (a=w) = true ∧ decide (b=w) = true)) = true at e
      simp only [Bool.or_eq_true, decide_eq_true_eq] at e
      rcases e with ⟨u,hu,h⟩ | ⟨a,b,adj,ha,hb⟩
      · exact (hw (h ▸ hu)).elim
      · have eq : a = b := ha.trans hb.symm
        exact (adj.ne eq).elim
  have out : C.output ≠ v.val := by
    intro eq
    let a : Fin n → Bool := fun u => decide (u=v)
    have bit : (C.wires (List.ofFn a)).getD v.val false = true := by
      let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
          (gs.foldl step w).getD i false = w.getD i false := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hi
      change (C.gates.foldl step (List.ofFn a)).getD v.val false = true
      rw [keep _ _ _ (by simpa only [List.length_ofFn] using v.isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using v.isLt),List.getElem_ofFn]
      simp [a]
    have contradictionAt := congrFun eval a
    rw [unitFalse v hv] at contradictionAt
    change (C.wires (List.ofFn a)).getD C.output false = false at contradictionAt
    rw [eq,bit] at contradictionAt
    contradiction
  have vDegree : (G.neighborSet v).ncard ≠ 0 := by rw [deg v hv]; decide
  obtain ⟨w,adj⟩ := Set.nonempty_of_ncard_ne_zero vDegree
  have hAdj : G.Adj v w := adj
  have hw : w ∉ A := isolated w v hAdj.symm
  let x : Fin n → Bool := fun u => decide (u=w)
  let y := Function.update x v true
  have diff : f x ≠ f y := by
    rw [unitFalse w hw]
    have yes : f y = true := by
      change (decide (∃ u ∈ A, y u = true) ||
        decide (∃ a b, G.Adj a b ∧ y a = true ∧ y b = true)) = true
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨v,w,hAdj,Function.update_self .., by
        change Function.update x v true w = true
        rw [Function.update_of_ne hAdj.ne.symm]; simp [x]⟩
    rw [yes]
    decide
  have wiresLen (a : Fin n → Bool) : (C.wires (List.ofFn a)).length = n+C.gates.length := by
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have foldLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length+gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
    change (C.gates.foldl step (List.ofFn a)).length = _
    rw [foldLen,List.length_ofFn]
  have existsReader : ∃ j < C.gates.length, r v.val (gateAt C j) = true := by
    by_contra none
    have far (a : Fin n → Bool) : (C.wires (List.ofFn a)).getD (n+C.gates.length) false = false :=
      List.getD_eq_default _ _ (wiresLen a).le
    have common : (C.wires (List.ofFn x)).getD (n+C.gates.length) false =
        (C.wires (List.ofFn y)).getD (n+C.gates.length) false := (far x).trans (far y).symm
    apply diff
    have same := factor n C v C.gates.length minimal.1 out
      (fun k hk hr => False.elim (none ⟨k,hk,hr⟩)) x y
      (fun u hu => (Function.update_of_ne hu true x).symm) common
    simpa only [eval] using same
  obtain ⟨j,hj,reads⟩ := existsReader
  have uniqueList (L : List Gate) (limit : (L.filter (r v.val)).length ≤ 1) :
      ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
        r v.val L[a] = true → r v.val L[b] = true → a = b := by
    induction L with
    | nil => intro a _ ha; simp at ha
    | cons g gs ih =>
      by_cases pick : r v.val g = true
      · have length0 : (gs.filter (r v.val)).length = 0 := by
          simp only [List.filter_cons,pick,ite_true,List.length_cons] at limit
          omega
        have noTail (a : ℕ) (ha : a < gs.length) : r v.val gs[a] ≠ true := by
          have n := List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp length0)
          exact n _ (List.getElem_mem ha)
        intro a b ha hb ea eb
        cases a <;> cases b
        · rfl
        · exact (noTail _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hb) eb).elim
        · exact (noTail _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using ha) ea).elim
        · exact (noTail _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using ha) ea).elim
      · have lim : (gs.filter (r v.val)).length ≤ 1 := by simpa only [List.filter_cons,pick,Bool.false_eq_true,ite_false] using limit
        intro a b ha hb ea eb
        cases a <;> cases b
        · rfl
        · exact (pick ea).elim
        · exact (pick eb).elim
        · congr 1
          exact ih lim _ _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using ha)
            (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hb) ea eb
  have atGate (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] :=
    List.getD_eq_getElem _ _ hk
  have unique (k : ℕ) (hk : k < C.gates.length) (hr : r v.val (gateAt C k) = true) : k = j := by
    rw [atGate k hk] at hr
    have jread := reads
    rw [atGate j hj] at jread
    exact uniqueList _ small k j hk hj hr jread
  have later (nonOr : (gateAt C j).op ≠ .or) :
      ((Finset.range C.gates.length).filter fun k => j < k ∧ r (n+j) (gateAt C k) = true).card ≤ 2 := by
    have subset : ((Finset.range C.gates.length).filter fun k =>
        j < k ∧ r (n+j) (gateAt C k) = true) ⊆ near v j := by
      intro k hk
      obtain ⟨a,b,c⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨a, by omega, Or.inr ⟨b,c⟩⟩
    have bound := Finset.card_le_card subset
    by_contra! many
    apply low
    exact ⟨v,hv,j,hj,reads,nonOr,by omega⟩
  have use (op : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
      (u : Fin n) (hu : u ≠ v) : ¬(gateAt C j).inputs.Perm [v.val,u.val] := by
    intro pins
    have mem : gateAt C j ∈ R v := by
      exact List.mem_filter.mpr ⟨by rw [atGate j hj]; exact List.getElem_mem hj, reads⟩
    obtain ⟨na,no⟩ := raw (gateAt C j) mem u hu pins
    exact op.elim na no
  have gain (z : Fin n → Bool) (different :
      f (Function.update z v false) ≠ f (Function.update z v true)) :
      (C.wires (List.ofFn (Function.update z v false))).getD (n+j) false ≠
        (C.wires (List.ofFn (Function.update z v true))).getD (n+j) false := by
    intro same
    apply different
    have h := factor n C v j minimal.1 out unique _ _
      (fun u hu => by rw [Function.update_of_ne hu,Function.update_of_ne hu]) same
    simpa only [eval] using h
  have op : (gateAt C j).op = .and ∨ (gateAt C j).op = .or ∨ (gateAt C j).op = .not := by
    have h := (minimal.1 (gateAt C j) (by rw [atGate j hj]; exact List.getElem_mem hj)).1
    simpa using h
  rcases op with h | h | h
  · exact meet n G A C v j deg girth isolated minimal eval sparse hv hj reads h unique
      (later (by intro e; rw [h] at e; cases e)) (use (Or.inl h)) gain
  · exact join n G A C v j deg girth isolated minimal eval sparse hv hj reads h unique
      (use (Or.inr h)) gain
  · exact invert n G A C v j deg girth isolated minimal eval sparse hv hj reads h unique
      (later (by intro e; rw [h] at e; cases e))
