import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The shared union program is the representation used in R-meta-2866-714.
-- The second hypothesis counts its gates without using circuit semantics.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4618_58
  (compile : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
    300 ≤ q → n = q ^ 2 + q + 1 →
    (∀ l, (S l).card = q + 1) →
    (∀ a b : Fin n, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
    IsAO2 (n + n) C → C.output < n + n + C.size →
    (∀ g ∈ C.gates, g.inputs.Pairwise (· < ·)) →
    RightOnIncidentPairs S C →
    (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
    (n ≤ ∑ j : Fin C.size, ((C.gates.foldl
      (fun (w : List ℕ) g => w ++ [(if w.length = n + n + j.val then 1 else 0) +
        (g.inputs.map (fun i => w.getD i 0)).sum])
      (List.replicate (n + n) 0)).getD C.output 0 - 100)) →
    ∃ xs : List (Finset (Fin n)), xs.length ≤ 100 * C.size ∧ (∀ l, S l ∈ xs) ∧
      ∀ j T, xs[j]? = some T → ∃ A B : Finset (Fin n), T = A ∪ B ∧
        (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j))
  (count : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (xs : List (Finset (Fin n))),
    (∀ l, (S l).card = q + 1) →
    (∀ a b : Fin n, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
    (∀ l, S l ∈ xs) →
    (∀ j T, xs[j]? = some T → ∃ A B : Finset (Fin n), T = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)) →
    n * q ≤ xs.length) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             x5.output < x2 + x2 + x5.size →               (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →                 (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →                   (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →                     have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);                     x2 ≤ ∑ x16 : Fin x5.size, (x15 x16 - (100 : ℕ)) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I dec C hq order degree unique mono output pins positive negative mult heavy
  let S (l : Fin n) : Finset (Fin n) := Finset.univ.filter fun p => I p l
  have inc (p l : Fin n) : p ∈ S l ↔ I p l := by simp [S]
  have deg (l : Fin n) : (S l).card = q + 1 :=
    (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
  have pair (a b : Fin n) (ne : a ≠ b) : ∃! l, a ∈ S l ∧ b ∈ S l := by
    simpa only [inc] using unique a b ne
  have shapes (g : Gate) (hg : g ∈ C.gates) :
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a < b := by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    obtain ⟨a, b, pins, lt, _⟩ := pins i g (List.getElem?_eq_some_iff.mpr ⟨hi,e⟩)
    exact ⟨a,b,pins,lt⟩
  have sorted (g : Gate) (hg : g ∈ C.gates) : g.inputs.Pairwise (· < ·) := by
    obtain ⟨a,b,e,lt⟩ := shapes g hg
    simp [e, lt]
  have strict : IsAO2 (n + n) C := by
    refine ⟨fun g hg => (mono g hg).1, ?_, ?_⟩
    · intro k hk i hi
      have gate : gateAt C k = C.gates[k] := by
        change C.gates.getD k _ = _
        exact List.getD_eq_getElem _ _ hk
      obtain ⟨a, b, e, lt, back⟩ :=
        pins k C.gates[k] (List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩)
      rw [gate, e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact lt.trans back
      · exact back
    · intro g hg
      obtain ⟨a,b,e,_⟩ := shapes g hg
      simp [e]
  let input (X Y : Finset (Fin n)) : Fin (n + n) → Bool :=
    Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have eval (X Y : Finset (Fin n)) :
      C.eval (incidenceInput X Y) = circuitFun (n + n) C (input X Y) := by
    change C.eval (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin n => decide (l ∈ Y))) = C.eval (List.ofFn (input X Y))
    rw [show List.ofFn (input X Y) = _ from List.ofFn_fin_append _ _]
  have inputP (X Y : Finset (Fin n)) (p : Fin n) :
      input X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.append_left _ _ _
  have inputL (X Y : Finset (Fin n)) (l : Fin n) :
      input X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.append_right _ _ _
  have different (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro h
    have e := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at e
    omega
  have yes : RightOnIncidentPairs S C := by
    intro l p pl
    rw [eval]
    have e : input {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
      funext i
      refine Fin.addCases (fun r => ?_) (fun r => ?_) i
      · simp only [inputP, Finset.mem_singleton, Fin.castAdd_inj, different, or_false]
      · simp only [inputL, Finset.mem_singleton, Fin.natAdd_inj, Ne.symm (different p r), false_or]
    rw [e]
    exact positive p l ((inc p l).mp pl)
  have no (X Y : Finset (Fin n)) (few : Y.card ≤ q) (falseInput : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    rw [eval]
    apply negative
    · have e : Fintype.card {l : Fin n // input X Y (Fin.natAdd n l) = true} = Y.card := by
        simp only [inputL, decide_eq_true_eq, Fintype.card_coe]
      exact e.le.trans few
    · rintro ⟨p,l,ip,hp,hl⟩
      simp only [inputP, inputL, decide_eq_true_eq] at hp hl
      have apart := falseInput l hl
      exact (Finset.disjoint_left.mp apart) ((inc p l).mpr ip) hp
  obtain ⟨xs, cost, ends, valid⟩ :=
    compile q n S C hq order deg pair strict output sorted yes no heavy
  exact (count q n S xs deg pair ends valid).trans cost
