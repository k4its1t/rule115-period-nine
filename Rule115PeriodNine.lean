import Std

namespace Rule115

abbrev Row := Int → Bool
abbrev State := Row × Row

/-- Wolfram's elementary rule 115, with arguments ordered left, centre, right. -/
def localRule (left centre right : Bool) : Bool :=
  (!centre) || (left && !right)

/-- The first row is the previous time slice, and the second is the current one. -/
def step (s : State) : State :=
  (s.2, fun x => s.1 x ^^ localRule (s.2 (x - 1)) (s.2 x) (s.2 (x + 1)))

def evolve (s : State) : Nat → State
  | 0 => s
  | t + 1 => step (evolve s t)

/-- Both rows vanish outside a bounded interval of the integer lattice. -/
def FiniteInitial (s : State) : Prop :=
  ∃ left right : Int, ∀ x, x < left ∨ right < x → s.1 x = false ∧ s.2 x = false

def ExactPeriod (s : State) (p : Nat) : Prop :=
  0 < p ∧ evolve s p = s ∧ ∀ q, 0 < q → q < p → evolve s q ≠ s

private def blank : State := (fun _ => false, fun _ => false)

private theorem evolve_add (s : State) (a b : Nat) :
    evolve s (a + b) = evolve (evolve s a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg step ih

private theorem agreesOutside {s : State} {left right : Int}
    (h : ∀ x, x < left ∨ right < x → s.1 x = false ∧ s.2 x = false)
    (t : Nat) (x : Int) (hx : x < left - (t : Int) ∨ right + (t : Int) < x) :
    (evolve s t).1 x = (evolve blank t).1 x ∧
      (evolve s t).2 x = (evolve blank t).2 x := by
  induction t generalizing x with
  | zero => simpa [evolve, blank] using h x (by omega)
  | succ t ih =>
    have hl := ih (x - 1) (by omega)
    have hm := ih x (by omega)
    have hr := ih (x + 1) (by omega)
    exact ⟨hm.2, by simp only [evolve, step, hl.2, hm.1, hm.2, hr.2]⟩

/- The bit of index t in a column is the current row at time t, for 0 ≤ t < 9. -/
private abbrev Column := BitVec 9
private abbrev Pair := Column × Column

private def pack (bits : Fin 9 → Bool) : Column :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)

private theorem get_pack (bits : Fin 9 → Bool) (t : Nat) (ht : t < 9) :
    (pack bits).getLsbD t = bits ⟨t, ht⟩ := by
  rw [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ht]

private def column (s : State) (x : Int) : Column :=
  pack (fun t => (evolve s t.val).2 x)

private theorem column_bit (s : State) (x : Int) (t : Nat) (ht : t < 9) :
    (column s x).getLsbD t = (evolve s t).2 x :=
  get_pack _ t ht

private def background : Column := 146
private def ones : Column := 511

private theorem blank_column (x : Int) : column blank x = background := by
  have h (t : Nat) : (evolve blank t).2 x = (evolve blank t).2 0 := by
    have uniform (t : Nat) (y : Int) :
        (evolve blank t).1 y = (evolve blank t).1 0 ∧
          (evolve blank t).2 y = (evolve blank t).2 0 := by
      induction t generalizing y with
      | zero => exact ⟨rfl, rfl⟩
      | succ t ih =>
        refine ⟨(ih y).2, ?_⟩
        simp only [evolve, step, (ih y).1, (ih (y - 1)).2, (ih y).2,
          (ih (y + 1)).2, (ih (0 - 1)).2, (ih (0 + 1)).2]
    exact (uniform t x).2
  calc
    column blank x = column blank 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro t ht
      rw [column_bit _ _ _ ht, column_bit _ _ _ ht]
      exact h t
    _ = background := by decide

private theorem columnOutside {s : State} {left right : Int}
    (h : ∀ x, x < left ∨ right < x → s.1 x = false ∧ s.2 x = false)
    (x : Int) (hx : x < left - 8 ∨ right + 8 < x) :
    column s x = background := by
  rw [← blank_column x]
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [column_bit _ _ _ ht, column_bit _ _ _ ht]
  exact (agreesOutside h t x (by omega)).2

private def timeDifference (c : Column) : Column :=
  c.rotateLeft 1 ^^^ c.rotateRight 1

/-- Simultaneously impose the local rule at all nine time indices. -/
private abbrev legal (left centre right : Column) : Prop :=
  timeDifference centre = (~~~centre ||| (left &&& ~~~right))

private theorem timeDifference_bit (c : Column) (t : Nat) (ht : t < 9) :
    (timeDifference c).getLsbD t =
      (c.getLsbD ((t + 8) % 9) ^^ c.getLsbD ((t + 1) % 9)) := by
  simp only [timeDifference, BitVec.getLsbD_xor, BitVec.getLsbD_rotateLeft,
    BitVec.getLsbD_rotateRight, show 1 % 9 = 1 from rfl, show 9 - 1 = 8 from rfl,
    show decide (t < 9) = true from decide_eq_true ht, Bool.true_and]
  by_cases hzero : t = 0
  · subst t
    rfl
  by_cases hlast : t = 8
  · subst t
    rfl
  simp [show ¬ t < 1 by omega, show t < 8 by omega,
    show (t + 8) % 9 = t - 1 by omega, show (t + 1) % 9 = 1 + t by omega]

private theorem orbitPrevious {s : State} (h : evolve s 9 = s)
    (t : Nat) (ht : t < 9) (x : Int) :
    (evolve s ((t + 8) % 9)).2 x = (evolve s t).1 x := by
  cases t with
  | zero => exact congrArg (fun state : State => state.1 x) h
  | succ n =>
    rw [show (n + 1 + 8) % 9 = n by omega]
    rfl

private theorem orbitNext {s : State} (h : evolve s 9 = s)
    (t : Nat) (ht : t < 9) (x : Int) :
    (evolve s ((t + 1) % 9)).2 x = (evolve s (t + 1)).2 x := by
  by_cases last : t + 1 = 9
  · rw [last, show 9 % 9 = 0 from rfl, h]
    rfl
  · rw [Nat.mod_eq_of_lt (show t + 1 < 9 by omega)]

private theorem orbitLegal {s : State} (h : evolve s 9 = s) (x : Int) :
    legal (column s (x - 1)) (column s x) (column s (x + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [timeDifference_bit _ _ ht]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    show decide (t < 9) = true from decide_eq_true ht, Bool.true_and,
    column_bit _ _ _ ht,
    column_bit _ _ _ (Nat.mod_lt (t + 8) (by decide : 0 < 9)),
    column_bit _ _ _ (Nat.mod_lt (t + 1) (by decide : 0 < 9)),
    orbitPrevious h t ht, orbitNext h t ht]
  change ((evolve s t).1 x ^^ ((evolve s t).1 x ^^
    localRule ((evolve s t).2 (x - 1)) ((evolve s t).2 x) ((evolve s t).2 (x + 1)))) =
      localRule ((evolve s t).2 (x - 1)) ((evolve s t).2 x) ((evolve s t).2 (x + 1))
  cases (evolve s t).1 x <;>
    cases localRule ((evolve s t).2 (x - 1)) ((evolve s t).2 x) ((evolve s t).2 (x + 1)) <;> rfl

private def admissible (c : Column) : Bool :=
  (((~~~c) &&& ~~~(timeDifference c)) == 0#9)

private theorem admissible_of_legal {l c r : Column} (h : legal l c r) :
    admissible c = true := by
  unfold admissible
  rw [h, beq_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    show decide (t < 9) = true from decide_eq_true ht, Bool.true_and, BitVec.getLsbD_zero]
  cases c.getLsbD t <;> rfl

private def candidates : List Column :=
  ((List.range 512).map (BitVec.ofNat 9)).filter admissible

private theorem memCandidates {c : Column} (hc : admissible c = true) : c ∈ candidates := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨c.toNat, List.mem_range.mpr c.isLt, ?_⟩, hc⟩
  simp

/-- A list of 40 spatial pairs containing the forward reachability set. -/
private def forward : List Pair :=
  [(79, 230), (121, 307), (146, 146), (146, 158), (146, 242), (146, 254),
   (146, 403), (146, 415), (146, 499), (146, 511), (158, 457), (158, 460),
   (158, 484), (242, 79), (242, 103), (242, 295), (254, 121), (254, 313),
   (254, 316), (295, 115), (316, 409), (403, 121), (403, 313), (403, 316),
   (415, 79), (415, 103), (415, 295), (457, 412), (484, 206), (499, 457),
   (499, 460), (499, 484), (511, 146), (511, 158), (511, 242), (511, 254),
   (511, 403), (511, 415), (511, 499), (511, 511)]

private def core : List Pair :=
  [(background, background), (background, ones), (ones, background)]

/-- The forward set is closed. Within it, a successor in the core has a predecessor in the core. -/
private def checkCertificate : Bool :=
  forward.all fun (l, c) => candidates.all fun r =>
    if legal l c r then
      decide ((c, r) ∈ forward ∧ ((c, r) ∈ core → (l, c) ∈ core))
    else true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem certificateChecked : checkCertificate = true := by decide

set_option maxRecDepth 10000 in
private theorem certificateSizes : candidates.length = 31 ∧ forward.length = 40 ∧
    core.length = 3 := by decide

private theorem transition {l c r : Column} (hl : (l, c) ∈ forward)
    (hr : r ∈ candidates) (h : legal l c r) :
    (c, r) ∈ forward ∧ ((c, r) ∈ core → (l, c) ∈ core) := by
  have hCheck := certificateChecked
  unfold checkCertificate at hCheck
  have hOuter := List.all_eq_true.mp hCheck (l, c) hl
  have hInner := List.all_eq_true.mp hOuter r hr
  simp only [ite_eq_left h, decide_eq_true_eq] at hInner
  exact hInner

private theorem background_in_forward : (background, background) ∈ forward := by decide
private theorem background_in_core : (background, background) ∈ core := by decide

/-- Forward-closed sets containing the left background contain every spatial pair. -/
private theorem propagateFromLeft {P : Int → Prop} {left : Int}
    (base : ∀ x, x < left → P x) (next : ∀ x, P x → P (x + 1)) (x : Int) : P x := by
  have advance (y : Int) (n : Nat) (hy : P y) : P (y + (n : Int)) := by
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      have eqIndex : y + (n.succ : Int) = (y + (n : Int)) + 1 := by omega
      rw [eqIndex]
      exact next (y + (n : Int)) ih
  let y := min x (left - 1)
  have hyx : y ≤ x := Int.min_le_left _ _
  have hy : y < left := calc
    y ≤ left - 1 := Int.min_le_right _ _
    _ < left := by omega
  have eqIndex : y + ((x - y).toNat : Int) = x := by omega
  exact eqIndex ▸ advance y (x - y).toNat (base y hy)

/-- Backward-closed sets containing the right background contain every spatial pair. -/
private theorem propagateFromRight {P : Int → Prop} {right : Int}
    (base : ∀ x, right < x → P x) (prev : ∀ x, P (x + 1) → P x) (x : Int) : P x := by
  have advance (y : Int) (n : Nat) (hy : P y) : P (y - (n : Int)) := by
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      apply prev
      have eqIndex : (y - (n.succ : Int)) + 1 = y - (n : Int) := by omega
      rw [eqIndex]
      exact ih
  let y := max x (right + 1)
  have hxy : x ≤ y := Int.le_max_left _ _
  have hy : right < y := calc
    right < right + 1 := by omega
    _ ≤ y := Int.le_max_right _ _
  have eqIndex : y - ((y - x).toNat : Int) = x := by omega
  exact eqIndex ▸ advance y (y - x).toNat (base y hy)

private theorem orbitPairInCore {s : State} (hs : FiniteInitial s) (h : evolve s 9 = s)
    (x : Int) : (column s x, column s (x + 1)) ∈ core := by
  obtain ⟨left, right, hSupport⟩ := hs
  have allCandidates (i : Int) : column s i ∈ candidates :=
    memCandidates (admissible_of_legal (orbitLegal h i))
  have allLegal (i : Int) : legal (column s i) (column s (i + 1)) (column s (i + 2)) := by
    simpa only [show i + 1 - 1 = i by omega, show i + 1 + 1 = i + 2 by omega]
      using orbitLegal h (i + 1)
  have allForward (i : Int) : (column s i, column s (i + 1)) ∈ forward := by
    apply propagateFromLeft (left := left - 9) _ _ i
    · intro j hj
      rw [columnOutside hSupport j (by omega), columnOutside hSupport (j + 1) (by omega)]
      exact background_in_forward
    · intro j hj
      simpa only [show j + 1 + 1 = j + 2 by omega]
        using (transition hj (allCandidates (j + 2)) (allLegal j)).1
  apply propagateFromRight (right := right + 8) _ _ x
  · intro j hj
    rw [columnOutside hSupport j (by omega), columnOutside hSupport (j + 1) (by omega)]
    exact background_in_core
  · intro j hj
    apply (transition (allForward j) (allCandidates (j + 2)) (allLegal j)).2
    simpa only [show j + 1 + 1 = j + 2 by omega] using hj

/-- An isolated row has no pair of adjacent ones. -/
def Isolated (r : Row) : Prop := ∀ x, (r x && r (x + 1)) = false

private theorem initialPattern {s : State} (hs : FiniteInitial s) (h : evolve s 9 = s) :
    s.1 = s.2 ∧ Isolated s.2 := by
  have coreBits : ∀ pair ∈ core, pair.1.getLsbD 8 = pair.1.getLsbD 0 ∧
      (pair.1.getLsbD 0 && pair.2.getLsbD 0) = false := by decide
  constructor
  · funext x
    have hPrior : (evolve s 8).2 x = s.1 x :=
      congrArg (fun state : State => state.1 x) h
    change s.1 x = (evolve s 0).2 x
    rw [← hPrior, ← column_bit s x 8 (by decide), ← column_bit s x 0 (by decide)]
    exact (coreBits _ (orbitPairInCore hs h x)).1
  · intro x
    change ((evolve s 0).2 x && (evolve s 0).2 (x + 1)) = false
    rw [← column_bit s x 0 (by decide), ← column_bit s (x + 1) 0 (by decide)]
    exact (coreBits _ (orbitPairInCore hs h x)).2

private def allOnesRow : Row := fun _ => true

private theorem isolatedRule {r : Row} (hr : Isolated r) (x : Int) :
    localRule (r (x - 1)) (r x) (r (x + 1)) = !(r x) := by
  have hleft := hr (x - 1)
  rw [show x - 1 + 1 = x by omega] at hleft
  cases h : r x
  · simp [localRule]
  · have hl : r (x - 1) = false := by simpa [h] using hleft
    simp [hl, localRule]

private theorem isolatedPairReturns {r : Row} (hr : Isolated r) :
    evolve (r, r) 3 = (r, r) := by
  have first : step (r, r) = (r, allOnesRow) := by
    refine Prod.ext rfl ?_
    funext x
    change (r x ^^ localRule (r (x - 1)) (r x) (r (x + 1))) = true
    rw [isolatedRule hr x]
    cases r x <;> rfl
  have second : step (r, allOnesRow) = (allOnesRow, r) := by
    refine Prod.ext rfl ?_
    funext x
    change (r x ^^ false) = r x
    cases r x <;> rfl
  have third : step (allOnesRow, r) = (r, r) := by
    refine Prod.ext rfl ?_
    funext x
    change (true ^^ localRule (r (x - 1)) (r x) (r (x + 1))) = r x
    rw [isolatedRule hr x]
    cases r x <;> rfl
  change step (step (step (r, r))) = (r, r)
  rw [first, second, third]

private theorem patternReturns {s : State} (h : s.1 = s.2 ∧ Isolated s.2) :
    evolve s 3 = s := by
  have hs : s = (s.2, s.2) := Prod.ext h.1 rfl
  calc
    evolve s 3 = evolve (s.2, s.2) 3 := congrArg (fun state => evolve state 3) hs
    _ = (s.2, s.2) := isolatedPairReturns h.2
    _ = s := hs.symm

/-- Every finite-support orbit returning after nine steps already returns after three. -/
theorem return_after_nine_implies_three {s : State} (hs : FiniteInitial s)
    (h : evolve s 9 = s) : evolve s 3 = s :=
  patternReturns (initialPattern hs h)

/-- A finite initial state returns after nine steps exactly when its two rows agree
and their common row has no adjacent ones. -/
theorem return_after_nine_iff_equal_isolated_rows {s : State} (hs : FiniteInitial s) :
    evolve s 9 = s ↔ s.1 = s.2 ∧ Isolated s.2 := by
  refine ⟨initialPattern hs, ?_⟩
  intro h
  have h3 := patternReturns h
  have h6 : evolve s 6 = s := by simpa only [h3] using evolve_add s 3 3
  simpa only [h6, h3] using evolve_add s 6 3

/-- The affirmative answer to Formenti and Kamylia's Question 1 is false at p = 9. -/
theorem no_finite_exact_period_nine : ¬ ∃ s, FiniteInitial s ∧ ExactPeriod s 9 := by
  rintro ⟨s, hs, _, h, hmin⟩
  exact hmin 3 (by decide) (by decide) (return_after_nine_implies_three hs h)

end Rule115

#print axioms Rule115.return_after_nine_iff_equal_isolated_rows
#print axioms Rule115.return_after_nine_implies_three
#print axioms Rule115.no_finite_exact_period_nine
