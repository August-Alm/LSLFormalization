import Formalization.Typed

/-!
# The runs of readback are clear

`firstRunClear`: in the first run of the pointer machine on a locally safe term, no exit to
a lambda lies under the tape when the token leaves for that lambda or comes back to it. With
`firstRunLifo_of_clear` this gives `firstRunLifo`: the returns to each lambda come in
last-in-first-out order. `readbackLifo` is the same for every run of readback (`Point`).

The invariant `Inv` says three things about a state.

* The tape fits the type at the token (`Fits`), so the orders of the exits on the tape
  itself are below the order of that type.
* The exits are `Good`: the entries saved under an exit have the types of the arguments
  around its variable. By local safety, the exits under the exit of a local variable are
  local and of no higher order (`below_tree`).
* The exit of a global variable is on the tape itself only at its top, while the token is
  on the spine, on its way between the lambda of that variable and the argument matched
  with it (`Transit`, `seek`).
-/

namespace LSL

/-! ## The lambda matched with an application on the spine -/

/-- The lambda at which a token that goes down into the term pops what lies below `j` `q`s,
as an address in the term. -/
def seekIn : Term → Nat → Option Addr
  | .var _ _, _ => none
  | .lam _ _, 0 => some []
  | .lam _ b, j + 1 => (seekIn b j).map (· ++ [.body])
  | .app f _, j => (seekIn f (j + 1)).map (· ++ [.fn])

def seek (t : Term) (a : Addr) (j : Nat) : Option Addr :=
  (t.sub a).bind fun s => (seekIn s j).map (· ++ a)

theorem seek_var {t : Term} {a : Addr} {i : Nat} {π : Path} (h : t.sub a = some (.var i π))
    (j : Nat) : seek t a j = none := by
  simp [seek, h, seekIn]

theorem seek_lam_zero {t : Term} {a : Addr} {A : Ty} {b : Term}
    (h : t.sub a = some (.lam A b)) : seek t a 0 = some a := by
  simp [seek, h, seekIn]

theorem seek_lam_succ {t : Term} {a : Addr} {A : Ty} {b : Term}
    (h : t.sub a = some (.lam A b)) (j : Nat) : seek t a (j + 1) = seek t (.body :: a) j := by
  cases hs : seekIn b j <;> simp [seek, sub_cons, h, Term.child, seekIn, hs]

theorem seek_app {t : Term} {a : Addr} {f u : Term} (h : t.sub a = some (.app f u))
    (j : Nat) : seek t a j = seek t (.fn :: a) (j + 1) := by
  cases hs : seekIn f (j + 1) <;> simp [seek, sub_cons, h, Term.child, seekIn, hs]

/-- The application on the spine in whose argument the address lies. -/
def topApp : Addr → Addr
  | [] => []
  | _ :: a => if argDepth a = 0 then a else topApp a

theorem topApp_cons_pos {a : Addr} (h : 0 < argDepth a) (d : Dir) :
    topApp (d :: a) = topApp a := by
  simp [topApp, Nat.ne_of_gt h]

theorem topApp_arg_zero {a : Addr} (h : argDepth a = 0) : topApp (.arg :: a) = a := by
  simp [topApp, h]

theorem argDepth_append (e b : Addr) : argDepth (e ++ b) = argDepth e + argDepth b := by
  simp [argDepth]

theorem topApp_append {b : Addr} (h : 0 < argDepth b) : ∀ e : Addr, topApp (e ++ b) = topApp b
  | [] => rfl
  | d :: e => by
    have hp : 0 < argDepth (e ++ b) := by
      rw [argDepth_append]
      omega
    rw [List.cons_append, topApp_cons_pos hp, topApp_append h e]

theorem topApp_binder {o b : Addr} {i : Nat} (h : binder o i = .inr b) (hp : 0 < argDepth b) :
    topApp o = topApp b := by
  obtain ⟨e, rfl, _⟩ := binder_inr o i b h
  rw [topApp_append (by simpa using hp), topApp_cons_pos hp]

/-! ## Good exits -/

/-- The exit is not from a global variable: its lambda, if it has one, lies inside an
argument. -/
def IsLocal (t : Term) (e : Exit) : Prop :=
  ∀ β, binderOf t e.occ = some β → 0 < argDepth β

/-- An exit that is not from a variable of the term and has nothing saved under it. Readback
puts one on the tape for each argument of a head variable that it asks for. -/
def Dummy (t : Term) (e : Exit) : Prop :=
  binderOf t e.occ = none ∧ e.saved = []

theorem varTy_of_none {t : Term} {o : Addr} (h : binderOf t o = none) : varTy t o = none := by
  simp [varTy, h]

theorem Exit.tree_eq (e : Exit) : e.tree = e :: Exit.trees e.saved := by
  cases e with
  | mk o σ => simp [Exit.tree, Exit.saved]

/-- If `e` is the exit of a global variable, its lambda is the one matched with the
application at `α`. -/
def TopOK (t : Term) (α : Addr) (e : Exit) : Prop :=
  ∀ β, binderOf t e.occ = some β → argDepth β = 0 → seek t (.fn :: α) 0 = some β

/-- All entries of a log but the outermost are exits of local variables, and the outermost
one fits the application on the spine. -/
def LogOK (t : Term) (α : Addr) (L : List Exit) : Prop :=
  ∀ k e, L[k]? = some e → (k + 1 < L.length → IsLocal t e) ∧ (k + 1 = L.length → TopOK t α e)

theorem logOK_nil {t : Term} {α : Addr} : LogOK t α [] := by
  intro k e hk
  simp at hk

theorem logOK_drop {t : Term} {α : Addr} {L : List Exit} (n : Nat) (h : LogOK t α L) :
    LogOK t α (L.drop n) := by
  intro k e hk
  rw [List.getElem?_drop] at hk
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨h1, h2⟩ := h (n + k) e hk
  exact ⟨fun hh => h1 (by simp only [List.length_drop] at hh; omega),
    fun hh => h2 (by simp only [List.length_drop] at hh; omega)⟩

theorem logOK_take_local {t : Term} {α : Addr} {L : List Exit} {n : Nat} (h : LogOK t α L)
    (hn : n < L.length) : ∀ e ∈ L.take n, IsLocal t e := by
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  rw [List.getElem?_take] at hk
  split at hk
  · exact (h k e hk).1 (by omega)
  · cases hk

theorem logOK_single {t : Term} {α : Addr} {e : Exit} (h : TopOK t α e) : LogOK t α [e] := by
  intro k e' hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact ⟨fun hh => by simp at hh, fun _ => h⟩
  | succ k => simp at hk

theorem logOK_cons {t : Term} {α : Addr} {e : Exit} {L : List Exit} (he : IsLocal t e)
    (h : LogOK t α L) (hL : L ≠ []) : LogOK t α (e :: L) := by
  intro k e' hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    refine ⟨fun _ => he, fun hh => ?_⟩
    simp only [List.length_cons] at hh
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hL
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    obtain ⟨h1, h2⟩ := h k e' hk
    exact ⟨fun hh => h1 (by simp only [List.length_cons] at hh; omega),
      fun hh => h2 (by simp only [List.length_cons] at hh; omega)⟩

theorem logOK_append {t : Term} {α : Addr} {σ L : List Exit} (hσ : ∀ e ∈ σ, IsLocal t e)
    (h : LogOK t α L) (hL : L ≠ []) : LogOK t α (σ ++ L) := by
  have hpos : 0 < L.length := List.length_pos_iff.mpr hL
  intro k e hk
  by_cases hlt : k < σ.length
  · rw [List.getElem?_append_left hlt] at hk
    exact ⟨fun _ => hσ e (List.mem_of_getElem? hk),
      fun hh => by simp only [List.length_append] at hh; omega⟩
  · rw [List.getElem?_append_right (by omega)] at hk
    obtain ⟨h1, h2⟩ := h (k - σ.length) e hk
    exact ⟨fun hh => h1 (by simp only [List.length_append] at hh; omega),
      fun hh => h2 (by simp only [List.length_append] at hh; omega)⟩

theorem logOK_cons_addr {t : Term} {a : Addr} {L : List Exit} (d : Dir)
    (hlen : L.length = argDepth a) (h : LogOK t (topApp a) L) : LogOK t (topApp (d :: a)) L := by
  rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
  · rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0)]
    exact logOK_nil
  · rw [topApp_cons_pos hp]
    exact h

theorem logOK_addr_cons {t : Term} {a : Addr} {L : List Exit} (d : Dir)
    (hlen : L.length = argDepth a) (h : LogOK t (topApp (d :: a)) L) : LogOK t (topApp a) L := by
  rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
  · rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0)]
    exact logOK_nil
  · rw [topApp_cons_pos hp] at h
    exact h

mutual
/-- The exit is from a variable of the term, and the entries saved under it are those of a
log at that variable, up to its lambda. -/
def Good (t : Term) : Exit → Prop
  | .mk o σ => ∃ Δ m Γ i π A b, At t o Δ m Γ (.var i π) A ∧ binder o i = .inr b ∧
      Entries t (Δ.take (argDepth o - argDepth b)) σ ∧
      (0 < argDepth b → ∀ e ∈ σ, IsLocal t e) ∧ (argDepth b = 0 → LogOK t (topApp o) σ)
/-- The entries are dummies or good exits from variables of the given types. -/
def Entries (t : Term) : List Ty → List Exit → Prop
  | [], [] => True
  | D :: Ds, e :: es => (Dummy t e ∨ (varTy t e.occ = some D ∧ Good t e)) ∧ Entries t Ds es
  | _, _ => False
end

theorem good_iff (t : Term) (e : Exit) : Good t e ↔
    ∃ Δ m Γ i π A b, At t e.occ Δ m Γ (.var i π) A ∧ binder e.occ i = .inr b ∧
      Entries t (Δ.take (argDepth e.occ - argDepth b)) e.saved ∧
      (0 < argDepth b → ∀ e' ∈ e.saved, IsLocal t e') ∧
      (argDepth b = 0 → LogOK t (topApp e.occ) e.saved) := by
  cases e with
  | mk o σ => simp only [Good, Exit.occ, Exit.saved]

theorem Good.typed {t : Term} {e : Exit} (h : Good t e) :
    ∃ C β, varTy t e.occ = some C ∧ binderOf t e.occ = some β := by
  rw [good_iff] at h
  obtain ⟨Δ, m, Γ, i, π, A, b, hat, _⟩ := h
  obtain ⟨b', _, _, _, _, _, _, hbo, hvt, _⟩ := hat.var
  exact ⟨A, b', hvt, hbo⟩

theorem entries_nil (t : Term) : Entries t [] [] := by simp [Entries]

theorem entries_cons {t : Term} {D : Ty} {Ds : List Ty} {e : Exit} {es : List Exit} :
    Entries t (D :: Ds) (e :: es) ↔
      (Dummy t e ∨ (varTy t e.occ = some D ∧ Good t e)) ∧ Entries t Ds es := by
  simp [Entries]

namespace Entries

variable {t : Term}

theorem length : ∀ {Ds : List Ty} {es : List Exit}, Entries t Ds es → Ds.length = es.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Entries] at h
  | _ :: _, [], h => by simp [Entries] at h
  | D :: Ds, e :: es, h => by
    rw [entries_cons] at h
    simp [length h.2]

theorem get : ∀ {Ds : List Ty} {es : List Exit}, Entries t Ds es → ∀ (k : Nat) (e : Exit),
    es[k]? = some e →
      ∃ D, Ds[k]? = some D ∧ (Dummy t e ∨ (varTy t e.occ = some D ∧ Good t e))
  | [], [], _, k, e, hk => by simp at hk
  | [], _ :: _, h, _, _, _ => by simp [Entries] at h
  | _ :: _, [], h, _, _, _ => by simp [Entries] at h
  | D :: Ds, x :: es, h, k, e, hk => by
    rw [entries_cons] at h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨D, rfl, h.1⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact get h.2 k e hk

theorem take : ∀ (n : Nat) {Ds : List Ty} {es : List Exit}, Entries t Ds es →
    Entries t (Ds.take n) (es.take n)
  | 0, _, _, _ => by simp [Entries]
  | _ + 1, [], [], _ => by simp [Entries]
  | _ + 1, [], _ :: _, h => by simp [Entries] at h
  | _ + 1, _ :: _, [], h => by simp [Entries] at h
  | n + 1, D :: Ds, e :: es, h => by
    rw [entries_cons] at h
    simp only [List.take_succ_cons, entries_cons]
    exact ⟨h.1, take n h.2⟩

theorem drop : ∀ (n : Nat) {Ds : List Ty} {es : List Exit}, Entries t Ds es →
    Entries t (Ds.drop n) (es.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], _ => by simp [Entries]
  | _ + 1, [], _ :: _, h => by simp [Entries] at h
  | _ + 1, _ :: _, [], h => by simp [Entries] at h
  | n + 1, D :: Ds, e :: es, h => by
    rw [entries_cons] at h
    simp only [List.drop_succ_cons]
    exact drop n h.2

theorem append : ∀ {Ds : List Ty} {es : List Exit} {Ds' : List Ty} {es' : List Exit},
    Entries t Ds es → Entries t Ds' es' → Entries t (Ds ++ Ds') (es ++ es')
  | [], [], _, _, _, h' => by simpa using h'
  | [], _ :: _, _, _, h, _ => by simp [Entries] at h
  | _ :: _, [], _, _, h, _ => by simp [Entries] at h
  | D :: Ds, e :: es, _, _, h, h' => by
    rw [entries_cons] at h
    simp only [List.cons_append, entries_cons]
    exact ⟨h.1, append h.2 h'⟩

end Entries

/-! ## The order of the exits under a local exit -/

/-- The exit is from a variable of order at most `n`. -/
def Below (t : Term) (n : Nat) (e : Exit) : Prop :=
  ∀ C, varTy t e.occ = some C → C.order ≤ n

mutual
/-- Under the exit of a local variable, no exit is from a variable of higher order. -/
theorem below_tree (t : Term) (n : Nat) : ∀ e : Exit, Good t e → IsLocal t e → Below t n e →
    ∀ e' ∈ e.tree, Below t n e'
  | .mk o σ, hg, hl, hb, e', he' => by
    rw [good_iff] at hg
    obtain ⟨Δ, m, Γ, i, π, A, b, hat, hbi, hent, hloc, _⟩ := hg
    obtain ⟨b', _, _, _, _, _, hbi', hbo, hvt, _, _, _, hord⟩ := hat.var
    obtain rfl : b' = b := Sum.inr.inj (hbi'.symm.trans hbi)
    have hpos := hl _ hbo
    have hCn : A.order ≤ n := hb A hvt
    simp only [Exit.tree, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact hb
    · refine below_trees t n _ σ hent (fun e he => ⟨hloc hpos e he, ?_⟩) e' he'
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
      obtain ⟨D, hD, hDv⟩ := hent.get k e hk
      rw [List.getElem?_take] at hD
      split at hD
      · rename_i hkn
        intro C hC
        rcases hDv with hd | ⟨hDv, _⟩
        · rw [varTy_of_none hd.1] at hC
          cases hC
        · cases Option.some.inj (hC.symm.trans hDv)
          exact Nat.le_trans (hord hpos k _ hkn hD) hCn
      · cases hD
theorem below_trees (t : Term) (n : Nat) : ∀ (Ds : List Ty) (es : List Exit), Entries t Ds es →
    (∀ e ∈ es, IsLocal t e ∧ Below t n e) → ∀ e' ∈ Exit.trees es, Below t n e'
  | _, [], _, _, e', he' => by simp [Exit.trees_nil] at he'
  | [], _ :: _, h, _, _, _ => by simp [Entries] at h
  | D :: Ds, e :: es, h, hall, e', he' => by
    rw [entries_cons] at h
    simp only [Exit.trees, List.mem_append] at he'
    rcases he' with he' | he'
    · rcases h.1 with hd | ⟨_, hg⟩
      · rw [Exit.tree_eq, hd.2, Exit.trees_nil] at he'
        simp only [List.mem_singleton] at he'
        subst he'
        exact (hall _ (by simp)).2
      · exact below_tree t n e hg (hall e (by simp)).1 (hall e (by simp)).2 e' he'
    · exact below_trees t n Ds es h.2 (fun x hx => hall x (by simp [hx])) e' he'
end

theorem mem_trees {e' : Exit} : ∀ {es : List Exit}, e' ∈ Exit.trees es → ∃ e ∈ es, e' ∈ e.tree
  | [], h => by simp [Exit.trees_nil] at h
  | e :: es, h => by
    simp only [Exit.trees, List.mem_append] at h
    rcases h with h | h
    · exact ⟨e, by simp, h⟩
    · obtain ⟨x, hx, hx'⟩ := mem_trees h
      exact ⟨x, by simp [hx], hx'⟩

/-! ## The tape fits the type -/

inductive Fits (t : Term) : Ty → List Item → Prop
  | qs {A : Ty} (n : Nat) : Fits t A (List.replicate n .q)
  | q {A B : Ty} {T : List Item} : Fits t B T → Fits t (.arr A B) (.q :: T)
  | p {A B : Ty} {e : Exit} {T : List Item} :
      (∀ C, varTy t e.occ = some C → C = A) → Fits t A T → Fits t (.arr A B) (.p e :: T)

theorem tapeExits_replicate_append (j : Nat) (R : List Item) :
    tapeExits (List.replicate j Item.q ++ R) = tapeExits R := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ, tapeExits] using ih

theorem tapeExits_replicate (n : Nat) : tapeExits (List.replicate n Item.q) = [] := by
  simpa [tapeExits] using tapeExits_replicate_append n []

namespace Fits

variable {t : Term}

theorem pop_q {A B : Ty} {T : List Item} (h : Fits t (.arr A B) (.q :: T)) : Fits t B T := by
  generalize hC : Ty.arr A B = C at h
  generalize hT : Item.q :: T = T' at h
  cases h with
  | qs n =>
    cases n with
    | zero => simp at hT
    | succ n =>
      rw [List.replicate_succ] at hT
      cases hT
      exact .qs n
  | q h' =>
    cases hC
    cases hT
    exact h'
  | p _ _ => cases hT

theorem pop_p {A B : Ty} {e : Exit} {T : List Item} (h : Fits t (.arr A B) (.p e :: T)) :
    (∀ C, varTy t e.occ = some C → C = A) ∧ Fits t A T := by
  generalize hC : Ty.arr A B = C at h
  generalize hT : Item.p e :: T = T' at h
  cases h with
  | qs n =>
    cases n with
    | zero => simp at hT
    | succ n =>
      rw [List.replicate_succ] at hT
      cases hT
  | q _ => cases hT
  | p hv h' =>
    cases hC
    cases hT
    exact ⟨hv, h'⟩

/-- The exits on the tape itself are from variables of lower order than the type. -/
theorem order {A : Ty} {T : List Item} (h : Fits t A T) :
    ∀ e ∈ tapeExits T, ∀ C, varTy t e.occ = some C → C.order < A.order := by
  induction h with
  | qs n =>
    intro e he
    simp [tapeExits_replicate] at he
  | @q A B T _ ih =>
    intro e he C hC
    have := ih e he C hC
    simp only [Ty.order]
    omega
  | @p A B e₀ T hv _ ih =>
    intro e he C hC
    simp only [tapeExits, List.mem_append, List.mem_singleton] at he
    simp only [Ty.order]
    rcases he with he | rfl
    · have := ih e he C hC
      omega
    · cases hv C hC
      omega

end Fits

/-- Under a tape that fits `A` and has only local exits on it, no exit is to a lambda whose
variable has type `A`. -/
theorem free_of_fits {t : Term} {A : Ty} {T : List Item} {b : Addr} (hfit : Fits t A T)
    (hgood : ∀ e ∈ tapeExits T, Dummy t e ∨ Good t e) (hloc : ∀ e ∈ tapeExits T, IsLocal t e)
    (hb : ∀ o, binderOf t o = some b → varTy t o = some A) : Free t b T := by
  intro e' he' hbe'
  obtain ⟨e, he, hin⟩ := mem_trees he'
  rcases hgood e he with hd | hg
  · rw [Exit.tree_eq, hd.2, Exit.trees_nil] at hin
    simp only [List.mem_singleton] at hin
    subst hin
    rw [hd.1] at hbe'
    cases hbe'
  · obtain ⟨C, _, hC, _⟩ := hg.typed
    have hle := below_tree t C.order e hg (hloc e he)
      (fun C' hC' => by rw [hC] at hC'; cases hC'; exact Nat.le_refl _) e' hin A (hb _ hbe')
    have hlt := hfit.order e he C hC
    omega

/-! ## Exits of global variables on the tape -/

/-- The tape of a token on the spine: only its topmost exit may be from a global variable,
and then the token is on its way to or from the lambda of that variable. -/
def Transit (t : Term) (a : Addr) (T : List Item) : Prop :=
  ∃ j R, T = List.replicate j Item.q ++ R ∧
    (R = [] ∨ ∃ e T', R = .p e :: T' ∧ (∀ e' ∈ tapeExits T', IsLocal t e') ∧
      ∀ β, binderOf t e.occ = some β → argDepth β = 0 → seek t a j = some β)

namespace Transit

variable {t : Term} {a a' : Addr} {T : List Item}

theorem push (h : Transit t a T) (hs : ∀ j, seek t a' (j + 1) = seek t a j) :
    Transit t a' (.q :: T) := by
  obtain ⟨j, R, rfl, hR⟩ := h
  refine ⟨j + 1, R, by simp [List.replicate_succ], ?_⟩
  rcases hR with hR | ⟨e, T', hR, hl, hk⟩
  · exact .inl hR
  · exact .inr ⟨e, T', hR, hl, fun β h1 h2 => by rw [hs]; exact hk β h1 h2⟩

theorem pop (h : Transit t a (.q :: T)) (hs : ∀ j, seek t a' j = seek t a (j + 1)) :
    Transit t a' T := by
  obtain ⟨j, R, hT, hR⟩ := h
  cases j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hT
    rcases hR with hR | ⟨e, T', hR, _, _⟩
    · rw [hR] at hT
      cases hT
    · rw [hR] at hT
      cases hT
  | succ j =>
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at hT
    subst hT
    refine ⟨j, R, rfl, ?_⟩
    rcases hR with hR | ⟨e, T', hR, hl, hk⟩
    · exact .inl hR
    · exact .inr ⟨e, T', hR, hl, fun β h1 h2 => by rw [hs]; exact hk β h1 h2⟩

theorem top {e : Exit} (h : Transit t a (.p e :: T)) : (∀ e' ∈ tapeExits T, IsLocal t e') ∧
    ∀ β, binderOf t e.occ = some β → argDepth β = 0 → seek t a 0 = some β := by
  obtain ⟨j, R, hT, hR⟩ := h
  cases j with
  | succ j => simp [List.replicate_succ] at hT
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hT
    subst hT
    rcases hR with hR | ⟨e₂, T', hR, hl, hk⟩
    · cases hR
    · cases hR
      exact ⟨hl, hk⟩

theorem intro_p {e : Exit} (hl : ∀ e' ∈ tapeExits T, IsLocal t e')
    (hk : ∀ β, binderOf t e.occ = some β → argDepth β = 0 → seek t a 0 = some β) :
    Transit t a (.p e :: T) :=
  ⟨0, .p e :: T, rfl, .inr ⟨e, T, rfl, hl, hk⟩⟩

/-- At a variable on the spine, no exit on the tape is from a global variable. -/
theorem local_at_var (h : Transit t a T) (hv : ∀ j, seek t a j = none) :
    ∀ e ∈ tapeExits T, IsLocal t e := by
  obtain ⟨j, R, rfl, hR⟩ := h
  rw [tapeExits_replicate_append]
  rcases hR with rfl | ⟨e, T', rfl, hl, hk⟩
  · intro e he
    simp [tapeExits] at he
  · intro e' he'
    simp only [tapeExits, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hl e' he'
    · intro β hβ
      refine Nat.pos_of_ne_zero fun h0 => ?_
      have := hk β hβ h0
      rw [hv] at this
      cases this

end Transit

theorem tape_split : ∀ T : List Item, ∃ j R, T = List.replicate j Item.q ++ R ∧
    (R = [] ∨ ∃ e T', R = .p e :: T')
  | [] => ⟨0, [], rfl, .inl rfl⟩
  | .p e :: T => ⟨0, .p e :: T, rfl, .inr ⟨e, T, rfl⟩⟩
  | .q :: T => by
    obtain ⟨j, R, hT, hR⟩ := tape_split T
    exact ⟨j + 1, R, by rw [List.replicate_succ, List.cons_append, ← hT], hR⟩

theorem transit_of_local {t : Term} {a : Addr} {T : List Item}
    (h : ∀ e ∈ tapeExits T, IsLocal t e) : Transit t a T := by
  obtain ⟨j, R, rfl, hR⟩ := tape_split T
  rw [tapeExits_replicate_append] at h
  refine ⟨j, R, rfl, ?_⟩
  rcases hR with hR | ⟨e, T', rfl⟩
  · exact .inl hR
  · refine .inr ⟨e, T', rfl, fun e' he' => h e' (by simp [tapeExits, he']), fun β hβ h0 => ?_⟩
    have := h e (by simp [tapeExits]) β hβ
    omega

/-! ## The invariant -/

def Pos.addr : Pos → Addr
  | .down a => a
  | .up a => a

def InvOf (t : Term) (a : Addr) (tape : List Item) (log : List Exit) : Prop :=
  ∃ Δ m Γ u A, At t a Δ m Γ u A ∧ Fits t A tape ∧ Entries t Δ log ∧ LogOK t (topApp a) log ∧
    (∀ e ∈ tapeExits tape, Dummy t e ∨ Good t e) ∧
    (0 < argDepth a → ∀ e ∈ tapeExits tape, IsLocal t e) ∧
    (argDepth a = 0 → Transit t a tape)

def Inv (t : Term) (s : PState) : Prop := InvOf t s.pos.addr s.tape s.log

theorem inv_first {t : Term} {A : Ty} (h : LocallySafe t A) (n : Nat) : Inv t (.first n) := by
  show InvOf t [] (List.replicate n Item.q) []
  refine ⟨[], false, [], t, A, .root h, .qs n, entries_nil t, logOK_nil, ?_, ?_, ?_⟩
  · intro e he
    simp [tapeExits_replicate] at he
  · intro hp
    simp at hp
  · intro _
    exact ⟨n, [], by simp, .inl rfl⟩

theorem inv_step {t : Term} {s s' : PState} (hinv : Inv t s) (hs : pstep t s = .next s') :
    Inv t s' := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | down a =>
    change InvOf t a tape log at hinv
    obtain ⟨Δ, m, Γ, u, A, hat, hfit, hent, hlog, hgood, hloc, htr⟩ := hinv
    have hlen : log.length = argDepth a := by rw [← hent.length, hat.depth]
    have hsub := hat.sub
    cases u with
    | var i π =>
      obtain ⟨b, Δb, mb, Γb, body, B, hbi, hbo, hvt, hatb, hΔb, hle, _⟩ := hat.var
      simp only [pstep, hsub, hbi, PResult.next.injEq] at hs
      subst hs
      show InvOf t b (.p ⟨a, log.take (argDepth a - argDepth b)⟩ :: tape)
        (log.drop (argDepth a - argDepth b))
      have htl : ∀ e ∈ tapeExits tape, IsLocal t e := by
        rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
        · exact (htr h0).local_at_var fun j => seek_var hsub j
        · exact hloc hp
      have hE : Good t ⟨a, log.take (argDepth a - argDepth b)⟩ := by
        rw [good_iff]
        refine ⟨Δ, m, Γ, i, π, A, b, hat, hbi, hent.take _, fun hp => ?_, fun h0 => ?_⟩
        · exact logOK_take_local hlog (by omega)
        · show LogOK t (topApp a) (log.take (argDepth a - argDepth b))
          rw [List.take_of_length_le (by omega)]
          exact hlog
      refine ⟨Δb, mb, Γb, _, _, hatb, .p (fun C hC => Option.some.inj (hC.symm.trans hvt)) hfit,
        by rw [hΔb]; exact hent.drop _, ?_, ?_, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos (argDepth b) with h0 | hp
        · rw [List.drop_eq_nil_of_le (by omega)]
          exact logOK_nil
        · rw [← topApp_binder hbi hp]
          exact logOK_drop _ hlog
      · intro e he
        simp only [tapeExits, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hgood e he
        · exact .inr hE
      · intro hp e he
        simp only [tapeExits, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact htl e he
        · intro β hβ
          cases hbo.symm.trans hβ
          exact hp
      · intro _
        refine Transit.intro_p htl fun β hβ _ => ?_
        cases hbo.symm.trans hβ
        exact seek_lam_zero hatb.sub
    | lam A₁ body =>
      have hls := hat.ls
      cases hls with
      | lam hbody =>
        rename_i B
        cases tape with
        | nil => simp [pstep, hsub] at hs
        | cons x T =>
          cases x with
          | q =>
            simp only [pstep, hsub, PResult.next.injEq] at hs
            subst hs
            show InvOf t (.body :: a) T log
            refine ⟨Δ, m, _, body, B, .body hat, hfit.pop_q, hent, logOK_cons_addr .body hlen hlog,
              hgood, ?_, ?_⟩
            · intro hp
              exact hloc (by simpa using hp)
            · intro h0
              exact (htr (by simpa using h0)).pop fun j => (seek_lam_succ hsub j).symm
          | p e =>
            by_cases hbe : binderOf t e.occ = some a
            · cases hpop : popNewest t a hist with
              | none => simp [pstep, hsub, hbe, hpop] at hs
              | some r =>
                obtain ⟨o, H⟩ := r
                by_cases ho : o = e.occ
                · simp only [pstep, hsub, hbe, hpop, ho, ite_true, PResult.next.injEq] at hs
                  subst hs
                  show InvOf t e.occ T (e.saved ++ log)
                  obtain ⟨hvt, hfitT⟩ := hfit.pop_p
                  have hTloc : ∀ e' ∈ tapeExits T, IsLocal t e' := by
                    rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
                    · exact (htr h0).top.1
                    · exact fun e' he' => hloc hp e' (by simp [tapeExits, he'])
                  have hge : Good t e := by
                    rcases hgood e (by simp [tapeExits]) with hd | hg
                    · rw [hd.1] at hbe
                      cases hbe
                    · exact hg
                  rw [good_iff] at hge
                  obtain ⟨Δo, mo, Γo, i, π, Ao, b, hato, hbi, hento, hlocσ, hglobσ⟩ := hge
                  obtain ⟨c, Δb, mb, Γb, body', B', hbi', hbo, hvt', hatb, hΔb, _, _⟩ := hato.var
                  obtain rfl : c = b := Sum.inr.inj (hbi'.symm.trans hbi)
                  obtain rfl : c = a := Option.some.inj (hbo.symm.trans hbe)
                  obtain ⟨hΔ, _, _, _, _⟩ := hat.unique hatb
                  cases hvt _ hvt'
                  refine ⟨Δo, mo, Γo, _, _, hato, hfitT, ?_, ?_,
                    fun e' he' => hgood e' (by simp [tapeExits, he']), fun _ => hTloc,
                    fun _ => transit_of_local hTloc⟩
                  · have hent' : Entries t (Δo.drop (argDepth e.occ - argDepth c)) log := by
                      rw [← hΔb, ← hΔ]
                      exact hent
                    have := hento.append hent'
                    rwa [List.take_append_drop] at this
                  · rcases Nat.eq_zero_or_pos (argDepth c) with h0 | hp
                    · rw [List.eq_nil_of_length_eq_zero (by omega : log.length = 0),
                        List.append_nil]
                      exact hglobσ h0
                    · rw [topApp_binder hbi hp]
                      exact logOK_append (hlocσ hp) hlog fun h => by
                        rw [h] at hlen
                        simp at hlen
                        omega
                · simp [pstep, hsub, hbe, hpop, ho] at hs
            · simp [pstep, hsub, hbe] at hs
    | app f u₂ =>
      have hls := hat.ls
      cases hls with
      | app hf hu =>
        simp only [pstep, hsub, PResult.next.injEq] at hs
        subst hs
        show InvOf t (.fn :: a) (.q :: tape) log
        refine ⟨Δ, m, Γ, f, _, .fn hat hf, .q hfit, hent, logOK_cons_addr .fn hlen hlog, hgood,
          ?_, ?_⟩
        · intro hp
          exact hloc (by simpa using hp)
        · intro h0
          exact (htr (by simpa using h0)).push fun j => (seek_app hsub j).symm
  | up a =>
    change InvOf t a tape log at hinv
    obtain ⟨Δ, m, Γ, u, A, hat, hfit, hent, hlog, hgood, hloc, htr⟩ := hinv
    have hlen : log.length = argDepth a := by rw [← hent.length, hat.depth]
    cases hat with
    | root _ => simp [pstep] at hs
    | @body a Δ m Γ A₁ B s₁ h' =>
      simp only [pstep, PResult.next.injEq] at hs
      subst hs
      show InvOf t a (.q :: tape) log
      refine ⟨Δ, m, Γ, _, _, h', .q hfit, hent,
        logOK_addr_cons .body (by simpa using hlen) hlog, hgood, ?_, ?_⟩
      · intro hp
        exact hloc (by simpa using hp)
      · intro h0
        exact (htr (by simpa using h0)).push fun j => seek_lam_succ h'.sub j
    | @fn a Δ m Γ f u₂ A₁ B h' hf =>
      cases tape with
      | nil => simp [pstep] at hs
      | cons x T =>
        cases x with
        | q =>
          simp only [pstep, PResult.next.injEq] at hs
          subst hs
          show InvOf t a T log
          refine ⟨Δ, m, Γ, _, _, h', hfit.pop_q, hent,
            logOK_addr_cons .fn (by simpa using hlen) hlog, hgood, ?_, ?_⟩
          · intro hp
            exact hloc (by simpa using hp)
          · intro h0
            exact (htr (by simpa using h0)).pop fun j => seek_app h'.sub j
        | p e =>
          simp only [pstep, PResult.next.injEq] at hs
          subst hs
          show InvOf t (.arg :: a) T (e :: log)
          obtain ⟨hvt, hfitT⟩ := hfit.pop_p
          have hge : Dummy t e ∨ (varTy t e.occ = some A₁ ∧ Good t e) :=
            (hgood e (by simp [tapeExits])).imp id fun hg =>
              let ⟨C, _, hC, _⟩ := hg.typed
              ⟨by rw [← hvt C hC]; exact hC, hg⟩
          have hls := h'.ls
          cases hls with
          | app hf' hu' =>
            cases LS.unique hf hf'
            have hTloc : ∀ e' ∈ tapeExits T, IsLocal t e' := by
              rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
              · exact (htr (by simpa using h0)).top.1
              · exact fun e' he' => hloc (by simpa using hp) e' (by simp [tapeExits, he'])
            refine ⟨_, true, _, _, _, .arg h' hf' hu', hfitT, entries_cons.mpr ⟨hge, hent⟩,
              ?_, fun e' he' => hgood e' (by simp [tapeExits, he']), fun _ => hTloc,
              fun h0 => by simp at h0⟩
            rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
            · rw [List.eq_nil_of_length_eq_zero (by simpa [h0] using hlen : log.length = 0),
                topApp_arg_zero h0]
              exact logOK_single (htr (by simpa using h0)).top.2
            · rw [topApp_cons_pos hp]
              refine logOK_cons (hloc (by simpa using hp) e (by simp [tapeExits]))
                (logOK_addr_cons .fn (by simpa using hlen) hlog) fun h => ?_
              rw [h] at hlen
              simp at hlen
              omega
    | @arg a Δ₀ m₀ Γ₀ f u₂ A₁ B h' hf hu =>
      cases log with
      | nil => simp [pstep] at hs
      | cons e L =>
        simp only [pstep, PResult.next.injEq] at hs
        subst hs
        show InvOf t (.fn :: a) (.p e :: tape) L
        rw [entries_cons] at hent
        obtain ⟨hde, hentL⟩ := hent
        have hvt : ∀ C, varTy t e.occ = some C → C = A := by
          intro C hC
          rcases hde with hd | ⟨hv, _⟩
          · rw [varTy_of_none hd.1] at hC
            cases hC
          · exact Option.some.inj (hC.symm.trans hv)
        have hge : Dummy t e ∨ Good t e := hde.imp id (·.2)
        have hlenL : L.length = argDepth a := by simpa using hlen
        have htl : ∀ e' ∈ tapeExits tape, IsLocal t e' := hloc (by simp)
        refine ⟨Δ₀, m₀, Γ₀, f, _, .fn h' hf, .p hvt hfit, hentL, ?_, ?_, ?_, ?_⟩
        · rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
          · rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0)]
            exact logOK_nil
          · rw [topApp_cons_pos hp] at hlog ⊢
            exact logOK_drop 1 hlog
        · intro e' he'
          simp only [tapeExits, List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · exact hgood e' he'
          · exact hge
        · intro hp e' he'
          simp only [tapeExits, List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · exact htl e' he'
          · have hp' : 0 < argDepth a := by simpa using hp
            exact (hlog 0 _ rfl).1 (by simp only [List.length_cons]; omega)
        · intro h0
          have h0' : argDepth a = 0 := by simpa using h0
          have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil
          refine Transit.intro_p htl ?_
          have := (hlog 0 e rfl).2 rfl
          rw [topApp_arg_zero h0'] at this
          exact this

theorem inv_reach {t : Term} {s s' : PState} (hr : PReach t s s') : Inv t s → Inv t s' := by
  induction hr with
  | refl => exact id
  | head hs _ ih => exact fun h => ih (inv_step h hs)

theorem clear_of_inv {t : Term} {s : PState} (hinv : Inv t s) : s.Clear t := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | up a => simp [PState.Clear]
  | down a =>
    change InvOf t a tape log at hinv
    obtain ⟨Δ, m, Γ, u, A, hat, hfit, hent, hlog, hgood, hloc, htr⟩ := hinv
    have hsub := hat.sub
    cases u with
    | var i π =>
      simp only [PState.Clear, hsub]
      intro b hb
      obtain ⟨_, _, _, _, _, _, _, _, hvt, _⟩ := hat.var
      have htl : ∀ e ∈ tapeExits tape, IsLocal t e := by
        rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
        · exact (htr h0).local_at_var fun j => seek_var hsub j
        · exact hloc hp
      refine free_of_fits hfit hgood htl fun o ho => ?_
      rw [← hvt]
      simp [varTy, ho, hb]
    | lam A₁ body =>
      cases tape with
      | nil => simp [PState.Clear, hsub]
      | cons x T =>
        cases x with
        | q => simp [PState.Clear, hsub]
        | p e =>
          simp only [PState.Clear, hsub]
          have hls := hat.ls
          cases hls with
          | lam _ =>
            obtain ⟨_, hfitT⟩ := hfit.pop_p
            have hTloc : ∀ e' ∈ tapeExits T, IsLocal t e' := by
              rcases Nat.eq_zero_or_pos (argDepth a) with h0 | hp
              · exact (htr h0).top.1
              · exact fun e' he' => hloc hp e' (by simp [tapeExits, he'])
            refine free_of_fits hfitT (fun e' he' => hgood e' (by simp [tapeExits, he'])) hTloc
              fun o ho => ?_
            simp [varTy, ho, hsub]
    | app f u₂ => simp [PState.Clear, hsub]

/-- In the first run on a locally safe term, no exit to a lambda lies under the tape when
the token leaves for that lambda or comes back to it. -/
theorem firstRunClear : FirstRunClear :=
  fun _ _ h n _ hr => clear_of_inv (inv_reach hr (inv_first h n))

/-- (A) for the first run: on a locally safe term every return of the pointer machine is to
the newest exit to its lambda. -/
theorem firstRunLifo : FirstRunLifo :=
  firstRunLifo_of_clear firstRunClear

/-- On `share t`, for a locally safe `t`, the first run of the pointer machine never stops
because of the order of returns, and the token machine makes the same steps. -/
theorem first_run_share {t : Term} {A : Ty} (h : LocallySafe t A) {n : Nat} {s : PState}
    (hr : PReach (share t) (.first n) s) :
    pstep (share t) s ≠ .parted ∧
      Follows (share t) Stacks.empty s (pstep (share t) s) :=
  ⟨firstRunLifo _ A (share_safe h) n s hr, follows (share_distinct t) (share_apart t) _ s⟩

/-! ## Every run of readback

Readback runs the machine for each point of the result. A run for a point ends at the root
with a tape `W ++ p e :: qᵐ`, where `e` is the exit from the head variable of the point. The
runs for argument `i` of that variable start with the history that this run leaves and with
the tape `W ++ p e :: qⁱ ++ [p d]`, followed by `q`s; the exit `d` stands for the argument. -/

/-- The exit that readback puts on the tape for an argument of a head variable. -/
def Exit.outside : Exit := .mk [] []

/-- The number of arguments that a term of the type takes. -/
def Ty.arity : Ty → Nat
  | .o => 0
  | .arr _ B => B.arity + 1

/-- The tape (without its final `q`s) and the history with which the runs for a point of
readback start. Argument `i` of a head variable is a point only if the type of the variable
has that many arguments. -/
inductive Point (t : Term) : List Item → List Addr → Prop
  | root : Point t [] []
  | arg {U : List Item} {H : List Addr} {n : Nat} {s : PState} {W : List Item} {e : Exit}
      {m i : Nat} {H' : List Addr} {A : Ty} :
      Point t U H → PReach t ⟨.down [], U ++ List.replicate n .q, [], H⟩ s →
      pstep t s = .done (W ++ .p e :: List.replicate m .q) H' →
      varTy t e.occ = some A → i < A.arity →
      Point t (W ++ .p e :: (List.replicate i .q ++ [.p .outside])) H'

/-- (A): in every run of readback on a locally safe term, every return of the pointer
machine is to the newest exit to its lambda. -/
def ReadbackLifo : Prop :=
  ∀ (t : Term) (A : Ty), LocallySafe t A → ∀ (U : List Item) (H : List Addr), Point t U H →
    ∀ (n : Nat) (s : PState), PReach t ⟨.down [], U ++ List.replicate n .q, [], H⟩ s →
      pstep t s ≠ .parted

theorem binderOf_root (t : Term) : binderOf t [] = none := by
  cases t <;> simp [binderOf, Term.sub, binder]

theorem binderOf_outside (t : Term) : binderOf t Exit.outside.occ = none := binderOf_root t

theorem varTy_outside (t : Term) : varTy t Exit.outside.occ = none :=
  varTy_of_none (binderOf_root t)

theorem pstep_done {t : Term} {s : PState} {T : List Item} {H : List Addr}
    (h : pstep t s = .done T H) : s.pos = .up [] ∧ s.tape = T ∧ s.hist = H := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | down a =>
    cases hsub : t.sub a with
    | none => simp [pstep, hsub] at h
    | some u =>
      cases u with
      | var i π => cases hb : binder a i <;> simp [pstep, hsub, hb] at h
      | lam A body =>
        cases tape with
        | nil => simp [pstep, hsub] at h
        | cons x T' =>
          cases x with
          | q => simp [pstep, hsub] at h
          | p e =>
            by_cases hbe : binderOf t e.occ = some a
            · cases hpop : popNewest t a hist with
              | none => simp [pstep, hsub, hbe, hpop] at h
              | some r =>
                obtain ⟨o, H₂⟩ := r
                by_cases ho : o = e.occ <;> simp [pstep, hsub, hbe, hpop, ho] at h
            · simp [pstep, hsub, hbe] at h
      | app f u => simp [pstep, hsub] at h
  | up a =>
    cases a with
    | nil =>
      simp only [pstep, PResult.done.injEq] at h
      exact ⟨rfl, h.1, h.2⟩
    | cons d a =>
      cases d with
      | body => simp [pstep] at h
      | fn =>
        cases tape with
        | nil => simp [pstep] at h
        | cons x T' => cases x <;> simp [pstep] at h
      | arg => cases log <;> simp [pstep] at h

theorem tapeExits_append : ∀ (X Y : List Item), tapeExits (X ++ Y) = tapeExits Y ++ tapeExits X
  | [], Y => by simp [tapeExits]
  | .q :: X, Y => by simpa [tapeExits] using tapeExits_append X Y
  | .p e :: X, Y => by simp [tapeExits, tapeExits_append X Y]

theorem Fits.inv_q {t : Term} {A : Ty} {T : List Item} (h : Fits t A (.q :: T)) :
    (∃ k, T = List.replicate k .q) ∨ ∃ A₁ B, A = .arr A₁ B ∧ Fits t B T := by
  generalize hT : Item.q :: T = T' at h
  cases h with
  | qs n =>
    cases n with
    | zero => simp at hT
    | succ n =>
      rw [List.replicate_succ] at hT
      cases hT
      exact .inl ⟨n, rfl⟩
  | q h' =>
    cases hT
    exact .inr ⟨_, _, rfl, h'⟩
  | p _ _ => cases hT

theorem Fits.inv_p {t : Term} {A : Ty} {e : Exit} {T : List Item} (h : Fits t A (.p e :: T)) :
    ∃ A₁ B, A = .arr A₁ B ∧ (∀ C, varTy t e.occ = some C → C = A₁) ∧ Fits t A₁ T := by
  generalize hT : Item.p e :: T = T' at h
  cases h with
  | qs n =>
    cases n with
    | zero => simp at hT
    | succ n =>
      rw [List.replicate_succ] at hT
      cases hT
  | q _ => cases hT
  | p hv h' =>
    cases hT
    exact ⟨_, _, rfl, hv, h'⟩

/-- What lies below the lowest exit of a tape can be replaced by anything that fits the
type of that exit. -/
theorem fits_swap {t : Term} {e : Exit} {m : Nat} {X : List Item}
    (hX : ∀ A, (∀ C, varTy t e.occ = some C → C = A) → Fits t A X) :
    ∀ (W : List Item) {A : Ty}, Fits t A (W ++ .p e :: List.replicate m .q) →
      Fits t A (W ++ .p e :: X)
  | [], _, h => by
    obtain ⟨A₁, B, rfl, hv, _⟩ := h.inv_p
    exact .p hv (hX A₁ hv)
  | .q :: W, _, h => by
    rcases h.inv_q with ⟨k, hk⟩ | ⟨A₁, B, rfl, h'⟩
    · have hmem : Item.p e ∈ List.replicate k Item.q := by
        rw [← hk]
        simp
      simp [List.mem_replicate] at hmem
    · exact .q (fits_swap hX W h')
  | .p e₁ :: W, _, h => by
    obtain ⟨A₁, B, rfl, hv, h'⟩ := h.inv_p
    exact .p hv (fits_swap hX W h')

theorem fits_arg {t : Term} {d : Exit} (hd : ∀ C, varTy t d.occ ≠ some C) (n : Nat) :
    ∀ (i : Nat) {A : Ty}, i < A.arity →
      Fits t A (List.replicate i .q ++ .p d :: List.replicate n .q)
  | _, .o, h => by simp [Ty.arity] at h
  | 0, .arr _ _, _ => .p (fun C hC => absurd hC (hd C)) (.qs n)
  | i + 1, .arr _ _, h => .q (fits_arg hd n i (by simpa [Ty.arity] using h))

theorem split_first {e e₁ : Exit} {Y T' : List Item} : ∀ (j : Nat) (W : List Item),
    W ++ .p e :: Y = List.replicate j .q ++ .p e₁ :: T' →
      (∃ W₁, W = List.replicate j .q ++ .p e₁ :: W₁ ∧ T' = W₁ ++ .p e :: Y) ∨
        (W = List.replicate j .q ∧ e₁ = e ∧ T' = Y)
  | 0, [], h => by
    simp only [List.nil_append, List.replicate_zero, List.cons.injEq, Item.p.injEq] at h
    exact .inr ⟨rfl, h.1.symm, h.2.symm⟩
  | 0, x :: W, h => by
    simp only [List.cons_append, List.replicate_zero, List.nil_append, List.cons.injEq] at h
    exact .inl ⟨W, by simp [h.1], h.2.symm⟩
  | j + 1, [], h => by simp [List.replicate_succ] at h
  | j + 1, x :: W, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rcases split_first j W h with ⟨W₁, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact .inl ⟨W₁, by simp [List.replicate_succ], rfl⟩
    · exact .inr ⟨by simp [List.replicate_succ], rfl, rfl⟩

/-- What lies below the lowest exit of a tape can be replaced by anything without exits of
global variables. -/
theorem transit_swap {t : Term} {a : Addr} {W : List Item} {e : Exit} {m : Nat}
    {X : List Item} (hX : ∀ e' ∈ tapeExits X, IsLocal t e')
    (h : Transit t a (W ++ .p e :: List.replicate m .q)) : Transit t a (W ++ .p e :: X) := by
  obtain ⟨j, R, hT, hR⟩ := h
  rcases hR with rfl | ⟨e₁, T', rfl, hl, hk⟩
  · have hmem : e ∈ tapeExits (W ++ .p e :: List.replicate m .q) := by
      simp [tapeExits_append, tapeExits]
    rw [hT] at hmem
    simp [tapeExits_replicate] at hmem
  · rcases split_first j W hT with ⟨W₁, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨j, .p e₁ :: (W₁ ++ .p e :: X), by simp, .inr ⟨e₁, _, rfl, fun e' he' => ?_, hk⟩⟩
      simp only [tapeExits_append, tapeExits, List.mem_append, List.mem_singleton] at he'
      rcases he' with (he' | rfl) | he'
      · exact hX e' he'
      · exact hl _ (by simp [tapeExits_append, tapeExits])
      · exact hl e' (by simp [tapeExits_append, tapeExits, he'])
    · exact ⟨j, .p e₁ :: X, rfl, .inr ⟨e₁, X, rfl, hX, hk⟩⟩

/-- The invariant and the agreement of the history hold where the runs for a point start. -/
theorem point_inv {t : Term} {A : Ty} (h : LocallySafe t A) {U : List Item} {H : List Addr}
    (hp : Point t U H) : ∀ n : Nat,
      Inv t ⟨.down [], U ++ List.replicate n .q, [], H⟩ ∧
        Agree t ⟨.down [], U ++ List.replicate n .q, [], H⟩ := by
  induction hp with
  | root => exact fun n => ⟨inv_first h n, agree_first t n⟩
  | @arg U H n₀ s W e m i H' A₁ _ hr hdone hvt hi ih =>
    intro n
    obtain ⟨hinv₀, hagr₀⟩ := ih n₀
    have hinv := inv_reach hr hinv₀
    have hagr := agree_reach hr hagr₀ fun u hu => clear_of_inv (inv_reach hu hinv₀)
    obtain ⟨pos, tape, log, hist⟩ := s
    have hd := pstep_done hdone
    dsimp only at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    change InvOf t [] (W ++ .p e :: List.replicate m .q) log at hinv
    obtain ⟨Δ, mm, Γ, u, A₂, hat, hfit, hent, hlog, hgood, hloc, htr⟩ := hinv
    have hlog0 : log = [] :=
      List.eq_nil_of_length_eq_zero (by rw [← hent.length, hat.depth]; rfl)
    subst hlog0
    have htape : (W ++ .p e :: (List.replicate i .q ++ [.p .outside])) ++ List.replicate n .q =
        W ++ .p e :: (List.replicate i .q ++ .p .outside :: List.replicate n .q) := by
      simp
    rw [htape]
    have hX : tapeExits (List.replicate i Item.q ++ .p .outside :: List.replicate n .q) =
        [Exit.outside] := by
      simp [tapeExits_replicate_append, tapeExits, tapeExits_replicate]
    have hold : tapeExits (W ++ .p e :: List.replicate m .q) = e :: tapeExits W := by
      simp [tapeExits_append, tapeExits, tapeExits_replicate]
    have hnew : tapeExits
        (W ++ .p e :: (List.replicate i .q ++ .p .outside :: List.replicate n .q)) =
        Exit.outside :: e :: tapeExits W := by
      simp [tapeExits_append, tapeExits, hX]
    have hout : ∀ b, binderOf t Exit.outside.occ ≠ some b := fun b hb => by
      rw [binderOf_outside] at hb
      cases hb
    refine ⟨?_, ?_⟩
    · show InvOf t [] _ []
      refine ⟨Δ, mm, Γ, u, A₂, hat, ?_, hent, logOK_nil, ?_, fun hp => by simp at hp,
        fun _ => ?_⟩
      · refine fits_swap (fun A' hA' => ?_) W hfit
        cases hA' A₁ hvt
        exact fits_arg (fun C hC => by rw [varTy_outside] at hC; cases hC) n i hi
      · intro e' he'
        rw [hnew] at he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact .inl ⟨binderOf_outside t, rfl⟩
        · exact hgood e' (by rw [hold]; exact he')
      · refine transit_swap (fun e' he' => ?_) (htr rfl)
        rw [hX] at he'
        simp only [List.mem_singleton] at he'
        subst he'
        exact fun β hβ => absurd hβ (hout β)
    · intro b
      have hb := hagr b
      simp only [PState.live, hold, Exit.trees_nil, List.append_nil] at hb
      simp only [PState.live, hnew, Exit.trees_cons Exit.outside,
        show Exit.outside.saved = [] from rfl, Exit.trees_nil, List.nil_append, List.append_nil,
        List.map_cons]
      rw [boundBy_cons_ne (hout b)]
      exact hb

/-- (A) for every run of readback. -/
theorem readbackLifo : ReadbackLifo := by
  intro t A h U H hp n s hr
  obtain ⟨hinv, hagr⟩ := point_inv h hp n
  have hc : ∀ u, PReach t ⟨.down [], U ++ List.replicate n .q, [], H⟩ u → u.Clear t :=
    fun u hu => clear_of_inv (inv_reach hu hinv)
  exact (agree_step (agree_reach hr hagr hc) (hc s hr)).1

/-- On `share t`, for a locally safe `t`, no run of readback stops because of the order of
returns, and the token machine makes the same steps. -/
theorem readback_share {t : Term} {A : Ty} (h : LocallySafe t A) {U : List Item}
    {H : List Addr} (hp : Point (share t) U H) {n : Nat} {s : PState}
    (hr : PReach (share t) ⟨.down [], U ++ List.replicate n .q, [], H⟩ s) :
    pstep (share t) s ≠ .parted ∧
      Follows (share t) Stacks.empty s (pstep (share t) s) :=
  ⟨readbackLifo _ A (share_safe h) U H hp n s hr,
    follows (share_distinct t) (share_apart t) _ s⟩

end LSL
